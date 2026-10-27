module

public import CFSG.LocalAnalysis.StandardType.GGTBRowF4FrameAux
public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Core
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4CoreAux
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTorus
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGLargeRowCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Multiplicative
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LieType.SeitzGeneration CFSG.RankThree.CentralCover

private theorem ggWTF4_congr_trans {G H I : Type} [Group G] [Group H] [Group I]
    (f : G ≃* H) (g : H ≃* I) (u : MulAut G) :
    MulAut.congr (f.trans g) u = MulAut.congr g (MulAut.congr f u) := by
  ext x
  simp only [ggMulAut_congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]

private theorem ggWTF4_congr_congr_symm {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (f : MulAut H) : MulAut.congr e (MulAut.congr e.symm f) = f := by
  ext x
  simp only [ggMulAut_congr_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply]

private theorem ggWTF4_induced_eq_automizer
    {p : ℕ} {R : Type} [Group R] {k : ℕ}
    {τ : Multiplicative (Fin k → ZMod p) →* R} {E : Subgroup R}
    (θ : Multiplicative (Fin k → ZMod p) ≃* ↥E)
    (hθ : ∀ f, (θ f : R) = τ f) :
    (ggTorusInduced τ).map (MulAut.congr θ).toMonoidHom = ggAutomizer ⊤ E := by
  have hrange : τ.range = E := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      show τ f ∈ E
      rw [← hθ f]
      exact (θ f).2
    · intro hx
      obtain ⟨f, hf⟩ := θ.surjective ⟨x, hx⟩
      exact ⟨f, by rw [← hθ f, hf]⟩
  apply le_antisymm
  · rintro u ⟨v, hv, rfl⟩
    obtain ⟨g, hg⟩ := mem_ggTorusInduced.mp hv
    refine Subgroup.subset_closure ⟨g, Subgroup.mem_top g, ?_, fun x => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← hrange] at hx ⊢
        obtain ⟨f, rfl⟩ := hx
        exact ⟨v f, (hg f).symm⟩
      · intro hx
        rw [← hrange] at hx ⊢
        obtain ⟨f, hf⟩ := hx
        refine ⟨v⁻¹ f, ?_⟩
        have h1 := hg (v⁻¹ f)
        rw [MulAut.apply_inv_self] at h1
        exact mul_left_cancel (mul_right_cancel (h1.trans hf))
    · obtain ⟨f, rfl⟩ := θ.surjective x
      change ((MulAut.congr θ v) (θ f) : R) = g * (θ f : R) * g⁻¹
      rw [ggMulAut_congr_apply, MulEquiv.symm_apply_apply, hθ (v f), hθ f]
      exact (hg f).symm
  · rw [ggAutomizer, Subgroup.closure_le]
    rintro φ ⟨g, -, hgN, hφ⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.congr θ.symm φ, mem_ggTorusInduced.mpr ⟨g, fun f => ?_⟩,
      ggWTF4_congr_congr_symm θ φ⟩
    have h1 : (φ (θ f) : R) = g * τ f * g⁻¹ := by
      simpa only [hθ f] using hφ (θ f)
    have h2 : (θ (MulAut.congr θ.symm φ f) : R) = (φ (θ f) : R) := by
      rw [ggMulAut_congr_apply, MulEquiv.symm_symm]
      exact congrArg Subtype.val (MulEquiv.apply_symm_apply θ (φ (θ f)))
    rw [← h1, ← h2]
    exact hθ _

theorem ggWTF4_coordFrameElt_adjointF4
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGTorusCoordFrameElt p 4 (adjointGroup .F4 K) CoxeterMatrix.F₄ := by
  intro E hE hr _ k τ hτ hτE
  have hcardE : Nat.card E = p ^ 4 := F4AutWeyl.card_eq_pow_four_of_le hp hp2 hE hr
  have hcardτ : Nat.card (Multiplicative (Fin k → ZMod p)) = Nat.card E :=
    Nat.card_congr ((MonoidHom.ofInjective hτ).trans (MulEquiv.subgroupCongr hτE))
  have hk : k = 4 := Nat.pow_right_injective hp.two_le (by
    show p ^ k = p ^ 4
    rw [← CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod k, hcardτ, hcardE])
  subst hk
  haveI : Fact p.Prime := ⟨hp⟩
  let L := FiniteField.Extension K 2 2
  have hLK : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hpL : p ∣ Nat.card L - 1 :=
    hLK ▸ F4AutWeyl.dvd_card_sq_sub_one_of_card_F4 hp hp2 hE hcardE
  obtain ⟨ψ, hψinj, hEV, hcos⟩ := F4AutWeyl.exists_descent_F4 hp hp2 hE hcardE
  have hW : ∀ w : WeylGroup .F4, ∃ h ∈ (⊤ : Subgroup (adjointGroup .F4 K)).map ψ,
      ∃ t ∈ torusGroup .F4 L,
        (h : ModGL .F4 L) = t * canonicalRep (coxeterSystem .F4) L w := by
    intro w
    obtain ⟨k', t, ht, hkt⟩ := hcos w
    exact ⟨ψ k', ⟨k', Subgroup.mem_top k', rfl⟩, t, ht, hkt⟩
  have hA := F4AutWeyl.ggAutomizer_torusPow_eq_range hp hp2 hpL hW
  rw [F4AutWeyl.ggAutomizer_map_eq hψinj ⊤ E hEV] at hA
  let θ : Multiplicative (Fin 4 → ZMod p) ≃* ↥E :=
    (MonoidHom.ofInjective hτ).trans (MulEquiv.subgroupCongr hτE)
  have hθ : ∀ f, (θ f : adjointGroup .F4 K) = τ f := fun f => rfl
  have hEq := ggWTF4_induced_eq_automizer θ hθ
  let e : ↥E ≃* ↥(TableBF4.torusPow L p) :=
    (E.equivMapOfInjective ψ hψinj).trans (MulEquiv.subgroupCongr hEV)
  have hcinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  let wA : ↥(ggAutomizer ⊤ E) ≃* ↥(F4AutWeyl.weylTorusAut L p).range :=
    (Subgroup.equivMapOfInjective (ggAutomizer ⊤ E) (MulAut.congr e).toMonoidHom hcinj).trans
      (MulEquiv.subgroupCongr hA)
  let Φw : WeylGroup .F4 ≃* ↥(ggAutomizer ⊤ E) :=
    (MonoidHom.ofInjective (F4AutWeyl.weylTorusAut_injective hp hp2 hpL)).trans wA.symm
  have hwA : ∀ x : ↥(ggAutomizer ⊤ E),
      (wA x : MulAut ↥(TableBF4.torusPow L p)) = MulAut.congr e (x : MulAut ↥E) := by
    intro x
    rfl
  have hΦw : ∀ w, MulAut.congr e (Φw w : MulAut ↥E) =
      F4AutWeyl.weylTorusAut L p w := by
    intro w
    have h1 : wA (Φw w) = (⟨F4AutWeyl.weylTorusAut L p w, ⟨w, rfl⟩⟩ :
        ↥(F4AutWeyl.weylTorusAut L p).range) := by
      change wA (wA.symm ((MonoidHom.ofInjective
        (F4AutWeyl.weylTorusAut_injective hp hp2 hpL)) w)) = _
      rw [wA.apply_symm_apply]
      exact Subtype.ext rfl
    have h2 := congrArg (fun z : ↥(F4AutWeyl.weylTorusAut L p).range =>
      (z : MulAut ↥(TableBF4.torusPow L p))) h1
    rw [hwA (Φw w)] at h2
    exact h2
  let Φ0 : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer ⊤ E) :=
    ggF4Row_coxeterGroupEquiv.trans Φw
  have hΦ0 : ∀ i, MulAut.congr e (Φ0 (CoxeterMatrix.F₄.simple i) : MulAut ↥E) =
      F4AutWeyl.weylTorusAut L p (simple .F4 i) := by
    intro i
    have h3 : (Φ0 (CoxeterMatrix.F₄.simple i) : MulAut ↥E) =
        (Φw (simple .F4 i) : MulAut ↥E) := by
      have h3' : Φ0 (CoxeterMatrix.F₄.simple i) = Φw (simple .F4 i) := by
        change ggF4Row_coxeterGroupEquiv.trans Φw (CoxeterMatrix.F₄.simple i) = _
        rw [MulEquiv.trans_apply]
        exact congrArg Φw (ggF4Row_coxeterGroupEquiv_simple i)
      exact congrArg (fun z : ↥(ggAutomizer ⊤ E) => (z : MulAut ↥E)) h3'
    rw [h3]
    exact hΦw (simple .F4 i)
  let cθ : MulAut (Multiplicative (Fin 4 → ZMod p)) →* MulAut ↥E :=
    (MulAut.congr θ).toMonoidHom
  have hcθinj : Function.Injective cθ := (MulAut.congr θ).injective
  let Ψ : ↥(ggTorusInduced τ) ≃* ↥(ggAutomizer ⊤ E) :=
    (Subgroup.equivMapOfInjective (ggTorusInduced τ) cθ hcθinj).trans
      (MulEquiv.subgroupCongr hEq)
  let Φ : CoxeterMatrix.F₄.Group ≃* ↥(ggTorusInduced τ) := Φ0.trans Ψ.symm
  have hΦ : ∀ i, MulAut.congr (θ.trans e) (Φ (CoxeterMatrix.F₄.simple i) :
      MulAut (Multiplicative (Fin 4 → ZMod p))) =
      F4AutWeyl.weylTorusAut L p (simple .F4 i) := by
    intro i
    have h2 : MulAut.congr θ (Φ (CoxeterMatrix.F₄.simple i) :
        MulAut (Multiplicative (Fin 4 → ZMod p))) =
        (Φ0 (CoxeterMatrix.F₄.simple i) : MulAut ↥E) := by
      have h1 : Ψ (Φ (CoxeterMatrix.F₄.simple i)) = Φ0 (CoxeterMatrix.F₄.simple i) :=
        Ψ.apply_symm_apply _
      exact congrArg (fun z : ↥(ggAutomizer ⊤ E) => (z : MulAut ↥E)) h1
    rw [ggWTF4_congr_trans θ e (Φ (CoxeterMatrix.F₄.simple i)), h2]
    exact hΦ0 i
  refine ⟨fun i => (Φ (CoxeterMatrix.F₄.simple i) :
    MulAut (Multiplicative (Fin 4 → ZMod p))), fun i => ?_, Φ, fun i => rfl⟩
  have hs_ind : (Φ (CoxeterMatrix.F₄.simple i) :
      MulAut (Multiplicative (Fin 4 → ZMod p))) ∈ ggTorusInduced τ :=
    (Φ (CoxeterMatrix.F₄.simple i)).2
  have hs_refl : GGIsReflection p (F4AutWeyl.weylTorusAut L p (simple .F4 i)) :=
    F4AutWeyl.isReflection_weylTorusAut_simple hp hp2 hpL i
  have hsq : (Φ (CoxeterMatrix.F₄.simple i) :
      MulAut (Multiplicative (Fin 4 → ZMod p))) ^ 2 = 1 := by
    apply (MulAut.congr (θ.trans e)).injective
    rw [map_pow, hΦ i, hs_refl.1, map_one]
  have hfix : Nat.card {f : Multiplicative (Fin 4 → ZMod p) //
      (Φ (CoxeterMatrix.F₄.simple i) :
        MulAut (Multiplicative (Fin 4 → ZMod p))) f = f} * p =
      Nat.card (Multiplicative (Fin 4 → ZMod p)) := by
    have hf : ∀ f : Multiplicative (Fin 4 → ZMod p),
        (θ.trans e) ((Φ (CoxeterMatrix.F₄.simple i) :
          MulAut (Multiplicative (Fin 4 → ZMod p))) f) =
          F4AutWeyl.weylTorusAut L p (simple .F4 i) ((θ.trans e) f) := by
      intro f
      have h := DFunLike.congr_fun (hΦ i) ((θ.trans e) f)
      rwa [ggMulAut_congr_apply, MulEquiv.symm_apply_apply] at h
    have h1 : Nat.card {f : Multiplicative (Fin 4 → ZMod p) //
        (Φ (CoxeterMatrix.F₄.simple i) :
          MulAut (Multiplicative (Fin 4 → ZMod p))) f = f} =
        Nat.card {v : ↥(TableBF4.torusPow L p) //
          F4AutWeyl.weylTorusAut L p (simple .F4 i) v = v} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (θ.trans e).toEquiv fun f => ?_)
      rw [(θ.trans e).injective.eq_iff.symm, hf]
      rfl
    rw [h1, hs_refl.2]
    exact (Nat.card_congr (θ.trans e).toEquiv).symm
  exact ⟨hsq, hfix, mem_ggTorusInduced.mp hs_ind⟩

theorem ggWTF4_weylTypeW_of_frame {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hcard : Nat.card M.Group ≠ 12) (hF : GGTorusWeylFrameW p r R I M) :
    GGTorusWeylTypeW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨n, hn, hweyl, hrefl, e, he⟩ := hF L' ψ A hA
  refine ⟨ι, M, e, hM, ?_, fun i => ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact hcard
  · rw [he i]
    exact ⟨n i, hn i, hweyl i, rfl, hrefl i⟩

theorem ggWTF4_weylFrameW_F4_three
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGTorusWeylFrameW 3 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) CoxeterMatrix.F₄ :=
  ggTorusWeylFrameW_of_coordFrameElt Nat.prime_three (by norm_num)
    (TableBF4.idImage_subset_inn K) (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all Nat.prime_three (by norm_num)))
    (ggTorusCoordFrameElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggWTF4_coordFrameElt_adjointF4 (K := K) Nat.prime_three (by norm_num)))

theorem ggWTF4_weylTypeW_F4_three
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGTorusWeylTypeW 3 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggWTF4_weylTypeW_of_frame (M := CoxeterMatrix.F₄)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)))))
    (by rw [l04fFRC_ord_card_coxeterF4]; norm_num) ggWTF4_weylFrameW_F4_three

end CFSG.StandardType

end
