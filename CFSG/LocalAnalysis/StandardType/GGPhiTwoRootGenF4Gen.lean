module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Cover
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Rat
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenLayer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4Two
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenSL
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.RootSpanInter
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LieType.Chevalley.F4FieldTwoEuclid
public import CFSG.LieType.Chevalley.CLSEvenCoordinateFieldsFourGroup
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcCore
public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenOmit
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenGen
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.HardMathSupport.Lang.AnisoF4.B4PlanesEven

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem hrat_F4
    {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∀ X : Subgroup (ModGL .F4 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .F4 (AlgebraicClosure K) →
        (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
          X ≤ (adjointGroup .F4 K).map
            (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  intro X _ hX hfix x hx
  exact mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr (hX hx) (hfix x hx)

open CFSG.LieType.Steinberg.Adjoint

private theorem symmetrizedCartan_apply_F4 (i j : Fin Tag.F4.rank) :
    Tag.F4.symmetrizedCartan i j = Tag.F4.symmetrizer i i * Tag.F4.cartan i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem symmetrizedCartan_symm_F4 (i j : Fin Tag.F4.rank) :
    Tag.F4.symmetrizedCartan i j = Tag.F4.symmetrizedCartan j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem iform_single_left_F4 (i : Fin Tag.F4.rank) (y : Fin Tag.F4.rank → ℤ) :
    iform (Pi.single i 1) y =
      Tag.F4.symmetrizer i i * ∑ j, Tag.F4.cartan i j * y j := by
  simp only [iform, Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_apply_F4, if_pos rfl]
  ring

private theorem sum_cartan_mul_single_F4 (i : Fin Tag.F4.rank) :
    ∑ j, Tag.F4.cartan i j * (Pi.single i 1 : Fin Tag.F4.rank → ℤ) j = 2 := by
  fin_cases i <;> decide

private theorem iform_single_single_F4 (i : Fin Tag.F4.rank) :
    iform (Pi.single i 1) (Pi.single i 1) = 2 * Tag.F4.symmetrizer i i := by
  rw [iform_single_left_F4, sum_cartan_mul_single_F4]
  ring

private theorem iform_comm_F4 (x y : Fin Tag.F4.rank → ℤ) : iform x y = iform y x := by
  simp only [iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_symm_F4 j i]
  ring

private theorem iform_add_left_F4 (x x' y : Fin Tag.F4.rank → ℤ) :
    iform (x + x') y = iform x y + iform x' y := by
  simp [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem iform_smul_left_F4 (c : ℤ) (x y : Fin Tag.F4.rank → ℤ) :
    iform (c • x) y = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem iform_sub_left_F4 (x x' y : Fin Tag.F4.rank → ℤ) :
    iform (x - x') y = iform x y - iform x' y := by
  rw [sub_eq_add_neg, iform_add_left_F4, ← neg_one_smul ℤ x', iform_smul_left_F4]
  ring

private theorem iform_sub_right_F4 (x y y' : Fin Tag.F4.rank → ℤ) :
    iform x (y - y') = iform x y - iform x y' := by
  rw [iform_comm_F4, iform_sub_left_F4, iform_comm_F4 y, iform_comm_F4 y']

private theorem iform_smul_right_F4 (c : ℤ) (x y : Fin Tag.F4.rank → ℤ) :
    iform x (c • y) = c * iform x y := by
  rw [iform_comm_F4, iform_smul_left_F4, iform_comm_F4]

private theorem iform_single_right_F4 (x : Fin Tag.F4.rank → ℤ) (i : Fin Tag.F4.rank) :
    iform x (Pi.single i 1) =
      Tag.F4.symmetrizer i i * ∑ j, Tag.F4.cartan i j * x j := by
  rw [iform_comm_F4, iform_single_left_F4]

private theorem iform_reflect_F4 (i : Fin Tag.F4.rank) (x y : Fin Tag.F4.rank → ℤ) :
    iform (reflect .F4 i x) (reflect .F4 i y) = iform x y := by
  have hx : reflect .F4 i x = x - (∑ j, Tag.F4.cartan i j * x j) • Pi.single i 1 := rfl
  have hy : reflect .F4 i y = y - (∑ j, Tag.F4.cartan i j * y j) • Pi.single i 1 := rfl
  rw [hx, hy, iform_sub_left_F4, iform_sub_right_F4, iform_sub_right_F4,
    iform_smul_left_F4, iform_smul_left_F4, iform_smul_right_F4, iform_smul_right_F4,
    iform_single_single_F4, iform_single_left_F4, iform_single_right_F4]
  ring

private theorem iform_smul_F4 (w : WeylGroup .F4) (x y : Fin Tag.F4.rank → ℤ) :
    iform (w • x) (w • y) = iform x y := by
  induction w using (coxeterSystem .F4).simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul, simple_smul, simple_smul,
      iform_reflect_F4 i (w • x) (w • y), ih]

private theorem corootPair_smul_single_F4 (w : WeylGroup .F4) (j : Fin Tag.F4.rank)
    (v : Fin Tag.F4.rank → ℤ) :
    corootPair (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) v =
      ∑ k, Tag.F4.cartan j k * (w⁻¹ • v) k := by
  have e1 : iform (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))
      (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) = 2 * Tag.F4.symmetrizer j j := by
    rw [iform_smul_F4, iform_single_single_F4]
  have e2 : iform (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) v =
      Tag.F4.symmetrizer j j * ∑ k, Tag.F4.cartan j k * (w⁻¹ • v) k := by
    rw [← smul_inv_smul w v, iform_smul_F4, iform_single_left_F4, inv_smul_smul]
  have hd : (2 * Tag.F4.symmetrizer j j : ℤ) ≠ 0 := by
    have hpos : 0 < Tag.F4.symmetrizer j j := by fin_cases j <;> decide
    omega
  rw [corootPair, e1, e2]
  rw [show 2 * (Tag.F4.symmetrizer j j * ∑ k, Tag.F4.cartan j k * (w⁻¹ • v) k) =
      (2 * Tag.F4.symmetrizer j j) * ∑ k, Tag.F4.cartan j k * (w⁻¹ • v) k by ring]
  exact Int.mul_ediv_cancel_left _ hd

private theorem rootReflection_smul_F4 {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (v : Fin Tag.F4.rank → ℤ) :
    rootReflection β • v = v - corootPair β v • β := by
  have hspec := Classical.choose_spec (Classical.choose_spec (isRoot_iff_exists_smul_single.1 hβ))
  simp only [rootReflection, hβ, ↓reduceDIte]
  rw [smul_conj_simple, ← corootPair_smul_single_F4, hspec]

private theorem rootReflection_eq_conj_F4 {β : Fin Tag.F4.rank → ℤ} {w : WeylGroup .F4}
    {j : Fin Tag.F4.rank} (h : w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = β) :
    rootReflection β = w * simple .F4 j * w⁻¹ := by
  have hβ : IsRoot .F4 β := h ▸ IsRoot.smul (isRoot_single .F4 j) w
  refine ext_single fun i => ?_
  rw [rootReflection_smul_F4 hβ, smul_conj_simple, ← corootPair_smul_single_F4, h]

private theorem exists_cartan_ne_zero_F4 (i : Fin Tag.F4.rank) :
    ∃ j : Fin Tag.F4.rank, j ≠ i ∧ Tag.F4.cartan j i ≠ 0 := by
  fin_cases i
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

private theorem reflect_single_F4 {i j : Fin Tag.F4.rank} :
    reflect .F4 j (Pi.single i 1) =
      Pi.single i 1 - (Tag.F4.cartan j i) • Pi.single j 1 := by
  rw [reflect, Finset.sum_eq_single i
    (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem exists_isRoot_smul_ne_F4
    {δ : Fin Tag.F4.rank → ℤ} (hδ : IsRoot .F4 δ) :
    ∃ ε : Fin Tag.F4.rank → ℤ, IsRoot .F4 ε ∧ ε ≠ δ ∧ ε ≠ -δ ∧ rootReflection ε • δ ≠ δ ∧
      rootReflection ε • δ ≠ -δ := by
  obtain ⟨u, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hδ
  let δ : Fin Tag.F4.rank → ℤ := u • (Pi.single i 1 : Fin Tag.F4.rank → ℤ)
  change ∃ ε : Fin Tag.F4.rank → ℤ, IsRoot .F4 ε ∧ ε ≠ δ ∧ ε ≠ -δ ∧
    rootReflection ε • δ ≠ δ ∧ rootReflection ε • δ ≠ -δ
  obtain ⟨j, hji, hcart⟩ := exists_cartan_ne_zero_F4 i
  let ε : Fin Tag.F4.rank → ℤ := u • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)
  have hε : IsRoot .F4 ε := by
    dsimp [ε]
    exact IsRoot.smul (IsRoot.basis j) u
  have hεeq : rootReflection ε • δ =
      u • (Pi.single i 1 - (Tag.F4.cartan j i) • Pi.single j 1) := by
    have hr : rootReflection ε = u * simple .F4 j * u⁻¹ :=
      rootReflection_eq_conj_F4 (w := u) (j := j) rfl
    rw [hr]
    dsimp [δ]
    rw [mul_smul, mul_smul, inv_smul_smul, simple_smul, reflect_single_F4]
  have hcancel : ∀ {v v' : Fin Tag.F4.rank → ℤ}, u • v = u • v' → v = v' := by
    intro v v' h
    simpa using congrArg (fun x => u⁻¹ • x) h
  have hεneδ : ε ≠ δ := by
    intro h
    have h' : (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = Pi.single i 1 := by
      apply hcancel
      simpa [ε, δ] using h
    have hj := congrFun h' j
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hji] at hj
    exact one_ne_zero hj
  have hεnenδ : ε ≠ -δ := by
    intro h
    have h' : (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = -Pi.single i 1 := by
      apply hcancel
      simpa [ε, δ] using h
    have hj := congrFun h' j
    simp only [Pi.single_eq_same, Pi.neg_apply, Pi.single_eq_of_ne hji, neg_zero] at hj
    exact one_ne_zero hj
  have hrεδ_ne : rootReflection ε • δ ≠ δ := by
    intro h
    have h' : (Pi.single i 1 - (Tag.F4.cartan j i) • Pi.single j 1 :
        Fin Tag.F4.rank → ℤ) = Pi.single i 1 := by
      apply hcancel
      simpa [δ] using hεeq.symm.trans h
    have hc0 : Tag.F4.cartan j i = 0 := by
      have hj := congrFun h' j
      simp [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji] at hj
      omega
    exact hcart hc0
  have hrεδ_ne_neg : rootReflection ε • δ ≠ -δ := by
    intro h
    have h' : (Pi.single i 1 - (Tag.F4.cartan j i) • Pi.single j 1 :
        Fin Tag.F4.rank → ℤ) = -Pi.single i 1 := by
      apply hcancel
      have hh : rootReflection ε • δ =
          u • (-Pi.single i 1 : Fin Tag.F4.rank → ℤ) := by
        simpa [δ] using h
      exact hεeq.symm.trans hh
    have hi := congrFun h' i
    rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hji),
      Pi.neg_apply, Pi.single_eq_same] at hi
    norm_num at hi
  exact ⟨ε, hε, hεneδ, hεnenδ, hrεδ_ne, hrεδ_ne_neg⟩

theorem iSup_phiTwoComp_ne_F4
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup .F4} (hcent : ∀ v : WeylGroup .F4, v * w = w * v)
    (hneg : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ → w • γ = -γ)
    {g0 : ModGL .F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    (j : {α : Fin Tag.F4.rank → ℤ // IsRoot .F4 α}) :
    (⨆ (i : {α : Fin Tag.F4.rank → ℤ // IsRoot .F4 α})
        (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl j.1),
      phiTwoComp g0 i.1) = ⊤ := by
  have htop : (⨆ γ : {γ : Fin Tag.F4.rank → ℤ // IsRoot .F4 γ}, phiTwoComp g0 γ.1) = ⊤ :=
    iSup_phiTwoComp_eq_top_F4 hK4 hFr hneg hg0C hg0
  have hweyl : ∀ ε, IsRoot .F4 ε → ∃ n ∈ phiTwoComp g0 ε, ∀ γ, IsRoot .F4 γ →
      (phiTwoComp g0 γ).map (MulAut.conj n).toMonoidHom =
        phiTwoComp g0 (rootReflection ε • γ) := by
    intro ε hε
    obtain ⟨n, hn, hnbase⟩ := exists_phiTwoWeyl (hrat_F4 hFr) hcent hg0C hg0 hε
    refine ⟨n, hn, fun γ hγ => ?_⟩
    exact map_conj_phiTwoComp (g0 := g0) (v := rootReflection ε) (n := n) hnbase hγ
  have hsep : ∀ α β, IsRoot .F4 α → IsRoot .F4 β →
      ExcSplitRootGen.excRefl (p := p) α = ExcSplitRootGen.excRefl β → β = α ∨ β = -α :=
    fun α β hα hβ h =>
      eq_or_eq_neg_of_excRefl_eq_excRefl (τ := .F4) (Or.inr (Or.inr (Or.inr rfl))) hp2 hα hβ h
  have hne : ∀ δ, IsRoot .F4 δ → ∃ ε, IsRoot .F4 ε ∧ ε ≠ δ ∧ ε ≠ -δ ∧
      rootReflection ε • δ ≠ δ ∧ rootReflection ε • δ ≠ -δ :=
    fun δ hδ => exists_isRoot_smul_ne_F4 hδ
  exact iSup_excRefl_ne_eq_top (J := fun γ => phiTwoComp g0 γ) hweyl hsep hne htop j

end CFSG.StandardType.PhiTwoRootGen

end
