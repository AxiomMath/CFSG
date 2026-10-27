module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGExcPlusFrameModelOn (τ : Tag) (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (ι : Multiplicative (Fin τ.rank → ZMod p) →* R) (m : Fin τ.rank → R),
      Function.Injective ι ∧ ι.range = E ∧
      (∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p), m i * ι (Multiplicative.ofAdd s) * (m i)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s))) ∧
      ∀ g ∈ Subgroup.normalizer (E : Set R), ∃ u : WeylGroup τ,
        ∀ s : Fin τ.rank → ZMod p, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
          ι (Multiplicative.ofAdd (TableBExc.torusAct τ p u s))

theorem ggExcPlusWeylModelSCr_of_frameModelOn {τ : Tag} {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGExcPlusFrameModelOn τ p r R) :
    GGExcPlusWeylModelSCr τ p r R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, -, hsc⟩ := hA
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨l, rfl⟩ := hψ x
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  obtain ⟨ι, m, hιinj, hιrange, hm, hnormE⟩ :=
    h E hEab (by rw [hcardE]; exact hr) hscE
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set R) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2 : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2
  have hweyl : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n := by
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  have hιE : ∀ x, ι x ∈ E := fun x => hιrange ▸ ⟨x, rfl⟩
  let θ : Multiplicative (Fin τ.rank → ZMod p) →* A :=
    { toFun := fun x => ⟨Λ (ι x), hιE x⟩
      map_one' := Subtype.ext (show Λ (ι 1) = 1 by rw [map_one, map_one])
      map_mul' := fun x y => Subtype.ext (show Λ (ι (x * y)) = Λ (ι x) * Λ (ι y) by
        rw [map_mul, map_mul]) }
  have hθ : ∀ x, ((θ x : A) : MulAut L') = Λ (ι x) := fun _ => rfl
  have hθbij : Function.Bijective θ := by
    refine ⟨fun x y hxy => hιinj (hΛinj (congrArg Subtype.val hxy)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hιrange] at heE
    obtain ⟨x, rfl⟩ := heE
    exact ⟨x, Subtype.ext he⟩
  let Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p) := (MulEquiv.ofBijective θ hθbij).symm
  have hΦθ : ∀ x, Φ (θ x) = x := fun x => (MulEquiv.ofBijective θ hθbij).symm_apply_apply x
  have hθΦ : ∀ a : A, θ (Φ a) = a := fun a => (MulEquiv.ofBijective θ hθbij).apply_symm_apply a
  have hR : Finite R := Finite.of_surjective ψ hψ
  let w : Fin τ.rank → L' := fun i => Function.surjInv hψ (m i)
  have hw : ∀ i, ψ (w i) = m i := fun i => Function.surjInv_eq hψ (m i)
  have hmN : ∀ i, m i ∈ Subgroup.normalizer (E : Set R) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rw [← hιrange] at he ⊢
      obtain ⟨x, rfl⟩ := he
      exact ⟨_, (hm i (Multiplicative.toAdd x)).symm⟩
    ·
      have hmaps : ∀ e ∈ E, m i * e * (m i)⁻¹ ∈ E := by
        intro e he
        rw [← hιrange] at he ⊢
        obtain ⟨x, rfl⟩ := he
        exact ⟨_, (hm i (Multiplicative.toAdd x)).symm⟩
      let c : E → E := fun e => ⟨m i * e * (m i)⁻¹, hmaps e e.2⟩
      have hc : Function.Injective c := fun e₁ e₂ h12 => Subtype.ext (by
        have h' : m i * (e₁ : R) * (m i)⁻¹ = m i * e₂ * (m i)⁻¹ := congrArg Subtype.val h12
        simpa using h')
      obtain ⟨e', he'⟩ := Finite.injective_iff_surjective.mp hc ⟨_, he⟩
      have h1 : m i * (e' : R) * (m i)⁻¹ = m i * e * (m i)⁻¹ := congrArg Subtype.val he'
      have h2 : (e' : R) = e := by simpa using h1
      rw [← h2]
      exact e'.2
  refine ⟨Φ, w, fun i => hweyl (w i) (hnorm_to (w i) (by rw [hw]; exact hmN i)), ?_, ?_⟩
  · intro i a b hab
    have hb : b = θ (Multiplicative.ofAdd
        (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)))) := by
      apply Subtype.ext
      have hΛm : Λ (m i) = MulAut.conj (w i) := by rw [← hw]; exact hΛn (w i)
      calc (b : MulAut L') = MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ := hab
        _ = Λ (m i) * Λ (ι (Φ a)) * (Λ (m i))⁻¹ := by rw [hΛm, ← hθ, hθΦ]
        _ = Λ (m i * ι (Multiplicative.ofAdd (Multiplicative.toAdd (Φ a))) * (m i)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          rfl
        _ = Λ (ι (Multiplicative.ofAdd
            (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a))))) := by rw [hm]
        _ = _ := (hθ _).symm
    rw [hb, hΦθ]
    rfl
  · intro n hn
    obtain ⟨u, hu⟩ := hnormE (ψ n) (hnorm_of n hn)
    refine ⟨u, fun a b hab => ?_⟩
    have hb : b = θ (Multiplicative.ofAdd
        (TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ a)))) := by
      apply Subtype.ext
      calc (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ := hab
        _ = Λ (ψ n) * Λ (ι (Φ a)) * (Λ (ψ n))⁻¹ := by rw [hΛn, ← hθ, hθΦ]
        _ = Λ (ψ n * ι (Multiplicative.ofAdd (Multiplicative.toAdd (Φ a))) * (ψ n)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          rfl
        _ = Λ (ι (Multiplicative.ofAdd
            (TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ a))))) := by rw [hu]
        _ = _ := (hθ _).symm
    rw [hb, hΦθ]
    rfl

theorem GGExcPlusFrameModelOn.of_mulEquiv {τ : Tag} {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGExcPlusFrameModelOn τ p r R') : GGExcPlusFrameModelOn τ p r R := by
  intro E hE hcard hsc
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := hE.map e.toMonoidHom
  have hcard' : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  have hsc' : ∀ g' : R', (∀ x ∈ E.map e.toMonoidHom, g' * x = x * g') → g' ^ p = 1 →
      g' ∈ E.map e.toMonoidHom := by
    intro g' hg' hgp
    have hg : e.symm g' ∈ E := by
      refine hsc _ (fun x hx => ?_) (by rw [← map_pow, hgp, map_one])
      have h1 := hg' (e x) ⟨x, hx, rfl⟩
      have h2 := congrArg e.symm h1
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
    exact ⟨e.symm g', hg, e.apply_symm_apply g'⟩
  obtain ⟨ι, m, hinj, hrange, hm, hnorm⟩ := h _ hE' (by rw [hcard']; exact hcard) hsc'
  refine ⟨e.symm.toMonoidHom.comp ι, fun i => e.symm (m i),
    e.symm.injective.comp hinj, ?_, fun i s => ?_, fun g hg => ?_⟩
  · rw [MonoidHom.range_comp, hrange, Subgroup.map_map]
    convert Subgroup.map_id E
    ext x
    exact e.symm_apply_apply x
  · change e.symm (m i) * e.symm (ι _) * (e.symm (m i))⁻¹ = e.symm (ι _)
    rw [← map_inv, ← map_mul, ← map_mul, hm]
  · have hg' : e g ∈ Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup R') : Set R') := by
      rw [Subgroup.mem_normalizer_iff] at hg ⊢
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y * g⁻¹, (hg y).mp hy, by simp⟩
      · rintro ⟨y, hy, hyx⟩
        have hz : g⁻¹ * y * g ∈ E :=
          (hg _).mpr (by rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]; exact hy)
        refine ⟨g⁻¹ * y * g, hz, ?_⟩
        change e (g⁻¹ * y * g) = x
        have hyx' : e y = e g * x * (e g)⁻¹ := hyx
        rw [map_mul, map_mul, map_inv, hyx']
        group
    obtain ⟨u, hu⟩ := hnorm (e g) hg'
    refine ⟨u, fun s => ?_⟩
    change g * e.symm (ι _) * g⁻¹ = e.symm (ι _)
    rw [← hu, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

@[expose] def GGExcPlusFrameModel (τ : Tag) (p : ℕ) (K : Type) [Field K] : Prop :=
  ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ (τ.rank - 1) ≤ Nat.card E →
    (∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) →
    ∃ (ι : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K)
      (m : Fin τ.rank → adjointGroup τ K), Function.Injective ι ∧ ι.range = E ∧
      (∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p), m i * ι (Multiplicative.ofAdd s) * (m i)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s))) ∧
      ∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup τ K)), ∃ u : WeylGroup τ,
        ∀ s : Fin τ.rank → ZMod p, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
          ι (Multiplicative.ofAdd (TableBExc.torusAct τ p u s))

theorem GGExcPlusFrameModel.on {τ : Tag} {p : ℕ} {K : Type} [Field K]
    (h : GGExcPlusFrameModel τ p K) :
    GGExcPlusFrameModelOn τ p (τ.rank - 1) (adjointGroup τ K) := by
  intro E hE hcard hsc
  refine h E hE hcard fun x hx hxp => hsc x (fun e he => ?_) hxp
  exact ((Subgroup.mem_centralizer_iff.mp hx) e he).symm

theorem ggExcPlusWeylModelSCr_of_frameModel
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K]
    [Finite K] [CharP K 2]
    (h : GGExcPlusFrameModel τ p K) :
    GGExcPlusWeylModelSCr τ p (τ.rank - 1) (TableBExc.RecipeGroup τ K)
      (TableBExc.RecipeID τ K) := by
  have hon := h.on.of_mulEquiv (TableBExc.recipeEquiv τ K)
  rcases hτ with rfl | rfl
  · obtain ⟨f, hf, hK⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨⟨f, hf⟩, -, hK⟩ := FiniteField.card K 2
      exact ⟨f, hf, by rw [Nat.card_eq_fintype_card, hK]; rfl⟩
    exact ggExcPlusWeylModelSCr_of_frameModelOn hp (TableBExc.center_recipeGroup_eq_bot .E7 K)
      (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
      (ExcSplitL.ggCenterPrime_recipe_E7 hf hK hp hp2) hon
  · exact ggExcPlusWeylModelSCr_of_frameModelOn hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
      (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
      (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) hon

end CFSG.StandardType

end
