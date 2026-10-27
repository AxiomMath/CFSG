module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Map
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

private theorem exists_commutator_eq_of_notMem_center {F : Type*} [Field F] {x z : Heis F}
    (hx : x ∉ Subgroup.center (Heis F)) (hz : z ∈ Subgroup.center (Heis F)) :
    ∃ y : Heis F, ⁅x, y⁆ = z := by
  have hx' : x.a ≠ 0 ∨ x.b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (Heis.mem_center.mpr h)
  have hz' := Heis.mem_center.mp hz
  rcases hx' with ha | hb
  · refine ⟨⟨0, z.c / x.a, 0⟩, ?_⟩
    rw [Heis.commutator_eq]
    ext
    · simp [hz'.1]
    · simp [hz'.2]
    · simp
      field_simp
  · refine ⟨⟨-(z.c / x.b), 0, 0⟩, ?_⟩
    rw [Heis.commutator_eq]
    ext
    · simp [hz'.1]
    · simp [hz'.2]
    · simp
      field_simp

private theorem center_quotient_eq_map_center {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    {D : Subgroup (Heis F)} [D.Normal] (hDle : D ≤ Subgroup.center (Heis F))
    (hDrel : D.relIndex (Subgroup.center (Heis F)) = p) :
    Subgroup.center (Heis F ⧸ D) =
      (Subgroup.center (Heis F)).map (QuotientGroup.mk' D) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
    have hxZ : x ∈ Subgroup.center (Heis F) := by
      by_contra hx
      have hDne : D ≠ Subgroup.center (Heis F) := by
        intro hDZ
        rw [hDZ, Subgroup.relIndex_self] at hDrel
        exact hp.ne_one hDrel.symm
      have hnotle : ¬ Subgroup.center (Heis F) ≤ D := fun h => hDne (le_antisymm hDle h)
      rw [SetLike.le_def] at hnotle
      push Not at hnotle
      obtain ⟨z, hzZ, hzD⟩ := hnotle
      obtain ⟨w, hw⟩ := exists_commutator_eq_of_notMem_center hx hzZ
      have hmem : ⁅x, w⁆ ∈ D := by
        have hcomm : Commute ((QuotientGroup.mk' D) x) ((QuotientGroup.mk' D) w) :=
          (Subgroup.mem_center_iff.mp hy ((QuotientGroup.mk' D) w)).symm
        have h1 : ((⁅x, w⁆ : Heis F) : Heis F ⧸ D) = 1 := by
          change (QuotientGroup.mk' D) ⁅x, w⁆ = 1
          rw [map_commutatorElement]
          exact hcomm.commutator_eq
        exact (QuotientGroup.eq_one_iff (N := D) ⁅x, w⁆).mp h1
      rw [hw] at hmem
      exact hzD hmem
    exact Subgroup.mem_map_of_mem _ hxZ
  · exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective D)

private theorem card_map_center_quotient {F : Type*} [Field F] {p : ℕ}
    {D : Subgroup (Heis F)} [D.Normal]
    (hDrel : D.relIndex (Subgroup.center (Heis F)) = p) :
    Nat.card ((Subgroup.center (Heis F)).map (QuotientGroup.mk' D)) = p := by
  rw [← Subgroup.relIndex_ker (f := QuotientGroup.mk' D) (K := Subgroup.center (Heis F)),
    QuotientGroup.ker_mk']
  exact hDrel

private theorem isPGroup_heis {F : Type*} [Field F] {p e : ℕ}
    (hF : Nat.card F = p ^ e) : IsPGroup p (Heis F) :=
  IsPGroup.of_card (n := e * 3) (by rw [Heis.card_eq, hF, pow_mul])

private theorem isExtraspecialPGroup_quotient_heis {F : Type*} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F p] (hF : Nat.card F = p ^ e)
    (D : Subgroup (Heis F)) [D.Normal] (hDle : D ≤ Subgroup.center (Heis F))
    (hDrel : D.relIndex (Subgroup.center (Heis F)) = p) :
    CFSG.IsExtraspecialPGroup p (Heis F ⧸ D) := by
  have : Finite (Heis F) := Finite.of_equiv _ Heis.equivProd.symm
  let π := QuotientGroup.mk' D
  have hcenter : Subgroup.center (Heis F ⧸ D) =
      (Subgroup.center (Heis F)).map π := center_quotient_eq_map_center hp hDle hDrel
  have hcard : Nat.card (Subgroup.center (Heis F ⧸ D)) = p := by
    rw [hcenter]
    exact card_map_center_quotient hDrel
  have hpg : IsPGroup p (Heis F) := isPGroup_heis hF
  have hPp : IsPGroup p (Heis F ⧸ D) := hpg.to_quotient D
  have hexpP : ∀ x : Heis F ⧸ D, x ^ p = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D x
    rw [← map_pow, Heis.pow_prime_eq_one hp hp2, map_one]
  have hmapcomm : (_root_.commutator (Heis F)).map π =
      _root_.commutator (Heis F ⧸ D) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective D)]
  have hcomm : _root_.commutator (Heis F ⧸ D) =
      Subgroup.center (Heis F ⧸ D) := by
    calc _root_.commutator (Heis F ⧸ D)
        = (_root_.commutator (Heis F)).map π := hmapcomm.symm
      _ = (Subgroup.center (Heis F)).map π := by
        rw [_root_.commutator_def, Heis.commutator_eq_center]
      _ = Subgroup.center (Heis F ⧸ D) := hcenter.symm
  have hfr : frattini (Heis F ⧸ D) = _root_.commutator (Heis F ⧸ D) := by
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (IsPGroup p (Heis F ⧸ D)) := ⟨hPp⟩
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (hy | ⟨x, rfl⟩)
      · exact hy
      · show x ^ p ∈ _root_.commutator (Heis F ⧸ D)
        rw [hexpP x]
        exact one_mem _
    · exact fun y hy => Subgroup.subset_closure (Or.inl hy)
  exact ⟨hPp, hcomm, hfr.trans hcomm, hcard⟩

theorem isSpecialType_heis {F : Type*} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [CharP F p] (hF : Nat.card F = p ^ e) : IsSpecialType p e e (Heis F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact Heis.pow_prime_eq_one hp hp2 x
  · calc Nat.card (Heis F) = (p ^ e) ^ 3 := by rw [Heis.card_eq, hF]
      _ = p ^ (e + 2 * e) := by rw [← pow_mul]; congr 1; ring
  · rw [Heis.card_center, hF]
  · intro D hDnorm hDle hDrel
    exact isExtraspecialPGroup_quotient_heis hp hp2 hF D hDle hDrel

theorem isSpecialGood_of_heis {F : Type*} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [CharP F p] (hF : Nat.card F = p ^ e) (h3 : 3 < p ^ e) {S : Type*} [Group S]
    {ι : Heis F →* S} (hι : Function.Injective ι) (x : Heis F) : IsSpecialGood p (ι x) := by
  have hx : IsSpecialGood p x :=
    ⟨⊤, e, e, Subgroup.mem_top x,
      (isSpecialType_heis hp hp2 hF).of_mulEquiv Subgroup.topEquiv.symm, le_rfl, h3⟩
  exact hx.map hι

theorem InvolInvertsGood.of_mulEquiv {p : ℕ} {S T : Type*} [Group S] [Group T] [Finite T]
    (φ : S ≃* T) (h : InvolInvertsGood p S) : InvolInvertsGood p T := by
  intro σ hσ
  let σ' : MulAut S := MulAut.congr φ.symm σ
  have hσ' : orderOf σ' = 2 :=
    (MulEquiv.orderOf_eq (MulAut.congr φ.symm) σ).trans hσ
  obtain ⟨x, hx, hinv, hgood⟩ := h σ' hσ'
  refine ⟨φ x, ?_, ?_, ?_⟩
  · exact (MulEquiv.orderOf_eq φ x).trans hx
  · have hconj : σ (φ x) = φ (σ' x) := by
      simp [σ', MulAut.congr_apply]
    rw [hconj, hinv, map_inv]
  · rcases hgood with hgood | hgood
    · exact Or.inl (IsSpecialGood.map (f := (φ : S →* T)) φ.injective hgood)
    · exact Or.inr (IsOrbitGood.map (f := (φ : S →* T)) φ.injective hgood)

theorem exists_inv_good_of_conj {p : ℕ} {S : Type*} [Group S] [Finite S] {σ σ₀ γ : MulAut S}
    (hσ : σ = γ * σ₀ * γ⁻¹) {x : S} (hx : orderOf x = p) (hinv : σ₀ x = x⁻¹)
    (hgood : IsSpecialGood p x ∨ IsOrbitGood p x) :
    ∃ y : S, orderOf y = p ∧ σ y = y⁻¹ ∧ (IsSpecialGood p y ∨ IsOrbitGood p y) := by
  refine ⟨γ x, ?_, ?_, ?_⟩
  · exact (MulEquiv.orderOf_eq γ x).trans hx
  · rw [hσ]
    simp [MulAut.mul_apply, hinv]
  · rcases hgood with hgood | hgood
    · exact Or.inl (IsSpecialGood.map (f := (γ : S →* S)) γ.injective hgood)
    · exact Or.inr (IsOrbitGood.map (f := (γ : S →* S)) γ.injective hgood)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
