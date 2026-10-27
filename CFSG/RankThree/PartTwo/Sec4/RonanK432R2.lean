module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Subgroup

theorem r2_exists_conj_le_of_index {S : Type} [Group S] [Finite S] (C : Subgroup S)
    (hC : ¬ 3 ∣ C.index) {R : Subgroup S} (hR : IsPGroup 3 R) :
    ∃ s : S, ∀ r ∈ R, s⁻¹ * r * s ∈ C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 C) := inferInstance
  set Q' : Subgroup S := (Q : Subgroup C).map C.subtype with hQ'
  have hQ'p : IsPGroup 3 Q' := Q.isPGroup'.map C.subtype
  obtain ⟨P, hQP⟩ := hQ'p.exists_le_sylow
  have hCS : Nat.card C * C.index = Nat.card S := Subgroup.card_mul_index C
  have hindex0 : C.index.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hC
  have hCpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hindpos : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card S).factorization 3 = (Nat.card C).factorization 3 := by
    rw [← hCS, Nat.factorization_mul hCpos hindpos]
    simp [hindex0]
  have hQcard : Nat.card Q' = Nat.card P := by
    have h1 : Nat.card Q' = Nat.card (Q : Subgroup C) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv.symm
    rw [h1, Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P, hfac]
  have hQP' : Q' = (P : Subgroup S) :=
    Subgroup.eq_of_le_of_card_ge hQP (le_of_eq hQcard.symm)
  obtain ⟨P₂, hRP₂⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P₂ P
  refine ⟨g⁻¹, fun r hr => ?_⟩
  have hconj : g * r * g⁻¹ ∈ (P : Subgroup S) := by
    have h1 : (P : Subgroup S) = (g • P₂ : Sylow 3 S) := by rw [hg]
    rw [h1, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul r (MulAut.conj g) _ (hRP₂ hr)
  rw [← hQP'] at hconj
  obtain ⟨c, hcQ, hc⟩ := Subgroup.mem_map.mp hconj
  have hcc : (c : S) = g * r * g⁻¹ := hc
  have : g⁻¹⁻¹ * r * g⁻¹ ∈ C := by
    rw [inv_inv, ← hcc]
    exact c.2
  simpa using (show g * r * g⁻¹ ∈ C from hcc ▸ c.2)

theorem r2_exists_conj_fixes {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    {σ : MulAut S} (hσ : σ ^ 3 = 1) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hw : AutWeaklyClosed σ) {R : Subgroup S} (hR : IsPGroup 3 R) :
    ∃ s : S, ∀ r ∈ R, (MulAut.conj s * σ * (MulAut.conj s)⁻¹) r = r := by
  have hC := three_not_dvd_index_of_autWeaklyClosed hσ hout hw
  obtain ⟨s, hs⟩ := r2_exists_conj_le_of_index _ hC hR
  refine ⟨s, fun r hr => ?_⟩
  have h1 := (mem_comap_conj_centralizer_iff hZ σ (s⁻¹ * r * s)).mp (hs r hr)
  have h2 : (MulAut.conj s * σ * (MulAut.conj s)⁻¹) r = s * σ (s⁻¹ * r * s) * s⁻¹ := by
    simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_symm_apply]
  rw [h2, h1]
  group

theorem r2_conj_pow_three {S : Type} [Group S] {σ : MulAut S} (hσ : σ ^ 3 = 1) (s : S) :
    (MulAut.conj s * σ * (MulAut.conj s)⁻¹) ^ 3 = 1 := by
  have : (MulAut.conj s * σ * (MulAut.conj s)⁻¹) ^ 3 =
      MulAut.conj s * σ ^ 3 * (MulAut.conj s)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_mul_cancel_left]
  rw [this, hσ]
  group

theorem r2_conj_not_inner {S : Type} [Group S] {σ : MulAut S}
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) (s : S) :
    MulAut.conj s * σ * (MulAut.conj s)⁻¹ ∉ (MulAut.conj : S →* MulAut S).range := by
  intro h
  apply hout
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp h
  refine MonoidHom.mem_range.mpr ⟨s⁻¹ * y * s, ?_⟩
  rw [map_mul, map_mul, map_inv, hy]
  group

theorem r2_outerRow {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    {R : Subgroup S} (hR : IsPGroup 3 R)
    (hbad : ∀ τ : MulAut S, τ ^ 3 = 1 → τ ∉ (MulAut.conj : S →* MulAut S).range →
      (∀ r ∈ R, τ r = r) → False) : OuterRow S := by
  intro _ σ hσ hout hw
  obtain ⟨s, hs⟩ := r2_exists_conj_fixes hZ hσ hout hw hR
  exact hbad _ (r2_conj_pow_three hσ s) (r2_conj_not_inner hout s) hs

end CFSG.RankThree.PartTwo.Sec4.RonanK432
