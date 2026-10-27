module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce

public section

namespace CFSG.StandardType.E6IDB

open CFSG.Assembly

theorem le_sup_zpowers_of_card_le {G : Type*} [Group G] [Finite G] {Eb Eh : Subgroup G}
    (hle : Eb ≤ Eh) (hEh : IsElemAbelian 3 Eh) (hcard : Nat.card Eh ≤ 3 * Nat.card Eb)
    {φ : G} (hφ : φ ∈ Eh) (hφb : φ ∉ Eb) : Eh ≤ Eb ⊔ Subgroup.zpowers φ := by
  have := Fact.mk Nat.prime_three
  set H := Eb ⊔ Subgroup.zpowers φ with hH
  have hHEh : H ≤ Eh := sup_le hle ((Subgroup.zpowers_le).2 hφ)
  have hH3 : IsPGroup 3 H := (TableB.isPGroup_of_isElemAbelian hEh).to_le hHEh
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH3
  have hr := Subgroup.relIndex_mul_card Eb H
  rw [inf_of_le_left le_sup_left] at hr
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hk ▸ Subgroup.relIndex_dvd_card Eb H)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hφb (hj (Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)))
  have h3 : 3 ≤ Eb.relIndex H := hj ▸ Nat.le_self_pow hj0 3
  have hcardH : Nat.card Eh ≤ Nat.card H := by
    rw [← hr]
    exact hcard.trans (Nat.mul_le_mul_right _ h3)
  exact (Subgroup.eq_of_le_of_card_ge hHEh hcardH).ge

theorem ggInnerDiagBound_of_conj_core {R : Type} [Group R] [Finite R] (J : Subgroup (MulAut R))
    [hJ : J.Normal] (F : Set (MulAut R))
    (hLS : ∀ φ : MulAut R, φ ∉ J → φ ^ 3 = 1 → ∃ f ∈ F, ∃ ψ : MulAut R, ψ * φ * ψ⁻¹ = f)
    (hcore : ∀ f ∈ F, ∀ X : Subgroup (MulAut R), IsElemAbelian 3 X → X ≤ J →
      3 ^ 5 ≤ Nat.card X → (∀ x ∈ X, x * f = f * x) →
      ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ u ∈ U, f u ∈ U) ∧
        ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) :
    GGInnerDiagBound 3 5 R (J : Set (MulAut R)) := by
  intro Eb Eh hEbI hEb h5 _ hle hEh hcard hnot
  have : Finite (MulAut R) := Finite.of_injective (fun φ : MulAut R => (φ : R → R))
    DFunLike.coe_injective
  obtain ⟨φ, hφ, hφJ⟩ := Set.not_subset.mp hnot
  have hφ3 : φ ^ 3 = 1 := hEh.2 φ hφ
  obtain ⟨f, hf, ψ, hψ⟩ := hLS φ hφJ hφ3
  set c := (MulAut.conj ψ).toMonoidHom with hc
  have hXJ : Eb.map c ≤ J := by
    rintro _ ⟨b, hb, rfl⟩
    exact hJ.conj_mem b (hEbI hb) ψ
  have hXf : ∀ x ∈ Eb.map c, x * f = f * x := by
    rintro _ ⟨b, hb, rfl⟩
    have hbφ : b * φ = φ * b := TableB.IsElemAbelian.comm hEh (hle hb) hφ
    rw [← hψ, hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ψ * b * ψ⁻¹ * (ψ * φ * ψ⁻¹) = ψ * (b * φ) * ψ⁻¹ := by group
      _ = ψ * (φ * b) * ψ⁻¹ := by rw [hbφ]
      _ = ψ * φ * ψ⁻¹ * (ψ * b * ψ⁻¹) := by group
  obtain ⟨V, hV, hV2, hVf, hVX⟩ := hcore f hf (Eb.map c) (TableB.isElemAbelian_map hEb _) hXJ
    (by rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective]; exact h5) hXf
  let S : Subgroup (MulAut R) :=
    { carrier := {g | ∀ u, ψ (g u) ∈ V ↔ ψ u ∈ V}
      mul_mem' := fun {a b} ha hb u => (ha (b u)).trans (hb u)
      one_mem' := fun _ => Iff.rfl
      inv_mem' := fun {a} ha u => by
        have h := ha (a⁻¹ u)
        rw [MulAut.apply_inv_self] at h
        exact h.symm }
  have hmem : ∀ g : MulAut R, (∀ v ∈ V, (ψ * g * ψ⁻¹) v ∈ V) →
      (∀ v ∈ V, (ψ * g⁻¹ * ψ⁻¹) v ∈ V) → g ∈ S := by
    intro g h1 h2 u
    have e1 : ψ (g u) = (ψ * g * ψ⁻¹) (ψ u) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    have e2 : ψ u = (ψ * g⁻¹ * ψ⁻¹) (ψ (g u)) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, MulAut.inv_apply_self]
    constructor
    · intro h
      rw [e2]
      exact h2 _ h
    · intro h
      rw [e1]
      exact h1 _ h
  have hEbS : Eb ≤ S := fun b hb => hmem b (fun v hv => hVX _ ⟨b, hb, rfl⟩ v hv)
    (fun v hv => hVX _ ⟨b⁻¹, inv_mem hb, rfl⟩ v hv)
  have hφ2 : ψ * φ⁻¹ * ψ⁻¹ = f * f := by
    have h : φ⁻¹ = φ * φ := inv_eq_of_mul_eq_one_right ((pow_three φ).symm.trans hφ3)
    rw [h, ← hψ]
    group
  have hφS : φ ∈ S := hmem φ (by rw [hψ]; exact hVf)
    (by rw [hφ2]; exact fun v hv => hVf _ (hVf v hv))
  have hEhS : Eh ≤ S := (le_sup_zpowers_of_card_le hle hEh hcard hφ fun h => hφJ (hEbI h)).trans
    (sup_le hEbS ((Subgroup.zpowers_le).2 hφS))
  refine ⟨V.comap ψ.toMonoidHom, fun hbot => hV ?_, hV2.comap_of_injective _ ψ.injective,
    fun g hg u hu => (hEhS hg u).mpr hu⟩
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective V, hbot,
    Subgroup.map_bot]

end CFSG.StandardType.E6IDB

end
