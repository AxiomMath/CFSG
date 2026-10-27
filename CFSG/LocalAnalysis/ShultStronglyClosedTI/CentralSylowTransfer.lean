module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

theorem central_pSubgroup_le_sylow {E : Type*} [Group E] {p : ℕ}
    (P : Sylow p E) (A : Subgroup E)
    (hcentral : A ≤ Subgroup.center E) (hp : IsPGroup p A) :
    A ≤ (P : Subgroup E) := by
  let : A.Normal := Subgroup.normal_of_le_center hcentral
  exact hp.le_sylow_of_normal P

theorem central_element_mem_sylow_derived {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    (a : (P : Subgroup E)) (hcentral : (a : E) ∈ Subgroup.center E) :
    a ∈ commutator (P : Subgroup E) := by
  let φ : (P : Subgroup E) →* Abelianization (P : Subgroup E) := Abelianization.of
  have htrivial : φ.transfer = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ.transfer
  have hkey : ∀ (k : ℕ) (g : E),
      g⁻¹ * (a : E) ^ k * g ∈ (P : Subgroup E) →
        g⁻¹ * (a : E) ^ k * g = (a : E) ^ k := by
    intro k g _
    have hcomm := Subgroup.mem_center_iff.mp
      ((Subgroup.center E).pow_mem hcentral k) g
    calc
      g⁻¹ * (a : E) ^ k * g = g⁻¹ * (g * (a : E) ^ k) := by
        rw [mul_assoc, hcomm.symm]
      _ = (a : E) ^ k := inv_mul_cancel_left g _
  have hindex : (φ a) ^ (P : Subgroup E).index = 1 := by
    have hvalue : φ.transfer (a : E) = 1 :=
      congrArg (fun f : E →* Abelianization (P : Subgroup E) => f (a : E)) htrivial
    rw [MonoidHom.transfer_eq_pow φ (a : E) hkey] at hvalue
    change φ (a ^ (P : Subgroup E).index) = 1 at hvalue
    simpa only [map_pow] using hvalue
  have hcard : (φ a) ^ Nat.card (P : Subgroup E) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hone : φ a = 1 :=
    (pow_eq_one_iff_of_coprime P.card_coprime_index).mp ⟨hcard, hindex⟩
  rw [← Abelianization.ker_of (P : Subgroup E)]
  exact hone

theorem central_pSubgroup_le_sylow_derived {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    (A : Subgroup E) (hcentral : A ≤ Subgroup.center E) (hp : IsPGroup p A) :
    A ≤ (commutator (P : Subgroup E)).map (P : Subgroup E).subtype := by
  have hAP := central_pSubgroup_le_sylow P A hcentral hp
  intro a ha
  exact Subgroup.mem_map.mpr
    ⟨⟨a, hAP ha⟩, central_element_mem_sylow_derived P ⟨a, hAP ha⟩ (hcentral ha), rfl⟩

end CFSG.ShultStronglyClosedTI
