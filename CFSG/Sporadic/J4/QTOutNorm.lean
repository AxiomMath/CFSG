module

public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

theorem Hj_normalizes_Eg (hM : MatFacts) : ∀ g ∈ Hj, ∀ x ∈ Eg uJ 11, g * x * g⁻¹ ∈ Eg uJ 11 :=
  eg_normalizes (elem_uJ hM) Hj XJ act letters (fun _ hℓ c => hX_all hM hℓ c)
    (fun _ hℓ => XJ_inv hℓ) Hj_le_closure

theorem isCoatom_Hj (hF : J4Facts) : IsCoatom Hj := hF.coatom

theorem normalizer_Eg_eq_Hj (hF : J4Facts) : Subgroup.normalizer (Eg uJ 11 : Set J) = Hj := by
  have hM := hF.mat
  have hle : Hj ≤ Subgroup.normalizer (Eg uJ 11 : Set J) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact Hj_normalizes_Eg hM g hg x
    · intro hx
      have h1 := Hj_normalizes_Eg hM g⁻¹ (Hj.inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at h1
      exact h1
  rcases (isCoatom_Hj hF).le_iff.1 hle with h | h
  · exfalso
    have hnorm : (Eg uJ 11).Normal := Subgroup.normalizer_eq_top_iff.1 h
    have := isSimpleGroup_J hF
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Eg uJ 11) with h1 | h1
    · have := card_Eg_uJ hM
      rw [h1, Subgroup.card_bot] at this
      norm_num at this
    · have h2 := card_Eg_uJ hM
      rw [h1, Subgroup.card_top, card_J hF] at h2
      norm_num at h2
  · exact h

theorem Hj_of_Eg (hF : J4Facts) (α : MulAut J) (hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11)
    (x : J) : α x ∈ Hj ↔ x ∈ Hj := by
  have hN := normalizer_Eg_eq_Hj hF
  have key : ∀ z : J, z ∈ Hj ↔ ∀ y, y ∈ Eg uJ 11 ↔ z * y * z⁻¹ ∈ Eg uJ 11 := by
    intro z
    rw [← hN]
    exact Subgroup.mem_normalizer_iff
  rw [key, key]
  constructor
  · intro h y
    have h1 := h (α y)
    rw [hE] at h1
    have h2 : α x * α y * (α x)⁻¹ = α (x * y * x⁻¹) := by simp only [map_mul, map_inv]
    rw [h2, hE] at h1
    exact h1
  · intro h y
    have h1 := h (α.symm y)
    have h2 : α x * α (α.symm y) * (α x)⁻¹ = α (x * α.symm y * x⁻¹) := by
      simp only [map_mul, map_inv]
    rw [← hE (α.symm y), ← hE (x * α.symm y * x⁻¹)] at h1
    simpa [h2] using h1

end CFSG.Sporadic.J4.QT
