module

public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem commutator_mem_inf_centralizer {L V : Subgroup G} {t l : G} (hlL : l ∈ L)
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (htV : ∀ a ∈ V, t * a = a * t) :
    l * t * l⁻¹ * t⁻¹ ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
  have hinv : t * l⁻¹ * t⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp htL l⁻¹).mp (L.inv_mem hlL)
    exact this
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have := L.mul_mem hlL hinv
    simpa [mul_assoc] using this
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha1 : l⁻¹ * a * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hlL)) a).mp ha
      simpa using this
    have hta : t⁻¹ * a = a * t⁻¹ := by
      have h1 := htV a ha
      calc t⁻¹ * a = t⁻¹ * a * t * t⁻¹ := by group
        _ = t⁻¹ * (a * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * a) * t⁻¹ := by rw [h1]
        _ = a * t⁻¹ := by group
    have hta1 := htV _ ha1
    have e1 : l * t * l⁻¹ * t⁻¹ * a = l * t * (l⁻¹ * a * l) * l⁻¹ * t⁻¹ :=
      calc l * t * l⁻¹ * t⁻¹ * a = l * t * l⁻¹ * (t⁻¹ * a) := by group
        _ = l * t * l⁻¹ * (a * t⁻¹) := by rw [hta]
        _ = l * t * (l⁻¹ * a * l) * l⁻¹ * t⁻¹ := by group
    have e2 : a * (l * t * l⁻¹ * t⁻¹) = l * (l⁻¹ * a * l) * t * l⁻¹ * t⁻¹ := by group
    rw [e1, e2]
    calc l * (l⁻¹ * a * l) * t * l⁻¹ * t⁻¹ = l * ((l⁻¹ * a * l) * t) * l⁻¹ * t⁻¹ := by group
      _ = l * (t * (l⁻¹ * a * l)) * l⁻¹ * t⁻¹ := by rw [← hta1]
      _ = l * t * (l⁻¹ * a * l) * l⁻¹ * t⁻¹ := by group

theorem conjSub_eq_of_twin {L V T W : Subgroup G} {t l : G} (hlL : l ∈ L)
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (htV : ∀ a ∈ V, t * a = a * t) (hLT : L ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (htW : t ∈ Subgroup.normalizer (W : Set G)) :
    conjSub t (conjSub l⁻¹ W) = conjSub l⁻¹ W := by
  have hd := hLT (commutator_mem_inf_centralizer hlL htL hLV htV)
  have e : t * l⁻¹ = l⁻¹ * (l * t * l⁻¹ * t⁻¹) * t := by group
  rw [← conjSub_mul, e, conjSub_mul, conjSub_mul, F7.conjSub_eq_of_mem_normalizer htW,
    F7.conjSub_eq_of_mem_normalizer (hTW hd)]

end CFSG.Quasithin.SzVB
