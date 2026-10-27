module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Card

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem inf_normalizer_V_le : B ⊓ Subgroup.normalizer (V : Set D) ≤ A ⊓ B := by
  have hTM : A ⊓ B ≤ B ⊓ Subgroup.normalizer (V : Set D) :=
    le_inf inf_le_right (inf_le_left.trans h.natural.reduced.2.1)
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hTM
    (inf_le_left : B ⊓ Subgroup.normalizer (V : Set D) ≤ B)
  rw [h.gold.relIndex_right] at h1
  have hb : (B ⊓ Subgroup.normalizer (V : Set D)).relIndex B ∣ 3 :=
    ⟨(A ⊓ B).relIndex (B ⊓ Subgroup.normalizer (V : Set D)), by rw [← h1]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hb with hb1 | hb3
  · exfalso
    obtain ⟨b, hbB, hbN⟩ := h.exists_not_mem_normalizer
    exact hbN ((Subgroup.relIndex_eq_one.mp hb1) hbB).2
  · rw [hb3] at h1
    exact Subgroup.relIndex_eq_one.mp (by omega)

theorem mem_zpowers_of_mem_of_conj_mem {x c : D} (hxB : x ∈ B) (hxT : x ∉ A ⊓ B) (hc : c ∈ V)
    (hc' : x⁻¹ * c * x ∈ V) : c ∈ Subgroup.zpowers z := by
  by_contra hcz
  obtain ⟨a, ha1, haz, hVset⟩ := h.natural.basis
  have hmemV : ∀ u, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a ∨ u = z * a := by
    intro u
    have := Set.ext_iff.mp hVset u
    simpa using this
  have hzV : z ∈ V := h.natural.z_mem_V
  have hzz : z * z = 1 := by
    have := h.natural.z_sq
    rwa [pow_two] at this
  have hxz : x⁻¹ * z * x = z := by
    have := h.central x⁻¹ (B.inv_mem hxB)
    simpa using this
  have hc1 : c ≠ 1 := fun e => hcz (e ▸ Subgroup.one_mem _)
  have hcz' : c ≠ z := fun e => hcz (e ▸ Subgroup.mem_zpowers z)
  have hV' : ∀ u ∈ V, u = 1 ∨ u = z ∨ u = c ∨ u = z * c := by
    intro u hu
    rcases (hmemV c).mp hc with e | e | e | e
    · exact absurd e hc1
    · exact absurd e hcz'
    · rcases (hmemV u).mp hu with e' | e' | e' | e'
      · exact Or.inl e'
      · exact Or.inr (Or.inl e')
      · exact Or.inr (Or.inr (Or.inl (e'.trans e.symm)))
      · exact Or.inr (Or.inr (Or.inr (by rw [e', e])))
    · have ha' : a = z * c := by rw [e, ← mul_assoc, hzz, one_mul]
      rcases (hmemV u).mp hu with e' | e' | e' | e'
      · exact Or.inl e'
      · exact Or.inr (Or.inl e')
      · exact Or.inr (Or.inr (Or.inr (e'.trans ha')))
      · exact Or.inr (Or.inr (Or.inl (e'.trans e.symm)))
  have hVx : ∀ v ∈ V, x⁻¹ * v * x ∈ V := by
    intro v hv
    have hzc : x⁻¹ * (z * c) * x ∈ V := by
      have e : x⁻¹ * (z * c) * x = (x⁻¹ * z * x) * (x⁻¹ * c * x) := by group
      rw [e, hxz]
      exact V.mul_mem hzV hc'
    rcases hV' v hv with e | e | e | e
    · rw [e]; simp
    · rw [e, hxz]; exact hzV
    · rw [e]; exact hc'
    · rw [e]; exact hzc
  have hle : conjSub x⁻¹ V ≤ V := by
    intro y hy
    rw [mem_conjSub] at hy
    have h5 := hVx _ hy
    have e : x⁻¹ * (x⁻¹⁻¹ * y * x⁻¹) * x = y := by group
    rwa [e] at h5
  have heq : conjSub x⁻¹ V = V := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hxN : x ∈ Subgroup.normalizer (V : Set D) := by
    have := mem_normalizer_of_conjSub_eq heq
    simpa using Subgroup.inv_mem _ this
  exact hxT (h.inf_normalizer_V_le ⟨hxB, hxN⟩)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
