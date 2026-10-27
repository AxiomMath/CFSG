module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Act

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

namespace IsNaturalAt

variable {H T : Subgroup D} {z : D} {V : Subgroup D} (hn : IsNaturalAt H T z V)

include hn

omit [Finite D] in
theorem conj_eq_mul (hTH : T ≤ H) {t v : D} (ht : t ∈ T) (htQ : t ∉ pCoreOf 2 H) (hv : v ∈ V)
    (hv1 : v ≠ 1) (hvz : v ≠ z) : t * v * t⁻¹ = v * z := by
  rcases hn.conj_cases hTH ht hv with h | h
  · exfalso
    apply htQ
    have htC : t ∈ Subgroup.centralizer (V : Set D) := by
      obtain ⟨a, -, -, hVset⟩ := hn.basis
      have hmemV : ∀ u, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a ∨ u = z * a := by
        intro u
        have := Set.ext_iff.mp hVset u
        simpa using this
      have htz : t * z = z * t := Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht
      have htv : t * v = v * t := by
        calc t * v = (t * v * t⁻¹) * t := by group
          _ = v * t := by rw [h]
      have hta : t * a = a * t := by
        rcases (hmemV v).mp hv with h1 | h1 | h1 | h1
        · exact absurd h1 hv1
        · exact absurd h1 hvz
        · rw [h1] at htv; exact htv
        · rw [h1] at htv
          have h2 : z * (t * a) = z * (a * t) := by
            calc z * (t * a) = (z * t) * a := by rw [mul_assoc]
              _ = (t * z) * a := by rw [htz]
              _ = t * (z * a) := by rw [mul_assoc]
              _ = z * a * t := htv
              _ = z * (a * t) := by rw [mul_assoc]
          exact mul_left_cancel h2
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rcases (hmemV u).mp hu with h1 | h1 | h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact htz.symm
      · rw [h1]; exact hta.symm
      · rw [h1]
        calc z * a * t = z * (a * t) := mul_assoc _ _ _
          _ = z * (t * a) := by rw [hta]
          _ = (z * t) * a := (mul_assoc _ _ _).symm
          _ = (t * z) * a := by rw [htz]
          _ = t * (z * a) := mul_assoc _ _ _
    rw [← hn.centralizer_eq]
    exact ⟨hTH ht, htC⟩
  · exact h

end IsNaturalAt

theorem b_one_structure (h : GoldHyp G₁ G₂) {z₁ z₂ : D} {V₁ V₂ : Subgroup D}
    (hn₁ : IsNaturalAt G₁ (G₁ ⊓ G₂) z₁ V₁) (hn₂ : IsNaturalAt G₂ (G₁ ⊓ G₂) z₂ V₂)
    (hV₁ : ¬ V₁ ≤ pCoreOf 2 G₂) (hV₂ : ¬ V₂ ≤ pCoreOf 2 G₁) :
    z₁ = z₂ ∧ ∃ v₁ ∈ V₁, ∃ v₂ ∈ V₂, v₁ ∉ pCoreOf 2 G₂ ∧ v₂ ∉ pCoreOf 2 G₁ ∧
      v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₂ * v₁ * v₂⁻¹ = v₁ * z₁ ∧ v₁ * v₂ * v₁⁻¹ = v₂ * z₁ ∧
      pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ≤ Subgroup.centralizer ({v₁, v₂} : Set D) ∧
      G₁ ⊓ G₂ = pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ⊔ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ := by
  obtain ⟨v₁, hv₁V, hv₁Q⟩ : ∃ v ∈ V₁, v ∉ pCoreOf 2 G₂ := by
    by_contra hcon
    push Not at hcon
    exact hV₁ (fun x hx => hcon x hx)
  obtain ⟨v₂, hv₂V, hv₂Q⟩ : ∃ v ∈ V₂, v ∉ pCoreOf 2 G₁ := by
    by_contra hcon
    push Not at hcon
    exact hV₂ (fun x hx => hcon x hx)
  have hv₁Q₁ : v₁ ∈ pCoreOf 2 G₁ := hn₁.le_pCoreOf hv₁V
  have hv₂Q₂ : v₂ ∈ pCoreOf 2 G₂ := hn₂.le_pCoreOf hv₂V
  have hv₁T : v₁ ∈ G₁ ⊓ G₂ := h.pCoreOf_left_le hv₁Q₁
  have hv₂T : v₂ ∈ G₁ ⊓ G₂ := h.pCoreOf_right_le hv₂Q₂
  have hz₁Q₂ : z₁ ∈ pCoreOf 2 G₂ := h.centerOf_le_pCoreOf_right hn₁.z_mem
  have hz₂Q₁ : z₂ ∈ pCoreOf 2 G₁ := h.centerOf_le_pCoreOf_left hn₂.z_mem
  have hv₁1 : v₁ ≠ 1 := fun e => hv₁Q (by rw [e]; exact Subgroup.one_mem _)
  have hv₁z : v₁ ≠ z₁ := fun e => hv₁Q (by rw [e]; exact hz₁Q₂)
  have hv₂1 : v₂ ≠ 1 := fun e => hv₂Q (by rw [e]; exact Subgroup.one_mem _)
  have hv₂z : v₂ ≠ z₂ := fun e => hv₂Q (by rw [e]; exact hz₂Q₁)
  have hc₁ : v₂ * v₁ * v₂⁻¹ = v₁ * z₁ :=
    hn₁.conj_eq_mul inf_le_left hv₂T hv₂Q hv₁V hv₁1 hv₁z
  have hc₂ : v₁ * v₂ * v₁⁻¹ = v₂ * z₂ :=
    hn₂.conj_eq_mul inf_le_right hv₁T hv₁Q hv₂V hv₂1 hv₂z
  have hv₁2 : v₁ * v₁ = 1 := hn₁.mul_self_of_mem hv₁V
  have hv₂2 : v₂ * v₂ = 1 := hn₂.mul_self_of_mem hv₂V
  have hz₂v₂ : v₂ * z₂ = z₂ * v₂ := Subgroup.mem_centralizer_iff.mp hn₂.z_mem.2 v₂ hv₂T
  have hzz : z₁ = z₂ := by
    have hc₁' := hc₁
    have hc₂' := hc₂
    rw [inv_eq_of_mul_eq_one_right hv₂2] at hc₁'
    rw [inv_eq_of_mul_eq_one_right hv₁2] at hc₂'
    calc z₁ = v₁ * (v₁ * z₁) := by rw [← mul_assoc, hv₁2, one_mul]
      _ = v₁ * (v₂ * v₁ * v₂) := by rw [← hc₁']
      _ = (v₁ * v₂ * v₁) * v₂ := by group
      _ = (v₂ * z₂) * v₂ := by rw [hc₂']
      _ = v₂ * (z₂ * v₂) := by rw [mul_assoc]
      _ = v₂ * (v₂ * z₂) := by rw [hz₂v₂]
      _ = z₂ := by rw [← mul_assoc, hv₂2, one_mul]
  refine ⟨hzz, v₁, hv₁V, v₂, hv₂V, hv₁Q, hv₂Q, hv₁2, hv₂2, hc₁, hzz ▸ hc₂, ?_, ?_⟩
  ·
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with h1 | h1
    · rw [h1]
      exact (Subgroup.mem_centralizer_iff.mp (hn₁.le_center hv₁V).2 r hr.1).symm
    · rw [h1]
      exact (Subgroup.mem_centralizer_iff.mp (hn₂.le_center hv₂V).2 r hr.2).symm
  ·
    have hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂ := fun e => hv₁Q (e ▸ hv₁Q₁)
    have hR4 := h.relIndex_inf_pCoreOf hne
    have hQ₁T := h.relIndex_pCoreOf_T_left
    have hQ₂T := h.relIndex_pCoreOf_T_right
    have key : ∀ (Q : Subgroup D) (v : D), Q ≤ G₁ ⊓ G₂ → pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ≤ Q →
        Q.relIndex (G₁ ⊓ G₂) = 2 → v ∈ Q → v ∉ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ →
        Q ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ⊔ Subgroup.zpowers v := by
      intro Q v hQT hRQ hQ2 hvQ hvR
      have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) Q (G₁ ⊓ G₂) hRQ hQT
      rw [hR4, hQ2] at h1
      have h2 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex Q = 2 := by omega
      have hSQ : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ⊔ Subgroup.zpowers v ≤ Q :=
        sup_le hRQ (Subgroup.zpowers_le.mpr hvQ)
      have h3 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂)
        (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ⊔ Subgroup.zpowers v) Q le_sup_left hSQ
      rw [h2] at h3
      have hdvd : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex
          (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ⊔ Subgroup.zpowers v) ∣ 2 := Dvd.intro _ h3
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h4 | h4
      · exfalso
        have := Subgroup.relIndex_eq_one.mp h4
        exact hvR (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))
      · rw [h4] at h3
        exact Subgroup.relIndex_eq_one.mp (by omega)
    have hQ₁ := key (pCoreOf 2 G₁) v₁ h.pCoreOf_left_le inf_le_left hQ₁T hv₁Q₁
      (fun hr => hv₁Q hr.2)
    have hQ₂ := key (pCoreOf 2 G₂) v₂ h.pCoreOf_right_le inf_le_right hQ₂T hv₂Q₂
      (fun hr => hv₂Q hr.1)
    apply le_antisymm
    · rw [← h.pCoreOf_sup_eq hne]
      exact sup_le (hQ₁.trans le_sup_left)
        (hQ₂.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
    · exact sup_le (sup_le (inf_le_left.trans h.pCoreOf_left_le)
        (Subgroup.zpowers_le.mpr hv₁T)) (Subgroup.zpowers_le.mpr hv₂T)

end GoldAmL

end F6

end CFSG.Quasithin
