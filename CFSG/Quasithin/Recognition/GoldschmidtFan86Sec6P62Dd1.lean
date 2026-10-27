module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem conj_aux_K {Q : Type*} [Group Q] {z₁ z₂ w k : Q} (hw : w * w = 1)
    (hw2 : w * z₂ = z₂ * w) (hk : k * k = 1)
    (c1 : k * z₁ * k⁻¹ = z₁ ∨ k * z₁ * k⁻¹ = z₁ * w)
    (c2 : k * z₂ * k⁻¹ = z₂ ∨ k * z₂ * k⁻¹ = z₂ * w) :
    (z₁ * z₂)⁻¹ * k * (z₁ * z₂) * k = 1 ∨ (z₁ * z₂)⁻¹ * k * (z₁ * z₂) * k = w := by
  have hk' : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk
  have hconj : (k * z₁ * k⁻¹) * (k * z₂ * k⁻¹) = k * (z₁ * z₂) * k⁻¹ := by group
  have hres : (z₁ * z₂)⁻¹ * k * (z₁ * z₂) * k = (z₁ * z₂)⁻¹ * (k * (z₁ * z₂) * k⁻¹) := by
    rw [hk']; group
  have hu : ∃ u, (u = 1 ∨ u = w) ∧ k * (z₁ * z₂) * k⁻¹ = (z₁ * z₂) * u := by
    rw [← hconj]
    rcases c1 with e1 | e1 <;> rcases c2 with e2 | e2 <;> rw [e1, e2]
    · exact ⟨1, Or.inl rfl, by group⟩
    · exact ⟨w, Or.inr rfl, by group⟩
    · exact ⟨w, Or.inr rfl, by rw [mul_assoc, hw2, ← mul_assoc]⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      calc z₁ * w * (z₂ * w) = z₁ * (w * z₂) * w := by group
        _ = z₁ * (z₂ * w) * w := by rw [hw2]
        _ = z₁ * z₂ * (w * w) := by group
        _ = z₁ * z₂ * 1 := by rw [hw]
  obtain ⟨u, hu1, hu2⟩ := hu
  rw [hres, hu2, inv_mul_cancel_left]
  exact hu1

theorem conj_aux_S {Q : Type*} [Group Q] {z₁ z₂ w k : Q} (hw : w * w = 1)
    (hw1 : w * z₁ = z₁ * w) (hy : z₁ * z₂ * (z₁ * z₂) = w) (hk : k * k = 1)
    (hz1 : z₁ * z₁ = 1) (hz2 : z₂ * z₂ = 1)
    (c1 : k * z₁ * k⁻¹ = z₂ ∨ k * z₁ * k⁻¹ = z₂ * w)
    (c2 : k * z₂ * k⁻¹ = z₁ ∨ k * z₂ * k⁻¹ = z₁ * w) :
    (z₁ * z₂)⁻¹ * k * (z₁ * z₂) * k = 1 ∨ (z₁ * z₂)⁻¹ * k * (z₁ * z₂) * k = w := by
  have hk' : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk
  have hconj : (k * z₁ * k⁻¹) * (k * z₂ * k⁻¹) = k * (z₁ * z₂) * k⁻¹ := by group
  have hres : (z₁ * z₂)⁻¹ * k * (z₁ * z₂) * k = (z₁ * z₂)⁻¹ * (k * (z₁ * z₂) * k⁻¹) := by
    rw [hk']; group
  have hinv : (z₁ * z₂)⁻¹ = z₂ * z₁ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hz1, inv_eq_of_mul_eq_one_right hz2]
  have hyy : (z₂ * z₁) * (z₂ * z₁) = w := by
    calc z₂ * z₁ * (z₂ * z₁) = (z₁ * z₂)⁻¹ * (z₁ * z₂)⁻¹ := by rw [hinv]
      _ = (z₁ * z₂ * (z₁ * z₂))⁻¹ := (mul_inv_rev _ _).symm
      _ = w⁻¹ := by rw [hy]
      _ = w := inv_eq_of_mul_eq_one_right hw
  have hu : ∃ u, (u = 1 ∨ u = w) ∧ k * (z₁ * z₂) * k⁻¹ = (z₂ * z₁) * u := by
    rw [← hconj]
    rcases c1 with e1 | e1 <;> rcases c2 with e2 | e2 <;> rw [e1, e2]
    · exact ⟨1, Or.inl rfl, by group⟩
    · exact ⟨w, Or.inr rfl, by group⟩
    · exact ⟨w, Or.inr rfl, by rw [mul_assoc, hw1, ← mul_assoc]⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      calc z₂ * w * (z₁ * w) = z₂ * (w * z₁) * w := by group
        _ = z₂ * (z₁ * w) * w := by rw [hw1]
        _ = z₂ * z₁ * (w * w) := by group
        _ = z₂ * z₁ * 1 := by rw [hw]
  obtain ⟨u, hu1, hu2⟩ := hu
  rw [hres, hu2, hinv, ← mul_assoc, hyy]
  rcases hu1 with rfl | rfl
  · right
    exact mul_one _
  · left
    exact hw

variable {L : ZLab Γ G} (F : FanTree Γ G) (H : LabHyp L)
include F H

theorem label_br {d ν l l' : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) (h' : Br Γ d ν l') :
    L.z l = L.z l' ∨ L.z l = L.z l' * L.z d := by
  by_cases hll : l' = l
  · exact Or.inl (by rw [hll])
  · exact Or.inr (sib_label F H hd h' h hll)

theorem conj_label_K {d ν l l' : V} {k : G} (hd : valence Γ d = 5) (hk : k ∈ nbrStab Γ G d)
    (h : Br Γ d ν l) (h' : Br Γ d ν l') :
    k * L.z l * k⁻¹ = L.z l' ∨ k * L.z l * k⁻¹ = L.z l' * L.z d := by
  rw [← z_smul (Br.valence F hd h).2 k]
  exact label_br F H hd (Br.of_mem_nbrStab F hk h) h'

theorem conj_label_S {d μ μ' l l' : V} {s k : G} (hd : valence Γ d = 5)
    (hs : s ∈ MulAction.stabilizer G d) (hks : k * s ∈ nbrStab Γ G d) (hsm : s • μ' = μ)
    (h : Br Γ d μ l) (h' : Br Γ d μ' l') :
    k * L.z l * k⁻¹ = L.z l' ∨ k * L.z l * k⁻¹ = L.z l' * L.z d := by
  have hsd : s⁻¹ • d = d := MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G d).inv_mem hs)
  have hb := Br.smul F s⁻¹ h
  rw [hsd, inv_smul_eq_iff.2 hsm.symm] at hb
  have hb2 := Br.of_mem_nbrStab F hks hb
  rw [mul_smul, smul_inv_smul] at hb2
  rw [← z_smul (Br.valence F hd h).2 k]
  exact label_br F H hd hb2 h'

theorem conj_y_mem {d μ₁ μ₂ l₁ l₂ : V} {s k : G} (hd : valence Γ d = 5) (h₁ : Br Γ d μ₁ l₁)
    (h₂ : Br Γ d μ₂ l₂) (hnc : NC L l₁ l₂) (hs : s ∈ MulAction.stabilizer G d)
    (hsμ₁ : s • μ₁ = μ₂) (hsμ₂ : s • μ₂ = μ₁) (hkk : k * k = 1)
    (hk : k ∈ nbrStab Γ G d ∨ k * s ∈ nbrStab Γ G d) :
    (L.z l₁ * L.z l₂)⁻¹ * k * (L.z l₁ * L.z l₂) * k = 1 ∨
      (L.z l₁ * L.z l₂)⁻¹ * k * (L.z l₁ * L.z l₂) * k = L.z d := by
  have hv₁ := (Br.valence F hd h₁).2
  have hv₂ := (Br.valence F hd h₂).2
  have hy := nc_sq F H hd (Br.dist_two F h₁) (Br.dist_two F h₂) hnc
  have hw := z_sq (L := L) hd
  have hc₁ := z_comm_dist F H hd (Br.dist_two F h₁)
  have hc₂ := z_comm_dist F H hd (Br.dist_two F h₂)
  rcases hk with hk | hk
  · exact conj_aux_K hw hc₂.symm hkk (conj_label_K F H hd hk h₁ h₁) (conj_label_K F H hd hk h₂ h₂)
  · exact conj_aux_S hw hc₁.symm hy hkk (z_sq hv₁) (z_sq hv₂)
      (conj_label_S F H hd hs hk hsμ₂ h₁ h₂) (conj_label_S F H hd hs hk hsμ₁ h₂ h₁)

end P62

end CFSG.Quasithin.Fan86
