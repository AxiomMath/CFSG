module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FGeo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2F

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem fcomm_label {v : V} (hv : valence Γ v = 5) (g : G) :
    fcomm g (L.z v) = L.z (g⁻¹ • v) * L.z v := by
  unfold fcomm
  rw [L.z_inv hv, L.z_inv_smul g hv]

theorem lbl_prod {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a) (ha : a * a = 1) :
    a * b * (c * a) = b * c := by
  calc a * b * (c * a) = (b * a) * (c * a) := by rw [hab]
    _ = b * (a * c) * a := by simp only [mul_assoc]
    _ = b * (c * a) * a := by rw [hac]
    _ = b * c * (a * a) := by simp only [mul_assoc]
    _ = b * c := by rw [ha, mul_one]

theorem label_comm (F : FanTree Γ G) (h71c : Fan71c F L) {a p q : V} (hp : valence Γ p = 5)
    (hq : valence Γ q = 5) (hpa : Γ.dist a p = 2) (hqa : Γ.dist a q = 2) :
    L.z p * L.z q = L.z q * L.z p := by
  refine h71c.z_comm_of_dist_le hp hq ?_
  have h1 := F.isTree.connected.dist_triangle (u := p) (v := a) (w := q)
  have h2 : Γ.dist p a = Γ.dist a p := SimpleGraph.dist_comm
  omega

variable {D}

theorem smul_delta_facts (F : FanTree Γ G) {g : G} (hg : g • D.alpha 0 = D.alpha 0) :
    Γ.dist (D.alpha 0) (g • D.delta 0) = 2 ∧ valence Γ (g • D.delta 0) = 5 := by
  refine ⟨?_, by rw [valence_smul F]; exact D.valence_delta F 0⟩
  have := dist_smul F g (D.alpha 0) (D.delta 0)
  rw [hg] at this
  rw [this, D.dist_alpha_delta F 0]

theorem fcomm_u_labels (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ') :
    D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4 =
        L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z (D.delta 0) ∧
      D.y δ' 2 * D.y δ' 1 * (D.y δ' 4 * D.y δ' 3) =
        L.z ((D.y δ' 2 * D.y δ' 1) • D.delta 0) * L.z (D.delta 0) := by
  have hR := fiveRel D F h71c h83a h83b h83d hY
  obtain ⟨hr1, hr2⟩ := refl_one_two D F h71c hY
  obtain ⟨hc1, hc2⟩ := fcomm_u_eq (D.zd_mul_self F 0) hR.sq_a hr2 hr1
  constructor
  · rw [← hc1, fcomm_label (D.valence_delta F 0)]
  · rw [← hc2, fcomm_label (D.valence_delta F 0), inv_inv]

theorem y_labels (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ') :
    prodFive (D.y δ') = L.z δ' * L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) ∧
      D.y δ' 0 * (D.y δ' 2 * D.y δ' 1 * (D.y δ' 4 * D.y δ' 3)) =
        L.z δ' * L.z ((D.y δ' 2 * D.y δ' 1) • D.delta 0) ∧
      D.x⁻¹ * prodFive (D.y δ') * D.x = prodFive (D.y δ') := by
  obtain ⟨hP, hP'⟩ := fcomm_u_labels F h71c h83a h83b h83d hY
  have hv' := Sec8P3.valence_of_isYPair D F hY
  have hu : (D.y δ' 2 * D.y δ' 1) • D.alpha 0 = D.alpha 0 := u_fix_alpha F h71c h83a h83b hY
  have hu' : (D.y δ' 2 * D.y δ' 1)⁻¹ • D.alpha 0 = D.alpha 0 := inv_smul_eq_iff.2 hu.symm
  have h0 := D.zd_mul_self F 0
  have hy0 : D.y δ' 0 = L.z (D.delta 0) * L.z δ' := y_zero D δ'
  have hd' : Γ.dist (D.alpha 0) δ' = 2 := hY.2.2.2.2.1
  have hd0 : Γ.dist (D.alpha 0) (D.delta 0) = 2 := D.dist_alpha_delta F 0
  have key : ∀ g : G, g • D.alpha 0 = D.alpha 0 →
      L.z (D.delta 0) * L.z δ' * (L.z (g • D.delta 0) * L.z (D.delta 0)) =
        L.z δ' * L.z (g • D.delta 0) := fun g hg => by
    obtain ⟨hdg, hvg⟩ := smul_delta_facts F (D := D) hg
    exact lbl_prod (label_comm F h71c (D.valence_delta F 0) hv' hd0 hd')
      (label_comm F h71c (D.valence_delta F 0) hvg hd0 hdg) h0
  refine ⟨?_, ?_, ?_⟩
  · calc prodFive (D.y δ') = D.y δ' 0 * (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) := by
          simp only [prodFive, mul_assoc]
      _ = L.z (D.delta 0) * L.z δ' *
          (L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z (D.delta 0)) := by rw [hy0, hP]
      _ = _ := key _ hu'
  · rw [hy0, hP']
    exact key _ hu
  · have e1 : D.x⁻¹ * prodFive (D.y δ') * D.x =
        D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4 * D.y δ' 0 := by
      have s0 : D.x⁻¹ * D.y δ' 0 * D.x = D.y δ' 1 := by simpa using y_shift D δ' 0
      have s1 : D.x⁻¹ * D.y δ' 1 * D.x = D.y δ' 2 := by simpa using y_shift D δ' 1
      have s2 : D.x⁻¹ * D.y δ' 2 * D.x = D.y δ' 3 := by simpa using y_shift D δ' 2
      have s3 : D.x⁻¹ * D.y δ' 3 * D.x = D.y δ' 4 := by simpa using y_shift D δ' 3
      have s4 : D.x⁻¹ * D.y δ' 4 * D.x = D.y δ' 0 := by simpa using y_shift D δ' 4
      unfold prodFive
      calc D.x⁻¹ * (D.y δ' 0 * D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) * D.x
          = (D.x⁻¹ * D.y δ' 0 * D.x) * (D.x⁻¹ * D.y δ' 1 * D.x) * (D.x⁻¹ * D.y δ' 2 * D.x) *
            (D.x⁻¹ * D.y δ' 3 * D.x) * (D.x⁻¹ * D.y δ' 4 * D.x) := by group
        _ = _ := by rw [s0, s1, s2, s3, s4]
    obtain ⟨hdg, hvg⟩ := smul_delta_facts F (D := D) hu'
    have hcomm' : L.z δ' * L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) =
        L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z δ' :=
      label_comm F h71c hv' hvg hd' hdg
    have hcomm0 : L.z (D.delta 0) * L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) =
        L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z (D.delta 0) :=
      label_comm F h71c (D.valence_delta F 0) hvg hd0 hdg
    have hfirst : prodFive (D.y δ') = L.z δ' * L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) := by
      calc prodFive (D.y δ') = D.y δ' 0 * (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) := by
            simp only [prodFive, mul_assoc]
        _ = L.z (D.delta 0) * L.z δ' *
            (L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z (D.delta 0)) := by rw [hy0, hP]
        _ = _ := key _ hu'
    rw [e1]
    calc D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4 * D.y δ' 0
        = (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) * D.y δ' 0 := rfl
      _ = (L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z (D.delta 0)) *
          (L.z (D.delta 0) * L.z δ') := by rw [hP, hy0]
      _ = L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * (L.z (D.delta 0) * L.z (D.delta 0)) *
          L.z δ' := by simp only [mul_assoc]
      _ = L.z ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) * L.z δ' := by rw [h0, mul_one]
      _ = prodFive (D.y δ') := by rw [hfirst, hcomm']

end Sec8P2F

end CFSG.Quasithin.Fan86
