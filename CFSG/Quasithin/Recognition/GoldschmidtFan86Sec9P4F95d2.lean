module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95d1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExY
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2C

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem w_shape_dt (F : FanTree Γ G) (h7 : Fan7 F L) (h83a : Fan83a F L) (h83b : Fan83b F L)
    (h87 : Fan87 F L) (h512 : Fan512 F L) :
    S.w ∈ nbrStab Γ G ((S.xβ ^ 2)⁻¹ • S.α) ∧
    (S.w * S.w = S.zEta13 * L.z S.α →
      S.w • (S.dt F).alpha 1 = (S.dt F).alpha 1 ∧ S.w • (S.dt F).alpha 3 ≠ (S.dt F).alpha 3 ∧
        S.w • (S.dt F).alpha 4 ≠ (S.dt F).alpha 4) ∧
    (S.w * S.w = S.zEta13 →
      S.w • (S.dt F).alpha 3 = (S.dt F).alpha 3 ∧ S.w • (S.dt F).alpha 1 ≠ (S.dt F).alpha 1 ∧
        S.w • (S.dt F).alpha 4 ≠ (S.dt F).alpha 4) := by
  obtain ⟨δ'', hY⟩ := exists_isYPair h7 (S.dt F)
  obtain ⟨h0, h2⟩ := S.dt_w_fixes F
  have hord := S.orderOf_w F h7.2.2.1
  have hz1 : L.z S.α ≠ 1 := L.z_ne_one S.D.val
  have hn1 := S.zNb_one_mul_zNb_two F h512
  have hne1 : S.zNb 1 ≠ 1 := fun h' => by
    rw [S.zNb_one] at h'
    exact L.z_ne_one ((valence_smul F S.xβ⁻¹ S.α).trans S.D.val) h'
  have hres := fun hsq => (S.dt F).fixed_pair_of_shape_f F h7.1 h7.2.2.1 h83a h83b h87 hY h0 h2
    hord hsq
  have hεn : S.w * S.w = S.zEta13 → S.w ∈ nbrStab Γ G ((S.xβ ^ 2)⁻¹ • S.α) := fun hε =>
    (hres (Or.inr (by rw [S.z_dt_alpha_zero]; exact hε))).1
  have hεn' : S.w * S.w = S.zEta13 * L.z S.α → S.w ∈ nbrStab Γ G ((S.xβ ^ 2)⁻¹ • S.α) :=
    fun hε => (hres (Or.inl ⟨1, by
      simp only [Fin.val_one, pow_one]
      rw [S.z_dt_alpha_zero, S.z_dt_alpha_two, S.z_dt_center, mul_assoc, hn1]
      exact hε⟩)).1
  refine ⟨?_, fun hε => ?_, fun hε => ?_⟩
  · by_cases hε : S.w * S.w = S.zEta13
    · exact hεn hε
    · rcases S.isW1.sq with h | h
      · exact hεn' h
      · exact absurd h hε
  · have hsq : (∃ f : Fin 2, S.w * S.w = L.z ((S.dt F).alpha 0) * L.z ((S.dt F).alpha 2) *
        L.z ((S.xβ ^ 2)⁻¹ • S.α) ^ (f : ℕ)) ∨ S.w * S.w = L.z ((S.dt F).alpha 0) :=
      Or.inl ⟨1, by
        simp only [Fin.val_one, pow_one]
        rw [S.z_dt_alpha_zero, S.z_dt_alpha_two, S.z_dt_center, mul_assoc, hn1]
        exact hε⟩
    rcases (hres hsq).2 with ⟨-, p1, p3, p4⟩ | ⟨hs0, -⟩
    · exact ⟨p1, p3, p4⟩
    · exfalso
      rw [S.z_dt_alpha_zero] at hs0
      exact hz1 (mul_eq_left.1 (hε.symm.trans hs0))
  · have hsq : (∃ f : Fin 2, S.w * S.w = L.z ((S.dt F).alpha 0) * L.z ((S.dt F).alpha 2) *
        L.z ((S.xβ ^ 2)⁻¹ • S.α) ^ (f : ℕ)) ∨ S.w * S.w = L.z ((S.dt F).alpha 0) :=
      Or.inr (by rw [S.z_dt_alpha_zero]; exact hε)
    rcases (hres hsq).2 with ⟨⟨f, hf⟩, -⟩ | ⟨-, p3, p1, p4⟩
    · exfalso
      rw [S.z_dt_alpha_zero, S.z_dt_alpha_two, S.z_dt_center, hε] at hf
      have h1 : S.zNb 1 * S.zNb 2 ^ (f : ℕ) = 1 := by
        have h2 : S.zEta13 * 1 = S.zEta13 * (S.zNb 1 * S.zNb 2 ^ (f : ℕ)) := by
          rw [mul_one, ← mul_assoc]
          exact hf
        exact (mul_left_cancel h2).symm
      fin_cases f
      · simp only [pow_zero, mul_one] at h1
        exact hne1 h1
      · simp only [pow_one] at h1
        rw [hn1] at h1
        exact hz1 h1
    · exact ⟨p3, p1, p4⟩

@[expose] def qv : V := (S.D.x ^ ((2 : Fin 5) : ℕ))⁻¹ • S.η'

theorem yEta_two_eq (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.yEta 2 = L.z (S.D.delta 2) * L.z S.qv := S.D.y_eq F h71c (S.valence_eta' F) 2

theorem isZ2Pair_qv (F : FanTree Γ G) (h71c : Fan71c F L) :
    IsZ2Pair Γ G S.α (S.D.alpha 2) (S.D.beta 2) (S.D.delta 2) S.qv 2 :=
  S.D.isZ2Pair_translate F h71c S.isBeta.pair 2

theorem valence_qv (F : FanTree Γ G) : valence Γ S.qv = 5 :=
  (valence_smul F _ _).trans (S.valence_eta' F)

theorem w_fix_qv (F : FanTree Γ G) (h71c : Fan71c F L) : S.w • S.qv = S.qv := by
  have h1 : S.w * S.yEta 2 = S.yEta 2 * S.w := mul_comm_of_fcomm_eq_one S.commutes
  rw [S.yEta_two_eq F h71c] at h1
  have hδ : S.w * L.z (S.D.delta 2) = L.z (S.D.delta 2) * S.w :=
    (h71c.comm_z_iff (S.D.valence_delta F 2) S.w).2 (S.w_fix_vert 4 (by norm_num))
  have h2 : S.w * L.z S.qv = L.z S.qv * S.w := by
    have h3 : L.z (S.D.delta 2) * (S.w * L.z S.qv) = L.z (S.D.delta 2) * (L.z S.qv * S.w) := by
      calc L.z (S.D.delta 2) * (S.w * L.z S.qv) = (L.z (S.D.delta 2) * S.w) * L.z S.qv := by
            group
        _ = (S.w * L.z (S.D.delta 2)) * L.z S.qv := by rw [hδ]
        _ = S.w * (L.z (S.D.delta 2) * L.z S.qv) := by group
        _ = (L.z (S.D.delta 2) * L.z S.qv) * S.w := h1
        _ = L.z (S.D.delta 2) * (L.z S.qv * S.w) := by group
    exact mul_left_cancel h3
  exact (h71c.comm_z_iff (S.valence_qv F) S.w).1 h2

end Sec9Cfg

end CFSG.Quasithin.Fan86
