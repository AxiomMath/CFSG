module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Card
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Ids

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure P5Hyp (F : FanTree Γ G) (L : ZLab Γ G) : Prop where
  h7 : Fan7 F L
  h8 : Fan8Parts F L
  h65 : Fan65 F
  h512 : Fan512 F L
  h92 : Fan92 F L
  h93 : Fan93 F L
  h94 : Fan94 F L
  h95 : Fan95 F L
  h98 : Fan98 F L
  h99 : Fan99 F L

variable {F : FanTree Γ G} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L)

theorem c_mem_calpha_gen : S.c ∈ S.D.calpha := S.gen ▸ Subgroup.mem_zpowers S.c

theorem wA_one : S.wA 1 = S.xβ⁻¹ * S.w * S.xβ := by simp [wA]

theorem cA_one : S.cA 1 = S.xβ⁻¹ * S.c * S.xβ := by simp [cA]

theorem p1Rel (H : P5Hyp F L) : P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1 := by
  rcases S.D.card_stabilizer_cases F H.h7 H.h8 H.h65 H.h512 with ⟨-, hc⟩ | ⟨-, hc⟩
  · exact ((H.h92 S).1 hc).1
  · exact ((H.h92 S).2 hc).1

theorem p1cRel (H : P5Hyp F L) (h4 : Nat.card S.D.calpha = 4) :
    P1cRel S.D.x (L.z S.α) S.c S.yEta S.zMu1 := by
  rcases S.D.card_stabilizer_cases F H.h7 H.h8 H.h65 H.h512 with ⟨h2, -⟩ | ⟨-, hc⟩
  · omega
  · exact ((H.h92 S).2 hc).2.1

theorem fcomm_wc (H : P5Hyp F L) (h4 : Nat.card S.D.calpha = 4) : fcomm S.w S.c = 1 := by
  have h := (H.h99 S h4).2.2
  have e : fcomm (S.wA 1) (S.cA 1) = S.xβ⁻¹ * fcomm S.w S.c * S.xβ := by
    rw [S.wA_one, S.cA_one]
    unfold fcomm
    group
  rw [e] at h
  calc fcomm S.w S.c = S.xβ * (S.xβ⁻¹ * fcomm S.w S.c * S.xβ) * S.xβ⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem star_sq (H : P5Hyp F L) (hS : S.Star) : S.w * S.w = S.zEta13 * L.z S.α := by
  rcases S.isW1.sq with h | h
  · exact h
  · exfalso
    have h4 : Nat.card S.D.calpha = 4 := ((H.h98 S).2 h).1
    have hC := S.p1cRel H h4
    have hcw : S.c * S.w = S.w * S.c := commute_of_fcomm_one (S.fcomm_wc H h4)
    have hc := S.c_mem_calpha_gen
    have hcx : S.D.x * S.c = S.c * S.D.x :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 S.D.x (Set.mem_singleton _)
    have hcfix : S.c ∈ (S.D.P 2).stab G := (Arc.mem_stab G).2 fun m hm =>
      S.D.fix_of_mem_calpha F H.h7.1 H.h7.2.2.1 hc 2 hm
    have hsq : (S.w * S.c) * (S.w * S.c) = S.zEta13 * L.z S.α := by
      calc (S.w * S.c) * (S.w * S.c) = S.w * (S.c * S.w) * S.c := by group
        _ = S.w * (S.w * S.c) * S.c := by rw [hcw]
        _ = (S.w * S.w) * (S.c * S.c) := by group
        _ = S.zEta13 * L.z S.α := by rw [h, ← pow_two, hC.c2]; rfl
    refine hS.2 h ⟨S.w * S.c, ⟨Subgroup.mul_mem _ S.isW1.fixes hcfix, ?_, Or.inl hsq⟩, hsq⟩
    have h2 : S.D.x ^ 2 * S.c = S.c * S.D.x ^ 2 :=
      (Commute.pow_left (show Commute S.D.x S.c from hcx) 2).eq
    calc (S.w * S.c)⁻¹ * S.D.x * (S.w * S.c) = S.c⁻¹ * (S.w⁻¹ * S.D.x * S.w) * S.c := by group
      _ = S.c⁻¹ * S.D.x ^ 2 * S.c := by rw [S.isW1.conj]
      _ = S.D.x ^ 2 := by rw [mul_assoc, h2, inv_mul_cancel_left]

theorem zEta13_eq (H : P5Hyp F L) (hS : S.Star) : S.zEta13 = S.w * S.w * L.z S.α := by
  have h := S.star_sq H hS
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  calc S.zEta13 = S.zEta13 * (L.z S.α * L.z S.α) := by rw [hz, mul_one]
    _ = (S.zEta13 * L.z S.α) * L.z S.α := by group
    _ = S.w * S.w * L.z S.α := by rw [← h]

theorem ids (H : P5Hyp F L) (hS : S.Star) {e₁ e₂ : ℕ} (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1)
    (hw2 : S.wA 1 = S.yEta 3 * S.yEta 4 * S.zMu1 3 * S.zNb 2 ^ e₁ * S.zNb 0 ^ e₂) :
    P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e₁ e₂ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := H.h95.2.2.2 S
  have hsq := S.star_sq H hS
  have hε : S.zMu 2 = S.w * S.w * L.z S.α := by rw [a2]; exact S.zEta13_eq H hS
  have h3 := S.xb_pow_three
  have hub : S.ub * S.xβ = S.xβ * S.ub := fcomm_eq_one_iff.1 (H.h93 S).1
  exact
    { e1le := he₁
      e2le := he₂
      t_eq := rfl
      xb3 := h3
      xb_t := S.isBeta.inverts
      zm0 := a1
      zm1 := a3
      zm2 := hε
      za0 := a4
      za1 := a5
      za2 := a6
      ym0 := by rw [S.yMu_eq F 0]; simp
      ym1 := a7
      ym2 := a8 hsq
      ub_eq := by
        unfold ub
        rw [S.zMuij_eq F 0 1, S.zMuij_eq F 0 3]
        simp
      w2_eq := by rw [hw2, a6, a4]
      xz := fun i => by
        rw [S.zMu_eq F i, S.zMu_eq F (i + 1)]
        exact conj_shift h3 _ i
      xy := fun i => by
        rw [S.yMu_eq F i, S.yMu_eq F (i + 1)]
        exact conj_shift h3 _ i
      xa := fun i => by
        rw [S.zNb_eq i, S.zNb_eq (i + 1)]
        exact conj_shift h3 _ i
      xub := by
        calc S.xβ⁻¹ * S.ub * S.xβ = S.xβ⁻¹ * (S.ub * S.xβ) := by group
          _ = S.xβ⁻¹ * (S.xβ * S.ub) := by rw [hub]
          _ = S.ub := by group
      xw := S.wA_one.symm }

end Sec9Cfg

end CFSG.Quasithin.Fan86
