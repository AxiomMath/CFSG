module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Ids
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
  {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L)

theorem baseIds (F : FanTree Γ G) (h95 : Fan95d F L) :
    IdsBase S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t S.ub S.zMu S.yMu S.zNb := by
  obtain ⟨a1, -, a3, a4, a5, a6, a7, -, -, -⟩ := h95 S
  have h3 := S.xb_pow_three
  exact
    { t_eq := rfl
      zm0 := a1
      zm1 := a3
      za0 := a4
      za1 := a5
      za2 := a6
      ym0 := by rw [S.yMu_eq F 0]; simp
      ym1 := a7
      ub_eq := by
        unfold ub
        rw [S.zMuij_eq F 0 1, S.zMuij_eq F 0 3]
        simp
      xz := fun i => by
        rw [S.zMu_eq F i, S.zMu_eq F (i + 1)]
        exact conj_shift h3 _ i
      xy := fun i => by
        rw [S.yMu_eq F i, S.yMu_eq F (i + 1)]
        exact conj_shift h3 _ i
      xa := fun i => by
        rw [S.zNb_eq i, S.zNb_eq (i + 1)]
        exact conj_shift h3 _ i }

theorem e1ids (F : FanTree Γ G) (h95 : Fan95d F L) (hsq : S.w * S.w = S.zEta13 * L.z S.α) :
    E1Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t S.ub S.zMu S.yMu S.zNb := by
  obtain ⟨-, a2, -, -, -, -, -, a8, -, -⟩ := h95 S
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  refine { S.baseIds F h95 with zm2 := ?_, ym2 := a8 hsq }
  rw [a2]
  calc S.zEta13 = S.zEta13 * (L.z S.α * L.z S.α) := by rw [hz, mul_one]
    _ = (S.zEta13 * L.z S.α) * L.z S.α := by group
    _ = S.w * S.w * L.z S.α := by rw [← hsq]

theorem e0ids (F : FanTree Γ G) (h95 : Fan95d F L) (hsq : S.w * S.w = S.zEta13) :
    E0Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t S.ub S.zMu S.yMu S.zNb := by
  obtain ⟨-, a2, -, -, -, -, -, -, a9, -⟩ := h95 S
  exact { S.baseIds F h95 with zm2 := by rw [a2, hsq], ym2 := a9 hsq }

theorem p1RelOf (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h92 : Fan92 F L) :
    P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1 := by
  rcases S.D.card_stabilizer_cases F h7 h8 h65 h512 with ⟨-, hc⟩ | ⟨-, hc⟩
  · exact ((h92 S).1 hc).1
  · exact ((h92 S).2 hc).1

theorem p1cRelOf (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h92 : Fan92 F L) (h4 : Nat.card S.D.calpha = 4) :
    P1cRel S.D.x (L.z S.α) S.c S.yEta S.zMu1 := by
  rcases S.D.card_stabilizer_cases F h7 h8 h65 h512 with ⟨h2, -⟩ | ⟨-, hc⟩
  · omega
  · exact ((h92 S).2 hc).2.1

theorem dichOf (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h92 : Fan92 F L) (h4 : Nat.card S.D.calpha = 4) :
    fcomm S.w S.c = 1 ∨ S.w⁻¹ * S.c * S.w = S.c⁻¹ := by
  rcases S.D.card_stabilizer_cases F h7 h8 h65 h512 with ⟨h2, -⟩ | ⟨-, hc⟩
  · omega
  · exact ((h92 S).2 hc).2.2.1

theorem cWWOf (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h92 : Fan92 F L) (h4 : Nat.card S.D.calpha = 4) :
    S.c * (S.w * S.w) = S.w * S.w * S.c := by
  rcases S.dichOf F h7 h8 h65 h512 h92 h4 with h | h
  · have hcw : S.c * S.w = S.w * S.c := commute_of_fcomm_one h
    calc S.c * (S.w * S.w) = (S.c * S.w) * S.w := by group
      _ = (S.w * S.c) * S.w := by rw [hcw]
      _ = S.w * (S.c * S.w) := by group
      _ = S.w * (S.w * S.c) := by rw [hcw]
      _ = S.w * S.w * S.c := by group
  · have h1 : S.c * S.w = S.w * S.c⁻¹ := by
      calc S.c * S.w = S.w * (S.w⁻¹ * S.c * S.w) := by group
        _ = S.w * S.c⁻¹ := by rw [h]
    have h2 : S.c⁻¹ * S.w = S.w * S.c := by
      calc S.c⁻¹ * S.w = S.w * (S.w⁻¹ * S.c⁻¹ * S.w) := by group
        _ = S.w * (S.w⁻¹ * S.c * S.w)⁻¹ := by group
        _ = S.w * S.c := by rw [h, inv_inv]
    calc S.c * (S.w * S.w) = (S.c * S.w) * S.w := by group
      _ = S.w * (S.c⁻¹ * S.w) := by rw [h1]; group
      _ = S.w * S.w * S.c := by rw [h2]; group

theorem hubOf (h93 : Fan93 F L) : S.xβ⁻¹ * S.ub * S.xβ = S.ub :=
  conj_of_comm (fcomm_eq_one_iff.1 (h93 S).1).symm

theorem za_ne_one : L.z S.α ≠ 1 := L.z_ne_one S.D.val

theorem zMu1_two_ne_one (F : FanTree Γ G) : S.zMu1 2 ≠ 1 :=
  L.z_ne_one (S.D.valence_alpha F 2)

theorem zNb_one_ne_one : S.zNb 1 ≠ 1 := by
  intro h
  rw [S.zNb_eq 1] at h
  have h' : S.xβ⁻¹ * L.z S.α * S.xβ = 1 := by simpa using h
  apply S.za_ne_one
  calc L.z S.α = S.xβ * (S.xβ⁻¹ * L.z S.α * S.xβ) * S.xβ⁻¹ := by group
    _ = 1 := by rw [h']; group

theorem zMu1_two_mul_za_ne_one (h95 : Fan95d F L) : S.zMu1 2 * L.z S.α ≠ 1 := by
  obtain ⟨-, -, -, -, a5, -⟩ := h95 S
  intro h
  exact S.zNb_one_ne_one (a5.trans h)

end Sec9Cfg

end CFSG.Quasithin.Fan86
