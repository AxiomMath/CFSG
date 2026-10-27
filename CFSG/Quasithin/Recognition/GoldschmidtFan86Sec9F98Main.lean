module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Cfg

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
  {L : ZLab Γ G}

theorem fan_9_8 (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F) (h512 : Fan512 F L)
    (h92 : Fan92 F L) (h93 : Fan93 F L) (h95 : Fan95 F L) (h97 : Fan97 F L) : Fan98 F L := by
  intro S
  have h95d : Fan95d F L := h95.2.2.2
  obtain ⟨-, -, -, a4, -, a6, -⟩ := h95d S
  have hne := S.zMu1_two_mul_za_ne_one h95d
  refine ⟨fun hsq => ?_, fun hsq => ?_⟩
  · obtain ⟨e₁, e₂, e₃, hw⟩ := (h97 S).1 hsq
    have ha : (e₁ : ℕ) = 0 :=
      (S.e1ids F h95d hsq).a_zero (S.p1RelOf F h7 h8 h65 h512 h92) (S.hubOf h93) S.wA_one.symm
        (by omega) hw hne
    refine ⟨e₂, e₃, ?_⟩
    rw [hw, ha, a4, a6]
    simp
  · obtain ⟨h4, e₁, e₂, e₃, hw⟩ := (h97 S).2 hsq
    have ha : (e₁ : ℕ) = 0 :=
      (S.e0ids F h95d hsq).a_zero (S.p1RelOf F h7 h8 h65 h512 h92)
        (S.p1cRelOf F h7 h8 h65 h512 h92 h4) (S.cWWOf F h7 h8 h65 h512 h92 h4) (S.hubOf h93)
        S.wA_one.symm (by omega) hw hne
    refine ⟨h4, e₂, e₃, ?_⟩
    rw [hw, ha, a4, a6]
    simp

end CFSG.Quasithin.Fan86
