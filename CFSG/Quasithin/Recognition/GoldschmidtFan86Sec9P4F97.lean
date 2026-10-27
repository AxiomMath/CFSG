module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F97Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Cfg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
  {L : ZLab Γ G}

theorem fan_9_7 (h7 : Fan7 F L) (h82a : Fan82a F L) (h83b : Fan83b F L) (h83c : Fan83c F L)
    (h83d : Fan83d F L) (h85 : Fan85 F L) (h512 : Fan512 F L) (h93 : Fan93 F L)
    (h95 : Fan95 F L) (h96 : Fan96 F L) : Fan97 F L := by
  intro S
  have h95d : Fan95d F L := h95.2.2.2
  have hR := S.p1Rel_of F h7.2.2.1 h82a h83b h83d h85
  have hub := S.hubOf h93
  obtain ⟨h96a1, h96a2, h96a3⟩ := h96.1 S
  refine ⟨fun hsq => ?_, fun hsq => ?_⟩
  · obtain ⟨e₁, e₂, e₃, e₄, hw⟩ := (h95.1 S).1 hsq
    have hlt : (e₁ : ℕ) = (e₂ : ℕ) :=
      (S.e1ids F h95d hsq).exp_eq hR hub h96a1 (h96a2 hsq) S.wA_one.symm (by omega) (by omega)
        hw S.za_ne_one
    refine ⟨e₁, e₃, e₄, ?_⟩
    rw [hw, hlt]
  · obtain ⟨h4, e₁, e₂, e₃, e₄, hw⟩ := (h95.1 S).2 hsq
    have hC := S.p1cRel_of F h7.2.2.1 h7.1 h512 h83c h4
    have hlt : (e₁ : ℕ) = (e₃ : ℕ) :=
      (S.e0ids F h95d hsq).exp_eq hR hC hub h96a1 (h96a3 hsq) S.wA_one.symm (by omega) (by omega)
        hw S.za_ne_one
    have hcomm : S.zMu1 2 ^ (e₂ : ℕ) * S.zMu1 3 ^ (e₁ : ℕ) =
        S.zMu1 3 ^ (e₁ : ℕ) * S.zMu1 2 ^ (e₂ : ℕ) :=
      ((show Commute (S.zMu1 2) (S.zMu1 3) from commute_of_fcomm_one (hR.zz 3 2)).pow_pow _ _).eq
    refine ⟨h4, e₁, e₂, e₄, ?_⟩
    rw [hw, ← hlt]
    simp only [mul_assoc]
    rw [← mul_assoc (S.zMu1 2 ^ (e₂ : ℕ)), hcomm]
    simp only [mul_assoc]

end CFSG.Quasithin.Fan86
