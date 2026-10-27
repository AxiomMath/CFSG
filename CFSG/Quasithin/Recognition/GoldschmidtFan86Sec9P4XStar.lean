module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4W2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

theorem exists_w1star (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h84a : Fan84a F L) : Fan91star F L := by
  intro α D
  have hcal := h84a α (D.shift 2)
  obtain ⟨w₁, hw₁⟩ := Sec8P3.exists_w1 (D.shift 2) F h7.1 h7.2.2.1 h7.2.2.2.2.2.2.2.2 h65 hcal.1
    hcal.2
  have hw := D.isW1_of_isW1Elem_shift hw₁
  by_cases hex : ∃ w' : G, IsW1 D w' ∧ w' * w' = L.z (D.delta 2) * L.z α
  · obtain ⟨w', hw', hsq⟩ := hex
    refine ⟨w', hw', fun h => ?_⟩
    rw [hsq] at h
    have hz : L.z α = 1 :=
      mul_left_cancel (a := L.z (D.delta 2)) (h.trans (mul_one _).symm)
    exact absurd hz (L.z_ne_one D.val)
  · exact ⟨w₁, hw, fun _ ⟨w'', h1, h2⟩ => hex ⟨w'', h1, h2⟩⟩

end P4X

end CFSG.Quasithin.Fan86
