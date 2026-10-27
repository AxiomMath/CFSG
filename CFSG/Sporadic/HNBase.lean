
module

public import CFSG.Sporadic.HN.Commutant
public import CFSG.Sporadic.HN.CoprimeSimple
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

@[expose] public section

namespace CFSG.Sporadic.HN

open CFSG.Blueprint CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native

theorem simple_of_facts {D : F5Data} {g : J D} (hA : mA D ^ 2 = 1) (hB : mB D ^ 3 = 1)
    (hx : orderOf (a D * (g⁻¹ * b D * g)) = 19) (hd : D.d % 4 = 1)
    (hcomm : ∀ M : Matrix (Fin D.d) (Fin D.d) (ZMod 5), M * mA D = mA D * M →
      M * mB D = mB D * M → ∃ c : ZMod 5, M = c • 1)
    (hc : Nat.card (J D) = 273030912000000) : IsSimpleGroup (J D) := by
  have : Finite (J D) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have ha : a D ^ 2 = 1 := by
    apply mat_injective D
    change mat D (a D ^ 2) = mat D 1
    rw [show mat D (a D ^ 2) = mat D (a D) ^ 2 from rfl, mat_a' (det_ne_zero_of_pow_eq_one'
      (by norm_num) hA), hA]
    rfl
  have hb : b D ^ 3 = 1 := by
    apply mat_injective D
    change mat D (b D ^ 3) = mat D 1
    rw [show mat D (b D ^ 3) = mat D (b D) ^ 3 from rfl, mat_b' (det_ne_zero_of_pow_eq_one'
      (by norm_num) hB), hB]
    rfl
  have hx19 : (a D * (g⁻¹ * b D * g)) ^ 19 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  have hZ := center_J_eq_bot hd hA hB (by norm_num) hx19 hcomm
  refine isSimpleGroup_of_conjProd (by norm_num) (closure_ab D) ha hb hx ?_ hZ ?_
  · rw [hc]
    norm_num
  · rw [hc]
    exact hn_GL_condition

end CFSG.Sporadic.HN
