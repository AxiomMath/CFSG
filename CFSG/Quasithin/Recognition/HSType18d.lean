module

public import CFSG.Quasithin.Recognition.HSType18c
public import CFSG.Quasithin.Recognition.RuTypeA65

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open HSSetting

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem card_quot_eq_100
    (hF : FactM22SubgroupIndex) {t : G} (ht : orderOf t = 2) (hzt : ¬ IsConj C.z t)
    (hcl : ∀ x : G, orderOf x = 2 → IsConj C.z x ∨ IsConj t x)
    (hstar : ∀ u v : G, IsConj C.z u → IsConj C.z v → u * v = v * u → u * v ≠ 1 →
      IsConj C.z (u * v))
    (hn : Nat.card {u : G // IsConj C.z u ∧ u * t = t * u} ≤ 82)
    (hd : Nat.card {u : G // IsConj C.z u ∧ u * C.z = C.z * u} ≤ 111) :
    Nat.card (G ⧸ C.J) = 100 := by
  rcases C.card_quot_eq_or_ge hF with h | h
  · exact h
  · exfalso
    have hA := RuType.A65.index_centralizer_le C.h.orderOf_z ht hzt hcl hstar
    have hidx : (Subgroup.centralizer ({C.z} : Set G)).index ≤ 82 * (82 + 111) := by
      calc (Subgroup.centralizer ({C.z} : Set G)).index ≤ _ := hA
        _ ≤ 82 * (82 + 111) := Nat.mul_le_mul hn (Nat.add_le_add hn hd)
    have hH : Nat.card (Subgroup.centralizer ({C.z} : Set G)) = 64 * 120 := C.h.card_H
    have hG1 := (Subgroup.centralizer ({C.z} : Set G)).card_mul_index
    have hG2 := C.J.card_mul_index
    rw [C.card_J] at hG2
    rw [hH] at hG1
    have hq : C.J.index = Nat.card (G ⧸ C.J) := rfl
    rw [hq] at hG2
    nlinarith

end HSCtx

end CFSG.Quasithin.HSType
