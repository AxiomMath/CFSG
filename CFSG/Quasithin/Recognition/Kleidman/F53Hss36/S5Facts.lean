module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open Equiv CFSG.Quasithin.F53Mod

set_option maxRecDepth 20000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem centralizer_T_type_all : ∀ a b : Perm (Fin 5), a * a = 1 → b * b = 1 →
    a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a → Perm.sign a = 1 → Perm.sign b = 1 →
    ∀ x : Perm (Fin 5), x * a = a * x → x * b = b * x →
      x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  decide +kernel

theorem centralizer_T_type {a b x : Perm (Fin 5)} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a)
    (hsa : Perm.sign a = 1) (hsb : Perm.sign b = 1) (hxa : x * a = a * x) (hxb : x * b = b * x) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  centralizer_T_type_all a b ha hb ha1 hb1 hab hc hsa hsb x hxa hxb

end CFSG.Quasithin.Kleidman.F53Hss36

end
