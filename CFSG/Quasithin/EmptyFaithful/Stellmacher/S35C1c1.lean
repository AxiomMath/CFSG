module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Tab

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53B3.O1

set_option maxRecDepth 100000 in
private theorem l3_faithful_table : ∀ t ∈ S5SylF,
    (∀ w : orth.W, Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 = 0 → orth.act t w = w) →
      t = 1 := by
  decide +kernel

theorem eq_one_of_fixes_l3 {t : Perm (Fin 5)} (ht : t ∈ S5Syl)
    (hfix : ∀ w ∈ l3, orth.act t w = w) : t = 1 :=
  l3_faithful_table t ((mem_S5Syl_iff t).mp ht) fun w hw => hfix w ((mem_l3).mpr hw)

theorem eq_one_of_fixes_invSub_card_eight {Y : Subgroup orth.W} (hY : IsInvSub orth S5Syl Y)
    (hc : Nat.card Y = 2 ^ 3) {t : Perm (Fin 5)} (ht : t ∈ S5Syl)
    (hfix : ∀ y ∈ Y, orth.act t y = y) : t = 1 := by
  rw [eq_l3_of_invSub hY hc] at hfix
  exact eq_one_of_fixes_l3 ht hfix

end CFSG.Quasithin.F53.Stellmacher.S35.C1
