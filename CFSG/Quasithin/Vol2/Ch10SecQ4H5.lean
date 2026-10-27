module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {v : G}
  (hUe : IsElemAbelian 2 (conjClosure (Subgroup.zpowers v) H))

theorem le_of_isUniqueMaxOver' {T X Y : Subgroup G} (hU : IsUniqueMaxOver H T X)
    (hTY : T ≤ Y) (hYH : Y < H) : Y ≤ X := by
  obtain ⟨N, hN, hYN⟩ := exists_isMaxSubgroupIn hYH
  rw [← (isUniqueMaxOver_iff.mp hU).2.2 N hN (hTY.trans hYN)]
  exact hYN

theorem orderOf_pow_div_three {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B) (y : A)
    (hy : orderOf (φ y) = 3) : orderOf (y ^ (orderOf y / 3)) = 3 := by
  have hdvd : 3 ∣ orderOf y := hy ▸ orderOf_map_dvd φ y
  exact orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd

theorem exists_orderOf_three_of_lt {T M : Subgroup G} (hTH : T ≤ H)
    (hUM : IsUniqueMaxOver H T (H ⊓ M))
    {X : Subgroup (MulAut (IntMod (conjClosure (Subgroup.zpowers v) H) hUe))}
    (hTX : autI hUe T ≤ X) (hXlt : X < autI hUe H) {x : MulAut _} (hxX : x ∈ X)
    (hx3 : orderOf x = 3) : ∃ y ∈ H ⊓ M, orderOf y = 3 := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure (Subgroup.zpowers v) H : Set G) :=
    le_normalizer_conjClosure _ H
  set Y := preI hUe H hHU X with hY
  have hTY : T ≤ Y := by
    intro s hs
    refine (mem_preI hUe).2 ⟨hTH hs, hTX ?_⟩
    exact convI_mem_autI hUe hs (hHU (hTH hs))
  have hYH : Y < H := by
    refine lt_of_le_of_ne (preI_le hUe) fun heq => hXlt.ne ?_
    have := autI_preI hUe (hA := hHU) hXlt.le
    rw [← hY, heq] at this
    exact this.symm
  have hYM := le_of_isUniqueMaxOver' hUM hTY hYH
  obtain ⟨k, hk⟩ : x ∈ (convHom hUe H hHU).range := by
    rw [range_convHom]
    exact hXlt.le hxX
  have hkY : (k : G) ∈ Y := (mem_preI hUe).2 ⟨k.2, by rw [hk]; exact hxX⟩
  have hk3 := orderOf_pow_div_three (convHom hUe H hHU) k (by rw [hk]; exact hx3)
  refine ⟨(k : G) ^ (orderOf k / 3), hYM (Y.pow_mem hkY _), ?_⟩
  rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]
  exact hk3

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
