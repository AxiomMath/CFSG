module

public import CFSG.Quasithin.Vol2.Ch10SecA314ND
public import CFSG.Quasithin.Vol2.Ch10SecKIB45
public import CFSG.Quasithin.Vol2.Ch10SecQ4Obl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.A5N

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem factA314B45_of' (h312 : Vol2Native.A312ListFactsCat) (h45 : AsB45) : FactA314B45 := by
  intro Y _ hY hq S B hSyl hSB hne hB W _ _ hW ρ hker b hbB hb hc
  have := hY.finite
  have hS := Vol2Native.SQTKHypCat.isSQTKCat hY
  rcases alt5_overgroup_cases' h312 hq hS hY.o2 hSyl hSB hne hB with hA7 | hrest
  · exact Or.inl hA7
  obtain ⟨hT, hhs⟩ := C10KH.target_props hrest
  by_cases hfin : IsHat Y ↥(alternatingGroup (Fin 7)) ∧ Subgroup.center Y ≤ ρ.ker
  · exact Or.inr hfin
  exfalso
  rcases hhs with hhat | hsimp
  ·
    have hZn : ¬ Subgroup.center Y ≤ ρ.ker := fun h => hfin ⟨hhat, h⟩
    have hc3 : Nat.card (Subgroup.center Y) = 3 := hhat.2.1
    have hinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases C10KH.eq_bot_or_eq_of_le_three hc3 hker with h | h
      · exact h
      · exact absurd h.ge hZn
    refine C10KH.false_of_action h45 hS hq hT hc3.le hW ρ hinj (Subgroup.center Y) ?_ ?_ ?_ hb hc
    · intro K _ hK n hn
      rw [C10KH.eq_mul_self_mul_of_three hc3 hn]
      exact K.mul_mem (hK n hn) (hK n hn)
    · intro K hKn hNK
      rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq K with h | h
      · rcases C10KH.eq_bot_or_eq_of_le_three hc3 h with h' | h'
        · exact h'
        · exact absurd h'.ge hNK
      · exact absurd (h ▸ le_top) hNK
    · intro h
      rw [h, Subgroup.card_bot] at hc3
      omega
  ·
    have hnc := InternalSec.exists_noncomm_of_isQuasisimple hq
    have hcen : Subgroup.center Y = ⊥ := SecA.center_eq_bot_of_simple hnc
    have hinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hcen.le
    refine C10KH.false_of_action h45 hS hq hT (by rw [hcen, Subgroup.card_bot]; omega) hW ρ hinj
      ⊤ ?_ ?_ ?_ hb hc
    · intro K hKn hK
      rcases hsimp.eq_bot_or_eq_top_of_normal K with h | h
      · exfalso
        obtain ⟨a, c, hac⟩ := hnc
        refine hac (C10KH.mul_comm_of_mul_self (fun y => ?_) a c)
        have := hK y trivial
        rwa [h, Subgroup.mem_bot] at this
      · exact h ▸ le_rfl
    · intro K hKn hNK
      rcases hsimp.eq_bot_or_eq_top_of_normal K with h | h
      · exact h
      · exact absurd (h ▸ le_rfl) hNK
    · have := hsimp.toNontrivial
      exact top_ne_bot

end CFSG.Quasithin.Vol2.Ch10.SecF.A5N
