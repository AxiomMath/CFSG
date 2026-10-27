module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresRel1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresRel2c
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.Quasithin.Fan86

@[expose] def p1Words : List (List (Fin 13 × Bool)) := PresP1.rels.map FreeGroup.toWord

@[expose] def p1cWords : List (List (Fin 14 × Bool)) := PresP1.relsC.map FreeGroup.toWord

@[expose] def p2Words : List (List (Fin 14 × Bool)) := PresP2.rels.map FreeGroup.toWord

@[expose] def p2cWords : List (List (Fin 15 × Bool)) := PresP2.relsC.map FreeGroup.toWord

theorem map_mk_words {α : Type*} [DecidableEq α] (rs : List (FreeGroup α)) :
    (rs.map FreeGroup.toWord).map FreeGroup.mk = rs := by
  simp [List.map_map, Function.comp_def, FreeGroup.mk_toWord]

theorem lift_eq_one_of_words {α : Type*} [DecidableEq α] {H : Type*} [Group H] (g : α → H)
    {rs : List (FreeGroup α)} (h : ∀ r ∈ rs, FreeGroup.lift g r = 1) :
    ∀ r ∈ {r : FreeGroup α | r ∈ (rs.map FreeGroup.toWord).map FreeGroup.mk},
      FreeGroup.lift g r = 1 := by
  intro r hr
  have hr' : r ∈ (rs.map FreeGroup.toWord).map FreeGroup.mk := hr
  rw [map_mk_words] at hr'
  exact h r hr'

end CFSG.Quasithin.Fan86
