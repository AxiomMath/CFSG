
module

public import CFSG.Sporadic.Recognition.RuMultiplierInputs
public import CFSG.Sporadic.Recognition.CoverTransferWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Sporadic.Recognition.RuMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.VecSurj CFSG.Sporadic.Bridge CFSG.Monster.B.Co2
  CFSG.LieType.Multipliers.Tits CFSG.Sporadic.Recognition.CoverTransfer

abbrev ruVec : CFSG.Sporadic.SmallF2.Native.VecData := CFSG.Sporadic.Ru.Native.ruData

@[expose] noncomputable def ruGen (i : Fin gc) : J ruVec := img ruSpec (seedG ruVec) i.val

theorem lift_ruGen_mk (w : List (Fin gc × Bool)) :
    FreeGroup.lift ruGen (FreeGroup.mk w) =
      wordG (imgG ruSpec (seedG ruVec)) ((natWord w).map letterOf) := by
  rw [wordG_map_letterOf]
  exact lift_mk_eq_wordProd (img ruSpec (seedG ruVec)) w

abbrev RuTabFact : Prop := ∀ w ∈ ruTabWords, FreeGroup.lift ruGen (FreeGroup.mk w) = 1

theorem lift_ruGen_eq_one (h : RuTabFact) {w : List (Fin gc × Bool)} (hw : w ∈ ruTabWords) :
    FreeGroup.lift ruGen (FreeGroup.mk w) = 1 :=
  h w hw

theorem lift_ruCommWord
    (h : RuTabFact) (i : Fin gc) :
    FreeGroup.lift ruGen (FreeGroup.mk (ruCommWord i)) = ruGen i := by
  have h1 := lift_ruGen_eq_one h (w := (i, false) :: ruCommWord i) (by
    unfold ruTabWords
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
  rw [show FreeGroup.mk ((i, false) :: ruCommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (ruCommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

@[expose] noncomputable def ruAbcJ (k : Fin 3) : J ruVec :=
  FreeGroup.lift ruGen (FreeGroup.mk (ruAbc.getD k []))

theorem lift_ruAbcJ_mk (r : List (Fin 3 × Bool)) :
    FreeGroup.lift ruAbcJ (FreeGroup.mk r) =
      FreeGroup.lift ruGen (FreeGroup.mk (substWord ruAbc r)) :=
  lift_mk_substWord ruGen ruAbc r

theorem lift_ruAbcJ_titsOneWords
    (h : RuTabFact) {r : List (Fin 3 × Bool)} (hr : r ∈ titsOneWords) :
    FreeGroup.lift ruAbcJ (FreeGroup.mk r) = 1 := by
  rw [lift_ruAbcJ_mk]
  exact lift_ruGen_eq_one h (by
    unfold ruTabWords
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hr)))

theorem lift_ruAbcJ_of_inv_mul
    (h : RuTabFact) {i : Fin gc} {r : List (Fin 3 × Bool)}
    (hr : (i, false) :: substWord ruAbc r ∈ ruTabWords) :
    FreeGroup.lift ruAbcJ (FreeGroup.mk r) = ruGen i := by
  have h1 := lift_ruGen_eq_one h hr
  rw [show FreeGroup.mk ((i, false) :: substWord ruAbc r) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (substWord ruAbc r) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, ← lift_ruAbcJ_mk] at h1
  exact h1.symm

theorem lift_ruAbcJ_U
    (h : RuTabFact) :
    FreeGroup.lift ruAbcJ (FreeGroup.mk ruUInAbc) = ruGen ⟨0, by decide⟩ :=
  lift_ruAbcJ_of_inv_mul h (by
    have e : ruW [1] ++ substWord ruAbc ruUInAbc =
        ((⟨0, by decide⟩ : Fin gc), false) :: substWord ruAbc ruUInAbc := rfl
    unfold ruTabWords
    rw [← e]
    exact List.mem_append_right _ List.mem_cons_self)

theorem lift_ruAbcJ_T
    (h : RuTabFact) :
    FreeGroup.lift ruAbcJ (FreeGroup.mk ruTInAbc) = ruGen ⟨2, by decide⟩ :=
  lift_ruAbcJ_of_inv_mul h (by
    have e : ruW [5] ++ substWord ruAbc ruTInAbc =
        ((⟨2, by decide⟩ : Fin gc), false) :: substWord ruAbc ruTInAbc := rfl
    unfold ruTabWords
    rw [← e]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem lift_ruGen_toLetters : ∀ (w : List ℤ), (∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 3) →
    FreeGroup.lift ruGen (FreeGroup.mk (toLetters gc w)) = wordG (imgG ruSpec (seedG ruVec)) w
  | [], _ => by simp [toLetters, wordG]
  | z :: w, hw => by
    have hz : z ≠ 0 ∧ z.natAbs ≤ gc := hw z List.mem_cons_self
    have ih := lift_ruGen_toLetters w fun z' h' => hw z' (List.mem_cons_of_mem _ h')
    have hlt : z.natAbs - 1 < gc := by have h3 : gc = 3 := rfl; omega
    have hcons : toLetters gc (z :: w) =
        ((⟨z.natAbs - 1, hlt⟩ : Fin gc), decide (0 < z)) :: toLetters gc w := by
      simp only [toLetters, List.filterMap_cons, dite_eq_left hz]
    have hmk : FreeGroup.mk (((⟨z.natAbs - 1, hlt⟩ : Fin gc), decide (0 < z)) :: toLetters gc w) =
        FreeGroup.mk [((⟨z.natAbs - 1, hlt⟩ : Fin gc), decide (0 < z))] *
          FreeGroup.mk (toLetters gc w) := by
      rw [FreeGroup.mul_mk]; rfl
    rw [hcons, hmk, map_mul, ih]
    simp only [wordG, List.map_cons, List.prod_cons]
    by_cases hpos : 0 < z
    · have e : (z - 1).toNat = z.natAbs - 1 := by omega
      rw [decide_eq_true hpos, show FreeGroup.mk [((⟨z.natAbs - 1, hlt⟩ : Fin gc), true)] =
        FreeGroup.of ⟨z.natAbs - 1, hlt⟩ from rfl, FreeGroup.lift_apply_of, imgG,
        ite_eq_left hpos, e]
      rfl
    · have e : (-z - 1).toNat = z.natAbs - 1 := by omega
      rw [decide_eq_false hpos, show FreeGroup.mk [((⟨z.natAbs - 1, hlt⟩ : Fin gc), false)] =
        (FreeGroup.of ⟨z.natAbs - 1, hlt⟩)⁻¹ from rfl, map_inv, FreeGroup.lift_apply_of, imgG,
        ite_eq_right hpos, e]
      rfl

theorem a_sq : a ruVec ^ 2 = 1 := by
  have hB := CFSG.Sporadic.Ru.ruFacts.toBaseFacts
  have h : mA ruVec ^ 2 = 1 := mA_pow hB
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, a_val hB]
  exact h

end CFSG.Sporadic.Recognition.RuMultiplier
