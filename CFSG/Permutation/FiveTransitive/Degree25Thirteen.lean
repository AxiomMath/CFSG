module

public import CFSG.Permutation.FiveTransitive.Degree25SmallSupport
public import CFSG.Permutation.FiveTransitive.Degree25ThirteenFiniteChecks
import CFSG.Permutation.FiveTransitive.Degree24SevenCycle

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_thirteenCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 25)))
    (h5 : ∀ a b : Fin 5 → Fin 25,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg :
      Degree25ThirteenFiniteChecks.thirteenCycle ∈ P) :
    alternatingGroup (Fin 25) ≤ P := by
  classical
  let g := Degree25ThirteenFiniteChecks.thirteenCycle
  have hgcycle : g.IsCycle :=
    Degree25ThirteenFiniteChecks.thirteenCycle_isCycle
  have hP5 : MulAction.IsMultiplyPretransitive P (Fin 25) 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Fin.val (hq i)
  have hP2 : MulAction.IsMultiplyPretransitive P (Fin 25) 2 := by
    letI : MulAction.IsMultiplyPretransitive P (Fin 25) 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := Fin 25) (m := 2) (n := 5)
        (by omega) (by norm_num)
  have hPprimitive : MulAction.IsPreprimitive P (Fin 25) :=
    MulAction.isPreprimitive_of_is_two_pretransitive hP2
  let s : Set (Fin 25) :=
    (g.support : Set (Fin 25))ᶜ
  have hscard : s.ncard = 12 := by
    have hcomp : sᶜ = (g.support : Set (Fin 25)) := by
      simp [s]
    have hgsupport : g.support.card = 13 :=
      Degree25ThirteenFiniteChecks.thirteenCycle_card_support
    have htotal := Set.ncard_add_ncard_compl s
    rw [hcomp, Set.ncard_coe_finset, hgsupport,
      Nat.card_fin] at htotal
    omega
  have hfixTrans :
      MulAction.IsPretransitive
        (fixingSubgroup P s)
        (SubMulAction.ofFixingSubgroup P s) := by
    simpa only [s, g] using
      (Equiv.Perm.isPretransitive_of_isCycle_mem
        (G := P) hgcycle hg)
  have hfixCard :
      Nat.card (SubMulAction.ofFixingSubgroup P s) = 13 := by
    change Nat.card ↥(sᶜ : Set (Fin 25)) = 13
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_fin, hscard] at htotal
    omega
  have hfixPrimitive :
      MulAction.IsPreprimitive
        (fixingSubgroup P s)
        (SubMulAction.ofFixingSubgroup P s) := by
    letI :
        MulAction.IsPretransitive
          (fixingSubgroup P s)
          (SubMulAction.ofFixingSubgroup P s) :=
      hfixTrans
    apply MulAction.IsPreprimitive.of_prime_card
    rw [hfixCard]
    norm_num
  have hP13Primitive :
      MulAction.IsMultiplyPreprimitive P (Fin 25) 13 := by
    apply hPprimitive.isMultiplyPreprimitive
        (s := s) (n := 11)
    · omega
    · norm_num
    · exact hfixPrimitive
  have hP13 :
      MulAction.IsMultiplyPretransitive P (Fin 25) 12 :=
    by
      letI : MulAction.IsMultiplyPretransitive P (Fin 25) 13 :=
        hP13Primitive.isMultiplyPretransitive
      exact MulAction.isMultiplyPretransitive_of_le
        (G := P) (α := Fin 25) (m := 12) (n := 13)
          (by omega) (by norm_num)
  let a : Fin 12 ↪ Fin 25 :=
    ⟨Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.sourceTuple_injective⟩
  let b : Fin 12 ↪ Fin 25 :=
    ⟨Degree25ThirteenFiniteChecks.targetTuple,
      Degree25ThirteenFiniteChecks.targetTuple_injective⟩
  obtain ⟨p, hp⟩ :=
    (MulAction.isMultiplyPretransitive_iff.mp hP13) a b
  have hp' (i : Fin 12) :
      (p : Equiv.Perm (Fin 25))
          (Degree25ThirteenFiniteChecks.sourceTuple i) =
        Degree25ThirteenFiniteChecks.targetTuple i := by
    have hi := congrArg (fun e : Fin 12 ↪ Fin 25 => e i) hp
    simpa [a, b, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hi
  have hp0 : (p : Equiv.Perm (Fin 25)) 0 = 0 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (0 : Fin 12)
  have hp1 : (p : Equiv.Perm (Fin 25)) 1 = 1 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (1 : Fin 12)
  have hp2 : (p : Equiv.Perm (Fin 25)) 2 = 2 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (2 : Fin 12)
  have hp3 : (p : Equiv.Perm (Fin 25)) 3 = 3 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (3 : Fin 12)
  have hp4 : (p : Equiv.Perm (Fin 25)) 4 = 4 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (4 : Fin 12)
  have hp5 : (p : Equiv.Perm (Fin 25)) 5 = 5 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (5 : Fin 12)
  have hp6 : (p : Equiv.Perm (Fin 25)) 6 = 6 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (6 : Fin 12)
  have hp7 : (p : Equiv.Perm (Fin 25)) 7 = 7 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (7 : Fin 12)
  have hp8 : (p : Equiv.Perm (Fin 25)) 8 = 8 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (8 : Fin 12)
  have hp9 : (p : Equiv.Perm (Fin 25)) 9 = 9 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (9 : Fin 12)
  have hp10 : (p : Equiv.Perm (Fin 25)) 10 = 10 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (10 : Fin 12)
  have hp13 : (p : Equiv.Perm (Fin 25)) 13 = 11 := by
    simpa [Degree25ThirteenFiniteChecks.sourceTuple,
      Degree25ThirteenFiniteChecks.targetTuple] using hp' (11 : Fin 12)
  let x : Fin 25 := (p : Equiv.Perm (Fin 25)) 11
  let y : Fin 25 := (p : Equiv.Perm (Fin 25)) 12
  have hxNotRange :
      x ∉ Set.range
        Degree25ThirteenFiniteChecks.targetTuple := by
    rintro ⟨i, hi⟩
    apply Degree25ThirteenFiniteChecks.sourceTuple_ne_eleven i
    apply (p : Equiv.Perm (Fin 25)).injective
    calc
      (p : Equiv.Perm (Fin 25))
          (Degree25ThirteenFiniteChecks.sourceTuple i) =
          Degree25ThirteenFiniteChecks.targetTuple i :=
        hp' i
      _ = x := hi
      _ = (p : Equiv.Perm (Fin 25)) 11 := rfl
  have hyNotRange :
      y ∉ Set.range
        Degree25ThirteenFiniteChecks.targetTuple := by
    rintro ⟨i, hi⟩
    apply Degree25ThirteenFiniteChecks.sourceTuple_ne_twelve i
    apply (p : Equiv.Perm (Fin 25)).injective
    calc
      (p : Equiv.Perm (Fin 25))
          (Degree25ThirteenFiniteChecks.sourceTuple i) =
          Degree25ThirteenFiniteChecks.targetTuple i :=
        hp' i
      _ = y := hi
      _ = (p : Equiv.Perm (Fin 25)) 12 := rfl
  have hx : 12 ≤ x.val := by
    rw [Degree25ThirteenFiniteChecks.mem_range_targetTuple_iff] at hxNotRange
    omega
  have hy : 12 ≤ y.val := by
    rw [Degree25ThirteenFiniteChecks.mem_range_targetTuple_iff] at hyNotRange
    omega
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 25)).injective.ne (by decide)
  let q : Equiv.Perm (Fin 25) :=
    (p : Equiv.Perm (Fin 25)) * g *
      (p : Equiv.Perm (Fin 25))⁻¹
  have hq :
      q = Degree25ThirteenFiniteChecks.comparisonCycle x y := by
    change
      (p : Equiv.Perm (Fin 25)) * g *
          (p : Equiv.Perm (Fin 25))⁻¹ =
        Degree25ThirteenFiniteChecks.comparisonCycle x y
    rw [← Equiv.permCongr_eq_mul]
    change
      (p : Equiv.Perm (Fin 25)).permCongr
          Degree25ThirteenFiniteChecks.thirteenCycle =
        Degree25ThirteenFiniteChecks.comparisonCycle x y
    rw [Degree25ThirteenFiniteChecks.thirteenCycle,
      Helpers.permCongr_formPerm]
    simp [Degree25ThirteenFiniteChecks.comparisonCycle,
      x, y, hp0, hp1, hp2, hp3, hp4, hp5, hp6,
      hp7, hp8, hp9, hp10]
  let w :=
    Degree25ThirteenFiniteChecks.smallWord x y
  have hwData :=
    Degree25ThirteenFiniteChecks.smallWord_all x y hx hy hxy
  have hwMem : w ∈ P := by
    have hclosure :
        Subgroup.closure
            ({g,
              Degree25ThirteenFiniteChecks.comparisonCycle x y} :
              Set (Equiv.Perm (Fin 25))) ≤ P := by
      rw [Subgroup.closure_le]
      intro u hu
      rcases hu with (rfl | rfl)
      · exact hg
      · rw [← hq]
        exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
    exact hclosure
      (Degree25ThirteenFiniteChecks.smallWord_mem_closure x y)
  exact alternatingGroup_le_of_nontrivial_support_le_seven
    (Fin 25) P (by norm_num) h5 hwMem hwData.1
      (hwData.2.trans (by omega))

private theorem alternatingGroup_le_of_thirteenCycle
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (hgcycle : g.IsCycle) (hgsupport : g.support.card = 13) :
    alternatingGroup X ≤ P := by
  classical
  apply Degree25Seven.alternatingGroup_le_of_cycleType_eq
      X P hcard h5 hg
      Degree25ThirteenFiniteChecks.thirteenCycle
  · calc
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
          {((Fintype.equivFinOfCardEq hcard).permCongr g).support.card} :=
        (FiveTransitive.Degree24Seven.isCycle_permCongr
          (Fintype.equivFinOfCardEq hcard) hgcycle).cycleType
      _ = {13} := by
        congr 1
        have hsupportMap :
            ((Fintype.equivFinOfCardEq hcard).permCongr g).support =
              g.support.map
                (Fintype.equivFinOfCardEq hcard).toEmbedding := by
          ext y
          simp [Equiv.Perm.mem_support, Equiv.permCongr_apply]
          constructor
          · intro h h'
            apply h
            rw [h',
              (Fintype.equivFinOfCardEq hcard).apply_symm_apply]
          · intro h h'
            apply h
            apply (Fintype.equivFinOfCardEq hcard).injective
            simpa using h'
        rw [hsupportMap, Finset.card_map, hgsupport]
      _ = Degree25ThirteenFiniteChecks.thirteenCycle.cycleType := by
        rw [Degree25ThirteenFiniteChecks.thirteenCycle_isCycle.cycleType,
          Degree25ThirteenFiniteChecks.thirteenCycle_card_support]
  · intro Q h5Q hcanonical
    exact alternatingGroup_le_of_thirteenCycle_mem
      Q h5Q hcanonical

theorem thirteen_not_dvd_card_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P) :
    ¬13 ∣ Nat.card P := by
  intro hthirteen
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' 13 hthirteen
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 13 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 13 := by
    rw [← hgcycle.orderOf, hgorder]
  exact hnotAlt
    (alternatingGroup_le_of_thirteenCycle
      X P hcard h5 u.prop hgcycle hgsupport)

end FiveTransitive.Degree25

end CFSG
