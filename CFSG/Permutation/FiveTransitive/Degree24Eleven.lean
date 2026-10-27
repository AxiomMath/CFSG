module

public import CFSG.Permutation.FiveTransitive.Degree24SmallSupport
public import CFSG.Permutation.FiveTransitive.Degree24ElevenFiniteChecks

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_elevenCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 24)))
    (h5 : ∀ a b : Fin 5 → Fin 24,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg :
      Degree24ElevenFiniteChecks.elevenCycle ∈ P) :
    alternatingGroup (Fin 24) ≤ P := by
  classical
  let g := Degree24ElevenFiniteChecks.elevenCycle
  have hgcycle : g.IsCycle :=
    Degree24ElevenFiniteChecks.elevenCycle_isCycle
  have hP5 : MulAction.IsMultiplyPretransitive P (Fin 24) 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Fin.val (hq i)
  have hP2 : MulAction.IsMultiplyPretransitive P (Fin 24) 2 := by
    letI : MulAction.IsMultiplyPretransitive P (Fin 24) 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := Fin 24) (m := 2) (n := 5)
        (by omega) (by norm_num)
  have hPprimitive : MulAction.IsPreprimitive P (Fin 24) :=
    MulAction.isPreprimitive_of_is_two_pretransitive hP2
  let s : Set (Fin 24) :=
    (g.support : Set (Fin 24))ᶜ
  have hscard : s.ncard = 13 := by
    have hcomp : sᶜ = (g.support : Set (Fin 24)) := by
      simp [s]
    have hgsupport : g.support.card = 11 :=
      Degree24ElevenFiniteChecks.elevenCycle_card_support
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
      Nat.card (SubMulAction.ofFixingSubgroup P s) = 11 := by
    change Nat.card ↥(sᶜ : Set (Fin 24)) = 11
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
  have hP14Primitive :
      MulAction.IsMultiplyPreprimitive P (Fin 24) 14 := by
    apply hPprimitive.isMultiplyPreprimitive
        (s := s) (n := 12)
    · omega
    · norm_num
    · exact hfixPrimitive
  have hP14 :
      MulAction.IsMultiplyPretransitive P (Fin 24) 14 :=
    hP14Primitive.isMultiplyPretransitive
  have hP10 :
      MulAction.IsMultiplyPretransitive P (Fin 24) 10 := by
    letI : MulAction.IsMultiplyPretransitive P (Fin 24) 14 := hP14
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := Fin 24) (m := 10) (n := 14)
        (by omega) (by norm_num)
  let a : Fin 10 ↪ Fin 24 :=
    ⟨Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.sourceTuple_injective⟩
  let b : Fin 10 ↪ Fin 24 :=
    ⟨Degree24ElevenFiniteChecks.targetTuple,
      Degree24ElevenFiniteChecks.targetTuple_injective⟩
  obtain ⟨p, hp⟩ :=
    (MulAction.isMultiplyPretransitive_iff.mp hP10) a b
  have hp' (i : Fin 10) :
      (p : Equiv.Perm (Fin 24))
          (Degree24ElevenFiniteChecks.sourceTuple i) =
        Degree24ElevenFiniteChecks.targetTuple i := by
    have hi := congrArg (fun e : Fin 10 ↪ Fin 24 => e i) hp
    simpa [a, b, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hi
  have hp0 : (p : Equiv.Perm (Fin 24)) 0 = 0 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (0 : Fin 10)
  have hp1 : (p : Equiv.Perm (Fin 24)) 1 = 1 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (1 : Fin 10)
  have hp2 : (p : Equiv.Perm (Fin 24)) 2 = 2 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (2 : Fin 10)
  have hp3 : (p : Equiv.Perm (Fin 24)) 3 = 3 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (3 : Fin 10)
  have hp4 : (p : Equiv.Perm (Fin 24)) 4 = 4 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (4 : Fin 10)
  have hp5 : (p : Equiv.Perm (Fin 24)) 5 = 5 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (5 : Fin 10)
  have hp6 : (p : Equiv.Perm (Fin 24)) 6 = 6 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (6 : Fin 10)
  have hp7 : (p : Equiv.Perm (Fin 24)) 7 = 7 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (7 : Fin 10)
  have hp8 : (p : Equiv.Perm (Fin 24)) 8 = 8 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (8 : Fin 10)
  have hp11 : (p : Equiv.Perm (Fin 24)) 11 = 9 := by
    simpa [Degree24ElevenFiniteChecks.sourceTuple,
      Degree24ElevenFiniteChecks.targetTuple] using hp' (9 : Fin 10)
  let x : Fin 24 := (p : Equiv.Perm (Fin 24)) 9
  let y : Fin 24 := (p : Equiv.Perm (Fin 24)) 10
  have hxNotRange :
      x ∉ Set.range
        Degree24ElevenFiniteChecks.targetTuple := by
    rintro ⟨i, hi⟩
    apply Degree24ElevenFiniteChecks.sourceTuple_ne_nine i
    apply (p : Equiv.Perm (Fin 24)).injective
    calc
      (p : Equiv.Perm (Fin 24))
          (Degree24ElevenFiniteChecks.sourceTuple i) =
          Degree24ElevenFiniteChecks.targetTuple i :=
        hp' i
      _ = x := hi
      _ = (p : Equiv.Perm (Fin 24)) 9 := rfl
  have hyNotRange :
      y ∉ Set.range
        Degree24ElevenFiniteChecks.targetTuple := by
    rintro ⟨i, hi⟩
    apply Degree24ElevenFiniteChecks.sourceTuple_ne_ten i
    apply (p : Equiv.Perm (Fin 24)).injective
    calc
      (p : Equiv.Perm (Fin 24))
          (Degree24ElevenFiniteChecks.sourceTuple i) =
          Degree24ElevenFiniteChecks.targetTuple i :=
        hp' i
      _ = y := hi
      _ = (p : Equiv.Perm (Fin 24)) 10 := rfl
  have hx : 10 ≤ x.val := by
    rw [Degree24ElevenFiniteChecks.mem_range_targetTuple_iff] at hxNotRange
    omega
  have hy : 10 ≤ y.val := by
    rw [Degree24ElevenFiniteChecks.mem_range_targetTuple_iff] at hyNotRange
    omega
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 24)).injective.ne (by decide)
  let q : Equiv.Perm (Fin 24) :=
    (p : Equiv.Perm (Fin 24)) * g *
      (p : Equiv.Perm (Fin 24))⁻¹
  have hq :
      q = Degree24ElevenFiniteChecks.comparisonCycle x y := by
    change
      (p : Equiv.Perm (Fin 24)) * g *
          (p : Equiv.Perm (Fin 24))⁻¹ =
        Degree24ElevenFiniteChecks.comparisonCycle x y
    rw [← Equiv.permCongr_eq_mul]
    change
      (p : Equiv.Perm (Fin 24)).permCongr
          Degree24ElevenFiniteChecks.elevenCycle =
        Degree24ElevenFiniteChecks.comparisonCycle x y
    rw [Degree24ElevenFiniteChecks.elevenCycle,
      Helpers.permCongr_formPerm]
    simp [Degree24ElevenFiniteChecks.comparisonCycle,
      x, y, hp0, hp1, hp2, hp3, hp4, hp5, hp6,
      hp7, hp8]
  let w :=
    Degree24ElevenFiniteChecks.smallWord x y
  have hwData :=
    Degree24ElevenFiniteChecks.smallWord_all x y hx hy hxy
  have hwMem : w ∈ P := by
    have hclosure :
        Subgroup.closure
            ({g,
              Degree24ElevenFiniteChecks.comparisonCycle x y} :
              Set (Equiv.Perm (Fin 24))) ≤ P := by
      rw [Subgroup.closure_le]
      intro u hu
      rcases hu with (rfl | rfl)
      · exact hg
      · rw [← hq]
        exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
    exact hclosure
      (Degree24ElevenFiniteChecks.smallWord_mem_closure x y)
  exact alternatingGroup_le_of_nontrivial_support_le_seven
    (Fin 24) P (by norm_num) h5 hwMem hwData.1
      (hwData.2.trans (by omega))

theorem alternatingGroup_le_of_elevenCycle
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (hgcycle : g.IsCycle) (hgsupport : g.support.card = 11) :
    alternatingGroup X ≤ P := by
  classical
  apply Degree24Seven.alternatingGroup_le_of_cycleType_eq
      X P hcard h5 hg
      Degree24ElevenFiniteChecks.elevenCycle
  · calc
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
          {((Fintype.equivFinOfCardEq hcard).permCongr g).support.card} :=
        (Degree24Seven.isCycle_permCongr
          (Fintype.equivFinOfCardEq hcard) hgcycle).cycleType
      _ = {11} := by
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
      _ = Degree24ElevenFiniteChecks.elevenCycle.cycleType := by
        rw [Degree24ElevenFiniteChecks.elevenCycle_isCycle.cycleType,
          Degree24ElevenFiniteChecks.elevenCycle_card_support]
  · intro Q h5Q hcanonical
    exact alternatingGroup_le_of_elevenCycle_mem
      Q h5Q hcanonical

end FiveTransitive.Degree24

end CFSG
