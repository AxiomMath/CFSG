module

public import CFSG.Monster.AxisCount.DenseCheck
public import CFSG.Monster.B.Rep4371.GlueDefs
public import CFSG.Monster.B.Rep4371.Interp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem coordOf_pauliQ (y : Model.Pauli) : coordOf (pauliQ y) = (toC y.a, toD y.d) :=
  coordOf_spinEquiv _

theorem pauliQ_odd' (n : ℕ) (hn : n.testBit 0 = false) (i : Fin 24) :
    pauliQ ⟨false, Model.oddCode n i,
      Model.thetaN (Model.oddCode n i) ^^^ Model.dualN (2 ^ (i : ℕ))⟩ = rOdd (π₀ (toC n)) i := by
  have hc : ((π₀ (toC n) : C₀) : C) = toC n := by
    rw [coe_π₀_toC]
    unfold Model.pi0N
    simp [hn]
  have haOdd : aOdd (π₀ (toC n)) i = toC (Model.oddCode n i) := by
    rw [aOdd, mOdd, hc, Model.oddCode, toC_xor, toC_ite, coe_toC_apply, P_toC, boolZ_xor,
      ΩC_eq_toC]
  have e : toSC ⟨false, Model.oddCode n i,
      Model.thetaN (Model.oddCode n i) ^^^ Model.dualN (2 ^ (i : ℕ))⟩ =
      ⟨0, aOdd (π₀ (toC n)) i, thetaD (aOdd (π₀ (toC n)) i) +
        Submodule.Quotient.mk (Pi.single i 1)⟩ := by
    refine SpinCoord.ext rfl haOdd.symm ?_
    rw [haOdd, thetaD_toC, ← bvec_two_pow, mk_bvec_eq_toD, ← toD_xor]
    rfl
  exact (congrArg spinEquiv e).trans (rOdd_eq _ i).symm

@[expose] def octSetG (a m : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter fun i => (Native.spreadG (Model.wordN a) m).testBit i

theorem ind_octSetG (a m : ℕ) :
    Octad.ind (octSetG a m) = bvec 24 (Native.spreadG (Model.wordN a) m) := by
  funext i
  simp only [Octad.ind, octSetG, Finset.mem_filter, Finset.mem_univ, true_and, bvec]

theorem card_octSetG (a m : ℕ) :
    (octSetG a m).card = popc 24 (Native.spreadG (Model.wordN a) m) := by
  rw [← hammingNorm_bvec, ← ind_octSetG]
  exact (hammingNorm_ind _).symm

theorem octCodeG_eq (a m : ℕ) :
    Native.octCodeG a m = a ^^^
      (if Model.popcN 24 (Native.spreadG (Model.wordN a) m) / 2 % 2 == 1 then 63 else 0) := by
  simp [Native.octCodeG, native_popcN, native_wordN]

theorem aOct_eqG (a m : ℕ) : aOct (toC a) (octSetG a m) = toC (Native.octCodeG a m) := by
  rw [aOct, nOct, card_octSetG, octCodeG_eq, toC_xor, toC_ite, ΩC_eq_toC, popcN_eq_popc,
    boolZ_mod_two]

theorem pauliQ_octG (a m : ℕ) :
    pauliQ ⟨false, Native.octCodeG a m, Model.thetaN (Native.octCodeG a m) ^^^
      Model.dualN (Native.spreadG (Model.wordN a) m)⟩ = rOct (toC a) (octSetG a m) := by
  have e : toSC ⟨false, Native.octCodeG a m, Model.thetaN (Native.octCodeG a m) ^^^
      Model.dualN (Native.spreadG (Model.wordN a) m)⟩ =
      ⟨0, aOct (toC a) (octSetG a m), thetaD (aOct (toC a) (octSetG a m)) +
        Submodule.Quotient.mk (Octad.ind (octSetG a m))⟩ := by
    refine SpinCoord.ext rfl (aOct_eqG a m).symm ?_
    rw [aOct_eqG, thetaD_toC, ind_octSetG, mk_bvec_eq_toD, ← toD_xor]
    rfl
  exact (congrArg spinEquiv e).trans (rOct_eq _ _).symm

theorem octadWord_of (a : ℕ) (ha : Native.popcN 24 (Native.wordN a) = 8) :
    hammingNorm ((toC a : C) : Fin 24 → ZMod 2) = 8 := by
  rw [coe_toC, hammingNorm_bvec, ← popcN_eq_popc, ← native_wordN, ← native_popcN]
  exact ha

theorem short_octG (o q : ℕ) (ho : o < 759) (hq : q < 64) :
    IsShortCoord (coordOf (rOct (toC Native.octTab[o]!)
      (octSetG Native.octTab[o]! Native.evenTab[q]!))) := by
  obtain ⟨ha, hpop⟩ := Native.octTab_spec o ho
  obtain ⟨hm, hev⟩ := Native.evenTab_spec q hq
  have hm256 : Native.evenTab[q]! < 256 := by omega
  obtain ⟨hsub, hcard, -⟩ := (Native.octCheck_parts o ho).1 _ hm256
  have hw := octadWord_of _ hpop
  let D : OctadWord := ⟨toC Native.octTab[o]!, hw⟩
  have hsubset : octSetG Native.octTab[o]! Native.evenTab[q]! ⊆ octSupp D := by
    intro i hi
    simp only [octSetG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : (Native.spreadG (Native.wordN Native.octTab[o]!) Native.evenTab[q]! &&&
        Native.wordN Native.octTab[o]!).testBit i =
        (Native.spreadG (Native.wordN Native.octTab[o]!) Native.evenTab[q]!).testBit i := by
      rw [hsub]
    rw [Nat.testBit_and] at h1
    simp only [native_wordN] at h1 hi
    have h2 : (Model.wordN Native.octTab[o]!).testBit i = true := by
      cases h : (Model.wordN Native.octTab[o]!).testBit i
      · rw [h, Bool.and_false] at h1
        rw [hi] at h1
        exact absurd h1 (by simp)
      · rfl
    show i ∈ supp ((toC Native.octTab[o]! : C) : Fin 24 → ZMod 2)
    rw [mem_supp_iff, coe_toC]
    simp [bvec, h2]
  have hevenc : Even (octSetG Native.octTab[o]! Native.evenTab[q]!).card := by
    rw [card_octSetG, ← popcN_eq_popc, ← native_popcN, ← native_wordN, hcard, Nat.even_iff]
    exact hev
  have hl := isShortCoord_labelElt (.inr (.inr (.inr ⟨D, Octad.cls (octSupp D)
    (octSetG Native.octTab[o]! Native.evenTab[q]!)⟩)))
  rw [labelElt, rOctQ_cls hsubset hevenc] at hl
  exact hl

end CFSG.Monster.AxisCount
