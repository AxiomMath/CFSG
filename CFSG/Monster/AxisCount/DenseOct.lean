module

public import CFSG.Monster.AxisCount.DenseShort
public import CFSG.Monster.Griess.TrialityMatrix.Blocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B.Rep4371 Matrix

@[expose] noncomputable def octW
    (o : ℕ) (ho : o < 759) : OctadWord :=
  ⟨toC Native.octTab[o]!, octadWord_of _ (Native.octTab_spec o ho).2⟩

theorem wordN_lt (a : ℕ) : Model.wordN a < 2 ^ 24 :=
  testBit_combN_two_pow_lt a 24 (by decide)

theorem testBit_octSupp (o : ℕ) (ho : o < 759) (i : Fin 24) :
    i ∈ octSupp (octW o ho) ↔ (Model.wordN Native.octTab[o]!).testBit i = true := by
  show i ∈ supp ((toC Native.octTab[o]! : C) : Fin 24 → ZMod 2) ↔ _
  rw [mem_supp_iff, coe_toC]
  simp [bvec]

theorem octSetG_subset
    (o : ℕ) (ho : o < 759) (m : ℕ) (hm : m < 256) :
    octSetG Native.octTab[o]! m ⊆ octSupp (octW o ho) := by
  obtain ⟨hsub, -, -⟩ := (Native.octCheck_parts o ho).1 m hm
  intro i hi
  simp only [octSetG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have h1 : (Native.spreadG (Native.wordN Native.octTab[o]!) m &&&
      Native.wordN Native.octTab[o]!).testBit i =
      (Native.spreadG (Native.wordN Native.octTab[o]!) m).testBit i := by rw [hsub]
  rw [Nat.testBit_and] at h1
  simp only [native_wordN] at h1 hi
  rw [testBit_octSupp o ho]
  cases h : (Model.wordN Native.octTab[o]!).testBit i
  · rw [h, Bool.and_false] at h1
    rw [hi] at h1
    exact absurd h1 (by simp)
  · rfl

theorem card_octSetG' (o : ℕ) (ho : o < 759) (m : ℕ) (hm : m < 256) :
    (octSetG Native.octTab[o]! m).card = Native.popcN 8 m := by
  obtain ⟨-, hcard, -⟩ := (Native.octCheck_parts o ho).1 m hm
  rw [card_octSetG, ← popcN_eq_popc, ← native_popcN, ← native_wordN]
  exact hcard

theorem octSetG_and
    (o : ℕ) (ho : o < 759) (m m' : ℕ) (hm : m < 256) (hm' : m' < 256) :
    octSetG Native.octTab[o]! (m &&& m') =
      octSetG Native.octTab[o]! m ∩ octSetG Native.octTab[o]! m' := by
  obtain ⟨hand, -⟩ := (Native.octCheck_parts o ho).2 m m' hm hm'
  simp only [native_wordN] at hand
  ext i
  simp only [octSetG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, hand,
    Nat.testBit_and, Bool.and_eq_true]

theorem octSetG_compl (o : ℕ) (ho : o < 759) (m : ℕ) (hm : m < 256) :
    octSetG Native.octTab[o]! (m ^^^ 255) = octSupp (octW o ho) \ octSetG Native.octTab[o]! m := by
  obtain ⟨hsub, -, hcomp⟩ := (Native.octCheck_parts o ho).1 m hm
  simp only [native_wordN] at hsub hcomp
  ext i
  simp only [octSetG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    testBit_octSupp o ho, hcomp, Nat.testBit_xor]
  have h1 := congrArg (fun x => x.testBit i) hsub
  simp only [Nat.testBit_and] at h1
  cases hs : (Native.spreadG (Model.wordN Native.octTab[o]!) m).testBit i <;>
    cases hw : (Model.wordN Native.octTab[o]!).testBit i <;> simp_all

theorem octSetG_injective
    (o : ℕ) (ho : o < 759) (m m' : ℕ) (hm : m < 256) (hm' : m' < 256)
    (h : octSetG Native.octTab[o]! m = octSetG Native.octTab[o]! m') : m = m' := by
  obtain ⟨hsub, -, -⟩ := (Native.octCheck_parts o ho).1 m hm
  obtain ⟨hsub', -, -⟩ := (Native.octCheck_parts o ho).1 m' hm'
  obtain ⟨-, hinj⟩ := (Native.octCheck_parts o ho).2 m m' hm hm'
  rcases hinj with h' | h'
  · exact h'
  · refine absurd ?_ h'
    simp only [native_wordN] at hsub hsub' h' ⊢
    have hw := wordN_lt Native.octTab[o]!
    have l1 : Native.spreadG (Model.wordN Native.octTab[o]!) m < 2 ^ 24 :=
      lt_of_le_of_lt (by rw [← hsub]; exact Nat.and_le_right) hw
    have l2 : Native.spreadG (Model.wordN Native.octTab[o]!) m' < 2 ^ 24 :=
      lt_of_le_of_lt (by rw [← hsub']; exact Nat.and_le_right) hw
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 24
    · have := congrArg (fun s => (⟨i, hi⟩ : Fin 24) ∈ s) h
      simp only [octSetG, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      exact Bool.eq_iff_iff.2 this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le l2 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem evenTab_inj {q q' : ℕ} (hq : q < 64) (hq' : q' < 64)
    (h : Native.evenTab[q]! = Native.evenTab[q']!) : q = q' := by
  have hnd : ((List.range 128).filter fun m => Native.popcN 8 m % 2 == 0).Nodup :=
    List.Nodup.filter _ (List.nodup_range)
  have hs := Native.evenTab_size
  have key : ∀ (k : ℕ) (hk : k < ((List.range 128).filter fun m => Native.popcN 8 m % 2 == 0).length),
      Native.evenTab[k]! = ((List.range 128).filter fun m => Native.popcN 8 m % 2 == 0)[k] := by
    intro k hk
    have hk' : k < Native.evenTab.size := by simpa [Native.evenTab] using hk
    rw [getElem!_pos Native.evenTab k hk']
    rfl
  have hl : q < ((List.range 128).filter fun m => Native.popcN 8 m % 2 == 0).length := by
    have : q < Native.evenTab.size := by omega
    simpa [Native.evenTab] using this
  have hl' : q' < ((List.range 128).filter fun m => Native.popcN 8 m % 2 == 0).length := by
    have : q' < Native.evenTab.size := by omega
    simpa [Native.evenTab] using this
  rw [key q hl, key q' hl'] at h
  exact (hnd.getElem_inj_iff (hi := hl) (hj := hl')).1 h

theorem evenTab_lt
    (q : ℕ) (hq : q < 64) : Native.evenTab[q]! < 128 :=
  (Native.evenTab_spec q hq).1

@[expose] noncomputable def octCls (o : ℕ) (ho : o < 759) (q : ℕ) :
    Octad.EvenQuot (octSupp (octW o ho)) :=
  Octad.cls (octSupp (octW o ho)) (octSetG Native.octTab[o]! Native.evenTab[q]!)

theorem octSetG_even (o : ℕ) (ho : o < 759) (q : ℕ) (hq : q < 64) :
    Even (octSetG Native.octTab[o]! Native.evenTab[q]!).card := by
  rw [card_octSetG' o ho _ (by have := evenTab_lt q hq; omega)]
  exact Nat.even_iff.2 (Native.evenTab_spec q hq).2

theorem octCls_inj_nat
    (o : ℕ) (ho : o < 759) (q q' : ℕ) (hq : q < 64) (hq' : q' < 64)
    (h : octCls o ho q = octCls o ho q') : q = q' := by
  unfold octCls at h
  have hl := evenTab_lt q hq
  have hl' := evenTab_lt q' hq'
  have h1 : Native.evenTab[q]! < 256 := by omega
  have h1' : Native.evenTab[q']! < 256 := by omega
  rw [Octad.cls_eq_cls_iff (octSetG_subset o ho _ h1) (octSetG_even o ho q hq)
    (octSetG_subset o ho _ h1') (octSetG_even o ho q' hq')] at h
  rcases h with h | h
  · exact (evenTab_inj hq' hq (octSetG_injective o ho _ _ h1' h1 h)).symm
  · exfalso
    have hx : Native.evenTab[q]! ^^^ 255 < 256 := Nat.xor_lt_two_pow (n := 8) h1 (by norm_num)
    rw [← octSetG_compl o ho _ h1] at h
    have h2 := octSetG_injective o ho _ _ h1' hx h
    have b1 : (Native.evenTab[q']!).testBit 7 = false := Nat.testBit_lt_two_pow (by omega)
    have b2 : (Native.evenTab[q]!).testBit 7 = false := Nat.testBit_lt_two_pow (by omega)
    have h3 := congrArg (fun x => x.testBit 7) h2
    simp only [Nat.testBit_xor, b1, b2] at h3
    exact absurd h3 (by decide)

theorem octCls_injective (o : ℕ) (ho : o < 759) :
    Function.Injective fun q : Fin 64 => octCls o ho q := fun q q' h =>
  Fin.ext (octCls_inj_nat o ho q q' q.2 q'.2 h)

theorem octCls_bijective (o : ℕ) (ho : o < 759) :
    Function.Bijective fun q : Fin 64 => octCls o ho q :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨octCls_injective o ho, by rw [Fintype.card_fin, card_evenQuot_octSupp]⟩

theorem neg_one_pow_eq_sgnI (n : ℕ) :
    ((-1 : ℚ) ^ n) = ((Native.sgnI (n % 2 == 1) : ℤ) : ℚ) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, Nat.even_iff.1 h]
    norm_num [Native.sgnI]
  · rw [h.neg_one_pow, Nat.odd_iff.1 h]
    norm_num [Native.sgnI]

theorem octHD_octCls
    (o : ℕ) (ho : o < 759) (q q' : ℕ) (hq : q < 64) (hq' : q' < 64) :
    octHD (octW o ho) (octCls o ho q) (octCls o ho q') =
      ((Native.octSign Native.evenTab[q]! Native.evenTab[q']! : ℤ) : ℚ) / 8 := by
  have hl := evenTab_lt q hq
  have hl' := evenTab_lt q' hq'
  have h1 : Native.evenTab[q]! < 256 := by omega
  have h1' : Native.evenTab[q']! < 256 := by omega
  have hand : Native.evenTab[q]! &&& Native.evenTab[q']! < 256 :=
    lt_of_le_of_lt Nat.and_le_left h1
  unfold octCls
  rw [octHD_cls _ (octSetG_subset o ho _ h1) (octSetG_even o ho q hq)
    (octSetG_subset o ho _ h1') (octSetG_even o ho q' hq'),
    ← octSetG_and o ho _ _ h1 h1', card_octSetG' o ho _ hand, card_octSetG' o ho _ h1',
    neg_one_pow_eq_sgnI]
  unfold Native.octSign
  rw [native_popcN]
  ring

end CFSG.Monster.AxisCount
