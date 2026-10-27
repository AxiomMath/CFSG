module

public import CFSG.Monster.B.Rep4371.Raw
public import CFSG.Monster.Griess.TrialityMatrix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess Matrix

theorem octCoeffs_size (hoct : Model.octDataOK = true) : Model.octCoeffs.size = 77 := by
  have h := hoct
  simp only [Model.octDataOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem oct_facts (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77) {m m' : ℕ}
    (hm : m < 256) (hm' : m' < 256) :
    let w := Model.wordN Model.octCoeffs[b]!
    (Model.spreadN w m &&& w = Model.spreadN w m) ∧
    Model.popcN 24 (Model.spreadN w m) = Model.popcN 8 m ∧
    Model.spreadN w (m ^^^ 255) = Model.spreadN w m ^^^ w ∧
    Model.spreadN w (m &&& m') = Model.spreadN w m &&& Model.spreadN w m' ∧
    (m = m' ∨ Model.spreadN w m % 16777216 ≠ Model.spreadN w m' % 16777216) := by
  have h := hoct
  simp only [Model.octDataOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h b hb m hm
  obtain ⟨h5, h6⟩ := h4 m' hm'
  exact ⟨h1, h2, h3, h5, h6⟩

theorem mem_octCoeffsOf {n a : ℕ} (h : a ∈ Model.octCoeffsOf n) :
    Model.popcN 24 (Model.wordN a) = 8 ∧ Model.wordN a % 4 = 3 := by
  rw [Model.octCoeffsOf, List.mem_toArray, List.mem_mergeSort, List.mem_filter] at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h.2

theorem octCoeffs_mem (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77) :
    Model.popcN 24 (Model.wordN Model.octCoeffs[b]!) = 8 ∧
      Model.wordN Model.octCoeffs[b]! % 4 = 3 := by
  have hs : b < Model.octCoeffs.size := (octCoeffs_size hoct).symm ▸ hb
  rw [getElem!_pos Model.octCoeffs b hs]
  exact mem_octCoeffsOf (n := 4096) (Array.getElem_mem hs)

@[expose] noncomputable def octadW (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77) :
    OctadWord :=
  ⟨octC b, by
    show hammingNorm ((toC Model.octCoeffs[b]! : C) : Fin 24 → ZMod 2) = 8
    rw [coe_toC, hammingNorm_bvec, ← popcN_eq_popc]
    exact (octCoeffs_mem hoct hb).1⟩

section Oct

variable (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77)

include hoct hb

theorem mem_octSupp_iff (i : Fin 24) :
    i ∈ octSupp (octadW hoct hb) ↔ (Model.wordN Model.octCoeffs[b]!).testBit i = true := by
  show i ∈ supp ((toC Model.octCoeffs[b]! : C) : Fin 24 → ZMod 2) ↔ _
  rw [supp, Finset.mem_filter, coe_toC, bvec_ne_zero_iff]
  simp

theorem octSet_subset {m : ℕ} (hm : m < 256) : octSet b m ⊆ octSupp (octadW hoct hb) := by
  intro i hi
  rw [mem_octSupp_iff]
  have h1 := (oct_facts hoct hb hm hm).1
  rw [octSet, Finset.mem_filter] at hi
  rw [← h1, Nat.testBit_and, Bool.and_eq_true] at hi
  exact hi.2.2

theorem card_octSet' {m : ℕ} (hm : m < 256) : (octSet b m).card = Model.popcN 8 m := by
  rw [card_octSet, ← popcN_eq_popc]
  exact (oct_facts hoct hb hm hm).2.1

theorem octSet_and {m m' : ℕ} (hm : m < 256) (hm' : m' < 256) :
    octSet b (m &&& m') = octSet b m ∩ octSet b m' := by
  ext i
  simp only [octSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    (oct_facts hoct hb hm hm').2.2.2.1, Nat.testBit_and, Bool.and_eq_true]

theorem octSet_compl {m : ℕ} (hm : m < 256) :
    octSet b (m ^^^ 255) = octSupp (octadW hoct hb) \ octSet b m := by
  ext i
  have h1 := (oct_facts hoct hb hm hm).1
  have h3 := (oct_facts hoct hb hm hm).2.2.1
  simp only [octSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    mem_octSupp_iff, h3, Nat.testBit_xor]
  have h1' := congrArg (fun x => x.testBit i) h1
  simp only [Nat.testBit_and] at h1'
  cases hs : (Model.spreadN (Model.wordN Model.octCoeffs[b]!) m).testBit i <;>
    cases hw : (Model.wordN Model.octCoeffs[b]!).testBit i <;> simp_all

theorem octSet_injective {m m' : ℕ} (hm : m < 256) (hm' : m' < 256)
    (h : octSet b m = octSet b m') : m = m' := by
  rcases (oct_facts hoct hb hm hm').2.2.2.2 with h' | h'
  · exact h'
  · refine absurd ?_ h'
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show (16777216 : ℕ) = 2 ^ 24 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < 24
    · have := congrArg (fun s => (⟨i, hi⟩ : Fin 24) ∈ s) h
      simp only [octSet, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      simp only [hi, decide_true, Bool.true_and]
      exact Bool.eq_iff_iff.2 this
    · simp [hi]

theorem exists_octSet_eq {ε : Finset (Fin 24)} (hε : ε ⊆ octSupp (octadW hoct hb)) :
    ∃ z < 256, octSet b z = ε := by
  classical
  let f : Fin 256 → (octSupp (octadW hoct hb)).powerset :=
    fun z => ⟨octSet b z, Finset.mem_powerset.2 (octSet_subset hoct hb z.2)⟩
  have hf : Function.Injective f := fun z z' h =>
    Fin.ext (octSet_injective hoct hb z.2 z'.2 (congrArg Subtype.val h))
  have hcard : Fintype.card (Fin 256) = Fintype.card (octSupp (octadW hoct hb)).powerset := by
    rw [Fintype.card_fin, Fintype.card_coe, Finset.card_powerset, card_octSupp]
    norm_num
  obtain ⟨z, hz⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩).2
    ⟨ε, Finset.mem_powerset.2 hε⟩
  exact ⟨z, z.2, congrArg Subtype.val hz⟩

end Oct

theorem localPairs_facts : ∀ i < 16,
    (Model.localPairs[i]!).1 < 256 ∧ (Model.localPairs[i]!).2 < 256 ∧
      Model.popcN 8 (Model.localPairs[i]!).1 % 2 = 0 ∧
      Model.popcN 8 (Model.localPairs[i]!).2 % 2 = 0 := by
  decide

theorem even_of_popcN {m : ℕ} (h : Model.popcN 8 m % 2 = 0) : Even (Model.popcN 8 m) :=
  Nat.even_iff.2 h

theorem octSign_eq (hsign : Model.octSignOK = true) {i z : ℕ} (hi : i < 16) (hz : z < 256)
    (he : Model.popcN 8 z % 2 = 0) :
    Model.octSign (Model.localPairs[i]!).1 z - Model.octSign (Model.localPairs[i]!).2 z =
      Model.sumRange (fun j => 2 * Model.Mentry i j *
        ((if z = (Model.localPairs[j]!).1 ∨ z = (Model.localPairs[j]!).1 ^^^ 255 then 1 else 0) -
          (if z = (Model.localPairs[j]!).2 ∨ z = (Model.localPairs[j]!).2 ^^^ 255 then 1 else 0)))
        16 := by
  have h := hsign
  simp only [Model.octSignOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  rcases h i hi z hz with h' | h'
  · omega
  · exact h'

theorem neg_one_pow_eq_sgnI (n : ℕ) : ((-1 : ℚ) ^ n) = ((Model.sgnI (n % 2 == 1) : ℤ) : ℚ) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, Nat.even_iff.1 h]
    rfl
  · rw [h.neg_one_pow, Nat.odd_iff.1 h]
    rfl

theorem octSet_and_lt {x z : ℕ} (hx : x < 256) : x &&& z < 256 :=
  lt_of_le_of_lt Nat.and_le_left hx

section OctTau

variable (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77)

@[expose] noncomputable def octT (w : Octad.EvenQuot (octSupp (octadW hoct hb))) : SpaceB :=
  tbasis (.inr (.inr (.inr ⟨octadW hoct hb, w⟩)))

include hoct hb

theorem inX_Xlift_rOct {m : ℕ} (hm : m < 256) (he : Model.popcN 8 m % 2 = 0) :
    inX (Xlift (rOct (octC b) (octSet b m))) =
      octT hoct hb (Octad.cls (octSupp (octadW hoct hb)) (octSet b m)) := by
  rw [octT, tbasis_oct_cls (octSet_subset hoct hb hm)]
  · rfl
  · rw [card_octSet' hoct hb hm]
    exact even_of_popcN he

theorem octVec_eq {i : ℕ} (hi : i < 16) :
    octVec b i = octT hoct hb (Octad.cls _ (octSet b (Model.localPairs[i]!).1)) -
      octT hoct hb (Octad.cls _ (octSet b (Model.localPairs[i]!).2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := localPairs_facts i hi
  rw [octVec, rawOct, ← inX_Xlift_rOct hoct hb h1 h3, ← inX_Xlift_rOct hoct hb h2 h4]
  simp [inX, Prod.mk_sub_mk]

theorem tauB_octT (v : Octad.EvenQuot (octSupp (octadW hoct hb))) :
    tauB (octT hoct hb v) = ∑ w, octHD (octadW hoct hb) v w • octT hoct hb w :=
  tauB_oct _ v

open _root_.Classical in
theorem octT_eq_sum (v : Octad.EvenQuot (octSupp (octadW hoct hb))) :
    octT hoct hb v = ∑ w, (if w = v then (1 : ℚ) else 0) • octT hoct hb w := by
  simp

open _root_.Classical in
theorem cls_octSet_eq_iff {z x : ℕ} (hz : z < 256) (hze : Model.popcN 8 z % 2 = 0) (hx : x < 256)
    (hxe : Model.popcN 8 x % 2 = 0) :
    Octad.cls (octSupp (octadW hoct hb)) (octSet b z) =
        Octad.cls (octSupp (octadW hoct hb)) (octSet b x) ↔ z = x ∨ z = x ^^^ 255 := by
  rw [Octad.cls_eq_cls_iff (octSet_subset hoct hb hz)
    (by rw [card_octSet' hoct hb hz]; exact even_of_popcN hze) (octSet_subset hoct hb hx)
    (by rw [card_octSet' hoct hb hx]; exact even_of_popcN hxe), ← octSet_compl hoct hb hz]
  have hz' : z ^^^ 255 < 256 := Nat.xor_lt_two_pow (n := 8) hz (by norm_num)
  constructor
  · rintro (h | h)
    · exact Or.inl (octSet_injective hoct hb hx hz h).symm
    · right
      have := octSet_injective hoct hb hx hz' h
      rw [this, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

open _root_.Classical in
theorem coef_octHD (hsign : Model.octSignOK = true) {i : ℕ} (hi : i < 16)
    (w : Octad.EvenQuot (octSupp (octadW hoct hb))) :
    octHD (octadW hoct hb) (Octad.cls _ (octSet b (Model.localPairs[i]!).1)) w -
        octHD (octadW hoct hb) (Octad.cls _ (octSet b (Model.localPairs[i]!).2)) w =
      ∑ j : Fin 16, ((Model.Mentry i j : ℚ) / 4) *
        ((if w = Octad.cls _ (octSet b (Model.localPairs[(j : ℕ)]!).1) then 1 else 0) -
          (if w = Octad.cls _ (octSet b (Model.localPairs[(j : ℕ)]!).2) then 1 else 0)) := by
  obtain ⟨ε, hεs, hεe, rfl⟩ := Octad.exists_cls_eq w
  obtain ⟨z, hz, rfl⟩ := exists_octSet_eq hoct hb hεs
  have hze : Model.popcN 8 z % 2 = 0 := by
    rw [card_octSet' hoct hb hz] at hεe
    exact Nat.even_iff.1 hεe
  obtain ⟨h1, h2, h3, h4⟩ := localPairs_facts i hi
  have hS : ∀ {m : ℕ}, m < 256 → Model.popcN 8 m % 2 = 0 → Even (octSet b m).card :=
    fun hm hme => by rw [card_octSet' hoct hb hm]; exact even_of_popcN hme
  rw [octHD_cls _ (octSet_subset hoct hb h1) (hS h1 h3) (octSet_subset hoct hb hz) hεe,
    octHD_cls _ (octSet_subset hoct hb h2) (hS h2 h4) (octSet_subset hoct hb hz) hεe,
    ← octSet_and hoct hb h1 hz, ← octSet_and hoct hb h2 hz,
    card_octSet' hoct hb (octSet_and_lt h1), card_octSet' hoct hb (octSet_and_lt h2),
    card_octSet' hoct hb hz, neg_one_pow_eq_sgnI, neg_one_pow_eq_sgnI]
  have key := congrArg (fun n : ℤ => (n : ℚ)) (octSign_eq hsign hi hz hze)
  simp only [Model.octSign, Int.cast_sub, cast_sumRange] at key
  rw [← mul_sub, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨h1j, h2j, h3j, h4j⟩ := localPairs_facts j j.2
  have e1 : (if Octad.cls (octSupp (octadW hoct hb)) (octSet b z) =
      Octad.cls (octSupp (octadW hoct hb)) (octSet b (Model.localPairs[(j : ℕ)]!).1)
        then (1 : ℚ) else 0) =
      (((if z = (Model.localPairs[(j : ℕ)]!).1 ∨ z = (Model.localPairs[(j : ℕ)]!).1 ^^^ 255
        then 1 else 0 : ℤ)) : ℚ) := by
    by_cases h : z = (Model.localPairs[(j : ℕ)]!).1 ∨ z = (Model.localPairs[(j : ℕ)]!).1 ^^^ 255
    · rw [ite_eq_left ((cls_octSet_eq_iff hoct hb hz hze h1j h3j).2 h), ite_eq_left h]
      norm_num
    · rw [ite_eq_right (fun h' => h ((cls_octSet_eq_iff hoct hb hz hze h1j h3j).1 h')),
        ite_eq_right h]
      norm_num
  have e2 : (if Octad.cls (octSupp (octadW hoct hb)) (octSet b z) =
      Octad.cls (octSupp (octadW hoct hb)) (octSet b (Model.localPairs[(j : ℕ)]!).2)
        then (1 : ℚ) else 0) =
      (((if z = (Model.localPairs[(j : ℕ)]!).2 ∨ z = (Model.localPairs[(j : ℕ)]!).2 ^^^ 255
        then 1 else 0 : ℤ)) : ℚ) := by
    by_cases h : z = (Model.localPairs[(j : ℕ)]!).2 ∨ z = (Model.localPairs[(j : ℕ)]!).2 ^^^ 255
    · rw [ite_eq_left ((cls_octSet_eq_iff hoct hb hz hze h2j h4j).2 h), ite_eq_left h]
      norm_num
    · rw [ite_eq_right (fun h' => h ((cls_octSet_eq_iff hoct hb hz hze h2j h4j).1 h')),
        ite_eq_right h]
      norm_num
  rw [e1, e2]
  push_cast
  ring

theorem tauB_octVec (hsign : Model.octSignOK = true) {i : ℕ} (hi : i < 16) :
    tauB (octVec b i) = ∑ j : Fin 16, ((Model.Mentry i j : ℚ) / 4) • octVec b j := by
  classical
  set T := octT hoct hb
  set v := Octad.cls (octSupp (octadW hoct hb)) (octSet b (Model.localPairs[i]!).1)
  set v' := Octad.cls (octSupp (octadW hoct hb)) (octSet b (Model.localPairs[i]!).2)
  set ind : Fin 16 → Octad.EvenQuot (octSupp (octadW hoct hb)) → ℚ := fun j w =>
    (if w = Octad.cls _ (octSet b (Model.localPairs[(j : ℕ)]!).1) then (1 : ℚ) else 0) -
      (if w = Octad.cls _ (octSet b (Model.localPairs[(j : ℕ)]!).2) then 1 else 0)
  have h : ∀ j : Fin 16, octVec b j = ∑ w, ind j w • T w := by
    intro j
    rw [octVec_eq hoct hb j.2, octT_eq_sum hoct hb, octT_eq_sum hoct hb,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => (sub_smul _ _ _).symm
  have hl : tauB (octVec b i) =
      ∑ w, (octHD (octadW hoct hb) v w - octHD (octadW hoct hb) v' w) • T w := by
    rw [octVec_eq hoct hb hi, map_sub, tauB_octT, tauB_octT, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => (sub_smul _ _ _).symm
  have hr : ∑ j : Fin 16, ((Model.Mentry i j : ℚ) / 4) • octVec b j =
      ∑ w, (∑ j : Fin 16, ((Model.Mentry i j : ℚ) / 4) * ind j w) • T w := by
    calc ∑ j : Fin 16, ((Model.Mentry i j : ℚ) / 4) • octVec b j
        = ∑ j : Fin 16, ∑ w, (((Model.Mentry i j : ℚ) / 4) * ind j w) • T w :=
          Finset.sum_congr rfl fun j _ => by
            rw [h j, Finset.smul_sum]
            exact Finset.sum_congr rfl fun w _ => smul_smul _ _ _
      _ = ∑ w, ∑ j : Fin 16, (((Model.Mentry i j : ℚ) / 4) * ind j w) • T w := Finset.sum_comm
      _ = ∑ w, (∑ j : Fin 16, ((Model.Mentry i j : ℚ) / 4) * ind j w) • T w :=
          Finset.sum_congr rfl fun w _ => Finset.sum_smul.symm
  rw [hl, hr]
  exact Finset.sum_congr rfl fun w _ => congrArg (· • T w) (coef_octHD hoct hb hsign hi w)

end OctTau

end CFSG.Monster.B.Rep4371
