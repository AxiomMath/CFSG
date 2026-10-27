module

public import CFSG.GH74.Uniqueness.SU.SU13TA3PermE
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.KFacts.K412Alternating
import CFSG.RankThree.PartTwo.Sec15.ThmDA10Core
import CFSG.Quasithin.Background.SmithC27Perm
import CFSG.GroupTheory.TwoReflections
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Perm3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10
open CFSG.RankThree.PartTwo.KFacts.KP2

@[expose] def atilde : Subgroup (Perm (Fin 10)) := Subgroup.closure {pa, pb, pc}

@[expose] def blockPt (k r : Fin 3) : Fin 10 := ⟨3 * k.val + r.val, by omega⟩

@[expose] def block (k : Fin 3) : Finset (Fin 10) := Finset.univ.image (blockPt k)

@[expose] def tBlock (k : Fin 3) : Finset (Fin 10) := insert 9 (block k)

@[expose] def kleinV (k : Fin 3) : Subgroup (Perm (Fin 10)) :=
  Subgroup.closure {swap (blockPt k 0) (blockPt k 1) * swap (blockPt k 2) 9,
    swap (blockPt k 0) (blockPt k 2) * swap (blockPt k 1) 9}

@[expose] def altOff (s : Finset (Fin 10)) : Subgroup (Perm (Fin 10)) :=
  alternatingGroup (Fin 10) ⊓ fixingSubgroup (Perm (Fin 10)) (s : Set (Fin 10))

theorem blockPt_injective (k : Fin 3) : Function.Injective (blockPt k) := by
  intro r r' h
  apply Fin.ext
  simp only [blockPt, Fin.mk.injEq] at h
  omega

theorem blockPt_ne_nine (k r : Fin 3) : blockPt k r ≠ 9 := by
  intro h
  have := congrArg Fin.val h
  simp only [blockPt, Fin.val_mk] at this
  omega

theorem mem_block_iff {k : Fin 3} {x : Fin 10} :
    x ∈ block k ↔ ∃ r : Fin 3, x = blockPt k r := by
  simp [block, eq_comm]

theorem blockPt_mem (k r : Fin 3) : blockPt k r ∈ block k :=
  mem_block_iff.mpr ⟨r, rfl⟩

theorem card_block (k : Fin 3) : (block k).card = 3 := by
  rw [block, Finset.card_image_of_injective _ (blockPt_injective k), Finset.card_univ,
    Fintype.card_fin]

theorem disjoint_block {j k : Fin 3} (hjk : j ≠ k) : Disjoint (block j) (block k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨r, hxr⟩ := mem_block_iff.mp hx
  obtain ⟨s, hs⟩ := mem_block_iff.mp hy
  have hv : 3 * j.val + r.val = 3 * k.val + s.val := by
    calc 3 * j.val + r.val = x.val := by rw [hxr]; rfl
      _ = 3 * k.val + s.val := by rw [hs]; rfl
  have hj := j.isLt
  have hk := k.isLt
  have hr := r.isLt
  have hs' := s.isLt
  have : j.val = k.val := by omega
  exact hjk (Fin.ext this)

theorem mem_tBlock_iff {k : Fin 3} {x : Fin 10} :
    x ∈ tBlock k ↔ x = 9 ∨ x ∈ block k := by
  simp [tBlock]

theorem nine_mem_tBlock (k : Fin 3) : (9 : Fin 10) ∈ tBlock k := by
  simp [tBlock]

theorem block_subset_tBlock (k : Fin 3) : block k ⊆ tBlock k := by
  intro x hx
  exact mem_tBlock_iff.mpr (Or.inr hx)

theorem card_tBlock (k : Fin 3) : (tBlock k).card = 4 := by
  have h9 : (9 : Fin 10) ∉ block k := by
    intro h
    obtain ⟨r, hr⟩ := mem_block_iff.mp h
    exact blockPt_ne_nine k r hr.symm
  rw [tBlock, Finset.card_insert_of_notMem h9, card_block]

theorem support_toP (i j k : Fin 3) : (toP i j k).support =
    (if i = 0 then ∅ else block 0) ∪ (if j = 0 then ∅ else block 1) ∪
      (if k = 0 then ∅ else block 2) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

private def atildeF : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ i j k : Fin 3, x = toP i j k}
  one_mem' := ⟨0, 0, 0, by decide +kernel⟩
  mul_mem' := by
    rintro x y ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact ⟨i + i', j + j', k + k',
      CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul i j k i' j' k'⟩
  inv_mem' := by
    rintro x ⟨i, j, k, rfl⟩
    have h3 : toP i j k ^ 3 = 1 := CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i j k
    have hmul : toP i j k * (toP i j k * toP i j k) = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using h3
    refine ⟨i + i, j + j, k + k, ?_⟩
    rw [← CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul i j k i j k]
    exact inv_eq_of_mul_eq_one_right hmul

private theorem atilde_eq_atildeF : atilde = atildeF := by
  apply le_antisymm
  · rw [atilde, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by decide +kernel⟩
    · exact ⟨0, 1, 0, by decide +kernel⟩
    · exact ⟨0, 0, 1, by decide +kernel⟩
  · rintro x ⟨i, j, k, rfl⟩
    rw [atilde]
    simp only [toP]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem mem_atilde_iff {x : Perm (Fin 10)} : x ∈ atilde ↔ ∃ i j k : Fin 3, x = toP i j k := by
  rw [atilde_eq_atildeF]
  rfl

theorem card_support_of_mem_atilde {x : Perm (Fin 10)} (hx : x ∈ atilde) (h1 : x ≠ 1) :
    x.support.card = 3 ∨ x.support.card = 6 ∨ x.support.card = 9 := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | (exfalso; exact h1 (by decide +kernel))
      | decide +kernel

theorem card_atilde : Nat.card atilde = 27 := by
  let f : Fin 3 × Fin 3 × Fin 3 → atilde := fun p =>
    ⟨toP p.1 p.2.1 p.2.2, mem_atilde_iff.mpr ⟨p.1, p.2.1, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
      have h' := congrArg (fun x : atilde => (x : Perm (Fin 10))) h
      simp only [f] at h'
      obtain ⟨h1, h2, h3⟩ := toP_injective h'
      exact Prod.ext h1 (Prod.ext h2 h3)
    · rintro ⟨x, hx⟩
      obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
      exact ⟨(i, j, k), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp [Nat.card_prod]

theorem isElemAbelian_atilde : CFSG.Open.IsElemAbelian 3 atilde := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, j, k, hx⟩ := mem_atilde_iff.mp x.2
    obtain ⟨i', j', k', hy⟩ := mem_atilde_iff.mp y.2
    refine Subtype.ext ?_
    change (x : Perm (Fin 10)) * (y : Perm (Fin 10)) =
      (y : Perm (Fin 10)) * (x : Perm (Fin 10))
    rw [hx, hy, CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul,
      CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul, add_comm i' i, add_comm j' j,
      add_comm k' k]
  · obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
    exact CFSG.RankThree.PartTwo.Sec15.ThmD.toP_pow_three i j k

private theorem commute_of_mem_atilde {a b : Perm (Fin 10)} (ha : a ∈ atilde) (hb : b ∈ atilde) :
    Commute a b := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp ha
  obtain ⟨i', j', k', rfl⟩ := mem_atilde_iff.mp hb
  show toP i j k * toP i' j' k' = toP i' j' k' * toP i j k
  rw [CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul,
    CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul, add_comm i' i, add_comm j' j,
    add_comm k' k]

private theorem cycleType_of_support_three_or_six {x : Perm (Fin 10)} (h3 : x ^ 3 = 1)
    (hne : x ≠ 1) (hsupp : x.support.card = 3 ∨ x.support.card = 6) :
    x.cycleType = {3} ∨ x.cycleType = {3, 3} := by
  have hord : orderOf x = 3 :=
    orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) h3 hne
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hn
  have hsum := congrArg Multiset.sum hn
  rw [Equiv.Perm.sum_cycleType, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hnle : n ≤ 1 := by
    rcases hsupp with h | h <;> rw [h] at hsum <;> omega
  interval_cases n
  · left; rw [hn]; rfl
  · right; rw [hn]; rfl

theorem atilde_le_alternatingGroup : atilde ≤ alternatingGroup (Fin 10) := by
  intro x hx
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  exact Perm.mem_alternatingGroup.mpr (sign_toP i j k)

theorem atilde_eq_map_Ebar : atilde = Ebar.map (alternatingGroup (Fin 10)).subtype := by
  ext x
  rw [mem_atilde_iff]
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact Subgroup.mem_map.mpr ⟨toE i j k, mem_Ebar_iff_toE.mpr ⟨i, j, k, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hy
    exact ⟨i, j, k, rfl⟩

theorem centralizer_atilde : Subgroup.centralizer (atilde : Set (Perm (Fin 10))) = atilde := by
  apply le_antisymm
  · intro x hx
    have hx' := Subgroup.mem_centralizer_iff.mp hx
    have ha : Commute x pa :=
      (hx' pa (by rw [atilde]; exact Subgroup.subset_closure (by simp))).symm
    have hb : Commute x pb :=
      (hx' pb (by rw [atilde]; exact Subgroup.subset_closure (by simp))).symm
    have hc : Commute x pc :=
      (hx' pc (by rw [atilde]; exact Subgroup.subset_closure (by simp))).symm
    obtain ⟨i, j, k, rfl⟩ := exists_toP_of_commute ha hb hc
    exact mem_atilde_iff.mpr ⟨i, j, k, rfl⟩
  · intro x hx
    obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i', j', k', rfl⟩ := mem_atilde_iff.mp hy
    change toP i' j' k' * toP i j k = toP i j k * toP i' j' k'
    rw [CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul,
      CFSG.RankThree.PartTwo.Sec15.ThmD.wt2_toP_mul, add_comm i i', add_comm j j',
      add_comm k k']

private def kv1 (k : Fin 3) : Perm (Fin 10) :=
  swap (blockPt k 0) (blockPt k 1) * swap (blockPt k 2) 9

private def kv2 (k : Fin 3) : Perm (Fin 10) :=
  swap (blockPt k 0) (blockPt k 2) * swap (blockPt k 1) 9

private def kv3 (k : Fin 3) : Perm (Fin 10) :=
  swap (blockPt k 0) 9 * swap (blockPt k 1) (blockPt k 2)

private theorem blockPt_ne_of_ne {k : Fin 3} {r s : Fin 3} (h : r ≠ s) :
    blockPt k r ≠ blockPt k s := fun e => h (blockPt_injective k e)

private theorem sq_one_apply_apply {v : Perm (Fin 10)} (hv2 : v ^ 2 = 1) (x : Fin 10) :
    v (v x) = x := by
  have := congrArg (fun f : Perm (Fin 10) => f x) hv2
  simpa [pow_two] using this

private theorem eq_swap_mul_swap_of_apply {a b c d : Fin 10}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {v : Perm (Fin 10)} (hva : v a = b) (hvb : v b = a) (hvc : v c = d) (hvd : v d = c)
    (hfix : ∀ x, ¬ (x = a ∨ x = b ∨ x = c ∨ x = d) → v x = x) :
    v = swap a b * swap c d := by
  ext y
  by_cases hy : y = a ∨ y = b ∨ y = c ∨ y = d
  · rcases hy with rfl | rfl | rfl | rfl
    · simp only [hva, Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hac had]
    · simp only [hvb, Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hbc hbd]
    · simp only [hvc, Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
    · simp only [hvd, Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · have hya : y ≠ a := fun e => hy (Or.inl e)
    have hyb : y ≠ b := fun e => hy (Or.inr (Or.inl e))
    have hyc : y ≠ c := fun e => hy (Or.inr (Or.inr (Or.inl e)))
    have hyd : y ≠ d := fun e => hy (Or.inr (Or.inr (Or.inr e)))
    rw [hfix y (by simp [hya, hyb, hyc, hyd])]
    simp [swap_apply_of_ne_of_ne, hya, hyb, hyc, hyd]

private theorem maps_other_pair_of_sq_one {a b c d : Fin 10}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {v : Perm (Fin 10)} (hv2 : v ^ 2 = 1)
    (hT : ∀ x, x ∈ v.support ↔ x = a ∨ x = b ∨ x = c ∨ x = d)
    (hva : v a = b) (hvb : v b = a) :
    v c = d ∧ v d = c := by
  have hvv : ∀ x, v (v x) = x := fun x => sq_one_apply_apply hv2 x
  constructor
  · have hc_s : c ∈ v.support := by rw [hT]; exact Or.inr (Or.inr (Or.inl rfl))
    have hc_mem : v c ∈ v.support := Equiv.Perm.apply_mem_support.mpr hc_s
    rw [hT] at hc_mem
    have hc_ne : v c ≠ c := by simpa [Equiv.Perm.mem_support] using hc_s
    rcases hc_mem with e | e | e | e
    · have hcb : c = b := by rw [← hvv c, e, hva]
      exact (hbc hcb.symm).elim
    · have hca : c = a := by rw [← hvv c, e, hvb]
      exact (hac hca.symm).elim
    · exact (hc_ne e).elim
    · exact e
  · have hd_s : d ∈ v.support := by rw [hT]; exact Or.inr (Or.inr (Or.inr rfl))
    have hd_mem : v d ∈ v.support := Equiv.Perm.apply_mem_support.mpr hd_s
    rw [hT] at hd_mem
    have hd_ne : v d ≠ d := by simpa [Equiv.Perm.mem_support] using hd_s
    rcases hd_mem with e | e | e | e
    · have hdb : d = b := by rw [← hvv d, e, hva]
      exact (hbd hdb.symm).elim
    · have hda : d = a := by rw [← hvv d, e, hvb]
      exact (had hda.symm).elim
    · exact e
    · exact (hd_ne e).elim

private theorem eq_doubleTransposition_of_sq_one_support {a b c d : Fin 10}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {v : Perm (Fin 10)} (hv2 : v ^ 2 = 1) (hv : v.support = {a, b, c, d}) :
    v = swap a b * swap c d ∨ v = swap a c * swap b d ∨ v = swap a d * swap b c := by
  classical
  have hT : ∀ x, x ∈ v.support ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x; rw [hv]; simp
  have hfix : ∀ x, ¬ (x = a ∨ x = b ∨ x = c ∨ x = d) → v x = x := by
    intro x hx
    have hx' : x ∉ v.support := by rwa [hT]
    simpa [Equiv.Perm.mem_support, not_not] using hx'
  have hvv : ∀ x, v (v x) = x := fun x => sq_one_apply_apply hv2 x
  have ha : v a ≠ a := by
    have : a ∈ v.support := by rw [hT]; exact Or.inl rfl
    simpa [Equiv.Perm.mem_support] using this
  have hva_mem : v a ∈ v.support :=
    Equiv.Perm.apply_mem_support.mpr (Equiv.Perm.mem_support.mpr ha)
  rw [hT] at hva_mem
  rcases hva_mem with h | h | h | h
  · exact (ha h).elim
  · have hvb : v b = a := by
      have := hvv a
      rwa [h] at this
    obtain ⟨hvc, hvd⟩ := maps_other_pair_of_sq_one hab hac had hbc hbd hcd hv2 hT h hvb
    exact Or.inl (eq_swap_mul_swap_of_apply hab hac had hbc hbd hcd h hvb hvc hvd hfix)
  · have hvc : v c = a := by
      have := hvv a
      rwa [h] at this
    have hT_acbd : ∀ x, x ∈ v.support ↔ x = a ∨ x = c ∨ x = b ∨ x = d := by
      intro x; rw [hT]; simp [or_comm, or_assoc, or_left_comm]
    have hfix_acbd : ∀ x, ¬ (x = a ∨ x = c ∨ x = b ∨ x = d) → v x = x := by
      intro x hx
      exact hfix x (by simpa [or_comm, or_assoc, or_left_comm] using hx)
    obtain ⟨hvb, hvd⟩ := maps_other_pair_of_sq_one hac hab had hbc.symm hcd hbd hv2 hT_acbd h hvc
    exact Or.inr (Or.inl (eq_swap_mul_swap_of_apply hac hab had hbc.symm hcd hbd
      h hvc hvb hvd hfix_acbd))
  · have hvd : v d = a := by
      have := hvv a
      rwa [h] at this
    have hT_adbc : ∀ x, x ∈ v.support ↔ x = a ∨ x = d ∨ x = b ∨ x = c := by
      intro x; rw [hT]; simp [or_comm, or_assoc, or_left_comm]
    have hfix_adbc : ∀ x, ¬ (x = a ∨ x = d ∨ x = b ∨ x = c) → v x = x := by
      intro x hx
      exact hfix x (by simpa [or_comm, or_assoc, or_left_comm] using hx)
    obtain ⟨hvb, hvc⟩ := maps_other_pair_of_sq_one had hab hac hbd.symm hcd.symm hbc
      hv2 hT_adbc h hvd
    exact Or.inr (Or.inr (eq_swap_mul_swap_of_apply had hab hac hbd.symm hcd.symm hbc
      h hvd hvb hvc hfix_adbc))

private theorem tBlock_eq_insert (k : Fin 3) :
    tBlock k = {blockPt k 0, blockPt k 1, blockPt k 2, 9} := by
  rw [tBlock, block]
  ext x
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro (rfl | ⟨r, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · fin_cases r <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · right; exact ⟨0, rfl⟩
    · right; exact ⟨1, rfl⟩
    · right; exact ⟨2, rfl⟩
    · left; rfl

private theorem eq_kv_of_sq_one_support {k : Fin 3} {v : Perm (Fin 10)}
    (hv2 : v ^ 2 = 1) (hv : v.support = tBlock k) :
    v = kv1 k ∨ v = kv2 k ∨ v = kv3 k := by
  have h := eq_doubleTransposition_of_sq_one_support
    (a := blockPt k 0) (b := blockPt k 1) (c := blockPt k 2) (d := 9)
    (blockPt_ne_of_ne (by decide)) (blockPt_ne_of_ne (by decide))
    (blockPt_ne_nine k 0) (blockPt_ne_of_ne (by decide))
    (blockPt_ne_nine k 1) (blockPt_ne_nine k 2) hv2 (by rwa [tBlock_eq_insert] at hv)
  simpa [kv1, kv2, kv3] using h

private def kleinVK (k : Fin 3) : Subgroup (Perm (Fin 10)) where
  carrier := {v | v = 1 ∨ v = kv1 k ∨ v = kv2 k ∨ v = kv3 k}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      fin_cases k <;> decide +kernel
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl) <;> fin_cases k <;> decide +kernel

private theorem kleinV_eq_kleinVK (k : Fin 3) : kleinV k = kleinVK k := by
  apply le_antisymm
  · rw [kleinV, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rintro x (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by left; rfl)
    · exact Subgroup.subset_closure (by right; rfl)
    · rw [kv3, show swap (blockPt k 0) 9 * swap (blockPt k 1) (blockPt k 2) =
        kv1 k * kv2 k by fin_cases k <;> decide +kernel]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by left; rfl))
        (Subgroup.subset_closure (by right; rfl))

theorem mem_kleinV_iff {k : Fin 3} {v : Perm (Fin 10)} :
    v ∈ kleinV k ↔ v = 1 ∨ (v ^ 2 = 1 ∧ v.support = tBlock k) := by
  rw [kleinV_eq_kleinVK]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · right
      refine ⟨?_, ?_⟩ <;> fin_cases k <;> decide +kernel
    · right
      refine ⟨?_, ?_⟩ <;> fin_cases k <;> decide +kernel
    · right
      refine ⟨?_, ?_⟩ <;> fin_cases k <;> decide +kernel
  · rintro (rfl | ⟨hv2, hv⟩)
    · exact Or.inl rfl
    · rcases eq_kv_of_sq_one_support hv2 hv with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

theorem card_kleinV (k : Fin 3) : Nat.card (kleinV k) = 4 := by
  rw [kleinV_eq_kleinVK]
  let f : Fin 4 → kleinVK k
    | ⟨0, _⟩ => ⟨1, Or.inl rfl⟩
    | ⟨1, _⟩ => ⟨kv1 k, Or.inr (Or.inl rfl)⟩
    | ⟨2, _⟩ => ⟨kv2 k, Or.inr (Or.inr (Or.inl rfl))⟩
    | ⟨3, _⟩ => ⟨kv3 k, Or.inr (Or.inr (Or.inr rfl))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      fin_cases m <;> fin_cases n <;> fin_cases k <;> simp [f] at h ⊢
      all_goals exact absurd h (by decide +kernel)
    · rintro ⟨v, hv⟩
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem mem_normalizer_kleinV {k : Fin 3} {g : Perm (Fin 10)}
    (hg : ∀ i ∈ tBlock k, g i ∈ tBlock k) :
    g ∈ normalizer (kleinV k : Set (Perm (Fin 10))) := by
  have himage_of : ∀ h : Perm (Fin 10), (∀ i ∈ tBlock k, h i ∈ tBlock k) →
      Finset.map (Equiv.toEmbedding h) (tBlock k) = tBlock k := by
    intro h hh
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact hh y hy
    · simp [card_tBlock]
  have key : ∀ h : Perm (Fin 10), (∀ i ∈ tBlock k, h i ∈ tBlock k) →
      ∀ u : Perm (Fin 10), u ∈ kleinV k → h * u * h⁻¹ ∈ kleinV k := by
    intro h hh u hu
    have himage := himage_of h hh
    rw [mem_kleinV_iff] at hu ⊢
    rcases hu with rfl | ⟨hu2, hus⟩
    · exact Or.inl (by simp)
    · right
      refine ⟨?_, ?_⟩
      · rw [conj_pow, hu2, mul_one]
        simp
      · rw [Equiv.Perm.support_conj, hus, himage]
  have himage := himage_of g hg
  have hg' : ∀ i ∈ tBlock k, g⁻¹ i ∈ tBlock k := by
    intro i hi
    have : i ∈ Finset.map (Equiv.toEmbedding g) (tBlock k) := by rw [himage]; exact hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp this
    have hgj : g⁻¹ i = j := by rw [← hji]; simp
    rw [hgj]
    exact hj
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact key g hg v hv
  · intro hv
    have hv' : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [hv']
    exact key g⁻¹ hg' (g * v * g⁻¹) hv

private def sh : Perm (Fin 10) := swap 6 9
private def csh : MulAut (Perm (Fin 10)) := MulAut.conj sh

private theorem sh_sq : sh * sh = 1 := by decide +kernel
private theorem sh_inv : sh⁻¹ = sh := inv_eq_of_mul_eq_one_right sh_sq
private theorem csh_apply (x : Perm (Fin 10)) : csh x = sh * x * sh := by
  simp [csh, MulAut.conj_apply, sh_inv]
private theorem csh_invol : ∀ x : Perm (Fin 10), csh (csh x) = x := by
  intro x
  rw [csh_apply, csh_apply]
  calc sh * (sh * x * sh) * sh = (sh * sh) * x * (sh * sh) := by group
    _ = x := by rw [sh_sq]; simp

private theorem csh_pa : csh pa = pa := by decide +kernel
private theorem csh_pb : csh pb = pb := by decide +kernel
private theorem csh_pc : csh pc = dThree ^ 2 := by decide +kernel
private theorem csh_dOne : csh dOne = pa ^ 2 := by decide +kernel
private theorem csh_dTwo : csh dTwo = pb ^ 2 := by decide +kernel
private theorem csh_dThree : csh dThree = pc ^ 2 := by decide +kernel

private theorem map_sh_atilde_le : atilde.map csh.toMonoidHom ≤ eTwentySeven := by
  rw [atilde, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · change csh pa ∈ eTwentySeven
    rw [csh_pa]; exact ⟨2, 0, 0, by decide +kernel⟩
  · change csh pb ∈ eTwentySeven
    rw [csh_pb]; exact ⟨0, 2, 0, by decide +kernel⟩
  · change csh pc ∈ eTwentySeven
    rw [csh_pc]; exact ⟨0, 0, 2, by decide +kernel⟩

private theorem map_sh_eTwentySeven_le : eTwentySeven.map csh.toMonoidHom ≤ atilde := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, b, c, rfl⟩ := hy
  rw [eTwentySevenF]
  rw [map_mul, map_mul, map_pow, map_pow, map_pow]
  change csh dOne ^ (a : ℕ) * csh dTwo ^ (b : ℕ) * csh dThree ^ (c : ℕ) ∈ atilde
  rw [csh_dOne, csh_dTwo, csh_dThree]
  have hpa : pa ^ 2 ∈ atilde := mem_atilde_iff.mpr ⟨2, 0, 0, by decide +kernel⟩
  have hpb : pb ^ 2 ∈ atilde := mem_atilde_iff.mpr ⟨0, 2, 0, by decide +kernel⟩
  have hpc : pc ^ 2 ∈ atilde := mem_atilde_iff.mpr ⟨0, 0, 2, by decide +kernel⟩
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ hpa _) (Subgroup.pow_mem _ hpb _))
    (Subgroup.pow_mem _ hpc _)

private theorem map_sh_eTwentySeven_ge : eTwentySeven ≤ atilde.map csh.toMonoidHom := by
  intro x hx
  have hx' : csh x ∈ atilde := map_sh_eTwentySeven_le (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  exact Subgroup.mem_map.mpr ⟨csh x, hx', csh_invol x⟩

private theorem map_sh_atilde : atilde.map csh.toMonoidHom = eTwentySeven := by
  apply le_antisymm map_sh_atilde_le
  exact map_sh_eTwentySeven_ge

private theorem kOne_eq_closure : kOne = Subgroup.closure {kOneF 1, kOneF 2} := by
  apply le_antisymm
  · rintro x ⟨m, rfl⟩
    fin_cases m
    · exact one_mem _
    · exact Subgroup.subset_closure (by left; rfl)
    · exact Subgroup.subset_closure (by right; rfl)
    · change kOneF 3 ∈ Subgroup.closure {kOneF 1, kOneF 2}
      rw [show kOneF 3 = kOneF 1 * kOneF 2 by decide +kernel]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by left; rfl))
        (Subgroup.subset_closure (by right; rfl))
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem kTwo_eq_closure : kTwo = Subgroup.closure {kTwoF 1, kTwoF 2} := by
  apply le_antisymm
  · rintro x ⟨m, rfl⟩
    fin_cases m
    · exact one_mem _
    · exact Subgroup.subset_closure (by left; rfl)
    · exact Subgroup.subset_closure (by right; rfl)
    · change kTwoF 3 ∈ Subgroup.closure {kTwoF 1, kTwoF 2}
      rw [show kTwoF 3 = kTwoF 1 * kTwoF 2 by decide +kernel]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by left; rfl))
        (Subgroup.subset_closure (by right; rfl))
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem kThree_eq_closure : kThree = Subgroup.closure {kThreeF 1, kThreeF 2} := by
  apply le_antisymm
  · rintro x ⟨m, rfl⟩
    fin_cases m
    · exact one_mem _
    · exact Subgroup.subset_closure (by left; rfl)
    · exact Subgroup.subset_closure (by right; rfl)
    · change kThreeF 3 ∈ Subgroup.closure {kThreeF 1, kThreeF 2}
      rw [show kThreeF 3 = kThreeF 1 * kThreeF 2 by decide +kernel]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by left; rfl))
        (Subgroup.subset_closure (by right; rfl))
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem csh_kOneF1 :
    csh (kOneF 1) = swap (blockPt 0 0) (blockPt 0 1) * swap (blockPt 0 2) 9 := by
  decide +kernel
private theorem csh_kOneF2 :
    csh (kOneF 2) = swap (blockPt 0 0) (blockPt 0 2) * swap (blockPt 0 1) 9 := by
  decide +kernel
private theorem csh_kTwoF1 :
    csh (kTwoF 1) = swap (blockPt 1 0) (blockPt 1 1) * swap (blockPt 1 2) 9 := by
  decide +kernel
private theorem csh_kTwoF2 :
    csh (kTwoF 2) = swap (blockPt 1 0) (blockPt 1 2) * swap (blockPt 1 1) 9 := by
  decide +kernel
private theorem csh_kThreeF1 : csh (kThreeF 1) = kThreeF 2 := by decide +kernel
private theorem csh_kThreeF2 : csh (kThreeF 2) = kThreeF 1 := by decide +kernel

private theorem map_sh_kOne : kOne.map csh.toMonoidHom = kleinV 0 := by
  rw [kOne_eq_closure, MonoidHom.map_closure]
  rw [show csh.toMonoidHom '' ({kOneF 1, kOneF 2} : Set (Perm (Fin 10))) =
      {swap (blockPt 0 0) (blockPt 0 1) * swap (blockPt 0 2) 9,
       swap (blockPt 0 0) (blockPt 0 2) * swap (blockPt 0 1) 9} by
    ext x; simp [csh_kOneF1, csh_kOneF2]]
  rfl

private theorem map_sh_kTwo : kTwo.map csh.toMonoidHom = kleinV 1 := by
  rw [kTwo_eq_closure, MonoidHom.map_closure]
  rw [show csh.toMonoidHom '' ({kTwoF 1, kTwoF 2} : Set (Perm (Fin 10))) =
      {swap (blockPt 1 0) (blockPt 1 1) * swap (blockPt 1 2) 9,
       swap (blockPt 1 0) (blockPt 1 2) * swap (blockPt 1 1) 9} by
    ext x; simp [csh_kTwoF1, csh_kTwoF2]]
  rfl

private theorem map_sh_kThree : kThree.map csh.toMonoidHom = kleinV 2 := by
  rw [kThree_eq_closure, MonoidHom.map_closure]
  rw [show csh.toMonoidHom '' ({kThreeF 1, kThreeF 2} : Set (Perm (Fin 10))) =
      {kThreeF 1, kThreeF 2} by
    ext x; simp [csh_kThreeF1, csh_kThreeF2, or_comm]]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.KFacts.KP2
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem exists_le_kleinV {W : Subgroup (Perm (Fin 10))}
    (hW : atilde ≤ normalizer (W : Set (Perm (Fin 10)))) (hcop : Nat.Coprime (Nat.card W) 3) :
    ∃ k : Fin 3, W ≤ kleinV k := by
  let c : MulAut (Perm (Fin 10)) := MulAut.conj sh
  let Q : Subgroup (Perm (Fin 10)) := W.map c.toMonoidHom
  have hQnorm : eTwentySeven ≤ normalizer (Q : Set (Perm (Fin 10))) := by
    have h1 : atilde.map c.toMonoidHom ≤ normalizer (Q : Set (Perm (Fin 10))) := by
      have h := Subgroup.map_mono (f := c.toMonoidHom) hW
      rwa [Subgroup.map_equiv_normalizer_eq W c] at h
    have hmap : atilde.map c.toMonoidHom = eTwentySeven := by simpa [c, csh] using map_sh_atilde
    rwa [hmap] at h1
  have hcop' : ¬ 3 ∣ Nat.card Q := by
    change ¬ 3 ∣ Nat.card (W.map c.toMonoidHom)
    rw [Subgroup.card_map_of_injective c.injective]
    exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop.symm
  have hQmap : Q.map c.toMonoidHom = W := by
    change (W.map c.toMonoidHom).map c.toMonoidHom = W
    rw [Subgroup.map_map]
    have hcomp : c.toMonoidHom.comp c.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      simpa [c, csh] using csh_invol x
    rw [hcomp, Subgroup.map_id]
  rcases CFSG.RankThree.PartTwo.KFacts.KP2.le_kOne_or_le_kTwo_or_le_kThree
    hcop' hQnorm with h | h | h
  · refine ⟨0, ?_⟩
    calc W = Q.map c.toMonoidHom := hQmap.symm
      _ ≤ kOne.map c.toMonoidHom := Subgroup.map_mono h
      _ = kleinV 0 := by simpa [c, csh] using map_sh_kOne
  · refine ⟨1, ?_⟩
    calc W = Q.map c.toMonoidHom := hQmap.symm
      _ ≤ kTwo.map c.toMonoidHom := Subgroup.map_mono h
      _ = kleinV 1 := by simpa [c, csh] using map_sh_kTwo
  · refine ⟨2, ?_⟩
    calc W = Q.map c.toMonoidHom := hQmap.symm
      _ ≤ kThree.map c.toMonoidHom := Subgroup.map_mono h
      _ = kleinV 2 := by simpa [c, csh] using map_sh_kThree

theorem exists_mem_card_support_three_or_nine {B : Subgroup (Perm (Fin 10))} (hB : B ≤ atilde)
    (hcard : Nat.card B = 9) : ∃ x ∈ B, x.support.card = 3 ∨ x.support.card = 9 := by
  let c : MulAut (Perm (Fin 10)) := MulAut.conj sh
  have hB' : B.map c.toMonoidHom ≤ eTwentySeven := by
    calc B.map c.toMonoidHom ≤ atilde.map c.toMonoidHom := Subgroup.map_mono hB
      _ = eTwentySeven := by simpa [c, csh] using map_sh_atilde
  have hcard' : Nat.card (B.map c.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective c.injective, hcard]
  obtain ⟨b', hb'B, -, hb'supp⟩ :=
    CFSG.RankThree.PartTwo.KFacts.K412.exists_support_card_of_card_nine hB' hcard'
  obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hb'B
  refine ⟨b, hbB, ?_⟩
  have hsupp : (c b).support.card = b.support.card := Equiv.Perm.card_support_conj
  rw [← hsupp]
  exact hb'supp

theorem isSylowOf_atilde {x : Perm (Fin 10)} (hx : x ∈ atilde)
    (hsupp : x.support.card = 3 ∨ x.support.card = 6) :
    CFSG.ABGLocalTools.IsSylowOf 3 atilde (centralizer ({x} : Set (Perm (Fin 10)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : atilde ≤ centralizer ({x} : Set (Perm (Fin 10))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (commute_of_mem_atilde hx hy).eq
  have hne : x ≠ 1 := by
    intro h
    rw [h, Equiv.Perm.support_one, Finset.card_empty] at hsupp
    omega
  have h3 : x ^ 3 = 1 := isElemAbelian_atilde.2 x hx
  have hcyc : x.cycleType = {3} ∨ x.cycleType = {3, 3} :=
    cycleType_of_support_three_or_six h3 hne hsupp
  have hcardC : Nat.card (centralizer ({x} : Set (Perm (Fin 10)))) = 15120 ∨
      Nat.card (centralizer ({x} : Set (Perm (Fin 10)))) = 432 := by
    rcases hcyc with h | h
    · left
      rw [Equiv.Perm.nat_card_centralizer, h]
      norm_num [Nat.factorial]
    · right
      rw [Equiv.Perm.nat_card_centralizer, h]
      norm_num [Nat.factorial]
  have hfac : (Nat.card (centralizer ({x} : Set (Perm (Fin 10))))).factorization 3 = 3 := by
    rcases hcardC with h | h <;> rw [h] <;> norm_num [Nat.factorization]
  refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
  rw [card_atilde, hfac]
  norm_num
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.KFacts.KP2
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem mem_altOff_iff {s : Finset (Fin 10)} {x : Perm (Fin 10)} :
    x ∈ altOff s ↔ x ∈ alternatingGroup (Fin 10) ∧ ∀ a ∈ s, x a = a := by
  simp [altOff, fixingSubgroup, fixingSubmonoid]

private theorem mem_normalizer_atilde_of_conj_gens {g : Perm (Fin 10)}
    (ha : g * pa * g⁻¹ ∈ atilde) (hb : g * pb * g⁻¹ ∈ atilde)
    (hc : g * pc * g⁻¹ ∈ atilde) :
    g ∈ normalizer (atilde : Set (Perm (Fin 10))) := by
  have hle : atilde.map (MulAut.conj g).toMonoidHom ≤ atilde := by
    rw [atilde, MonoidHom.map_closure, Subgroup.closure_le]
    rintro a ⟨b, hb', rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have heq : atilde.map (MulAut.conj g).toMonoidHom = atilde := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

private theorem exists_block_eq_support_of_card_three {x : Perm (Fin 10)} (hx : x ∈ atilde)
    (hsupp : x.support.card = 3) : ∃ i : Fin 3, x.support = block i := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    first
      | (exfalso; revert hsupp; decide +kernel)
      | exact ⟨0, by decide +kernel⟩
      | exact ⟨1, by decide +kernel⟩
      | exact ⟨2, by decide +kernel⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.KFacts.KP2
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private theorem nine_not_mem_support_of_mem_atilde {x : Perm (Fin 10)} (hx : x ∈ atilde) :
    (9 : Fin 10) ∉ x.support := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  simpa [Equiv.Perm.mem_support] using toP_apply_nine i j k

private theorem block_subset_support_of_moves {k : Fin 3} {x : Perm (Fin 10)}
    (hx : x ∈ atilde) (hmoves : ∃ a ∈ block k, x a ≠ a) : block k ⊆ x.support := by
  obtain ⟨i, j, l, rfl⟩ := mem_atilde_iff.mp hx
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals
    first
      | (exfalso; revert hmoves; decide +kernel)
      | decide +kernel

private theorem exists_mem_block_not_mem_block_of_mem_kleinV {k : Fin 3} {v : Perm (Fin 10)}
    (hv : v ∈ kleinV k) (hv1 : v ≠ 1) : ∃ a ∈ block k, v a ∉ block k := by
  rw [mem_kleinV_iff] at hv
  rcases hv with rfl | ⟨hv2, hvs⟩
  · exact (hv1 rfl).elim
  rcases eq_kv_of_sq_one_support hv2 hvs with rfl | rfl | rfl <;>
    fin_cases k <;> decide +kernel

private theorem not_commute_of_mem_kleinV_of_moves_block {k : Fin 3} {x v : Perm (Fin 10)}
    (hx : x ∈ atilde) (hv : v ∈ kleinV k) (hv1 : v ≠ 1)
    (hmoves : ∃ a ∈ block k, x a ≠ a) : ¬ Commute v x := by
  intro hcomm
  rw [mem_kleinV_iff] at hv
  rcases hv with rfl | ⟨hv2, hvs⟩
  · exact hv1 rfl
  have hblock_sub : block k ⊆ x.support := block_subset_support_of_moves hx hmoves
  have hinter : x.support ∩ tBlock k = block k := by
    ext a
    rw [Finset.mem_inter, mem_tBlock_iff]
    constructor
    · rintro ⟨ha, h9 | hb⟩
      · exact (nine_not_mem_support_of_mem_atilde hx (h9 ▸ ha)).elim
      · exact hb
    · intro hb
      exact ⟨hblock_sub hb, Or.inr hb⟩
  have hvx : v * x * v⁻¹ = x := by
    rw [hcomm.eq]
    group
  have hmap : Finset.map (Equiv.toEmbedding v) x.support = x.support := by
    rw [← Equiv.Perm.support_conj, hvx]
  obtain ⟨b, hb, hvb⟩ := exists_mem_block_not_mem_block_of_mem_kleinV
    (k := k) (v := v) (mem_kleinV_iff.mpr (Or.inr ⟨hv2, hvs⟩)) hv1
  have hb_supp : b ∈ x.support := hblock_sub hb
  have hvb_supp : v b ∈ x.support := by
    have hmem : v b ∈ Finset.map (Equiv.toEmbedding v) x.support :=
      Finset.mem_map.mpr ⟨b, hb_supp, rfl⟩
    rwa [hmap] at hmem
  have hvb_T : v b ∈ tBlock k := by
    by_contra h
    have hfix : v (v b) = v b := by
      have hnot : v b ∉ v.support := by rwa [hvs]
      simpa [Equiv.Perm.mem_support, not_not] using hnot
    have hv2b : v (v b) = b := by
      have := congrArg (fun f : Perm (Fin 10) => f b) hv2
      simpa [pow_two] using this
    rw [hv2b] at hfix
    have hbT : b ∈ tBlock k := block_subset_tBlock k hb
    rw [hfix] at hbT
    exact h hbT
  have hvb_block : v b ∈ block k := by
    rw [← hinter, Finset.mem_inter]
    exact ⟨hvb_supp, hvb_T⟩
  exact hvb hvb_block

private theorem kleinV_inf_centralizer_eq_bot_of_moves_block {k : Fin 3} {x : Perm (Fin 10)}
    (hx : x ∈ atilde) (hmoves : ∃ a ∈ block k, x a ≠ a) :
    kleinV k ⊓ centralizer ({x} : Set (Perm (Fin 10))) = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Subgroup.mem_bot]
    by_contra hv1
    have hcomm : Commute v x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2
    exact not_commute_of_mem_kleinV_of_moves_block hx (Subgroup.mem_inf.mp hv).1 hv1 hmoves hcomm
  · exact bot_le

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.KFacts.KP2
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private theorem le_relPPrimeCore_of_normal {Y N : Subgroup (Perm (Fin 10))}
    (hNY : N ≤ Y) (hN : (N.subgroupOf Y).Normal) (hcop : Nat.Coprime 3 (Nat.card N)) :
    N ≤ CFSG.Open.relPPrimeCore 3 Y := by
  rw [CFSG.Open.relPPrimeCore]
  exact le_sSup ⟨hNY, hN, hcop⟩

private theorem kleinV_inf_subgroupOf_normal {k : Fin 3} {Y : Subgroup (Perm (Fin 10))}
    (hY : Y ≤ normalizer (kleinV k : Set (Perm (Fin 10)))) :
    ((kleinV k ⊓ Y).subgroupOf Y).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  constructor
  · have hg : (g : Perm (Fin 10)) ∈ normalizer (kleinV k : Set (Perm (Fin 10))) := hY g.2
    have hnV : (n : Perm (Fin 10)) ∈ kleinV k := (Subgroup.mem_inf.mp hn).1
    have h := (Subgroup.mem_normalizer_iff.mp hg) (n : Perm (Fin 10))
    simpa using h.mp hnV
  · exact Y.mul_mem (Y.mul_mem g.2 hn.2) (Y.inv_mem g.2)

private theorem coprime_card_kleinV_inf (k : Fin 3) (Y : Subgroup (Perm (Fin 10))) :
    Nat.Coprime 3 (Nat.card ↥(kleinV k ⊓ Y)) := by
  have hdvd : Nat.card ↥(kleinV k ⊓ Y) ∣ 4 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : kleinV k ⊓ Y ≤ kleinV k)
    rwa [card_kleinV] at h
  have hnot : ¬ 3 ∣ Nat.card ↥(kleinV k ⊓ Y) := by
    intro h3
    have := Nat.dvd_trans h3 hdvd
    norm_num at this
  exact (Nat.prime_three.coprime_iff_not_dvd).mpr hnot

private theorem kleinV_inf_le_relPPrimeCore {k : Fin 3} {x : Perm (Fin 10)}
    {Y : Subgroup (Perm (Fin 10))} (hx : x ∈ atilde)
    (hsupp : x.support.card = 6)
    (hYx : Y ≤ centralizer ({x} : Set (Perm (Fin 10))))
    (hdisj : Disjoint (block k) x.support) :
    (kleinV k ⊓ Y) ≤ CFSG.Open.relPPrimeCore 3 Y := by
  have h9 : (9 : Fin 10) ∉ x.support := nine_not_mem_support_of_mem_atilde hx
  have hdisjT : Disjoint x.support (tBlock k) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [mem_tBlock_iff] at hb
    rcases hb with rfl | hb
    · exact h9 ha
    · exact (Finset.disjoint_left.mp hdisj) hb ha
  have hcard : x.support.card + (tBlock k).card = Fintype.card (Fin 10) := by
    rw [hsupp, card_tBlock]
    simp
  have hcompl : x.supportᶜ = tBlock k :=
    Finset.compl_eq_of_disjoint_of_card_add_eq hdisjT (by simpa using hcard)
  have hpres : ∀ y ∈ Y, Finset.map (Equiv.toEmbedding y) x.support = x.support := by
    intro y hy
    have hcomm : y * x = x * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYx hy)
    have hconj : y * x * y⁻¹ = x := by rw [hcomm]; group
    rw [← Equiv.Perm.support_conj, hconj]
  have hnormalizer : Y ≤ normalizer (kleinV k : Set (Perm (Fin 10))) := by
    intro y hy
    apply mem_normalizer_kleinV
    have hpresY := hpres y hy
    have hiff : ∀ a, a ∈ x.support ↔ y a ∈ x.support := by
      intro a
      have h := (Finset.mem_map' (Equiv.toEmbedding y) (s := x.support) (a := a))
      rw [hpresY] at h
      exact h.symm
    intro a ha
    have ha' : a ∉ x.support := by
      rwa [← hcompl, Finset.mem_compl] at ha
    rw [← hcompl, Finset.mem_compl]
    intro hya
    exact ha' ((hiff a).mpr hya)
  have hNnorm : ((kleinV k ⊓ Y).subgroupOf Y).Normal :=
    kleinV_inf_subgroupOf_normal hnormalizer
  have hcardN : Nat.Coprime 3 (Nat.card ↥(kleinV k ⊓ Y)) :=
    coprime_card_kleinV_inf k Y
  rw [CFSG.Open.relPPrimeCore]
  apply le_sSup
  exact ⟨inf_le_right, hNnorm, hcardN⟩

theorem le_relPPrimeCore_of_card_support {x : Perm (Fin 10)} (hx : x ∈ atilde)
    (hsupp : x.support.card = 6 ∨ x.support.card = 9) {Y : Subgroup (Perm (Fin 10))}
    (hYx : Y ≤ centralizer ({x} : Set (Perm (Fin 10))))
    {W : Subgroup (Perm (Fin 10))} (hWY : W ≤ Y)
    (hW : atilde ≤ normalizer (W : Set (Perm (Fin 10))))
    (hcop : Nat.Coprime (Nat.card W) 3) :
    W ≤ CFSG.Open.relPPrimeCore 3 Y := by
  obtain ⟨k, hWV⟩ := exists_le_kleinV hW hcop
  have hWN : W ≤ kleinV k ⊓ Y := le_inf hWV hWY
  by_cases hdisj : Disjoint (block k) x.support
  · have h6 : x.support.card = 6 := by
      rcases hsupp with h6 | h9
      · exact h6
      · exfalso
        have hsub : block k ⊆ x.supportᶜ := by
          intro a ha
          rw [Finset.mem_compl]
          intro hxa
          exact (Finset.disjoint_left.mp hdisj) ha hxa
        have hle := Finset.card_le_card hsub
        rw [card_block, Finset.card_compl, h9] at hle
        simp at hle
    exact hWN.trans (kleinV_inf_le_relPPrimeCore hx h6 hYx hdisj)
  · have hmoves : ∃ a ∈ block k, x a ≠ a := by
      by_contra h
      apply hdisj
      rw [Finset.disjoint_left]
      intro a ha hxa
      exact h ⟨a, ha, by simpa [Equiv.Perm.mem_support] using hxa⟩
    have hbot : kleinV k ⊓ centralizer ({x} : Set (Perm (Fin 10))) = ⊥ :=
      kleinV_inf_centralizer_eq_bot_of_moves_block hx hmoves
    have hNbot : kleinV k ⊓ Y = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro v hv
      have hvC : v ∈ centralizer ({x} : Set (Perm (Fin 10))) :=
        hYx (Subgroup.mem_inf.mp hv).2
      have : v ∈ kleinV k ⊓ centralizer ({x} : Set (Perm (Fin 10))) :=
        ⟨(Subgroup.mem_inf.mp hv).1, hvC⟩
      rw [hbot] at this
      exact this
    rw [hNbot] at hWN
    exact hWN.trans bot_le

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private def c5 (a b c d e : Fin 10) : Perm (Fin 10) :=
  swap a b * swap b c * swap c d * swap d e

private theorem not_mem_zpowers_of_disjoint_support {σ τ : Perm (Fin 10)}
    (hdisj : Disjoint σ τ) (hτ1 : τ ≠ 1) : τ ∉ Subgroup.zpowers σ := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hsub : τ.support ⊆ σ.support := by
    rw [← hk]
    exact Equiv.Perm.support_zpow_le σ k
  have hnonempty : τ.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    exact hτ1 (Equiv.Perm.support_eq_empty_iff.mp h0)
  obtain ⟨a, ha⟩ := hnonempty
  exact (Finset.disjoint_left.mp hdisj.disjoint_support) (hsub ha) ha

private theorem zpowers_inf_zpowers_eq_bot_of_not_mem {G : Type*} [Group G] [Finite G]
    {σ τ : G} {p : ℕ} [Fact p.Prime] (hσ : orderOf σ = p) (hτ : orderOf τ = p)
    (hτσ : τ ∉ Subgroup.zpowers σ) :
    Subgroup.zpowers σ ⊓ Subgroup.zpowers τ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  have hxσ : x ∈ Subgroup.zpowers σ := (Subgroup.mem_inf.mp hx).1
  have hxτ : x ∈ Subgroup.zpowers τ := (Subgroup.mem_inf.mp hx).2
  have hxord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := by
      rw [← hσ]
      exact orderOf_dvd_of_mem_zpowers hxσ
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with h1 | hp
    · exact (hx1 (orderOf_eq_one_iff.mp h1)).elim
    · exact hp
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have heqσ : Subgroup.zpowers x = Subgroup.zpowers σ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxσ)
    rw [Nat.card_zpowers, hσ, hcardx]
  have heqτ : Subgroup.zpowers x = Subgroup.zpowers τ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxτ)
    rw [Nat.card_zpowers, hτ, hcardx]
  have hEq : Subgroup.zpowers σ = Subgroup.zpowers τ := heqσ.symm.trans heqτ
  apply hτσ
  rw [hEq]
  exact Subgroup.mem_zpowers τ

private theorem isPGroup_and_not_isCyclic_closure_pair {p : ℕ} [hp : Fact p.Prime]
    {σ τ : Perm (Fin 10)} (hσp : σ ^ p = 1) (hτp : τ ^ p = 1)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hcomm : Commute σ τ)
    (hτσ : τ ∉ Subgroup.zpowers σ) :
    IsPGroup p (Subgroup.closure ({σ, τ} : Set (Perm (Fin 10)))) ∧
      ¬ IsCyclic (Subgroup.closure ({σ, τ} : Set (Perm (Fin 10)))) := by
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hτ : orderOf τ = p := orderOf_eq_prime hτp hτ1
  have hinf : Subgroup.zpowers σ ⊓ Subgroup.zpowers τ = ⊥ :=
    zpowers_inf_zpowers_eq_bot_of_not_mem hσ hτ hτσ
  have hEeq : Subgroup.closure ({σ, τ} : Set (Perm (Fin 10))) =
      Subgroup.zpowers σ ⊔ Subgroup.zpowers τ := by
    rw [show ({σ, τ} : Set (Perm (Fin 10))) = {σ} ∪ {τ} by ext x; simp [or_comm]]
    rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  have hcard := CFSG.GroupTheory.card_zpowers_sup_zpowers hcomm hσ hτ hinf
  have hcardE : Nat.card ↥(Subgroup.closure ({σ, τ} : Set (Perm (Fin 10)))) = p ^ 2 := by
    rw [hEeq]
    exact hcard.1
  have hcommE : ∀ x ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 10))),
      ∀ y ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 10))), Commute x y := by
    intro x hx y hy
    rw [hEeq] at hx hy
    exact hcard.2 x hx y hy
  constructor
  · exact IsPGroup.of_card (n := 2) hcardE
  · intro hcyc
    let E := Subgroup.closure ({σ, τ} : Set (Perm (Fin 10)))
    letI : IsCyclic ↥E := hcyc
    obtain ⟨g, hg⟩ := (IsCyclic.exists_generator (α := ↥E))
    have hgord : orderOf g = Nat.card ↥E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hpowE : ∀ x ∈ E, x ^ p = 1 := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => x ^ p = 1) ?_ ?_ ?_ ?_ hx
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hσp
        · exact hτp
      · simp
      · intro x y hx hy hx5 hy5
        rw [(hcommE x hx y hy).mul_pow, hx5, hy5, one_mul]
      · intro x hx hx5
        rw [inv_pow, hx5, inv_one]
    have hgp : (g : Perm (Fin 10)) ^ p = 1 := hpowE (g : Perm (Fin 10)) g.2
    have hgp' : (g : ↥E) ^ p = 1 := Subtype.ext hgp
    have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp'
    rw [hcardE] at hgord
    have hdvd' : p ^ 2 ∣ p := hgord ▸ hdvd
    have hpgt : 1 < p := hp.out.one_lt
    have hp2 : p < p ^ 2 := by nlinarith
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.out.pos hdvd'
    omega

private theorem exists_noncyclic_five_of_pair {i j : Fin 3} {σ τ : Perm (Fin 10)}
    (hσ : σ ∈ altOff (block i)) (hτ : τ ∈ altOff (block j))
    (hσ5 : σ ^ 5 = 1) (hτ5 : τ ^ 5 = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hcomm : Commute σ τ) (hτσ : τ ∉ Subgroup.zpowers σ) :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block i) ⊔ altOff (block j) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let E : Subgroup (Perm (Fin 10)) := Subgroup.closure {σ, τ}
  have h := isPGroup_and_not_isCyclic_closure_pair hσ5 hτ5 hσ1 hτ1 hcomm hτσ
  refine ⟨E, ?_, h.1, h.2⟩
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_sup_left hσ
  · exact Subgroup.mem_sup_right hτ

private theorem exists_noncyclic_five_01 :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 0) ⊔ altOff (block 1) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  refine exists_noncyclic_five_of_pair (i := 0) (j := 1)
    (σ := c5 3 4 5 6 7) (τ := c5 0 1 2 8 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · show (c5 3 4 5 6 7) * (c5 0 1 2 8 9) = (c5 0 1 2 8 9) * (c5 3 4 5 6 7)
    ext x <;> fin_cases x <;> decide +kernel
  · refine not_mem_zpowers_of_disjoint_support (σ := c5 3 4 5 6 7) ?_ ?_
    · rw [Equiv.Perm.disjoint_iff_disjoint_support]
      decide +kernel
    · decide +kernel

private theorem exists_noncyclic_five_02 :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 0) ⊔ altOff (block 2) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  refine exists_noncyclic_five_of_pair (i := 0) (j := 2)
    (σ := c5 6 7 8 3 4) (τ := c5 0 1 2 5 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · show (c5 6 7 8 3 4) * (c5 0 1 2 5 9) = (c5 0 1 2 5 9) * (c5 6 7 8 3 4)
    ext x <;> fin_cases x <;> decide +kernel
  · refine not_mem_zpowers_of_disjoint_support (σ := c5 6 7 8 3 4) ?_ ?_
    · rw [Equiv.Perm.disjoint_iff_disjoint_support]
      decide +kernel
    · decide +kernel

private theorem exists_noncyclic_five_10 :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 1) ⊔ altOff (block 0) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  refine exists_noncyclic_five_of_pair (i := 1) (j := 0)
    (σ := c5 0 1 2 6 7) (τ := c5 3 4 5 8 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · show (c5 0 1 2 6 7) * (c5 3 4 5 8 9) = (c5 3 4 5 8 9) * (c5 0 1 2 6 7)
    ext x <;> fin_cases x <;> decide +kernel
  · refine not_mem_zpowers_of_disjoint_support (σ := c5 0 1 2 6 7) ?_ ?_
    · rw [Equiv.Perm.disjoint_iff_disjoint_support]
      decide +kernel
    · decide +kernel

private theorem exists_noncyclic_five_12 :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 1) ⊔ altOff (block 2) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  refine exists_noncyclic_five_of_pair (i := 1) (j := 2)
    (σ := c5 6 7 8 0 1) (τ := c5 3 4 5 2 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · show (c5 6 7 8 0 1) * (c5 3 4 5 2 9) = (c5 3 4 5 2 9) * (c5 6 7 8 0 1)
    ext x <;> fin_cases x <;> decide +kernel
  · refine not_mem_zpowers_of_disjoint_support (σ := c5 6 7 8 0 1) ?_ ?_
    · rw [Equiv.Perm.disjoint_iff_disjoint_support]
      decide +kernel
    · decide +kernel

private theorem exists_noncyclic_five_20 :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 2) ⊔ altOff (block 0) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  refine exists_noncyclic_five_of_pair (i := 2) (j := 0)
    (σ := c5 0 1 2 3 4) (τ := c5 6 7 8 5 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · show (c5 0 1 2 3 4) * (c5 6 7 8 5 9) = (c5 6 7 8 5 9) * (c5 0 1 2 3 4)
    ext x <;> fin_cases x <;> decide +kernel
  · refine not_mem_zpowers_of_disjoint_support (σ := c5 0 1 2 3 4) ?_ ?_
    · rw [Equiv.Perm.disjoint_iff_disjoint_support]
      decide +kernel
    · decide +kernel

private theorem exists_noncyclic_five_21 :
    ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 2) ⊔ altOff (block 1) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E := by
  refine exists_noncyclic_five_of_pair (i := 2) (j := 1)
    (σ := c5 3 4 5 0 1) (τ := c5 6 7 8 2 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · rw [mem_altOff_iff]
    refine ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
    fin_cases r <;> simp [c5, blockPt] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · show (c5 3 4 5 0 1) * (c5 6 7 8 2 9) = (c5 6 7 8 2 9) * (c5 3 4 5 0 1)
    ext x <;> fin_cases x <;> decide +kernel
  · refine not_mem_zpowers_of_disjoint_support (σ := c5 3 4 5 0 1) ?_ ?_
    · rw [Equiv.Perm.disjoint_iff_disjoint_support]
      decide +kernel
    · decide +kernel

theorem exists_noncyclic_five {x y : Perm (Fin 10)} (hx : x ∈ atilde) (hy : y ∈ atilde)
    (hxs : x.support.card = 3) (hys : y.support.card = 3) (hne : x.support ≠ y.support) :
    ∃ E : Subgroup (Perm (Fin 10)), E ≤ altOff x.support ⊔ altOff y.support ∧ IsPGroup 5 E ∧
      ¬ IsCyclic E := by
  obtain ⟨i, hi⟩ := exists_block_eq_support_of_card_three hx hxs
  obtain ⟨j, hj⟩ := exists_block_eq_support_of_card_three hy hys
  rw [hi, hj]
  have hij : i ≠ j := by
    intro h
    apply hne
    rw [hi, hj, h]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 0) ⊔ altOff (block 1) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E
    exact exists_noncyclic_five_01
  · change ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 0) ⊔ altOff (block 2) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E
    exact exists_noncyclic_five_02
  · change ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 1) ⊔ altOff (block 0) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E
    exact exists_noncyclic_five_10
  · exact (hij rfl).elim
  · change ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 1) ⊔ altOff (block 2) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E
    exact exists_noncyclic_five_12
  · change ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 2) ⊔ altOff (block 0) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E
    exact exists_noncyclic_five_20
  · change ∃ E : Subgroup (Perm (Fin 10)),
      E ≤ altOff (block 2) ⊔ altOff (block 1) ∧ IsPGroup 5 E ∧ ¬ IsCyclic E
    exact exists_noncyclic_five_21
  · exact (hij rfl).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private theorem kleinV_inf_le_relPPrimeCore_of_le_normalizer {k : Fin 3}
    {Y : Subgroup (Perm (Fin 10))}
    (hY : Y ≤ normalizer (kleinV k : Set (Perm (Fin 10)))) :
    (kleinV k ⊓ Y) ≤ CFSG.Open.relPPrimeCore 3 Y :=
  le_relPPrimeCore_of_normal inf_le_right (kleinV_inf_subgroupOf_normal hY)
    (coprime_card_kleinV_inf k Y)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private def pgen (l : Fin 3) : Perm (Fin 10) := ![pa, pb, pc] l

private theorem pgen_mem_atilde (l : Fin 3) : pgen l ∈ atilde := by
  fin_cases l <;> simp [pgen] <;>
    (rw [atilde]; exact Subgroup.subset_closure (by simp))

private theorem pgen_isThreeCycle (l : Fin 3) : (pgen l).IsThreeCycle := by
  fin_cases l <;> simp [pgen]
  · exact isThreeCycle_pa
  · exact isThreeCycle_pb
  · exact isThreeCycle_pc

private theorem pgen_fixes_of_ne {i l : Fin 3} (h : l ≠ i) :
    ∀ z ∈ block i, pgen l z = z := by
  intro z hz
  obtain ⟨r, rfl⟩ := mem_block_iff.mp hz
  fin_cases i <;> fin_cases l <;> try contradiction
  all_goals (fin_cases r <;> simp [pgen, blockPt] <;> decide +kernel)

private theorem not_mem_iff_of_fixes {s : Finset (Fin 10)} {f : Perm (Fin 10)}
    (hfix : ∀ z ∈ s, f z = z) (z : Fin 10) : z ∉ s ↔ f z ∉ s := by
  constructor
  · intro hz hfz
    have h1 : f (f z) = f z := hfix (f z) hfz
    have h2 : f z = z := by
      have := congrArg f.symm h1
      simpa using this
    rw [h2] at hfz
    exact hz hfz
  · intro hfz hz
    exact hfz (by rw [hfix z hz]; exact hz)

private theorem preserve_block_of_mem_centralizer {x : Perm (Fin 10)} {i : Fin 3}
    (hxi : x.support = block i) {Y : Subgroup (Perm (Fin 10))}
    (hYx : Y ≤ centralizer ({x} : Set (Perm (Fin 10)))) :
    ∀ y ∈ Y, ∀ z : Fin 10, z ∈ block i ↔ y z ∈ block i := by
  intro y hy z
  have hcomm : y * x = x * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (hYx hy)
  have hconj : y * x * y⁻¹ = x := by rw [hcomm]; group
  have hmap : Finset.map (Equiv.toEmbedding y) (block i) = block i := by
    rw [← hxi, ← Equiv.Perm.support_conj, hconj]
  have h := (Finset.mem_map' (Equiv.toEmbedding y) (s := block i) (a := z))
  rw [hmap] at h
  exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private theorem pow_apply_mem_support {f : Perm (Fin 10)} (z : Fin 10)
    (hz : z ∈ f.support) (n : ℕ) : (f ^ n) z ∈ f.support := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      rw [pow_succ']
      exact Equiv.Perm.apply_mem_support.mpr ih

private def restrictHom {i : Fin 3} (Y : Subgroup (Perm (Fin 10)))
    (hpres : ∀ y ∈ Y, ∀ z : Fin 10, z ∈ block i ↔ y z ∈ block i) :
    ↥Y →* Perm {z : Fin 10 // z ∉ block i} :=
  { toFun := fun y => (y : Perm (Fin 10)).subtypePerm
      (fun z => (not_congr (hpres y y.2 z)).symm)
    map_one' := by ext z; rfl
    map_mul' := by intro a b; ext z; rfl }

private theorem restrictHom_apply {i : Fin 3} {Y : Subgroup (Perm (Fin 10))}
    {hpres : ∀ y ∈ Y, ∀ z : Fin 10, z ∈ block i ↔ y z ∈ block i}
    (y : ↥Y) (z : Fin 10) (hz : z ∉ block i) :
    ((restrictHom Y hpres y) ⟨z, hz⟩ : Fin 10) = (y : Perm (Fin 10)) z := rfl

private theorem eq_mul_pow_inv_of_action {i : Fin 3} {x y σ : Perm (Fin 10)} {e : ℕ}
    (hxi : x.support = block i) (hσfix : ∀ z ∈ block i, σ z = z)
    (he : ∀ t ∈ x.support, y t = (x ^ e) t)
    (hy_alpha : ∀ z : Fin 10, z ∉ block i → y z = σ z) :
    y * (x ^ e)⁻¹ = σ := by
  apply Equiv.ext
  intro z
  by_cases hz : z ∈ block i
  · have hz_supp : z ∈ x.support := by rwa [hxi]
    have hxez_mem : (x ^ e) z ∈ block i := by
      have := pow_apply_mem_support z hz_supp e
      rwa [hxi] at this
    have hinvz_mem : (x ^ e)⁻¹ z ∈ block i := by
      rw [← inv_pow]
      have hz_inv : z ∈ (x⁻¹).support := by rwa [Equiv.Perm.support_inv]
      have := pow_apply_mem_support z hz_inv e
      rwa [Equiv.Perm.support_inv, hxi] at this
    have hy_inv : y ((x ^ e)⁻¹ z) = (x ^ e) ((x ^ e)⁻¹ z) := by
      rw [hxi] at he
      exact he _ hinvz_mem
    calc (y * (x ^ e)⁻¹) z = y ((x ^ e)⁻¹ z) := Perm.mul_apply _ _ _
      _ = (x ^ e) ((x ^ e)⁻¹ z) := hy_inv
      _ = z := by simp
      _ = σ z := by rw [hσfix z hz]
  · have hxfix : x z = z := by
      have hz' : z ∉ x.support := by rwa [hxi]
      simpa [Equiv.Perm.mem_support, not_not] using hz'
    have hxez : (x ^ e) z = z := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix e
    have hinvz : (x ^ e)⁻¹ z = z := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hxez.symm
    calc (y * (x ^ e)⁻¹) z = y ((x ^ e)⁻¹ z) := Perm.mul_apply _ _ _
      _ = y z := by rw [hinvz]
      _ = σ z := hy_alpha z hz

private theorem mem_of_jordan_image {i : Fin 3} {x σ : Perm (Fin 10)}
    {Y : Subgroup (Perm (Fin 10))} (hx : x ∈ atilde) (hxi : x.support = block i)
    (hAY : atilde ≤ Y) (hYx : Y ≤ centralizer ({x} : Set (Perm (Fin 10))))
    (φ : ↥Y →* Perm {z : Fin 10 // z ∉ block i})
    (hφ : ∀ (y : ↥Y) (z : Fin 10) (hz : z ∉ block i),
      ((φ y) ⟨z, hz⟩ : Fin 10) = (y : Perm (Fin 10)) z)
    (hJordan : alternatingGroup {z : Fin 10 // z ∉ block i} ≤ φ.range)
    (hσ : σ ∈ altOff (block i)) : σ ∈ Y := by
  rw [mem_altOff_iff] at hσ
  obtain ⟨hσA, hσfix⟩ := hσ
  let α := {z : Fin 10 // z ∉ block i}
  have hσpres : ∀ z : Fin 10, z ∉ block i ↔ σ z ∉ block i :=
    not_mem_iff_of_fixes hσfix
  let σα : Perm α := σ.subtypePerm (fun z => (hσpres z).symm)
  have hσσα : σα ∈ alternatingGroup α := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hofσ : Equiv.Perm.ofSubtype σα = σ :=
      Equiv.Perm.ofSubtype_subtypePerm (fun z => (hσpres z).symm)
        (fun z hz hzb => hz (hσfix z hzb))
    rw [← Equiv.Perm.sign_ofSubtype σα, hofσ]
    exact Equiv.Perm.mem_alternatingGroup.mp hσA
  have hσαH : σα ∈ φ.range := hJordan hσσα
  obtain ⟨y, hyeq⟩ := hσαH
  have hy_alpha : ∀ z : Fin 10, z ∉ block i → (y : Perm (Fin 10)) z = σ z := by
    intro z hz
    have h := congrArg (fun t : α => (t : Fin 10))
      (congrArg (fun f : Perm α => f ⟨z, hz⟩) hyeq)
    rw [hφ y z hz, Equiv.Perm.subtypePerm_apply] at h
    simpa [σα] using h
  obtain ⟨e, he3, he⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD1426Perm3.centralizer_eq_pow_on_support
      (h3 := isElemAbelian_atilde.2 x hx)
      (hcard := by rw [hxi, card_block])
      (hx := Subgroup.mem_centralizer_singleton_iff.mp (hYx y.2))
  have hσ_eq : (y : Perm (Fin 10)) * (x ^ e)⁻¹ = σ :=
    eq_mul_pow_inv_of_action hxi hσfix he hy_alpha
  rw [← hσ_eq]
  exact Y.mul_mem y.2 (Y.inv_mem (hAY (Subgroup.pow_mem atilde hx e)))

private theorem altOff_le_of_transitive_on_compl {i : Fin 3} {x : Perm (Fin 10)}
    (hx : x ∈ atilde) (hxi : x.support = block i) {Y : Subgroup (Perm (Fin 10))}
    (hAY : atilde ≤ Y) (hYx : Y ≤ centralizer ({x} : Set (Perm (Fin 10))))
    (htrans : ∀ a b : Fin 10, a ∉ block i → b ∉ block i → ∃ y ∈ Y, y a = b) :
    altOff (block i) ≤ Y := by
  intro σ hσ
  let α := {z : Fin 10 // z ∉ block i}
  have hcardα : Fintype.card α = 7 := by
    rw [Fintype.card_subtype_compl (fun z => z ∈ block i)]
    rw [Fintype.card_subtype, Fintype.card_fin]
    simp [card_block]
  have h9 : (9 : Fin 10) ∉ block i := by
    have := nine_not_mem_support_of_mem_atilde hx
    rwa [hxi] at this
  let x0 : α := ⟨9, h9⟩
  have hpres : ∀ y ∈ Y, ∀ z : Fin 10, z ∈ block i ↔ y z ∈ block i :=
    preserve_block_of_mem_centralizer hxi hYx
  let φ := restrictHom Y hpres
  let H : Subgroup (Perm α) := φ.range
  have htransH : ∀ a b : α, ∃ h ∈ H, h a = b := by
    intro a b
    obtain ⟨y, hy, hyab⟩ := htrans a.1 b.1 a.2 b.2
    refine ⟨φ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [restrictHom_apply]
    exact hyab
  let l : Fin 3 := i + 1
  have hli : l ≠ i := by
    change i + 1 ≠ i
    fin_cases i <;> decide
  let p : Perm (Fin 10) := pgen l
  have hpA : p ∈ atilde := pgen_mem_atilde l
  have hpfix : ∀ z ∈ block i, p z = z := pgen_fixes_of_ne hli
  have hppres : ∀ z : Fin 10, z ∉ block i ↔ p z ∉ block i :=
    not_mem_iff_of_fixes hpfix
  let pα : Perm α := p.subtypePerm (fun z => (hppres z).symm)
  have hpα3 : pα.IsThreeCycle := by
    have hof : Equiv.Perm.ofSubtype pα = p :=
      Equiv.Perm.ofSubtype_subtypePerm (fun z => (hppres z).symm)
        (fun z hz hzb => hz (hpfix z hzb))
    have hcyc : pα.cycleType = {3} := by
      rw [← Equiv.Perm.cycleType_ofSubtype (g := pα), hof]
      exact pgen_isThreeCycle l
    exact hcyc
  have hpαH : pα ∈ H := ⟨⟨p, hAY hpA⟩, rfl⟩
  have hJordan : alternatingGroup α ≤ φ.range :=
    CFSG.Quasithin.SmithC27.alternatingGroup_le_of_prime
      (by rw [hcardα]; norm_num) (fun b => htransH x0 b) hpα3 hpαH
  exact mem_of_jordan_image hx hxi hAY hYx φ (fun y z hz => rfl) hJordan hσ

private theorem exists_atilde_apply_block (l : Fin 3) {a b : Fin 10}
    (ha : a ∈ block l) (hb : b ∈ block l) : ∃ g ∈ atilde, g a = b := by
  obtain ⟨r, rfl⟩ := mem_block_iff.mp ha
  obtain ⟨s, rfl⟩ := mem_block_iff.mp hb
  have h : ∃ i j k : Fin 3, toP i j k (blockPt l r) = blockPt l s := by
    fin_cases l <;> fin_cases r <;> fin_cases s <;> decide +kernel
  obtain ⟨i, j, k, hijk⟩ := h
  exact ⟨toP i j k, mem_atilde_iff.mpr ⟨i, j, k, rfl⟩, hijk⟩

private theorem block_compl_eq {i l : Fin 3} (hli : l ≠ i) :
    (block i)ᶜ = tBlock l ∪ block (-(i + l)) := by
  have hm : -(i + l) ≠ i ∧ -(i + l) ≠ l := by
    fin_cases i <;> fin_cases l
    · exact (hli rfl).elim
    · change (-(0 + 1) : Fin 3) ≠ 0 ∧ (-(0 + 1) : Fin 3) ≠ 1
      decide +kernel
    · change (-(0 + 2) : Fin 3) ≠ 0 ∧ (-(0 + 2) : Fin 3) ≠ 2
      decide +kernel
    · change (-(1 + 0) : Fin 3) ≠ 1 ∧ (-(1 + 0) : Fin 3) ≠ 0
      decide +kernel
    · exact (hli rfl).elim
    · change (-(1 + 2) : Fin 3) ≠ 1 ∧ (-(1 + 2) : Fin 3) ≠ 2
      decide +kernel
    · change (-(2 + 0) : Fin 3) ≠ 2 ∧ (-(2 + 0) : Fin 3) ≠ 0
      decide +kernel
    · change (-(2 + 1) : Fin 3) ≠ 2 ∧ (-(2 + 1) : Fin 3) ≠ 1
      decide +kernel
    · exact (hli rfl).elim
  have hm_ne_i : -(i + l) ≠ i := hm.1
  have hm_ne_l : -(i + l) ≠ l := hm.2
  have hdisj : Disjoint (tBlock l ∪ block (-(i + l))) (block i) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [mem_tBlock_iff] at ha
      rcases ha with rfl | ha
      · obtain ⟨r, hr⟩ := mem_block_iff.mp hb
        exact blockPt_ne_nine i r hr.symm
      · exact (Finset.disjoint_left.mp (disjoint_block hli)) ha hb
    · exact disjoint_block hm_ne_i
  have hcard : (tBlock l).card + (block (-(i + l))).card = 4 + 3 := by
    rw [card_tBlock, card_block]
  have hdisj2 : Disjoint (tBlock l) (block (-(i + l))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [mem_tBlock_iff] at ha
    rcases ha with rfl | ha
    · obtain ⟨r, hr⟩ := mem_block_iff.mp hb
      exact blockPt_ne_nine (-(i + l)) r hr.symm
    · exact (Finset.disjoint_left.mp (disjoint_block (Ne.symm hm_ne_l))) ha hb
  have hcardU : (tBlock l ∪ block (-(i + l))).card = 7 := by
    rw [Finset.card_union_of_disjoint hdisj2, card_tBlock, card_block]
  have hsum : (block i).card + (tBlock l ∪ block (-(i + l))).card = Fintype.card (Fin 10) := by
    rw [card_block, hcardU]
    simp
  exact Finset.compl_eq_of_disjoint_of_card_add_eq hdisj.symm hsum

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private theorem orbit_contains_tBlock_of_failure {l : Fin 3} {W Y : Subgroup (Perm (Fin 10))}
    (hWY : W ≤ Y) (hWV : W ≤ kleinV l) (hWne : W ≠ ⊥) (hAY : atilde ≤ Y)
    (O : Set (Fin 10)) (hO_9 : (9 : Fin 10) ∈ O)
    (hO_mem : ∀ y : ↥Y, (y : Perm (Fin 10)) 9 ∈ O)
    (hO_smul : ∀ a ∈ atilde, ∀ z, z ∈ O → a z ∈ O) :
    ∀ z, z ∈ tBlock l → z ∈ O := by
  have hW_nonid : ∃ w ∈ W, w ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one W with hbot | h
    · exact (hWne hbot).elim
    · exact h
  obtain ⟨w, hwW, hw1⟩ := hW_nonid
  have hwV : w ∈ kleinV l := hWV hwW
  have hw_supp : w.support = tBlock l := (mem_kleinV_iff.mp hwV).resolve_left hw1 |>.2
  have hw9_mem : w 9 ∈ block l := by
    have h9supp : (9 : Fin 10) ∈ w.support := by
      rw [hw_supp]
      exact nine_mem_tBlock l
    have hw9ne : w 9 ≠ 9 := by simpa [Equiv.Perm.mem_support] using h9supp
    have hw9supp : w 9 ∈ w.support := Equiv.Perm.apply_mem_support.mpr h9supp
    rw [hw_supp, mem_tBlock_iff] at hw9supp
    rcases hw9supp with h9eq | hb
    · exact (hw9ne h9eq).elim
    · exact hb
  have hO_w9 : w 9 ∈ O := hO_mem ⟨w, hWY hwW⟩
  have hO_block_l : ∀ z, z ∈ block l → z ∈ O := by
    intro z hz
    obtain ⟨g, hgA, hgz⟩ := exists_atilde_apply_block l hw9_mem hz
    rw [← hgz]
    exact hO_smul g hgA (w 9) hO_w9
  intro z hz
  rw [mem_tBlock_iff] at hz
  rcases hz with rfl | hz
  · exact hO_9
  · exact hO_block_l z hz

private theorem orbit_not_subset_tBlock_of_failure {l : Fin 3} {Y : Subgroup (Perm (Fin 10))}
    (hnotnorm : ¬ Y ≤ normalizer (kleinV l : Set (Perm (Fin 10))))
    (O : Set (Fin 10)) (hO_Y : ∀ y ∈ Y, ∀ z, z ∈ O → y z ∈ O)
    (hO_T_l : ∀ z, z ∈ tBlock l → z ∈ O) :
    ¬ O ⊆ {z | z ∈ tBlock l} := by
  intro hsub
  apply hnotnorm
  intro y hy
  apply mem_normalizer_kleinV
  intro z hz
  exact hsub (hO_Y y hy z (hO_T_l z hz))

private theorem orbit_contains_third_block_of_failure {i l : Fin 3}
    (hli : l ≠ i) (O : Set (Fin 10)) (hO_sub : ∀ z, z ∈ O → z ∉ block i)
    (hO_smul : ∀ a ∈ atilde, ∀ z, z ∈ O → a z ∈ O)
    (hO_T_l : ∀ z, z ∈ tBlock l → z ∈ O)
    (hnot_subset : ¬ O ⊆ {z | z ∈ tBlock l}) :
    ∀ z, z ∈ block (-(i + l)) → z ∈ O := by
  have hex : ∃ z0, z0 ∈ O ∧ z0 ∉ tBlock l := by
    by_contra h
    apply hnot_subset
    intro z hzO
    by_contra hzT
    exact h ⟨z, hzO, hzT⟩
  obtain ⟨z0, hz0O, hz0notT⟩ := hex
  have hz0compl : z0 ∈ (block i)ᶜ := by simpa using hO_sub z0 hz0O
  have hz0blockm : z0 ∈ block (-(i + l)) := by
    rw [block_compl_eq hli] at hz0compl
    rcases Finset.mem_union.mp hz0compl with hzT | hzm
    · exact (hz0notT hzT).elim
    · exact hzm
  intro z hz
  obtain ⟨g, hgA, hgz⟩ := exists_atilde_apply_block (-(i + l)) hz0blockm hz
  rw [← hgz]
  exact hO_smul g hgA z0 hz0O

private theorem orbit_eq_compl_of_failure {i l : Fin 3} (hli : l ≠ i)
    (O : Set (Fin 10)) (hO_sub : ∀ z, z ∈ O → z ∉ block i)
    (hO_T_l : ∀ z, z ∈ tBlock l → z ∈ O)
    (hO_block_m : ∀ z, z ∈ block (-(i + l)) → z ∈ O) :
    ∀ z, z ∈ O ↔ z ∉ block i := by
  intro z
  constructor
  · exact hO_sub z
  · intro hz
    have hzcompl : z ∈ (block i)ᶜ := by simpa using hz
    rw [block_compl_eq hli] at hzcompl
    rcases Finset.mem_union.mp hzcompl with hzT | hzm
    · exact hO_T_l z hzT
    · exact hO_block_m z hzm

private theorem orbit_smul_atilde {Y : Subgroup (Perm (Fin 10))} (hAY : atilde ≤ Y) :
    ∀ a ∈ atilde, ∀ z : Fin 10, (∃ y : ↥Y, (y : Perm (Fin 10)) 9 = z) →
      ∃ y : ↥Y, (y : Perm (Fin 10)) 9 = a z := by
  intro a ha z hz
  obtain ⟨y, hy⟩ := hz
  have ha9 : a 9 = 9 := by
    have := nine_not_mem_support_of_mem_atilde ha
    simpa [Equiv.Perm.mem_support, not_not] using this
  have ha9inv : a⁻¹ 9 = 9 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact ha9.symm
  let ynew : ↥Y := ⟨a * (y : Perm (Fin 10)) * a⁻¹,
    Y.mul_mem (Y.mul_mem (hAY ha) y.2) (Y.inv_mem (hAY ha))⟩
  refine ⟨ynew, ?_⟩
  change (ynew : Perm (Fin 10)) 9 = a z
  dsimp [ynew]
  change a ((y : Perm (Fin 10)) (a⁻¹ 9)) = a z
  rw [ha9inv, hy]

private theorem transitive_on_compl_of_failure {i l : Fin 3} {x : Perm (Fin 10)}
    {W Y : Subgroup (Perm (Fin 10))} (hx : x ∈ atilde) (hxi : x.support = block i)
    (hli : l ≠ i) (hWY : W ≤ Y) (hWV : W ≤ kleinV l) (hWne : W ≠ ⊥)
    (hYx : Y ≤ centralizer ({x} : Set (Perm (Fin 10)))) (hAY : atilde ≤ Y)
    (hnotnorm : ¬ Y ≤ normalizer (kleinV l : Set (Perm (Fin 10)))) :
    ∀ a b : Fin 10, a ∉ block i → b ∉ block i → ∃ y ∈ Y, y a = b := by
  have hpres := preserve_block_of_mem_centralizer hxi hYx
  have h9 : (9 : Fin 10) ∉ block i := by
    have := nine_not_mem_support_of_mem_atilde hx
    rwa [hxi] at this
  let O : Set (Fin 10) := {z | ∃ y : ↥Y, (y : Perm (Fin 10)) 9 = z}
  have hO_sub : ∀ z, z ∈ O → z ∉ block i := by
    rintro z ⟨y, rfl⟩
    intro hz
    exact h9 ((hpres y y.2 9).mpr hz)
  have hO_9 : (9 : Fin 10) ∈ O := ⟨1, by simp⟩
  have hO_Y : ∀ y ∈ Y, ∀ z, z ∈ O → y z ∈ O := by
    rintro y hy z ⟨y', hy'⟩
    exact ⟨⟨y * (y' : Perm (Fin 10)), Y.mul_mem hy y'.2⟩, by
      change (y * (y' : Perm (Fin 10))) 9 = y z
      rw [mul_apply, hy']⟩
  have hO_smul : ∀ a ∈ atilde, ∀ z, z ∈ O → a z ∈ O :=
    orbit_smul_atilde hAY
  have hO_T_l : ∀ z, z ∈ tBlock l → z ∈ O :=
    orbit_contains_tBlock_of_failure hWY hWV hWne hAY O hO_9 (fun y => ⟨y, rfl⟩) hO_smul
  have hnot_subset : ¬ O ⊆ {z | z ∈ tBlock l} :=
    orbit_not_subset_tBlock_of_failure hnotnorm O hO_Y hO_T_l
  have hO_block_m : ∀ z, z ∈ block (-(i + l)) → z ∈ O :=
    orbit_contains_third_block_of_failure hli O hO_sub hO_smul hO_T_l hnot_subset
  have hO_eq : ∀ z, z ∈ O ↔ z ∉ block i :=
    orbit_eq_compl_of_failure hli O hO_sub hO_T_l hO_block_m
  intro a b ha hb
  obtain ⟨y1, hy1⟩ := (hO_eq a).mpr ha
  obtain ⟨y2, hy2⟩ := (hO_eq b).mpr hb
  refine ⟨(y2 : Perm (Fin 10)) * (y1 : Perm (Fin 10))⁻¹, ?_, ?_⟩
  · exact Y.mul_mem y2.2 (Y.inv_mem y1.2)
  · change ((y2 : Perm (Fin 10)) * (y1 : Perm (Fin 10))⁻¹) a = b
    calc ((y2 : Perm (Fin 10)) * (y1 : Perm (Fin 10))⁻¹) a
        = (y2 : Perm (Fin 10)) ((y1 : Perm (Fin 10))⁻¹ a) := Perm.mul_apply _ _ _
      _ = (y2 : Perm (Fin 10)) 9 := by
          have hinv : (y1 : Perm (Fin 10))⁻¹ a = 9 := by
            rw [Equiv.Perm.inv_eq_iff_eq]
            exact hy1.symm
          rw [hinv]
      _ = b := hy2

theorem le_relPPrimeCore_or_altOff_le {x : Perm (Fin 10)} (hx : x ∈ atilde)
    (hsupp : x.support.card = 3) {Y : Subgroup (Perm (Fin 10))} (hAY : atilde ≤ Y)
    (hYx : Y ≤ centralizer {x}) :
    (∀ W : Subgroup (Perm (Fin 10)), W ≤ Y → atilde ≤ normalizer (W : Set (Perm (Fin 10))) →
      Nat.Coprime (Nat.card W) 3 → W ≤ CFSG.Open.relPPrimeCore 3 Y) ∨ altOff x.support ≤ Y := by
  obtain ⟨i, hi⟩ := exists_block_eq_support_of_card_three hx hsupp
  by_cases hcore : ∀ W : Subgroup (Perm (Fin 10)), W ≤ Y →
      atilde ≤ normalizer (W : Set (Perm (Fin 10))) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 Y
  · exact Or.inl hcore
  · right
    push Not at hcore
    obtain ⟨W, hWY, hWnorm, hWcop, hWnotcore⟩ := hcore
    obtain ⟨l, hWV⟩ := exists_le_kleinV hWnorm hWcop
    have hWne : W ≠ ⊥ := by
      intro hbot
      exact hWnotcore (by rw [hbot]; exact bot_le)
    have hmoves : ∃ a ∈ block i, x a ≠ a := by
      refine ⟨blockPt i 0, ?_, ?_⟩
      · exact blockPt_mem i 0
      · have hmem : blockPt i 0 ∈ x.support := by
          rw [hi]
          exact blockPt_mem i 0
        simpa [Equiv.Perm.mem_support] using hmem
    have hbot : kleinV i ⊓ centralizer ({x} : Set (Perm (Fin 10))) = ⊥ :=
      kleinV_inf_centralizer_eq_bot_of_moves_block hx hmoves
    have hli : l ≠ i := by
      intro h
      have hWlebot : W ≤ ⊥ := by
        calc W ≤ kleinV i ⊓ Y := le_inf (h ▸ hWV) hWY
          _ ≤ kleinV i ⊓ centralizer ({x} : Set (Perm (Fin 10))) :=
              inf_le_inf_left (kleinV i) hYx
          _ = ⊥ := hbot
      exact hWne (le_bot_iff.mp hWlebot)
    have hnotnorm : ¬ Y ≤ normalizer (kleinV l : Set (Perm (Fin 10))) := by
      intro hYnorm
      exact hWnotcore (le_trans (le_inf hWV hWY)
        (kleinV_inf_le_relPPrimeCore_of_le_normalizer hYnorm))
    have htrans := transitive_on_compl_of_failure hx hi hli hWY hWV hWne hYx hAY hnotnorm
    rw [hi]
    exact altOff_le_of_transitive_on_compl hx hi hAY hYx htrans

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Perm
