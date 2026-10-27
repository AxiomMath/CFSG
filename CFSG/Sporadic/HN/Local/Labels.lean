module

public import CFSG.Sporadic.HN.LocalK
public import CFSG.Sporadic.HN.Local.AltAbstract
public import CFSG.Sporadic.HN.Local.AltInvolutions
public import TauCeti.GroupTheory.Perm.Jordan
import CFSG.Sporadic.HN.Local.LabelsK

public section

namespace CFSG.Sporadic.HN.Local

open Equiv CFSG.Sporadic.HN.LocalK

@[expose] def maskSet (m : ℕ) : Finset (Fin 12) :=
  Finset.univ.filter fun i : Fin 12 => m.testBit i.val

@[expose] def pOne : Equiv.Perm (Fin 12) where
  toFun i := ⟨Native.altP1[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨Native.altP1inv[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def pTwo : Equiv.Perm (Fin 12) where
  toFun i := ⟨Native.altP2[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨Native.altP2inv[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  left_inv := by decide
  right_inv := by decide

theorem pOne_even : pOne ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem pTwo_even : pTwo ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem maskSet_isCanon : ∀ k : Fin 462, IsCanon (maskSet Native.altLabels[k.val]!) :=
  LabelsK.canonAll_sound (L := Native.altLabels) (by decide +kernel) (by decide +kernel)

@[expose] def labP (k : Fin 462) : Part := ⟨maskSet Native.altLabels[k.val]!, maskSet_isCanon k⟩

theorem lab_eq₁ : ∀ k : Fin 462, maskSet Native.altLabels[(pi2 k).val]! =
    canon ((maskSet Native.altLabels[k.val]!).map pOne.toEmbedding) :=
  LabelsK.labAll_sound (L := Native.altLabels) (P := Native.altPi2) (p := pOne)
    (q := fun j => Native.altP1inv[j]! % 12) (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem lab_eq₂ : ∀ k : Fin 462, maskSet Native.altLabels[(pi3 k).val]! =
    canon ((maskSet Native.altLabels[k.val]!).map pTwo.toEmbedding) :=
  LabelsK.labAll_sound (L := Native.altLabels) (P := Native.altPi3) (p := pTwo)
    (q := fun j => Native.altP2inv[j]! % 12) (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem masks_nodup : Native.altLabels.toList.Nodup :=
  (LabelsK.ndW_sound 0 (by decide +kernel)).1

theorem masks_lt : ∀ m ∈ Native.altLabels.toList, m < 4096 :=
  LabelsK.ltW_sound (by decide +kernel)

theorem maskSet_inj_of_lt {m m' : ℕ} (hm : m < 4096) (hm' : m' < 4096)
    (h : maskSet m = maskSet m') : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun S : Finset (Fin 12) => (⟨i, hi⟩ : Fin 12) ∈ S) h
    simpa [maskSet] using this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (by
        calc 4096 = 2 ^ 12 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm' (by
        calc 4096 = 2 ^ 12 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem altLabels_size : Native.altLabels.size = 462 := by decide +kernel

theorem labP_injective : Function.Injective labP := by
  intro i j h
  have h1 : maskSet Native.altLabels[i.val]! = maskSet Native.altLabels[j.val]! :=
    congrArg Subtype.val h
  have hi : i.val < Native.altLabels.toList.length := by
    rw [Array.length_toList, altLabels_size]; exact i.2
  have hj : j.val < Native.altLabels.toList.length := by
    rw [Array.length_toList, altLabels_size]; exact j.2
  have hmi : Native.altLabels[i.val]! = Native.altLabels.toList[i.val] := by
    rw [getElem!_pos Native.altLabels i.val (by rw [altLabels_size]; exact i.2)]; simp
  have hmj : Native.altLabels[j.val]! = Native.altLabels.toList[j.val] := by
    rw [getElem!_pos Native.altLabels j.val (by rw [altLabels_size]; exact j.2)]; simp
  have hlt : ∀ k (hk : k < Native.altLabels.toList.length), Native.altLabels.toList[k] < 4096 :=
    fun k hk => masks_lt _ (List.getElem_mem hk)
  have h2 : Native.altLabels.toList[i.val] = Native.altLabels.toList[j.val] :=
    maskSet_inj_of_lt (hlt _ hi) (hlt _ hj) (by rw [← hmi, ← hmj]; exact h1)
  exact Fin.ext ((List.Nodup.getElem_inj_iff masks_nodup).1 h2)

theorem labP_bijective : Function.Bijective labP :=
  (Fintype.bijective_iff_injective_and_card labP).2 ⟨labP_injective, by simp [card_part]⟩

theorem labP_pi2 (k : Fin 462) : labP (pi2 k) = pOne • labP k := Subtype.ext (lab_eq₁ k)

theorem labP_pi3 (k : Fin 462) : labP (pi3 k) = pTwo • labP k := Subtype.ext (lab_eq₂ k)

@[expose] def sig2 : Equiv.Perm (Fin 12) where
  toFun i := ⟨Native.typeS2[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨Native.typeS2inv[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def sig4 : Equiv.Perm (Fin 12) where
  toFun i := ⟨Native.typeS4[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨Native.typeS4inv[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩
  left_inv := by decide
  right_inv := by decide

theorem cycleType_of_support {σ : Equiv.Perm (Fin 12)} (h : σ ^ 2 = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) : σ.cycleType = Multiset.replicate k 2 := by
  have h1 := involution_cycleType h
  have h2 : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
  rw [h1] at h2
  simp only [Multiset.sum_replicate, smul_eq_mul] at h2
  rw [h1]
  congr 1
  omega

theorem sig2_sq : sig2 ^ 2 = 1 := by decide
theorem sig4_sq : sig4 ^ 2 = 1 := by decide
theorem pOne_sq : pOne ^ 2 = 1 := by decide

theorem sig2_type : sig2.cycleType = Multiset.replicate 2 2 :=
  cycleType_of_support sig2_sq (by decide)

theorem sig4_type : sig4.cycleType = Multiset.replicate 4 2 :=
  cycleType_of_support sig4_sq (by decide)

theorem pOne_type : pOne.cycleType = Multiset.replicate 6 2 :=
  cycleType_of_support pOne_sq (by decide)

theorem sig2_even : sig2 ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem sig4_even : sig4 ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem lab_eq_t2 : ∀ k : Fin 462, maskSet Native.altLabels[(pit2 k).val]! =
    canon ((maskSet Native.altLabels[k.val]!).map sig2.toEmbedding) :=
  LabelsK.labAll_sound (L := Native.altLabels) (P := Native.typePi2) (p := sig2)
    (q := fun j => Native.typeS2inv[j]! % 12) (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem lab_eq_t4 : ∀ k : Fin 462, maskSet Native.altLabels[(pit4 k).val]! =
    canon ((maskSet Native.altLabels[k.val]!).map sig4.toEmbedding) :=
  LabelsK.labAll_sound (L := Native.altLabels) (P := Native.typePi4) (p := sig4)
    (q := fun j => Native.typeS4inv[j]! % 12) (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem labP_pit2 (k : Fin 462) : labP (pit2 k) = sig2 • labP k := Subtype.ext (lab_eq_t2 k)

theorem labP_pit4 (k : Fin 462) : labP (pit4 k) = sig4 • labP k := Subtype.ext (lab_eq_t4 k)

noncomputable abbrev KP : Subgroup (Perm (Fin 12)) := Subgroup.closure {pOne, pTwo}

def reach : ℕ → Finset (Fin 12 × Fin 12)
  | 0 => {(0, 1)}
  | n + 1 => reach n ∪ (reach n).image (fun q => (pOne q.1, pOne q.2)) ∪
      (reach n).image (fun q => (pTwo q.1, pTwo q.2))

theorem reach_card : (reach 23).card = 132 :=
  LabelsK.card_of_words (p₁ := pOne) (p₂ := pTwo) reach.eq_1 reach.eq_2 LabelsK.wordAt
    (by decide +kernel)

theorem reach_sub : ∀ n, ∀ q ∈ reach n, q.1 ≠ q.2 ∧ ∃ g ∈ KP, g 0 = q.1 ∧ g 1 = q.2 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    rw [reach, Finset.mem_singleton] at hq
    subst hq
    exact ⟨by decide, 1, KP.one_mem, rfl, rfl⟩
  | succ n ih =>
    intro q hq
    simp only [reach, Finset.mem_union, Finset.mem_image] at hq
    rcases hq with (hq | ⟨q', hq', rfl⟩) | ⟨q', hq', rfl⟩
    · exact ih q hq
    · obtain ⟨hne, g, hg, h0, h1⟩ := ih q' hq'
      refine ⟨fun e => hne (pOne.injective e), pOne * g,
        KP.mul_mem (Subgroup.subset_closure (Set.mem_insert _ _)) hg, ?_, ?_⟩
      · simp [h0]
      · simp [h1]
    · obtain ⟨hne, g, hg, h0, h1⟩ := ih q' hq'
      refine ⟨fun e => hne (pTwo.injective e), pTwo * g,
        KP.mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hg, ?_, ?_⟩
      · simp [h0]
      · simp [h1]

theorem exists_pair {a b : Fin 12} (hab : a ≠ b) : ∃ g ∈ KP, g 0 = a ∧ g 1 = b := by
  classical
  have hsub : reach 23 ⊆ (Finset.univ : Finset (Fin 12 × Fin 12)).filter (fun q => q.1 ≠ q.2) :=
    fun q hq => Finset.mem_filter.2 ⟨Finset.mem_univ _, (reach_sub 23 q hq).1⟩
  have h132 : ((Finset.univ : Finset (Fin 12 × Fin 12)).filter (fun q => q.1 ≠ q.2)).card = 132 := by
    decide +kernel
  have hcard : ((Finset.univ : Finset (Fin 12 × Fin 12)).filter (fun q => q.1 ≠ q.2)).card ≤
      (reach 23).card := by
    rw [reach_card, h132]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : (a, b) ∈ reach 23 := by
    rw [heq]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩
  obtain ⟨-, g, hg, h0, h1⟩ := reach_sub 23 _ hmem
  exact ⟨g, hg, h0, h1⟩

theorem KP_two_pretransitive : MulAction.IsMultiplyPretransitive KP (Fin 12) 2 := by
  have key : ∀ f : Fin 2 ↪ Fin 12, ∃ g : KP, g • (⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 12) = f := by
    intro f
    obtain ⟨g, hg, h0, h1⟩ := exists_pair (a := f 0) (b := f 1)
      (fun e => absurd (f.injective e) (by decide))
    refine ⟨⟨g, hg⟩, ?_⟩
    apply DFunLike.ext
    intro i
    fin_cases i
    · exact h0
    · exact h1
  exact (MulAction.isPretransitive_iff_base _).2 key

set_option maxRecDepth 100000 in
theorem seven_order : orderOf ((pOne * pTwo) ^ 5) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem seven_cycle : ((pOne * pTwo) ^ 5).IsCycle ∧ ((pOne * pTwo) ^ 5).support.card = 7 := by
  have hs : ((pOne * pTwo) ^ 5).support.card = 7 := by decide +kernel
  refine ⟨Equiv.Perm.isCycle_of_prime_order (by rw [seven_order]; norm_num)
    (by rw [seven_order, hs]; norm_num), hs⟩

theorem closure_pOne_pTwo : KP = alternatingGroup (Fin 12) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact pOne_even
    · exact pTwo_even
  · have hprim : MulAction.IsPreprimitive KP (Fin 12) :=
      MulAction.isPreprimitive_of_is_two_pretransitive KP_two_pretransitive
    exact TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem hprim (p := 7)
      (by norm_num) (by simp) seven_cycle.1 seven_cycle.2
      (KP.pow_mem (KP.mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) 5)

theorem natHom_alt_injective :
    Function.Injective (natHom.comp (alternatingGroup (Fin 12)).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hs : IsSimpleGroup (alternatingGroup (Fin 12)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (natHom.comp (alternatingGroup (Fin 12)).subtype).ker with h | h
  · exact h
  · exfalso
    have hp : (⟨pOne, pOne_even⟩ : alternatingGroup (Fin 12)) ∈
        (natHom.comp (alternatingGroup (Fin 12)).subtype).ker := by rw [h]; trivial
    have e := congrArg (fun f : Perm Part => f (labP 0)) (MonoidHom.mem_ker.1 hp)
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, natHom_apply, Perm.coe_one, id_eq] at e
    rw [← labP_pi2] at e
    exact absurd (labP_injective e) (by decide +kernel)

end CFSG.Sporadic.HN.Local
