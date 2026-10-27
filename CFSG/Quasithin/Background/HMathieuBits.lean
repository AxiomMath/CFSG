module

public import CFSG.Monster.Code.Bits
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

abbrev Wn (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

@[expose] def toW (n m : ℕ) : Wn n := Multiplicative.ofAdd (bvec n m)

theorem toAdd_toW (n m : ℕ) : Multiplicative.toAdd (toW n m) = bvec n m := rfl

theorem toW_xor (n a b : ℕ) : toW n (a ^^^ b) = toW n a * toW n b := by
  rw [toW, bvec_xor]
  rfl

theorem toW_zero (n : ℕ) : toW n 0 = 1 := by
  rw [toW, bvec_zero]
  rfl

theorem testBit_eq_false_of_lt_pow {n m i : ℕ} (hm : m < 2 ^ n) (hi : n ≤ i) :
    m.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hi))

theorem bvec_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : bvec n a = bvec n b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrFun h ⟨i, hi⟩
    simp only [bvec_apply] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [testBit_eq_false_of_lt_pow ha (by omega), testBit_eq_false_of_lt_pow hb (by omega)]

theorem toW_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : toW n a = toW n b) : a = b :=
  bvec_inj ha hb (congrArg Multiplicative.toAdd h)

@[expose] def toWFin (n : ℕ) (m : Fin (2 ^ n)) : Wn n := toW n m

theorem toWFin_injective (n : ℕ) : Function.Injective (toWFin n) :=
  fun a b h => Fin.ext (toW_inj a.2 b.2 h)

theorem card_Wn (n : ℕ) : Fintype.card (Wn n) = 2 ^ n := by
  rw [Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem toWFin_bijective (n : ℕ) : Function.Bijective (toWFin n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨toWFin_injective n, by rw [Fintype.card_fin, card_Wn]⟩

theorem toW_surj (n : ℕ) (w : Wn n) : ∃ m < 2 ^ n, toW n m = w := by
  obtain ⟨m, hm⟩ := (toWFin_bijective n).2 w
  exact ⟨m, m.2, hm⟩

@[expose] def actM : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, m => (if m % 2 = 1 then c else 0) ^^^ actM cs (m / 2)

theorem actM_lt {k : ℕ} : ∀ {cs : List ℕ}, (∀ c ∈ cs, c < 2 ^ k) → ∀ m, actM cs m < 2 ^ k
  | [], _, m => by simp [actM]
  | c :: cs, h, m => by
    rw [actM]
    refine Nat.xor_lt_two_pow ?_ (actM_lt (fun d hd => h d (List.mem_cons_of_mem c hd)) _)
    split_ifs
    · exact h c List.mem_cons_self
    · exact Nat.two_pow_pos k

theorem bvec_actM (k : ℕ) : ∀ (cs : List ℕ) (m : ℕ),
    bvec k (actM cs m) =
      ∑ j ∈ Finset.range cs.length, if m.testBit j then bvec k (cs.getD j 0) else 0
  | [], m => by simp [actM, bvec_zero]
  | c :: cs, m => by
    rw [actM, bvec_xor, bvec_actM k cs (m / 2), List.length_cons, Finset.sum_range_succ',
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Nat.testBit_succ, List.getD_cons_succ]
    · simp only [Nat.testBit_zero, List.getD_cons_zero]
      by_cases h : m % 2 = 1
      · simp [h]
      · simp [h, bvec_zero]

theorem bvec_eq_sum (n m : ℕ) :
    bvec n m = ∑ j ∈ Finset.range n, if m.testBit j then bvec n (2 ^ j) else 0 := by
  funext i
  rw [Finset.sum_apply]
  have h : ∀ j ∈ Finset.range n, (if m.testBit j then bvec n (2 ^ j) else 0) i =
      if (i : ℕ) = j then bvec n m i else 0 := by
    intro j _
    by_cases hij : (i : ℕ) = j
    · subst hij
      by_cases hm : m.testBit i <;> simp [hm, bvec_apply]
    · rw [ite_eq_right hij]
      split_ifs
      · simp [bvec_apply, Ne.symm hij]
      · rfl
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq (Finset.range n) (i : ℕ),
    ite_eq_left (Finset.mem_range.2 i.2)]

theorem addHom_bvec {n k : ℕ} (f : (Fin n → ZMod 2) →+ (Fin k → ZMod 2)) (cs : List ℕ)
    (hlen : cs.length = n)
    (hcol : ∀ j < n, f (bvec n (2 ^ j)) = bvec k (cs.getD j 0)) (m : ℕ) :
    f (bvec n m) = bvec k (actM cs m) := by
  rw [bvec_eq_sum, map_sum, bvec_actM, hlen]
  refine Finset.sum_congr rfl fun j hj => ?_
  split_ifs
  · exact hcol j (Finset.mem_range.1 hj)
  · exact map_zero f

@[expose] def XorLin (f : ℕ → ℕ) : Prop := ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem two_mul_xor (a b : ℕ) : 2 * (a ^^^ b) = 2 * a ^^^ 2 * b := by
  have h := Nat.shiftLeft_xor_distrib (i := 1) (a := a) (b := b)
  simp only [Nat.shiftLeft_eq, pow_one] at h
  rw [mul_comm 2 (a ^^^ b), h, mul_comm a 2, mul_comm b 2]

theorem XorLin.map_zero {f : ℕ → ℕ} (hf : XorLin f) : f 0 = 0 := by
  have h := hf 0 0
  rw [Nat.zero_xor] at h
  have h2 : f 0 ^^^ f 0 = 0 := Nat.xor_self _
  rw [← h] at h2
  exact h2

theorem mod_two_xor (a b : ℕ) : (a ^^^ b) % 2 = 1 ↔ ¬ (a % 2 = 1 ↔ b % 2 = 1) := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1 <;> simp_all

theorem actM_xor : ∀ (cs : List ℕ), XorLin (actM cs)
  | [], a, b => by simp [actM]
  | c :: cs, a, b => by
    rw [actM, actM, actM, Nat.xor_div_two, actM_xor cs]
    have hif : (if (a ^^^ b) % 2 = 1 then c else 0) =
        (if a % 2 = 1 then c else 0) ^^^ (if b % 2 = 1 then c else 0) := by
      have hx := mod_two_xor a b
      by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1
      · rw [ite_eq_right (by tauto), ite_eq_left ha, ite_eq_left hb, Nat.xor_self]
      · rw [ite_eq_left (by tauto), ite_eq_left ha, ite_eq_right hb, Nat.xor_zero]
      · rw [ite_eq_left (by tauto), ite_eq_right ha, ite_eq_left hb, Nat.zero_xor]
      · rw [ite_eq_right (by tauto), ite_eq_right ha, ite_eq_right hb, Nat.xor_zero]
    rw [hif]
    ac_rfl

theorem XorLin.comp {f g : ℕ → ℕ} (hf : XorLin f) (hg : XorLin g) : XorLin (f ∘ g) :=
  fun a b => by
    show f (g (a ^^^ b)) = f (g a) ^^^ f (g b)
    rw [hg a b, hf]

theorem actM_map {f : ℕ → ℕ} (hf : XorLin f) : ∀ (ds : List ℕ) (m : ℕ),
    actM (ds.map f) m = f (actM ds m)
  | [], m => by simp [actM, hf.map_zero]
  | d :: ds, m => by
    rw [List.map_cons, actM, actM, actM_map hf ds, hf]
    by_cases h : m % 2 = 1
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, hf.map_zero]

theorem testBit_div_two_pow_mod (m n : ℕ) : m % 2 ^ (n + 1) / 2 = m / 2 % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Nat.testBit_succ, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_succ]
  congr 1

theorem actM_mod : ∀ (cs : List ℕ) (m : ℕ), actM cs (m % 2 ^ cs.length) = actM cs m
  | [], m => rfl
  | c :: cs, m => by
    rw [actM, actM, List.length_cons, testBit_div_two_pow_mod, actM_mod cs]
    congr 2
    rw [pow_succ, Nat.mod_mul_left_mod]

@[expose] def matOf (n : ℕ) (f : ℕ → ℕ) : List ℕ := (List.range n).map fun j => f (2 ^ j)

theorem length_matOf (n : ℕ) (f : ℕ → ℕ) : (matOf n f).length = n := by
  simp [matOf]

theorem actM_matOf {f : ℕ → ℕ} (hf : XorLin f) : ∀ (n m : ℕ), m < 2 ^ n →
    actM (matOf n f) m = f m
  | 0, m, hm => by
    have : m = 0 := by simpa using hm
    subst this
    simp [matOf, actM, hf.map_zero]
  | n + 1, m, hm => by
    have hf2 : XorLin fun x => f (2 * x) := fun a b => by
      show f (2 * (a ^^^ b)) = f (2 * a) ^^^ f (2 * b)
      rw [← hf, two_mul_xor]
    have ih := actM_matOf hf2 n (m / 2) (by
      rw [pow_succ] at hm
      omega)
    have hlist : matOf (n + 1) f = f 1 :: matOf n fun x => f (2 * x) := by
      simp only [matOf, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp [Function.comp_apply, pow_succ, mul_comm]
    rw [hlist, actM, ih]
    have hm2 : m = (m % 2) ^^^ (2 * (m / 2)) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rcases i with _ | i
      · rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero,
          Nat.mul_mod_right, Nat.mod_mod]
        simp
      · rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
        have : m % 2 / 2 = 0 := by omega
        rw [this, Nat.zero_testBit, Bool.false_xor]
    conv_rhs => rw [hm2, hf]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [h, ite_eq_right (by norm_num), hf.map_zero]
    · rw [h, ite_eq_left rfl]

structure MaskCoords (V : Type*) [CommGroup V] (n : ℕ) where
  vm : ℕ → V
  vm_xor : ∀ a b, vm (a ^^^ b) = vm a * vm b
  vm_mod : ∀ a, vm (a % 2 ^ n) = vm a
  vm_inj : ∀ a b, a < 2 ^ n → b < 2 ^ n → vm a = vm b → a = b
  vm_surj : ∀ v, ∃ m < 2 ^ n, vm m = v

theorem toW_mod (n a : ℕ) : toW n (a % 2 ^ n) = toW n a := by
  rw [toW, toW]
  congr 1
  funext i
  simp only [bvec_apply, Nat.testBit_mod_two_pow, i.2, decide_true, Bool.true_and]

@[expose] def MaskCoords.std (n : ℕ) : MaskCoords (Wn n) n where
  vm := toW n
  vm_xor := toW_xor n
  vm_mod := toW_mod n
  vm_inj _ _ ha hb h := toW_inj ha hb h
  vm_surj := toW_surj n

@[expose] def MaskCoords.ofEquiv {V : Type*} [CommGroup V] {n : ℕ} (e : V ≃* Wn n) :
    MaskCoords V n where
  vm m := e.symm (toW n m)
  vm_xor a b := by rw [toW_xor, map_mul]
  vm_mod a := by rw [toW_mod]
  vm_inj a b ha hb h := toW_inj ha hb (e.symm.injective h)
  vm_surj v := by
    obtain ⟨m, hm, hmv⟩ := toW_surj n (e v)
    exact ⟨m, hm, by rw [hmv, MulEquiv.symm_apply_apply]⟩

theorem MaskCoords.ofEquiv_vm {V : Type*} [CommGroup V] {n : ℕ} (e : V ≃* Wn n) (m : ℕ) :
    (MaskCoords.ofEquiv e).vm m = e.symm (toW n m) := rfl

namespace MaskCoords

variable {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n)

theorem vm_zero : c.vm 0 = 1 := by
  have h := c.vm_xor 0 0
  rw [Nat.zero_xor] at h
  exact left_eq_mul.1 h

theorem card_eq (U : Subgroup V) (P : ℕ → Bool) (hP : ∀ m < 2 ^ n, c.vm m ∈ U ↔ P m = true) :
    Nat.card U = ((List.range (2 ^ n)).filter P).length := by
  classical
  have hfin : Finite V := by
    refine Finite.of_surjective (fun m : Fin (2 ^ n) => c.vm m) fun v => ?_
    obtain ⟨m, hm, hmv⟩ := c.vm_surj v
    exact ⟨⟨m, hm⟩, hmv⟩
  have hinj : Set.InjOn c.vm (((List.range (2 ^ n)).filter P).toFinset : Set ℕ) := by
    intro a ha b hb hab
    simp only [List.coe_toFinset, List.mem_filter, List.mem_range, Set.mem_ofPred_eq] at ha hb
    exact c.vm_inj a b ha.1 hb.1 hab
  have himg : (((List.range (2 ^ n)).filter P).toFinset.image c.vm : Set V) = (U : Set V) := by
    ext v
    simp only [Finset.coe_image, List.coe_toFinset, List.mem_filter, List.mem_range,
      Set.mem_image, Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨m, ⟨hm, hPm⟩, rfl⟩
      exact (hP m hm).2 hPm
    · intro hv
      obtain ⟨m, hm, rfl⟩ := c.vm_surj v
      exact ⟨m, ⟨hm, (hP m hm).1 hv⟩, rfl⟩
  have hnd : ((List.range (2 ^ n)).filter P).Nodup := (List.nodup_range).filter _
  rw [← SetLike.coe_sort_coe, ← himg, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hnd]

theorem length_le_card (U : Subgroup V) (l : List ℕ) (hnd : l.Nodup)
    (hlt : ∀ m ∈ l, m < 2 ^ n) (hU : ∀ m ∈ l, c.vm m ∈ U) : l.length ≤ Nat.card U := by
  classical
  have hfin : Finite V := by
    refine Finite.of_surjective (fun m : Fin (2 ^ n) => c.vm m) fun v => ?_
    obtain ⟨m, hm, hmv⟩ := c.vm_surj v
    exact ⟨⟨m, hm⟩, hmv⟩
  have hinj : Set.InjOn c.vm (l.toFinset : Set ℕ) := by
    intro a ha b hb hab
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at ha hb
    exact c.vm_inj a b (hlt a ha) (hlt b hb) hab
  have hsub : ((l.toFinset.image c.vm : Finset V) : Set V) ⊆ (U : Set V) := by
    intro v hv
    simp only [Finset.coe_image, List.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    exact hU m hm
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = (l.toFinset.image c.vm).card := (Finset.card_image_of_injOn hinj).symm
    _ = ((l.toFinset.image c.vm : Finset V) : Set V).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (U : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card U := Nat.card_coe_set_eq _

end MaskCoords

@[expose] def xorAll : List ℕ → ℕ
  | [] => 0
  | a :: l => a ^^^ xorAll l

@[expose] def combos : List ℕ → List ℕ
  | [] => [0]
  | a :: l => combos l ++ (combos l).map (· ^^^ a)

theorem length_combos : ∀ l : List ℕ, (combos l).length = 2 ^ l.length
  | [] => rfl
  | a :: l => by
    rw [combos, List.length_append, List.length_map, length_combos l, List.length_cons,
      pow_succ]
    ring

theorem combos_lt {n : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a < 2 ^ n) → ∀ x ∈ combos l, x < 2 ^ n
  | [], _, x, hx => by
    simp only [combos, List.mem_singleton] at hx
    rw [hx]
    exact Nat.two_pow_pos n
  | a :: l, h, x, hx => by
    rw [combos, List.mem_append, List.mem_map] at hx
    have hl := combos_lt (fun b hb => h b (List.mem_cons_of_mem a hb))
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hl x hx
    · exact Nat.xor_lt_two_pow (hl y hy) (h a List.mem_cons_self)

theorem MaskCoords.vm_mem_of_combos {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n)
    (U : Subgroup V) : ∀ {l : List ℕ}, (∀ a ∈ l, c.vm a ∈ U) → ∀ x ∈ combos l, c.vm x ∈ U
  | [], _, x, hx => by
    simp only [combos, List.mem_singleton] at hx
    rw [hx, c.vm_zero]
    exact U.one_mem
  | a :: l, h, x, hx => by
    rw [combos, List.mem_append, List.mem_map] at hx
    have hl := MaskCoords.vm_mem_of_combos c U (fun b hb => h b (List.mem_cons_of_mem a hb))
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hl x hx
    · rw [c.vm_xor]
      exact U.mul_mem (hl y hy) (h a List.mem_cons_self)

theorem MaskCoords.pow_le_card {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n)
    (U : Subgroup V) (l : List ℕ) (hnd : (combos l).Nodup) (hlt : ∀ a ∈ l, a < 2 ^ n)
    (hU : ∀ a ∈ l, c.vm a ∈ U) : 2 ^ l.length ≤ Nat.card U := by
  rw [← length_combos]
  exact c.length_le_card U _ hnd (combos_lt hlt) (c.vm_mem_of_combos U hU)

end CFSG.Quasithin.H.Mathieu
