module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2xN_ztri (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = -1 := by
  have hval := ZMod.val_lt a
  have ha : a = (a.val : ZMod 3) := (ZMod.natCast_zmod_val a).symm
  interval_cases a.val
  · left; rw [ha]; decide
  · right; left; rw [ha]; decide
  · right; right; rw [ha]; decide

private lemma ggQ2xN_dot_self_eq_wt {n : ℕ} (v : GGBCV n) :
    v ⬝ᵥ v = (ggBCWt v : ZMod 3) := by
  rw [ggBCWt, dotProduct]
  rw [← Finset.sum_boole (fun i => v i ≠ 0) Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rcases ggQ2xN_ztri (v i) with h | h | h <;> rw [h] <;> decide

private lemma ggQ2xN_wt_eq_zero_iff {n : ℕ} (v : GGBCV n) : ggBCWt v = 0 ↔ v = 0 := by
  rw [ggBCWt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    exact not_not.mp (h (Finset.mem_univ i))
  · intro h i _
    rw [h]
    simp

private lemma ggQ2xN_refl_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  have hdot : ggBCDot c v = c ⬝ᵥ v := by
    simp [ggBCDot, dotProduct, Finset.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  have h : (ggBCRefl c hc : GGBCV n → GGBCV n) =
      @Module.preReflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup (ggBCModule n)
        c ((2 / (c ⬝ᵥ c)) • ggBCDot c) := rfl
  rw [h]
  rw [@Module.preReflection_apply (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
      (ggBCModule n) c ((2 / (c ⬝ᵥ c)) • ggBCDot c) v]
  change v - ((2 / (c ⬝ᵥ c)) * (ggBCDot c v)) • c = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c
  rw [hdot]
  have hsq : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := by
    rcases ggQ2xN_ztri (c ⬝ᵥ c) with h | h | h
    · exact absurd h hc
    · rw [h]; decide
    · rw [h]; decide
  have hcoef : (2 / (c ⬝ᵥ c)) * (c ⬝ᵥ v) = -((c ⬝ᵥ v) * (c ⬝ᵥ c)) := by
    rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_left hsq]
    rcases ggQ2xN_ztri (c ⬝ᵥ c) with hX | hX | hX
    · exact absurd hX hc
    · rw [hX]
      rcases ggQ2xN_ztri (c ⬝ᵥ v) with hY | hY | hY <;> rw [hY] <;> decide
    · rw [hX]
      rcases ggQ2xN_ztri (c ⬝ᵥ v) with hY | hY | hY <;> rw [hY] <;> decide
  rw [hcoef, show (-((c ⬝ᵥ v) * (c ⬝ᵥ c))) • c =
      -(((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c) from neg_smul _ _]
  abel

private lemma ggQ2xN_sum_single {n : ℕ} (i : Fin n) (a : ZMod 3) :
    ∑ j, (Pi.single i a : GGBCV n) j = a := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xN_wt_single_one {n : ℕ} (i : Fin n) :
    ggBCWt (Pi.single i (1 : ZMod 3) : GGBCV n) = 1 := by
  rw [ggBCWt]
  have h : (Finset.univ.filter fun j => (Pi.single i (1 : ZMod 3) : GGBCV n) j ≠ 0) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      rw [Pi.single_eq_of_ne hji] at hj
      exact hj rfl
    · intro hji
      rw [hji, Pi.single_eq_same]
      exact one_ne_zero
  rw [h, Finset.card_singleton]

private lemma ggQ2xN_single_one_dot_self {n : ℕ} (i : Fin n) :
    (Pi.single i (1 : ZMod 3) : GGBCV n) ⬝ᵥ Pi.single i 1 ≠ 0 := by
  rw [single_dotProduct, Pi.single_eq_same, one_mul]
  exact one_ne_zero

private lemma ggQ2xN_single_one_mem_roots {n : ℕ} (i : Fin n) :
    (Pi.single i (1 : ZMod 3) : GGBCV n) ∈ ggBCRoots n := by
  rw [ggBCRoots, Set.mem_setOf_eq, ggQ2xN_wt_single_one]
  norm_num

private noncomputable def ggQ2xN_flip {n : ℕ} (i : Fin n) (v : GGBCV n) : GGBCV n :=
  ggBCRefl (Pi.single i (1 : ZMod 3)) (ggQ2xN_single_one_dot_self i) v

private lemma ggQ2xN_flip_apply {n : ℕ} (i : Fin n) (v : GGBCV n) :
    ggQ2xN_flip i v = v + (v i) • Pi.single i (1 : ZMod 3) := by
  unfold ggQ2xN_flip
  rw [ggQ2xN_refl_apply, single_one_dotProduct, dotProduct_single, Pi.single_eq_same,
    mul_one, mul_one]

private lemma ggQ2xN_flip_apply_self {n : ℕ} (i : Fin n) (v : GGBCV n) :
    ggQ2xN_flip i v i = - v i := by
  rw [ggQ2xN_flip_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rcases ggQ2xN_ztri (v i) with h | h | h <;> rw [h] <;> decide

private lemma ggQ2xN_flip_apply_of_ne {n : ℕ} (i j : Fin n) (hij : j ≠ i) (v : GGBCV n) :
    ggQ2xN_flip i v j = v j := by
  rw [ggQ2xN_flip_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij,
    smul_zero, add_zero]

private lemma ggQ2xN_flip_wt {n : ℕ} (i : Fin n) (v : GGBCV n) :
    ggBCWt (ggQ2xN_flip i v) = ggBCWt v := by
  rw [ggBCWt, ggBCWt]
  congr 1
  apply Finset.filter_congr
  intro j _
  by_cases hji : j = i
  · rw [hji, ggQ2xN_flip_apply_self]
    exact neg_eq_zero.not
  · rw [ggQ2xN_flip_apply_of_ne i j hji]

private lemma ggQ2xN_flip_sum {n : ℕ} (i : Fin n) (v : GGBCV n) :
    ∑ j, ggQ2xN_flip i v j = (∑ j, v j) + v i := by
  rw [ggQ2xN_flip_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ggQ2xN_sum_single, mul_one]

private lemma ggQ2xN_flip_mem {n : ℕ} (Z : Set (GGBCV n)) (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {v : GGBCV n} (hv : v ∈ Z) (i : Fin n) : ggQ2xN_flip i v ∈ Z := by
  unfold ggQ2xN_flip
  exact hZcl _ (hZroots (ggQ2xN_single_one_mem_roots i)) _ hv (ggQ2xN_single_one_dot_self i)


private lemma ggQ2xN_wt_diff {n : ℕ} (i m : Fin n) (him : i ≠ m) :
    ggBCWt ((Pi.single i (1 : ZMod 3) : GGBCV n) - (Pi.single m (1 : ZMod 3) : GGBCV n)) = 2 := by
  rw [ggBCWt]
  have h : (Finset.univ.filter (fun j =>
      ((Pi.single i (1 : ZMod 3) : GGBCV n) -
        (Pi.single m (1 : ZMod 3) : GGBCV n)) j ≠ 0)) = {i, m} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Pi.sub_apply]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · right
        by_cases hjm : j = m
        · exact hjm
        · exfalso
          rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hjm] at hj
          exact hj (sub_zero 0)
    · rintro (rfl | rfl)
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne him]; decide
      · rw [Pi.single_eq_of_ne (Ne.symm him), Pi.single_eq_same]; decide
  rw [h, Finset.card_insert_of_notMem (by simp [him]), Finset.card_singleton]

private lemma ggQ2xN_sum_diff {n : ℕ} (i m : Fin n) (him : i ≠ m) :
    ∑ j, ((Pi.single i (1 : ZMod 3) : GGBCV n) - (Pi.single m (1 : ZMod 3) : GGBCV n)) j = 0 := by
  have h : ((Pi.single i (1 : ZMod 3) : GGBCV n) - (Pi.single m (1 : ZMod 3) : GGBCV n)) =
      (Pi.single i (1 : ZMod 3) : GGBCV n) + (Pi.single m (-1) : GGBCV n) := by
    ext j
    rw [Pi.sub_apply, Pi.add_apply]
    by_cases hji : j = i
    · rw [hji, Pi.single_eq_same, Pi.single_eq_of_ne him, Pi.single_eq_of_ne him]; decide
    · by_cases hjm : j = m
      · rw [hjm, Pi.single_eq_of_ne (Ne.symm him), Pi.single_eq_same, Pi.single_eq_same]; decide
      · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hjm, Pi.single_eq_of_ne hjm]; decide
  rw [h]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ggQ2xN_sum_single, ggQ2xN_sum_single]
  decide

private lemma ggQ2xN_dot_diff {n : ℕ} (z : GGBCV n) (i m : Fin n) :
    z ⬝ᵥ ((Pi.single i (1 : ZMod 3) : GGBCV n) -
      (Pi.single m (1 : ZMod 3) : GGBCV n)) = z i - z m := by
  rw [dotProduct_sub, dotProduct_single_one, dotProduct_single_one]

private lemma ggQ2xN_wt_refl_ge {n : ℕ} (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0) (i m : Fin n)
    (him : i ≠ m) (hi : z i ≠ 0) (hm : z m = 0) :
    ggBCWt z ≤ ggBCWt (ggBCRefl z hz
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - (Pi.single m (1 : ZMod 3) : GGBCV n))) := by
  set ρ : GGBCV n := (Pi.single i (1 : ZMod 3)) - (Pi.single m (1 : ZMod 3) : GGBCV n) with hρ
  change ggBCWt z ≤ ggBCWt (ggBCRefl z hz ρ)
  have hc0 : (z ⬝ᵥ ρ) * (z ⬝ᵥ z) ≠ 0 := by
    apply mul_ne_zero _ hz
    rw [hρ, ggQ2xN_dot_diff, hm]
    exact fun h => hi (sub_eq_zero.mp h)
  have hsub : (Finset.univ.filter (fun k => z k ≠ 0)).erase i ∪ {m} ⊆
      Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0) := by
    intro k hk
    rw [Finset.mem_union] at hk
    rcases hk with hk | hk
    · simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨hki, hkS⟩ := hk
      have hkm : k ≠ m := by rintro rfl; exact hkS hm
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ k, ?_⟩
      rw [ggQ2xN_refl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hρk : ρ k = 0 := by
        rw [hρ]
        simp only [Pi.sub_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkm]
        decide
      rw [hρk, zero_add]
      exact mul_ne_zero hc0 hkS
    · rw [Finset.mem_singleton] at hk
      rw [hk]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ m, ?_⟩
      rw [ggQ2xN_refl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hρm : ρ m = -1 := by
        rw [hρ]
        simp only [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm him), Pi.single_eq_same]
        decide
      rw [hρm, hm, mul_zero, add_zero]
      decide
  have hmS : m ∉ Finset.univ.filter (fun k => z k ≠ 0) := by
    rw [Finset.mem_filter]; rintro ⟨_, h⟩; exact h hm
  have hiS : i ∈ Finset.univ.filter (fun k => z k ≠ 0) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hi⟩
  have hdisj : Disjoint ((Finset.univ.filter (fun k => z k ≠ 0)).erase i) {m} := by
    rw [Finset.disjoint_singleton_right]
    intro hm
    rw [Finset.mem_erase] at hm
    exact hmS hm.2
  have hcard : ((Finset.univ.filter (fun k => z k ≠ 0)).erase i ∪ {m}).card =
      (Finset.univ.filter (fun k => z k ≠ 0)).card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
      Finset.card_erase_add_one hiS]
  rw [ggBCWt, ggBCWt]
  calc (Finset.univ.filter (fun k => z k ≠ 0)).card
      = ((Finset.univ.filter (fun k => z k ≠ 0)).erase i ∪ {m}).card := hcard.symm
    _ ≤ (Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0)).card :=
        Finset.card_le_card hsub

private lemma ggQ2xN_wt_refl_full_ge {n : ℕ} (hn : 5 ≤ n) (z : GGBCV n)
    (hz : z ⬝ᵥ z ≠ 0) (i j : Fin n) (hij : i ≠ j) (hzij : z i ≠ z j)
    (hfull : ∀ k, z k ≠ 0) :
    3 ≤ ggBCWt (ggBCRefl z hz
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - (Pi.single j (1 : ZMod 3) : GGBCV n))) := by
  set ρ : GGBCV n := (Pi.single i (1 : ZMod 3)) - (Pi.single j (1 : ZMod 3) : GGBCV n) with hρ
  change 3 ≤ (Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0)).card
  have hc0 : (z ⬝ᵥ ρ) * (z ⬝ᵥ z) ≠ 0 := by
    apply mul_ne_zero _ hz
    rw [hρ, ggQ2xN_dot_diff]
    exact sub_ne_zero.mpr hzij
  have hsub : (Finset.univ.erase i).erase j ⊆
      Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0) := by
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    obtain ⟨hkj, hki⟩ := hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ k, ?_⟩
    rw [ggQ2xN_refl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hρk : ρ k = 0 := by
      rw [hρ]
      simp only [Pi.sub_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
      decide
    rw [hρk, zero_add]
    exact mul_ne_zero hc0 (hfull k)
  have hcard : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem (by simp [Finset.mem_erase, Ne.symm hij]),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  calc 3 ≤ ((Finset.univ.erase i).erase j).card := by rw [hcard]; omega
    _ ≤ (Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0)).card :=
        Finset.card_le_card hsub

private lemma ggQ2xN_partA {n : ℕ} (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hHL : ∀ z ∈ Z, ∑ i, z i = 0 → ∀ ρ ∈ ggBCRootsLamN n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggBCRootsLamN n) :
    ∀ z ∈ Z, (∑ i, z i) = 0 → ggBCWt z ≤ 2 := by
  intro z hz hsum
  by_contra hle
  push Not at hle
  have hw3 : 3 ≤ ggBCWt z := by omega
  have hw4 : 4 ≤ ggBCWt z := by
    rcases lt_or_eq_of_le hw3 with h4 | h3
    · omega
    · exfalso
      have h3z : ((3 : ℕ) : ZMod 3) = 0 := by decide
      exact hZ0 z hz (by rw [ggQ2xN_dot_self_eq_wt]; simpa [h3] using h3z)
  by_cases hfull : ∀ k, z k ≠ 0
  · haveI : NeZero n := ⟨by omega⟩
    have hfullWt : ggBCWt z = n := by
      rw [ggBCWt]
      have h : (Finset.univ.filter fun k => z k ≠ 0) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro k _
        exact hfull k
      rw [h, Finset.card_univ, Fintype.card_fin]
    have hn3 : (n : ZMod 3) ≠ 0 := by
      have h0 := hZ0 z hz
      rw [ggQ2xN_dot_self_eq_wt, hfullWt] at h0
      exact h0
    have hne : ∃ i j, z i ≠ z j := by
      by_contra h
      push Not at h
      have hconst : ∀ k, z k = z 0 := fun k => h k 0
      have hsum' : ∑ k, z k = (n : ZMod 3) * z 0 := by
        rw [Finset.sum_congr rfl (fun k _ => hconst k)]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hsum'] at hsum
      have hz0 : z 0 ≠ 0 := hfull 0
      rcases mul_eq_zero.mp hsum with h0 | h0
      · exact hn3 h0
      · exact hz0 h0
    obtain ⟨i, j, hzij⟩ := hne
    have hsign : ∀ k, z k = 1 ∨ z k = -1 := by
      intro k
      rcases ggQ2xN_ztri (z k) with h0 | h1 | h1
      · exact absurd h0 (hfull k)
      · exact Or.inl h1
      · exact Or.inr h1
    have hzj : z j = - z i := by
      rcases hsign i with hi | hi <;> rcases hsign j with hj | hj
      · exact absurd (hi.trans hj.symm) hzij
      · simp [hi, hj]
      · rw [hi, hj]; decide
      · exact absurd (hi.trans hj.symm) hzij
    have hij : i ≠ j := by rintro rfl; exact hzij rfl
    let ρ : GGBCV n := (Pi.single i (1 : ZMod 3)) - (Pi.single j (1 : ZMod 3))
    have hρN : ρ ∈ ggBCRootsLamN n := by
      rw [ggBCRootsLamN]
      refine ⟨?_, ?_⟩
      · change ggBCWt ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single j (1 : ZMod 3) : GGBCV n)) = 2
        exact ggQ2xN_wt_diff i j hij
      · change ∑ k, ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single j (1 : ZMod 3) : GGBCV n)) k = 0
        exact ggQ2xN_sum_diff i j hij
    have hz' := hHL z hz hsum ρ hρN (hZ0 z hz)
    have hge : 3 ≤ ggBCWt (ggBCRefl z (hZ0 z hz) ρ) :=
      ggQ2xN_wt_refl_full_ge hn z (hZ0 z hz) i j hij hzij hfull
    have hwt' : ggBCWt (ggBCRefl z (hZ0 z hz) ρ) = 2 := by
      have := hz'; rw [ggBCRootsLamN] at this; exact this.1
    omega
  · push Not at hfull
    obtain ⟨m, hm⟩ := hfull
    have hex : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      have hzero : ggBCWt z = 0 := by
        rw [ggBCWt]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro k _ hk
        exact hk (h k)
      omega
    obtain ⟨i, hi⟩ := hex
    have him : i ≠ m := by rintro rfl; exact hi hm
    let ρ : GGBCV n := (Pi.single i (1 : ZMod 3)) - (Pi.single m (1 : ZMod 3))
    have hρN : ρ ∈ ggBCRootsLamN n := by
      rw [ggBCRootsLamN]
      refine ⟨?_, ?_⟩
      · change ggBCWt ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single m (1 : ZMod 3) : GGBCV n)) = 2
        exact ggQ2xN_wt_diff i m him
      · change ∑ k, ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single m (1 : ZMod 3) : GGBCV n)) k = 0
        exact ggQ2xN_sum_diff i m him
    have hz' := hHL z hz hsum ρ hρN (hZ0 z hz)
    have hge : ggBCWt z ≤ ggBCWt (ggBCRefl z (hZ0 z hz) ρ) :=
      ggQ2xN_wt_refl_ge z (hZ0 z hz) i m him hi hm
    have hwt' : ggBCWt (ggBCRefl z (hZ0 z hz) ρ) = 2 := by
      have := hz'; rw [ggBCRootsLamN] at this; exact this.1
    omega

private lemma ggQ2xN_partB {n : ℕ} (Z : Set (GGBCV n))
    (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    ∀ z ∈ Z, 3 ≤ ggBCWt z → ∃ z' ∈ Z, (∑ i, z' i) = 0 ∧ ggBCWt z' = ggBCWt z := by
  intro z hz hw
  have hcard : 1 < (Finset.univ.filter fun k => z k ≠ 0).card := by
    have : ggBCWt z = (Finset.univ.filter fun k => z k ≠ 0).card := rfl
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases ggQ2xN_ztri (∑ k, z k) with hs | hs | hs
  · exact ⟨z, hz, hs, rfl⟩
  · by_cases hneg : ∃ k, z k = -1
    · obtain ⟨k, hk⟩ := hneg
      refine ⟨ggQ2xN_flip k z, ggQ2xN_flip_mem Z hZroots hZcl hz k, ?_,
        ggQ2xN_flip_wt k z⟩
      rw [ggQ2xN_flip_sum, hs, hk]; decide
    · have hzi : z i = 1 := by
        rcases ggQ2xN_ztri (z i) with h0 | h1 | h1
        · exact absurd h0 hi
        · exact h1
        · exact absurd h1 (fun hh => hneg ⟨i, hh⟩)
      have hzj : z j = 1 := by
        rcases ggQ2xN_ztri (z j) with h0 | h1 | h1
        · exact absurd h0 hj
        · exact h1
        · exact absurd h1 (fun hh => hneg ⟨j, hh⟩)
      refine ⟨ggQ2xN_flip j (ggQ2xN_flip i z), ?_, ?_, ?_⟩
      · exact ggQ2xN_flip_mem Z hZroots hZcl (ggQ2xN_flip_mem Z hZroots hZcl hz i) j
      · rw [ggQ2xN_flip_sum, ggQ2xN_flip_apply_of_ne i j (Ne.symm hij), ggQ2xN_flip_sum,
          hs, hzi, hzj]
        decide
      · rw [ggQ2xN_flip_wt, ggQ2xN_flip_wt]
  · by_cases hpos : ∃ k, z k = 1
    · obtain ⟨k, hk⟩ := hpos
      refine ⟨ggQ2xN_flip k z, ggQ2xN_flip_mem Z hZroots hZcl hz k, ?_,
        ggQ2xN_flip_wt k z⟩
      rw [ggQ2xN_flip_sum, hs, hk]; decide
    · have hzi : z i = -1 := by
        rcases ggQ2xN_ztri (z i) with h0 | h1 | h1
        · exact absurd h0 hi
        · exact absurd h1 (fun hh => hpos ⟨i, hh⟩)
        · exact h1
      have hzj : z j = -1 := by
        rcases ggQ2xN_ztri (z j) with h0 | h1 | h1
        · exact absurd h0 hj
        · exact absurd h1 (fun hh => hpos ⟨j, hh⟩)
        · exact h1
      refine ⟨ggQ2xN_flip j (ggQ2xN_flip i z), ?_, ?_, ?_⟩
      · exact ggQ2xN_flip_mem Z hZroots hZcl (ggQ2xN_flip_mem Z hZroots hZcl hz i) j
      · rw [ggQ2xN_flip_sum, ggQ2xN_flip_apply_of_ne i j (Ne.symm hij), ggQ2xN_flip_sum,
          hs, hzi, hzj]
        decide
      · rw [ggQ2xN_flip_wt, ggQ2xN_flip_wt]

theorem ggQ2_bc_Z_aN (n : ℕ) (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, ∑ i, z i = 0 → ∀ ρ ∈ ggBCRootsLamN n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggBCRootsLamN n) :
    Z ⊆ ggBCRoots n := by
  intro z hz
  rw [ggBCRoots]
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have h0 : ggBCWt z = 0 := by omega
    have hz0 : z = 0 := (ggQ2xN_wt_eq_zero_iff z).mp h0
    exact hZ0 z hz (by rw [hz0]; simp)
  · by_contra h
    push Not at h
    have hw : 3 ≤ ggBCWt z := by omega
    obtain ⟨z', hz'Z, hsum', hwt'⟩ := ggQ2xN_partB Z hZroots hZcl z hz hw
    have hle := ggQ2xN_partA hn Z hZ0 hHL z' hz'Z hsum'
    omega

end CFSG.StandardType

end


