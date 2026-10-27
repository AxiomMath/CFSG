module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin


private def ggQ2xD1_flipS {n : ℕ} (S : Finset (Fin n)) (v : GGBCV n) : GGBCV n :=
  fun k => if k ∈ S then -v k else v k

private lemma ggQ2xD1_flipS_empty {n : ℕ} (v : GGBCV n) : ggQ2xD1_flipS ∅ v = v := by
  funext k; simp [ggQ2xD1_flipS]

private def ggQ2xD1_dist {n : ℕ} (a b : GGBCV n) : ℕ :=
  (Finset.univ.filter (fun k => ¬ a k = b k)).card

private lemma ggQ2xD1_eq_one_or_neg_one : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide

private lemma ggQ2xD1_prod_full {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b = if a = b then 1 else -1 := by
  rcases ggQ2xD1_eq_one_or_neg_one a ha with h | h <;>
    rcases ggQ2xD1_eq_one_or_neg_one b hb with h' | h' <;> rw [h, h'] <;> decide

private lemma ggQ2xD1_dot_full {n : ℕ} {a b : GGBCV n}
    (ha : ∀ k, a k ≠ 0) (hb : ∀ k, b k ≠ 0) :
    a ⬝ᵥ b = (n : ZMod 3) - 2 * (ggQ2xD1_dist a b : ZMod 3) := by
  rw [dotProduct]
  trans ∑ k, (if a k = b k then (1 : ZMod 3) else -1)
  · exact Finset.sum_congr rfl (fun k _ => ggQ2xD1_prod_full (ha k) (hb k))
  rw [Finset.sum_ite]
  have h1 : (∑ x ∈ Finset.univ.filter (fun k => a k = b k), (1 : ZMod 3))
      = ((Finset.univ.filter (fun k => a k = b k)).card : ZMod 3) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ x ∈ Finset.univ.filter (fun k => ¬ a k = b k), (-1 : ZMod 3))
      = -((Finset.univ.filter (fun k => ¬ a k = b k)).card : ZMod 3) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_neg_one _
  unfold ggQ2xD1_dist
  have hcard : (Finset.univ.filter (fun k => a k = b k)).card +
      (Finset.univ.filter (fun k => ¬ a k = b k)).card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hcast := congrArg (fun m : ℕ => (m : ZMod 3)) hcard
  push_cast at hcast
  rw [h1, h2, ← hcast]
  ring_nf
  exact (sub_eq_add_neg _ _).symm





private lemma ggQ2xD1_scalar_a (x y : ZMod 3) : y + (x + y) * 2 = -x := by
  revert x y; decide
private lemma ggQ2xD1_scalar_b (x y : ZMod 3) : x + (x + y) * 2 = -y := by
  revert x y; decide

private lemma ggQ2xD1_flipS_pair_apply {n : ℕ} (a b k : Fin n) (hab : a ≠ b) (v : GGBCV n) :
    ggQ2xD1_flipS ({a, b} : Finset (Fin n)) v k
      = if k = a then -v a else if k = b then -v b else v k := by
  simp only [ggQ2xD1_flipS, Finset.mem_insert, Finset.mem_singleton]
  by_cases hka : k = a
  · subst hka; simp
  · by_cases hkb : k = b
    · subst hkb; simp [hka]
    · simp [hka, hkb]

private lemma ggQ2xD1_mem_pair {n : ℕ} {Z : Set (GGBCV n)}
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {v : GGBCV n} (hv : v ∈ Z) {a b : Fin n} (hab : a ≠ b) :
    ggQ2xD1_flipS {a, b} v ∈ Z := by
  have hc1 : (Pi.single a 1 - Pi.single b 1 : GGBCV n) ⬝ᵥ
      (Pi.single a 1 - Pi.single b 1) = 2 := ggQ2x_sub_single_norm a b hab
  have hc1ne : (Pi.single a 1 - Pi.single b 1 : GGBCV n) ⬝ᵥ
      (Pi.single a 1 - Pi.single b 1) ≠ 0 := by rw [hc1]; decide
  have hroot1 : (Pi.single a 1 - Pi.single b 1 : GGBCV n) ∈ ggDRoots n := by
    rw [ggDRoots]; exact ggQ2x_wt_sub_single a b hab
  have hc2 : (Pi.single a 1 + Pi.single b 1 : GGBCV n) ⬝ᵥ
      (Pi.single a 1 + Pi.single b 1) = 2 := by
    rw [ggQ2x_dot_self_eq_wt,
      ggQ2x_wt_single_add_single a b hab 1 1 one_ne_zero one_ne_zero]
    decide
  have hc2ne : (Pi.single a 1 + Pi.single b 1 : GGBCV n) ⬝ᵥ
      (Pi.single a 1 + Pi.single b 1) ≠ 0 := by rw [hc2]; decide
  have hroot2 : (Pi.single a 1 + Pi.single b 1 : GGBCV n) ∈ ggDRoots n := by
    rw [ggDRoots]
    exact ggQ2x_wt_single_add_single a b hab 1 1 one_ne_zero one_ne_zero
  have h1mem : ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v ∈ Z :=
    hZcl _ (hZroots hroot1) v hv hc1ne
  have h1eq : ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v =
      fun k => v (Equiv.swap a b k) := ggQ2x_refl_sub_single a b hab v hc1ne
  have h2mem : ggBCRefl (Pi.single a 1 + Pi.single b 1) hc2ne
      (ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v) ∈ Z :=
    hZcl _ (hZroots hroot2) _ h1mem hc2ne
  have hcomp : ggBCRefl (Pi.single a 1 + Pi.single b 1) hc2ne
      (ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v)
      = ggQ2xD1_flipS {a, b} v := by
    rw [h1eq]
    have hD : (Pi.single a 1 + Pi.single b 1 : GGBCV n) ⬝ᵥ
        (fun k => v (Equiv.swap a b k)) = v a + v b := by
      rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    funext k
    rw [ggQ2x_ggBCRefl_apply, hD, hc2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hka : k = a
    · rw [hka, ggQ2xD1_flipS_pair_apply a b a hab v, if_pos rfl, Equiv.swap_apply_left]
      simp only [Pi.add_apply, Pi.single_apply]
      rw [if_pos trivial, if_neg hab, add_zero, mul_one]
      exact ggQ2xD1_scalar_a (v a) (v b)
    · rw [ggQ2xD1_flipS_pair_apply a b k hab v, if_neg hka]
      by_cases hkb : k = b
      · rw [hkb, if_pos rfl, Equiv.swap_apply_right]
        simp only [Pi.add_apply, Pi.single_apply]
        rw [if_neg (Ne.symm hab), if_pos trivial, zero_add, mul_one]
        exact ggQ2xD1_scalar_b (v a) (v b)
      · rw [if_neg hkb, Equiv.swap_apply_of_ne_of_ne hka hkb]
        simp only [Pi.add_apply, Pi.single_apply]
        rw [if_neg hkb, if_neg hka, add_zero, mul_zero, add_zero]
  rw [hcomp] at h2mem
  exact h2mem




private lemma ggQ2xD1_flipS_union {n : ℕ} (S T : Finset (Fin n)) (h : Disjoint S T)
    (v : GGBCV n) :
    ggQ2xD1_flipS (S ∪ T) v = ggQ2xD1_flipS S (ggQ2xD1_flipS T v) := by
  funext k
  rw [ggQ2xD1_flipS, ggQ2xD1_flipS, ggQ2xD1_flipS]
  by_cases hkS : k ∈ S
  · have hkT : k ∉ T := fun hkT => (Finset.disjoint_left.mp h) hkS hkT
    simp [Finset.mem_union, hkS, hkT]
  · by_cases hkT : k ∈ T
    · simp [Finset.mem_union, hkS, hkT]
    · simp [Finset.mem_union, hkS, hkT]

private lemma ggQ2xD1_mem_flipS {n : ℕ} {Z : Set (GGBCV n)}
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    ∀ (S : Finset (Fin n)), Even S.card → ∀ {v : GGBCV n}, v ∈ Z →
      ggQ2xD1_flipS S v ∈ Z := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS v hv
    by_cases h0 : S.card = 0
    · rw [Finset.card_eq_zero.mp h0, ggQ2xD1_flipS_empty]
      exact hv
    · have h2 : 1 < S.card := by
        obtain ⟨k, hk⟩ := hS
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
      have hbU : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
      have haU : a ∉ (S.erase a).erase b := by
        rw [Finset.mem_erase]
        push Not
        intro _; exact Finset.notMem_erase a S
      have hbU2 : b ∉ (S.erase a).erase b := Finset.notMem_erase b (S.erase a)
      have hUsub : (S.erase a).erase b ⊂ S :=
        (Finset.erase_ssubset hbU).trans (Finset.erase_ssubset ha)
      have hUeven : Even ((S.erase a).erase b).card := by
        have h1 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
        have h2' : ((S.erase a).erase b).card = (S.erase a).card - 1 :=
          Finset.card_erase_of_mem hbU
        rw [h2', h1]
        obtain ⟨k, hk⟩ := hS
        refine ⟨k - 1, ?_⟩
        omega
      have hseq : insert a (insert b ((S.erase a).erase b)) = S := by
        rw [Finset.insert_erase hbU, Finset.insert_erase ha]
      rw [← hseq]
      have hdisj : Disjoint ({a, b} : Finset (Fin n)) ((S.erase a).erase b) := by
        rw [Finset.disjoint_left]
        intro x hx hxU
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haU hxU
        · exact hbU2 hxU
      have hins : insert a (insert b ((S.erase a).erase b)) =
          ({a, b} : Finset (Fin n)) ∪ ((S.erase a).erase b) := by
        ext x; simp [Finset.mem_union]
      rw [hins, ggQ2xD1_flipS_union _ _ hdisj]
      exact ggQ2xD1_mem_pair hZroots hZcl
        (ih ((S.erase a).erase b) hUsub hUeven hv) hab




private lemma ggQ2xD1_zero_coord_le_two {n : ℕ} [NeZero n] (hn : 6 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n)
    {z : GGBCV n} (hz : z ∈ Z) (hzero : ∃ m, z m = 0) : ggBCWt z ≤ 2 := by
  obtain ⟨m, hm⟩ := hzero
  set z' : GGBCV n := fun k => z (Equiv.swap 0 m k) with hz'def
  have hz'Z : z' ∈ Z := by
    by_cases hm0 : m = 0
    · subst hm0
      simpa [hz'def] using hz
    · have h0m : (0 : Fin n) ≠ m := fun h => hm0 h.symm
      have hc : (Pi.single 0 1 - Pi.single m 1 : GGBCV n) ⬝ᵥ
          (Pi.single 0 1 - Pi.single m 1) ≠ 0 := by
        rw [ggQ2x_sub_single_norm 0 m h0m]; decide
      have hroot : (Pi.single 0 1 - Pi.single m 1 : GGBCV n) ∈ ggDRoots n := by
        rw [ggDRoots]; exact ggQ2x_wt_sub_single 0 m h0m
      have hmem := hZcl _ (hZroots hroot) z hz hc
      rwa [ggQ2x_refl_sub_single 0 m h0m z hc] at hmem
  have hz'0 : z' 0 = 0 := by
    rw [hz'def]; simp only [Equiv.swap_apply_left]; exact hm
  have hz'wt : ggBCWt z' = ggBCWt z := by
    rw [hz'def]
    by_cases hm0 : m = 0
    · subst hm0; simp
    · exact ggQ2x_wt_comp_swap 0 m z
  rw [← hz'wt]
  by_contra hle
  push Not at hle
  have hdot : z' ⬝ᵥ z' ≠ 0 := hZ0 z' hz'Z
  have hne3 : ggBCWt z' ≠ 3 := by
    intro h3
    exact hdot (by rw [ggQ2x_dot_self_eq_wt, h3]; decide)
  set S : Finset (Fin n) := Finset.univ.filter (fun k => z' k ≠ 0) with hSdef
  have hScard : S.card = ggBCWt z' := by rw [hSdef]; rfl
  by_cases hw5 : 5 ≤ ggBCWt z'
  · have hsupp : 1 < S.card := by rw [hScard]; omega
    obtain ⟨i, hiS, j, hjS, hij⟩ := Finset.one_lt_card.mp hsupp
    have hzi : z' i ≠ 0 := (Finset.mem_filter.mp hiS).2
    have hzj : z' j ≠ 0 := (Finset.mem_filter.mp hjS).2
    have hi0 : i ≠ 0 := fun h => hzi (by rw [h, hz'0])
    have hj0 : j ≠ 0 := fun h => hzj (by rw [h, hz'0])
    let ρ : GGBCV n := z' i • (Pi.single i 1 : GGBCV n) + z' j • (Pi.single j 1 : GGBCV n)
    have hρwt : ggBCWt ρ = 2 :=
      ggQ2x_wt_smul_single_add_single i j hij (z' i) (z' j) hzi hzj
    have hρ0 : ρ 0 = 0 := by
      change (z' i • (Pi.single i 1 : GGBCV n) + z' j • (Pi.single j 1 : GGBCV n)) 0 = 0
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_of_ne (Ne.symm hi0), Pi.single_eq_of_ne (Ne.symm hj0)]
      simp
    have hρlam : ρ ∈ ggDRootsLam1 n := ⟨hρwt, hρ0⟩
    have hzρ : z' ⬝ᵥ ρ = 2 := by
      change z' ⬝ᵥ (z' i • (Pi.single i 1 : GGBCV n) +
        z' j • (Pi.single j 1 : GGBCV n)) = 2
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_single_one,
        dotProduct_single_one, smul_eq_mul, smul_eq_mul,
        ggQ2x_mul_self_eq_one (z' i) hzi, ggQ2x_mul_self_eq_one (z' j) hzj]
      decide
    have hres := hHL z' hz'Z hz'0 ρ hρlam hdot
    have hsub : (S.erase i).erase j ⊆
        Finset.univ.filter (fun k => (ggBCRefl z' hdot ρ) k ≠ 0) := by
      intro k hk
      rw [Finset.mem_filter]
      rw [Finset.mem_erase, Finset.mem_erase] at hk
      obtain ⟨hkj, hki, hkS⟩ := hk
      have hzk : z' k ≠ 0 := (Finset.mem_filter.mp hkS).2
      refine ⟨Finset.mem_univ k, ?_⟩
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hρk : ρ k = 0 := by
        change (z' i • (Pi.single i 1 : GGBCV n) + z' j • (Pi.single j 1 : GGBCV n)) k = 0
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
        simp
      rw [hρk, zero_add]
      exact mul_ne_zero (mul_ne_zero (by rw [hzρ]; decide) hdot) hzk
    have hcard : ((S.erase i).erase j).card = ggBCWt z' - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hjS⟩),
        Finset.card_erase_of_mem hiS, hScard]
      omega
    have hle2 : ggBCWt z' - 2 ≤ ggBCWt (ggBCRefl z' hdot ρ) := by
      rw [← hcard]
      exact Finset.card_le_card hsub
    have hre := hres.1
    omega
  · have hw4 : ggBCWt z' = 4 := by omega
    have hScard4 : S.card = 4 := by rw [hScard, hw4]
    obtain ⟨i, hiS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hzi : z' i ≠ 0 := (Finset.mem_filter.mp hiS).2
    have hi0 : i ≠ 0 := fun h => hzi (by rw [h, hz'0])
    have hm : ∃ m : Fin n, m ∉ insert (0 : Fin n) S := by
      obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := insert (0 : Fin n) S) (t := Finset.univ) (by
          rw [Finset.card_univ, Fintype.card_fin]
          have hins := Finset.card_insert_le (0 : Fin n) S
          omega)
      exact ⟨m, hm⟩
    obtain ⟨m, hm⟩ := hm
    have hmS : m ∉ S := fun h => hm (Finset.mem_insert_of_mem h)
    have hm0 : m ≠ 0 := fun h => hm (h ▸ Finset.mem_insert_self (0 : Fin n) S)
    have hzm : z' m = 0 := by
      by_contra h
      exact hmS (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ m, h⟩)
    have him : i ≠ m := fun h => hmS (h ▸ hiS)
    have hmi : m ≠ i := fun h => hmS (h ▸ hiS)
    let ρ : GGBCV n := z' i • (Pi.single i 1 : GGBCV n) +
      (1 : ZMod 3) • (Pi.single m 1 : GGBCV n)
    have hρwt : ggBCWt ρ = 2 :=
      ggQ2x_wt_smul_single_add_single i m him (z' i) 1 hzi one_ne_zero
    have hρ0 : ρ 0 = 0 := by
      change (z' i • (Pi.single i 1 : GGBCV n) +
        (1 : ZMod 3) • (Pi.single m 1 : GGBCV n)) 0 = 0
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_of_ne (Ne.symm hi0), Pi.single_eq_of_ne (Ne.symm hm0)]
      simp
    have hρlam : ρ ∈ ggDRootsLam1 n := ⟨hρwt, hρ0⟩
    have hzρ : z' ⬝ᵥ ρ = 1 := by
      change z' ⬝ᵥ (z' i • (Pi.single i 1 : GGBCV n) +
        (1 : ZMod 3) • (Pi.single m 1 : GGBCV n)) = 1
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_single_one,
        dotProduct_single_one, smul_eq_mul, smul_eq_mul, hzm,
        ggQ2x_mul_self_eq_one (z' i) hzi]
      decide
    have hres := hHL z' hz'Z hz'0 ρ hρlam hdot
    have hsub : (S.erase i) ∪ {m} ⊆
        Finset.univ.filter (fun k => (ggBCRefl z' hdot ρ) k ≠ 0) := by
      intro k hk
      rw [Finset.mem_filter]
      rw [Finset.mem_union] at hk
      refine ⟨Finset.mem_univ k, ?_⟩
      rcases hk with hk | hk
      · rw [Finset.mem_erase] at hk
        obtain ⟨hki, hkS⟩ := hk
        have hzk : z' k ≠ 0 := (Finset.mem_filter.mp hkS).2
        have hkm : k ≠ m := fun h => hmS (h ▸ hkS)
        rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hρk : ρ k = 0 := by
          change (z' i • (Pi.single i 1 : GGBCV n) +
            (1 : ZMod 3) • (Pi.single m 1 : GGBCV n)) k = 0
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
            Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkm]
          simp
        rw [hρk, zero_add]
        exact mul_ne_zero (mul_ne_zero (by rw [hzρ]; decide) hdot) hzk
      · rw [Finset.mem_singleton] at hk
        rw [hk]
        rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hρm : ρ m = 1 := by
          change (z' i • (Pi.single i 1 : GGBCV n) +
            (1 : ZMod 3) • (Pi.single m 1 : GGBCV n)) m = 1
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
            Pi.single_eq_of_ne hmi, Pi.single_eq_same]
          simp
        rw [hρm, hzρ, hzm, mul_zero, add_zero]
        exact one_ne_zero
    have hcard : ((S.erase i) ∪ {m}).card = ggBCWt z' := by
      have hmiS : m ∉ S.erase i := fun h => hmS (Finset.mem_of_mem_erase h)
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hmiS),
        Finset.card_singleton, Finset.card_erase_of_mem hiS, hScard]
      omega
    have hle4 : ggBCWt z' ≤ ggBCWt (ggBCRefl z' hdot ρ) := by
      rw [← hcard]
      exact Finset.card_le_card hsub
    have hre := hres.1
    omega




private lemma ggQ2xD1_ne_neg_self : ∀ x : ZMod 3, x ≠ 0 → x ≠ -x := by decide

private lemma ggQ2xD1_flipS_full {n : ℕ} (S : Finset (Fin n)) {v : GGBCV n}
    (hv : ∀ k, v k ≠ 0) : ∀ k, ggQ2xD1_flipS S v k ≠ 0 := by
  intro k
  rw [ggQ2xD1_flipS]
  by_cases hk : k ∈ S
  · rw [if_pos hk]; exact neg_ne_zero.mpr (hv k)
  · rw [if_neg hk]; exact hv k

private lemma ggQ2xD1_dist_flipS_self {n : ℕ} (S : Finset (Fin n)) {v : GGBCV n}
    (hv : ∀ k, v k ≠ 0) : ggQ2xD1_dist v (ggQ2xD1_flipS S v) = S.card := by
  unfold ggQ2xD1_dist
  change (Finset.univ.filter
    (fun k => ¬ v k = (if k ∈ S then -v k else v k))).card = S.card
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
    exact ⟨fun _ => hk, fun _ => ggQ2xD1_ne_neg_self (v k) (hv k)⟩
  · rw [if_neg hk]
    exact ⟨fun h => absurd rfl h, fun h => absurd h hk⟩




private lemma ggQ2xD1_flipS_of_notMem {n : ℕ} (S : Finset (Fin n)) (v : GGBCV n) {k : Fin n}
    (hk : k ∉ S) : ggQ2xD1_flipS S v k = v k := by
  rw [ggQ2xD1_flipS, if_neg hk]

private lemma ggQ2xD1_flipS_of_mem {n : ℕ} (S : Finset (Fin n)) (v : GGBCV n) {k : Fin n}
    (hk : k ∈ S) : ggQ2xD1_flipS S v k = -v k := by
  rw [ggQ2xD1_flipS, if_pos hk]

private lemma ggQ2xD1_two_add_self_ne_zero : ∀ x : ZMod 3, x ≠ 0 → x + x ≠ 0 := by decide
private lemma ggQ2xD1_neg_add_self : ∀ x : ZMod 3, -x + x = 0 := by decide

private lemma ggQ2xD1_full_nmod1_false {n : ℕ} [NeZero n] (hn : 6 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n)
    {z : GGBCV n} (hz : z ∈ Z) (hfull : ∀ i, z i ≠ 0) (hmod : (n : ZMod 3) = 1) : False := by
  have hstep1 : ∀ z ∈ Z, (∃ m, z m = 0) → ggBCWt z ≤ 2 :=
    fun z hz hzero => ggQ2xD1_zero_coord_le_two hn Z hZ0 hZroots hZcl hHL hz hzero
  have hcard : 1 < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨i, -, j, -, hij⟩ := Finset.one_lt_card.mp hcard
  have hzi : z i ≠ 0 := hfull i
  have hzj : z j ≠ 0 := hfull j
  let ρ : GGBCV n := z i • (Pi.single i 1 : GGBCV n) + z j • (Pi.single j 1 : GGBCV n)
  have hρwt : ggBCWt ρ = 2 := ggQ2x_wt_smul_single_add_single i j hij (z i) (z j) hzi hzj
  have hρZ : ρ ∈ Z := hZroots (by rw [ggDRoots]; exact hρwt)
  have hzZ : ggBCRefl z (hZ0 z hz) ρ ∈ Z := hZcl z hz ρ hρZ (hZ0 z hz)
  have hwt : ggBCWt z = n := ggQ2x_wt_eq_of_full hfull
  have hzz : z ⬝ᵥ z = 1 := by rw [ggQ2x_dot_self_eq_wt, hwt, hmod]
  have hzρ : z ⬝ᵥ ρ = 2 := by
    change z ⬝ᵥ (z i • (Pi.single i 1 : GGBCV n) +
      z j • (Pi.single j 1 : GGBCV n)) = 2
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_single_one,
      dotProduct_single_one, smul_eq_mul, smul_eq_mul,
      ggQ2x_mul_self_eq_one (z i) hzi, ggQ2x_mul_self_eq_one (z j) hzj]
    decide
  have hval : ∀ k, (ggBCRefl z (hZ0 z hz) ρ) k = ρ k + 2 * z k := by
    intro k
    rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzρ, hzz]
    norm_num
  have hzero : ∃ k, (ggBCRefl z (hZ0 z hz) ρ) k = 0 := by
    refine ⟨i, ?_⟩
    rw [hval i]
    have hρi : ρ i = z i := by
      change (z i • (Pi.single i 1 : GGBCV n) + z j • (Pi.single j 1 : GGBCV n)) i = z i
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne hij]
      simp
    rw [hρi]
    exact (by decide : ∀ x : ZMod 3, x + 2 * x = 0) (z i)
  have hsub : (Finset.univ.erase i).erase j ⊆
      Finset.univ.filter (fun k => (ggBCRefl z (hZ0 z hz) ρ) k ≠ 0) := by
    intro k hk
    rw [Finset.mem_filter]
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hkj, hki, -⟩ := hk
    refine ⟨Finset.mem_univ k, ?_⟩
    rw [hval k]
    have hρk : ρ k = 0 := by
      change (z i • (Pi.single i 1 : GGBCV n) + z j • (Pi.single j 1 : GGBCV n)) k = 0
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
      simp
    rw [hρk, zero_add]
    exact mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hfull k)
  have hcard2 : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hge : n - 2 ≤ ggBCWt (ggBCRefl z (hZ0 z hz) ρ) := by
    rw [← hcard2]
    exact Finset.card_le_card hsub
  have hle := hstep1 _ hzZ hzero
  omega




private lemma ggQ2xD1_full_nmod2_le_eight {n : ℕ} [NeZero n] (hn : 6 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n)
    {z : GGBCV n} (hz : z ∈ Z) (hfull : ∀ i, z i ≠ 0) (hmod : (n : ZMod 3) = 2) :
    n ≤ 8 := by
  have hstep1 : ∀ z ∈ Z, (∃ m, z m = 0) → ggBCWt z ≤ 2 :=
    fun z hz hzero => ggQ2xD1_zero_coord_le_two hn Z hZ0 hZroots hZcl hHL hz hzero
  have hmem := ggQ2xD1_mem_flipS (Z := Z) hZroots hZcl
  obtain ⟨T, -, hTcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := 6) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hTeven : Even T.card := by rw [hTcard]; norm_num
  set z' : GGBCV n := ggQ2xD1_flipS T z with hz'def
  have hz'Z : z' ∈ Z := by rw [hz'def]; exact hmem T hTeven hz
  have hz'full : ∀ k, z' k ≠ 0 := by
    intro k; rw [hz'def]; exact ggQ2xD1_flipS_full T hfull k
  have hdist : ggQ2xD1_dist z z' = 6 := by
    rw [hz'def, ggQ2xD1_dist_flipS_self T hfull, hTcard]
  have hwt : ggBCWt z = n := ggQ2x_wt_eq_of_full hfull
  have hzz : z ⬝ᵥ z = 2 := by rw [ggQ2x_dot_self_eq_wt, hwt, hmod]
  have hzz' : z ⬝ᵥ z' = 2 := by
    rw [ggQ2xD1_dot_full hfull hz'full, hdist, hmod]
    decide
  set w : GGBCV n := ggBCRefl z (hZ0 z hz) z' with hwdef
  have hwZ : w ∈ Z := hZcl z hz z' hz'Z (hZ0 z hz)
  have hlam : (z ⬝ᵥ z') * (z ⬝ᵥ z) = 1 := by rw [hzz', hzz]; decide
  have hw_eq : w = z' + z := by
    funext k
    change (ggBCRefl z (hZ0 z hz) z') k = (z' + z) k
    rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlam]
    simp
  have hzero : ∃ k, w k = 0 := by
    obtain ⟨k0, hk0⟩ := Finset.card_pos.mp (by rw [hTcard]; norm_num : 0 < T.card)
    refine ⟨k0, ?_⟩
    rw [hw_eq, Pi.add_apply, hz'def, ggQ2xD1_flipS_of_mem T z hk0]
    exact ggQ2xD1_neg_add_self (z k0)
  have hcompl : Finset.univ \ T ⊆ Finset.univ.filter (fun k => w k ≠ 0) := by
    intro k hk
    rw [Finset.mem_filter]
    rw [Finset.mem_sdiff] at hk
    obtain ⟨-, hkT⟩ := hk
    refine ⟨Finset.mem_univ k, ?_⟩
    rw [hw_eq, Pi.add_apply, hz'def, ggQ2xD1_flipS_of_notMem T z hkT]
    exact ggQ2xD1_two_add_self_ne_zero (z k) (hfull k)
  have hcard_compl : (Finset.univ \ T).card = n - 6 := by
    rw [Finset.card_univ_diff, Fintype.card_fin, hTcard]
  have hge : n - 6 ≤ ggBCWt w := by
    rw [← hcard_compl]
    exact Finset.card_le_card hcompl
  have hle := hstep1 w hwZ hzero
  omega




private lemma ggQ2xD1_eq_neg_of_ne : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → x ≠ y → y = -x := by decide

private lemma ggQ2xD1_sum_parity {n : ℕ} {a b : GGBCV n}
    (ha : ∀ k, a k ≠ 0) (hb : ∀ k, b k ≠ 0) :
    (((Finset.univ.filter (fun k => a k = -1)).card +
      (Finset.univ.filter (fun k => b k = -1)).card : ℕ) : ZMod 2) =
    ((ggQ2xD1_dist a b : ℕ) : ZMod 2) := by
  rw [Nat.cast_add]
  rw [Finset.natCast_card_filter (fun k => a k = -1),
    Finset.natCast_card_filter (fun k => b k = -1)]
  unfold ggQ2xD1_dist
  rw [Finset.natCast_card_filter (fun k => ¬ a k = b k)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rcases ggQ2xD1_eq_one_or_neg_one (a k) (ha k) with h | h <;>
    rcases ggQ2xD1_eq_one_or_neg_one (b k) (hb k) with h' | h' <;>
    rw [h, h'] <;> decide

private lemma ggQ2xD1_even_dist {n : ℕ} {a b : GGBCV n}
    (ha : ∀ k, a k ≠ 0) (hb : ∀ k, b k ≠ 0)
    (h : Even (Finset.univ.filter (fun k => a k = -1)).card ↔
      Even (Finset.univ.filter (fun k => b k = -1)).card) :
    Even (ggQ2xD1_dist a b) := by
  have hsum := ggQ2xD1_sum_parity ha hb
  have heven : Even ((Finset.univ.filter (fun k => a k = -1)).card +
      (Finset.univ.filter (fun k => b k = -1)).card) := Nat.even_add.mpr h
  have h0 : (((Finset.univ.filter (fun k => a k = -1)).card +
      (Finset.univ.filter (fun k => b k = -1)).card : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr heven
  rw [hsum] at h0
  exact ZMod.natCast_eq_zero_iff_even.mp h0

private lemma ggQ2xD1_flipS_diff {n : ℕ} {a b : GGBCV n}
    (ha : ∀ k, a k ≠ 0) (hb : ∀ k, b k ≠ 0) :
    ggQ2xD1_flipS (Finset.univ.filter (fun k => ¬ a k = b k)) a = b := by
  funext k
  rw [ggQ2xD1_flipS]
  by_cases hk : k ∈ Finset.univ.filter (fun k => ¬ a k = b k)
  · rw [if_pos hk]
    have hk' : ¬ a k = b k := (Finset.mem_filter.mp hk).2
    exact (ggQ2xD1_eq_neg_of_ne (a k) (b k) (ha k) (hb k) hk').symm
  · rw [if_neg hk]
    by_contra hne
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩)

private lemma ggQ2xD1_dist3_false {n : ℕ} [NeZero n] (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n)
    (heq : n = 8) {a b : GGBCV n} (ha : a ∈ Z) (hb : b ∈ Z)
    (hafull : ∀ k, a k ≠ 0) (hbfull : ∀ k, b k ≠ 0)
    (hdist : ggQ2xD1_dist a b = 3) : False := by
  have hstep1 : ∀ z ∈ Z, (∃ m, z m = 0) → ggBCWt z ≤ 2 :=
    fun z hz hzero => ggQ2xD1_zero_coord_le_two (by omega) Z hZ0 hZroots hZcl hHL hz hzero
  have hzz : a ⬝ᵥ a = 2 := by
    rw [ggQ2x_dot_self_eq_wt, ggQ2x_wt_eq_of_full hafull, heq]; decide
  have hab : a ⬝ᵥ b = 2 := by
    rw [ggQ2xD1_dot_full hafull hbfull, hdist, heq]; norm_num
  have hlam : (a ⬝ᵥ b) * (a ⬝ᵥ a) = 1 := by rw [hab, hzz]; decide
  have hw_eq : ggBCRefl a (hZ0 a ha) b = b + a := by
    funext k
    rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlam]; simp
  have hwZ : ggBCRefl a (hZ0 a ha) b ∈ Z := hZcl a ha b hb (hZ0 a ha)
  have hDcard : (Finset.univ.filter (fun k => ¬ a k = b k)).card = 3 := hdist
  have hDne : (Finset.univ.filter (fun k => ¬ a k = b k)).Nonempty :=
    Finset.card_pos.mp (by rw [hDcard]; norm_num)
  obtain ⟨k0, hk0⟩ := hDne
  have hzero : ∃ k, (ggBCRefl a (hZ0 a ha) b) k = 0 := by
    refine ⟨k0, ?_⟩
    have hk0' : ¬ a k0 = b k0 := (Finset.mem_filter.mp hk0).2
    have hb0 : b k0 = -a k0 := ggQ2xD1_eq_neg_of_ne (a k0) (b k0) (hafull k0) (hbfull k0) hk0'
    rw [hw_eq, Pi.add_apply, hb0]
    exact ggQ2xD1_neg_add_self (a k0)
  have hsub : (Finset.univ \ Finset.univ.filter (fun k => ¬ a k = b k)) ⊆
      Finset.univ.filter (fun k => (ggBCRefl a (hZ0 a ha) b) k ≠ 0) := by
    intro k hk
    rw [Finset.mem_filter]
    rw [Finset.mem_sdiff] at hk
    obtain ⟨-, hkD⟩ := hk
    have hkab : a k = b k := by
      by_contra h
      exact hkD (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
    refine ⟨Finset.mem_univ k, ?_⟩
    rw [hw_eq, Pi.add_apply, hkab]
    exact ggQ2xD1_two_add_self_ne_zero (b k) (hbfull k)
  have hcard_compl : (Finset.univ \ Finset.univ.filter (fun k => ¬ a k = b k)).card = n - 3 := by
    rw [Finset.card_univ_diff, Fintype.card_fin, hDcard]
  have hge : 3 ≤ ggBCWt (ggBCRefl a (hZ0 a ha) b) := by
    have h1 : n - 3 ≤ (Finset.univ.filter
        (fun k => (ggBCRefl a (hZ0 a ha) b) k ≠ 0)).card := by
      rw [← hcard_compl]; exact Finset.card_le_card hsub
    change 3 ≤ (Finset.univ.filter
      (fun k => (ggBCRefl a (hZ0 a ha) b) k ≠ 0)).card
    omega
  have hle := hstep1 _ hwZ hzero
  omega




private lemma ggQ2xD1_full_parity {n : ℕ} [NeZero n] (hn : 6 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n)
    {z w : GGBCV n} (hz : z ∈ Z) (hw : w ∈ Z)
    (hzfull : ∀ k, z k ≠ 0) (hwfull : ∀ k, w k ≠ 0) (heq : n = 8) :
    Even (Finset.univ.filter (fun k => z k = -1)).card ↔
      Even (Finset.univ.filter (fun k => w k = -1)).card := by
  by_contra hne
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := 3) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  let c : GGBCV n := ggQ2xD1_flipS S z
  have hcfull : ∀ k, c k ≠ 0 := ggQ2xD1_flipS_full S hzfull
  have hdist_zc : ggQ2xD1_dist z c = 3 := by
    change ggQ2xD1_dist z (ggQ2xD1_flipS S z) = 3
    rw [ggQ2xD1_dist_flipS_self S hzfull, hScard]
  have hpar_zc : ¬ (Even (Finset.univ.filter (fun k => z k = -1)).card ↔
      Even (Finset.univ.filter (fun k => c k = -1)).card) := by
    intro hiff
    have hsum := ggQ2xD1_sum_parity hzfull hcfull
    have heven : Even ((Finset.univ.filter (fun k => z k = -1)).card +
        (Finset.univ.filter (fun k => c k = -1)).card) := Nat.even_add.mpr hiff
    have h0 : (((Finset.univ.filter (fun k => z k = -1)).card +
        (Finset.univ.filter (fun k => c k = -1)).card : ℕ) : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr heven
    rw [hsum, hdist_zc] at h0
    exact (by decide : ((3 : ℕ) : ZMod 2) ≠ 0) h0
  have hpar_cw : Even (Finset.univ.filter (fun k => c k = -1)).card ↔
      Even (Finset.univ.filter (fun k => w k = -1)).card := by
    tauto
  have hTw_even : Even (ggQ2xD1_dist w c) := ggQ2xD1_even_dist hwfull hcfull hpar_cw.symm
  have hcZ : c ∈ Z := by
    rw [← ggQ2xD1_flipS_diff hwfull hcfull]
    exact ggQ2xD1_mem_flipS (Z := Z) hZroots hZcl _ hTw_even hw
  exact ggQ2xD1_dist3_false Z hZ0 hZroots hZcl hHL heq hz hcZ hzfull hcfull hdist_zc




private lemma ggQ2xD1_zmod3_trichotomy : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide

private lemma ggQ2xD1_full_of_wt_eq {n : ℕ} {v : GGBCV n} (h : ggBCWt v = n) :
    ∀ i, v i ≠ 0 := by
  intro i
  have hsub : (Finset.univ.filter (fun k => v k ≠ 0)) ⊆ (Finset.univ : Finset (Fin n)) :=
    Finset.filter_subset _ _
  have hcard : (Finset.univ.filter (fun k => v k ≠ 0)).card =
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; exact h
  have heq : Finset.univ.filter (fun k => v k ≠ 0) = Finset.univ :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [heq]; exact Finset.mem_univ i
  exact (Finset.mem_filter.mp this).2

private lemma ggQ2xD1_full_force_eight {n : ℕ} [NeZero n] (hn : 6 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n)
    {z : GGBCV n} (hz : z ∈ Z) (hfull : ∀ i, z i ≠ 0) : n = 8 := by
  have hwt : ggBCWt z = n := ggQ2x_wt_eq_of_full hfull
  have hmod_ne : (n : ZMod 3) ≠ 0 := by
    intro h0
    exact hZ0 z hz (by rw [ggQ2x_dot_self_eq_wt, hwt, h0])
  rcases ggQ2xD1_zmod3_trichotomy (n : ZMod 3) with h0 | h1 | h2
  · exact absurd h0 hmod_ne
  · exact (ggQ2xD1_full_nmod1_false hn Z hZ0 hZroots hZcl hHL hz hfull h1).elim
  · have hle := ggQ2xD1_full_nmod2_le_eight hn Z hZ0 hZroots hZcl hHL hz hfull h2
    interval_cases n <;> revert h2 <;> decide

private lemma ggQ2xD2_ztri (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = -1 := by
  have hval := ZMod.val_lt a
  have ha : a = (a.val : ZMod 3) := (ZMod.natCast_zmod_val a).symm
  interval_cases a.val
  · left; rw [ha]; decide
  · right; left; rw [ha]; decide
  · right; right; rw [ha]; decide

private lemma ggQ2xD2_sum_single {n : ℕ} (i : Fin n) (a : ZMod 3) :
    ∑ j, (Pi.single i a : GGBCV n) j = a := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xD2_wt_eq_zero_iff {n : ℕ} (v : GGBCV n) : ggBCWt v = 0 ↔ v = 0 := by
  rw [ggBCWt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    exact not_not.mp (h (Finset.mem_univ i))
  · intro h i _
    rw [h]
    simp

private lemma ggQ2xD2_scalar_i : ∀ x y : ZMod 3, -x = y + (x + y) * 2 := by decide

private lemma ggQ2xD2_scalar_j : ∀ x y : ZMod 3, -y = x + (x + y) * 2 := by decide

private lemma ggQ2xD2_norm_add_single {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (Pi.single i (1 : ZMod 3) + Pi.single j 1 : GGBCV n) ⬝ᵥ
        (Pi.single i (1 : ZMod 3) + Pi.single j 1 : GGBCV n) = 2 := by
  rw [ggQ2x_dot_self_eq_wt,
    ggQ2x_wt_single_add_single i j hij 1 1 one_ne_zero one_ne_zero]
  norm_num

private lemma ggQ2xD2_dot_diff {n : ℕ} (z : GGBCV n) (i m : Fin n) :
    z ⬝ᵥ ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single m 1) = z i - z m := by
  rw [dotProduct_sub, dotProduct_single_one, dotProduct_single_one]

private lemma ggQ2xD2_sum_diff {n : ℕ} (i m : Fin n) (him : i ≠ m) :
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
  rw [Finset.sum_add_distrib, ggQ2xD2_sum_single, ggQ2xD2_sum_single]
  decide

private lemma ggQ2xD2_add_single_self {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (Pi.single i (1 : ZMod 3) + Pi.single j 1 : GGBCV n) i = 1 := by
  rw [Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, add_zero]

private lemma ggQ2xD2_add_single_other {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (Pi.single i (1 : ZMod 3) + Pi.single j 1 : GGBCV n) j = 1 := by
  rw [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), Pi.single_eq_same,
    zero_add]

private lemma ggQ2xD2_add_single_ne {n : ℕ} {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    (Pi.single i (1 : ZMod 3) + Pi.single j 1 : GGBCV n) k = 0 := by
  rw [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj, add_zero]

private def ggQ2xD2_negOn {n : ℕ} (S : Finset (Fin n)) (v : GGBCV n) : GGBCV n :=
  fun k => if k ∈ S then -v k else v k

private lemma ggQ2xD2_negOn_wt {n : ℕ} (S : Finset (Fin n)) (v : GGBCV n) :
    ggBCWt (ggQ2xD2_negOn S v) = ggBCWt v := by
  unfold ggBCWt
  congr 1
  apply Finset.filter_congr
  intro k _
  by_cases hk : k ∈ S
  · unfold ggQ2xD2_negOn
    rw [if_pos hk]
    exact neg_ne_zero
  · unfold ggQ2xD2_negOn
    rw [if_neg hk]

private lemma ggQ2xD2_negOn_sum {n : ℕ} (S : Finset (Fin n)) (v : GGBCV n) :
    (∑ k, ggQ2xD2_negOn S v k) = (∑ k, v k) + S.sum (fun k => v k) := by
  have hpt : ∀ k : Fin n,
      ggQ2xD2_negOn S v k = v k + (if k ∈ S then v k else 0) := by
    intro k
    by_cases hk : k ∈ S
    · simp only [ggQ2xD2_negOn, hk, ↓reduceIte]
      exact (by decide : ∀ x : ZMod 3, -x = x + x) (v k)
    · simp only [ggQ2xD2_negOn, hk, ↓reduceIte, add_zero]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter]

private lemma ggQ2xD2_negOn_pair_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : GGBCV n)
    (c d : GGBCV n) (hc : c = Pi.single i (1 : ZMod 3) + Pi.single j 1)
    (hd : d = Pi.single i (1 : ZMod 3) - Pi.single j 1)
    (h1 : c ⬝ᵥ c ≠ 0) (h2 : d ⬝ᵥ d ≠ 0) :
    ggQ2xD2_negOn ({i, j} : Finset (Fin n)) v = ggBCRefl d h2 (ggBCRefl c h1 v) := by
  subst hc
  subst hd
  funext k
  rw [ggQ2x_refl_sub_single i j hij _ h2]
  simp only [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_dotProduct, single_one_dotProduct, ggQ2xD2_norm_add_single i j hij]
  unfold ggQ2xD2_negOn
  by_cases hki : k = i
  · rw [hki]
    simp only [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij),
      Finset.mem_insert, Finset.mem_singleton, true_or, ↓reduceIte, zero_add, add_zero, mul_one]
    exact ggQ2xD2_scalar_i (v i) (v j)
  · by_cases hkj : k = j
    · rw [hkj]
      simp only [Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        Finset.mem_insert, Finset.mem_singleton, or_true, ↓reduceIte, zero_add, add_zero,
        mul_one]
      exact ggQ2xD2_scalar_j (v i) (v j)
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj,
        add_zero, mul_zero, add_zero]
      simp only [Finset.mem_insert, Finset.mem_singleton, hki, hkj, false_or, ↓reduceIte]

private lemma ggQ2xD2_negOn_pair_mem {n : ℕ} (Z : Set (GGBCV n))
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {i j : Fin n} (hij : i ≠ j) {v : GGBCV n} (hv : v ∈ Z) :
    ggQ2xD2_negOn ({i, j} : Finset (Fin n)) v ∈ Z := by
  set c : GGBCV n := Pi.single i (1 : ZMod 3) + Pi.single j 1 with hc
  set d : GGBCV n := Pi.single i (1 : ZMod 3) - Pi.single j 1 with hd
  have hplus : c ∈ ggDRoots n := by
    rw [hc, ggDRoots]
    exact ggQ2x_wt_single_add_single i j hij 1 1 one_ne_zero one_ne_zero
  have hminus : d ∈ ggDRoots n := by
    rw [hd, ggDRoots]
    exact ggQ2x_wt_sub_single i j hij
  have hc1 : c ⬝ᵥ c ≠ 0 := by rw [hc, ggQ2xD2_norm_add_single i j hij]; decide
  have hc2 : d ⬝ᵥ d ≠ 0 := by rw [hd, ggQ2x_sub_single_norm i j hij]; decide
  have h1 : ggBCRefl c hc1 v ∈ Z := hZcl c (hZroots hplus) v hv hc1
  have h2 : ggBCRefl d hc2 (ggBCRefl c hc1 v) ∈ Z :=
    hZcl d (hZroots hminus) _ h1 hc2
  have heq := ggQ2xD2_negOn_pair_eq i j hij v c d hc hd hc1 hc2
  rwa [← heq] at h2

private lemma ggQ2xD2_wt_refl_ge {n : ℕ} (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0) (i m : Fin n)
    (him : i ≠ m) (hi : z i ≠ 0) (hm : z m = 0) :
    ggBCWt z ≤ ggBCWt (ggBCRefl z hz
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single m (1 : ZMod 3))) := by
  set ρ : GGBCV n := (Pi.single i (1 : ZMod 3)) - (Pi.single m (1 : ZMod 3) : GGBCV n)
    with hρ
  change ggBCWt z ≤ ggBCWt (ggBCRefl z hz ρ)
  have hc0 : (z ⬝ᵥ ρ) * (z ⬝ᵥ z) ≠ 0 := by
    apply mul_ne_zero _ hz
    rw [hρ, ggQ2xD2_dot_diff, hm]
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
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
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
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
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

private lemma ggQ2xD2_wt_refl_full_ge {n : ℕ} (hn : 5 ≤ n) (z : GGBCV n)
    (hz : z ⬝ᵥ z ≠ 0) (i j : Fin n) (hij : i ≠ j) (hzij : z i ≠ z j)
    (hfull : ∀ k, z k ≠ 0) :
    3 ≤ ggBCWt (ggBCRefl z hz
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j (1 : ZMod 3))) := by
  set ρ : GGBCV n := (Pi.single i (1 : ZMod 3)) - (Pi.single j (1 : ZMod 3) : GGBCV n)
    with hρ
  change 3 ≤ (Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0)).card
  have hc0 : (z ⬝ᵥ ρ) * (z ⬝ᵥ z) ≠ 0 := by
    apply mul_ne_zero _ hz
    rw [hρ, ggQ2xD2_dot_diff]
    exact sub_ne_zero.mpr hzij
  have hsub : (Finset.univ.erase i).erase j ⊆
      Finset.univ.filter (fun k => (ggBCRefl z hz ρ) k ≠ 0) := by
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    obtain ⟨hkj, hki⟩ := hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ k, ?_⟩
    rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
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

private lemma ggQ2xD2_partA {n : ℕ} (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hHL : ∀ z ∈ Z, ∑ i, z i = 0 → ∀ ρ ∈ ggARoots n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARoots n) :
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
      exact hZ0 z hz (by rw [ggQ2x_dot_self_eq_wt]; simpa [h3] using h3z)
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
      rw [ggQ2x_dot_self_eq_wt, hfullWt] at h0
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
      rcases ggQ2xD2_ztri (z k) with h0 | h1 | h1
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
    have hρN : ρ ∈ ggARoots n := by
      rw [ggARoots]
      refine ⟨?_, ?_⟩
      · change ggBCWt ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single j (1 : ZMod 3) : GGBCV n)) = 2
        exact ggQ2x_wt_sub_single i j hij
      · change ∑ k, ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single j (1 : ZMod 3) : GGBCV n)) k = 0
        exact ggQ2xD2_sum_diff i j hij
    have hz' := hHL z hz hsum ρ hρN (hZ0 z hz)
    have hge : 3 ≤ ggBCWt (ggBCRefl z (hZ0 z hz) ρ) :=
      ggQ2xD2_wt_refl_full_ge hn z (hZ0 z hz) i j hij hzij hfull
    have hwt' : ggBCWt (ggBCRefl z (hZ0 z hz) ρ) = 2 := by
      have := hz'; rw [ggARoots] at this; exact this.1
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
    have hρN : ρ ∈ ggARoots n := by
      rw [ggARoots]
      refine ⟨?_, ?_⟩
      · change ggBCWt ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single m (1 : ZMod 3) : GGBCV n)) = 2
        exact ggQ2x_wt_sub_single i m him
      · change ∑ k, ((Pi.single i (1 : ZMod 3) : GGBCV n) -
          (Pi.single m (1 : ZMod 3) : GGBCV n)) k = 0
        exact ggQ2xD2_sum_diff i m him
    have hz' := hHL z hz hsum ρ hρN (hZ0 z hz)
    have hge : ggBCWt z ≤ ggBCWt (ggBCRefl z (hZ0 z hz) ρ) :=
      ggQ2xD2_wt_refl_ge z (hZ0 z hz) i m him hi hm
    have hwt' : ggBCWt (ggBCRefl z (hZ0 z hz) ρ) = 2 := by
      have := hz'; rw [ggARoots] at this; exact this.1
    omega

private lemma ggQ2xD2_flip_two {n : ℕ} (Z : Set (GGBCV n))
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {z : GGBCV n} (hz : z ∈ Z) {i j : Fin n} (hij : i ≠ j) :
    ggQ2xD2_negOn ({i, j} : Finset (Fin n)) z ∈ Z ∧
      (∑ k, ggQ2xD2_negOn ({i, j} : Finset (Fin n)) z k) =
        (∑ k, z k) + z i + z j ∧
      ggBCWt (ggQ2xD2_negOn ({i, j} : Finset (Fin n)) z) = ggBCWt z := by
  refine ⟨ggQ2xD2_negOn_pair_mem Z hZroots hZcl hij hz, ?_, ggQ2xD2_negOn_wt _ _⟩
  rw [ggQ2xD2_negOn_sum, Finset.sum_pair hij]
  abel

private lemma ggQ2xD2_flip_one {n : ℕ} (Z : Set (GGBCV n))
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {z : GGBCV n} (hz : z ∈ Z) {m : Fin n} (hm : z m = 0) {k : Fin n} (hkm : k ≠ m) :
    ggQ2xD2_negOn ({k, m} : Finset (Fin n)) z ∈ Z ∧
      (∑ i, ggQ2xD2_negOn ({k, m} : Finset (Fin n)) z i) = (∑ i, z i) + z k ∧
      ggBCWt (ggQ2xD2_negOn ({k, m} : Finset (Fin n)) z) = ggBCWt z := by
  have hmem : ggQ2xD2_negOn ({k, m} : Finset (Fin n)) z ∈ Z :=
    ggQ2xD2_negOn_pair_mem Z hZroots hZcl hkm hz
  refine ⟨hmem, ?_, ggQ2xD2_negOn_wt _ _⟩
  rw [ggQ2xD2_negOn_sum, Finset.sum_pair hkm, hm, add_zero]

private lemma ggQ2xD2_flip_four {n : ℕ} (Z : Set (GGBCV n))
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {z : GGBCV n} (hz : z ∈ Z) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    ggQ2xD2_negOn ({a, b} : Finset (Fin n))
        (ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z) ∈ Z ∧
      (∑ k, ggQ2xD2_negOn ({a, b} : Finset (Fin n))
        (ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z) k) =
        (∑ k, z k) + z a + z b + z c + z d ∧
      ggBCWt (ggQ2xD2_negOn ({a, b} : Finset (Fin n))
        (ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z)) = ggBCWt z := by
  have hcd' : ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z ∈ Z :=
    ggQ2xD2_negOn_pair_mem Z hZroots hZcl hcd hz
  have hmem : ggQ2xD2_negOn ({a, b} : Finset (Fin n))
      (ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z) ∈ Z :=
    ggQ2xD2_negOn_pair_mem Z hZroots hZcl hab hcd'
  have ha' : (ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z) a = z a := by
    unfold ggQ2xD2_negOn
    rw [if_neg]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac, had⟩
  have hb' : (ggQ2xD2_negOn ({c, d} : Finset (Fin n)) z) b = z b := by
    unfold ggQ2xD2_negOn
    rw [if_neg]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbc, hbd⟩
  refine ⟨hmem, ?_, ?_⟩
  · rw [ggQ2xD2_negOn_sum, ggQ2xD2_negOn_sum, Finset.sum_pair hcd, Finset.sum_pair hab,
      ha', hb']
    abel
  · rw [ggQ2xD2_negOn_wt, ggQ2xD2_negOn_wt]

private lemma ggQ2xD2_partB {n : ℕ} (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    ∀ z ∈ Z, 3 ≤ ggBCWt z → ∃ z' ∈ Z, (∑ i, z' i) = 0 ∧ ggBCWt z' = ggBCWt z := by
  intro z hz hw
  rcases ggQ2xD2_ztri (∑ k, z k) with hsum0 | hsum1 | hsumn1
  · exact ⟨z, hz, hsum0, rfl⟩
  · by_cases hfull : ∀ k, z k ≠ 0
    · let P := Finset.univ.filter (fun k => z k = 1)
      let M := Finset.univ.filter (fun k => z k = -1)
      have hPM : P ∪ M = Finset.univ := by
        ext k
        simp only [P, M, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (h | h) <;> trivial
        · intro _
          rcases ggQ2xD2_ztri (z k) with h | h | h
          · exact absurd h (hfull k)
          · exact Or.inl h
          · exact Or.inr h
      have hdisj : Disjoint P M := by
        rw [Finset.disjoint_left]
        intro k hkP hkM
        simp only [P, M, Finset.mem_filter, Finset.mem_univ, true_and] at hkP hkM
        rw [hkP] at hkM
        exact (by decide : (1 : ZMod 3) ≠ -1) hkM
      have hcard : P.card + M.card = n := by
        rw [← Finset.card_union_of_disjoint hdisj, hPM, Finset.card_univ, Fintype.card_fin]
      by_cases hP2 : 2 ≤ P.card
      · obtain ⟨a, haP, b, hbP, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
        have ha1 : z a = 1 := (Finset.mem_filter.mp haP).2
        have hb1 : z b = 1 := (Finset.mem_filter.mp hbP).2
        obtain ⟨hmem, hsum, hwt⟩ := ggQ2xD2_flip_two Z hZroots hZcl hz hab
        exact ⟨_, hmem, by rw [hsum, ha1, hb1, hsum1]; decide, by rw [hwt]⟩
      · have hM4 : 4 ≤ M.card := by omega
        obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hM4
        obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hS⟩ :=
          Finset.card_eq_four.mp hScard
        have ha : z a = -1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        have hb : z b = -1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        have hc : z c = -1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        have hd : z d = -1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        obtain ⟨hmem, hsum, hwt⟩ :=
          ggQ2xD2_flip_four Z hZroots hZcl hz hab hcd hac had hbc hbd
        exact ⟨_, hmem, by rw [hsum, ha, hb, hc, hd, hsum1]; decide, by rw [hwt]⟩
    · push Not at hfull
      obtain ⟨m, hm⟩ := hfull
      by_cases hneg : ∃ k, z k = -1
      · obtain ⟨k, hk⟩ := hneg
        have hkm : k ≠ m := by
          rintro rfl
          rw [hk] at hm
          exact (by decide : (-1 : ZMod 3) ≠ 0) hm
        obtain ⟨hmem, hsum, hwt⟩ := ggQ2xD2_flip_one Z hZroots hZcl hz hm hkm
        exact ⟨_, hmem, by rw [hsum, hk, hsum1]; decide, by rw [hwt]⟩
      · have hsupp : 1 < (Finset.univ.filter fun k => z k ≠ 0).card := by
          have hwt : ggBCWt z = (Finset.univ.filter fun k => z k ≠ 0).card := rfl
          omega
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hsupp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        have hzi : z i = 1 := by
          rcases ggQ2xD2_ztri (z i) with h0 | h1 | h1
          · exact absurd h0 hi
          · exact h1
          · exact absurd h1 (fun hh => hneg ⟨i, hh⟩)
        have hzj : z j = 1 := by
          rcases ggQ2xD2_ztri (z j) with h0 | h1 | h1
          · exact absurd h0 hj
          · exact h1
          · exact absurd h1 (fun hh => hneg ⟨j, hh⟩)
        have him : i ≠ m := by rintro rfl; exact hi hm
        have hjm : j ≠ m := by rintro rfl; exact hj hm
        have hfirst := ggQ2xD2_flip_one Z hZroots hZcl hz hm him
        have hfirst_zero : (ggQ2xD2_negOn ({i, m} : Finset (Fin n)) z) m = 0 := by
          unfold ggQ2xD2_negOn
          rw [if_pos (by simp), hm]
          exact neg_zero
        have hsec := ggQ2xD2_flip_one Z hZroots hZcl hfirst.1 hfirst_zero hjm
        have hsecond_wt : ggBCWt (ggQ2xD2_negOn ({j, m} : Finset (Fin n))
            (ggQ2xD2_negOn ({i, m} : Finset (Fin n)) z)) = ggBCWt z := by
          rw [hsec.2.2, hfirst.2.2]
        have hj' : (ggQ2xD2_negOn ({i, m} : Finset (Fin n)) z) j = z j := by
          unfold ggQ2xD2_negOn
          rw [if_neg]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hij h.symm, hjm⟩
        exact ⟨_, hsec.1,
          by rw [hsec.2.1, hfirst.2.1, hj', hzi, hzj, hsum1]; decide, hsecond_wt⟩
  · by_cases hfull : ∀ k, z k ≠ 0
    · let P := Finset.univ.filter (fun k => z k = 1)
      let M := Finset.univ.filter (fun k => z k = -1)
      have hPM : P ∪ M = Finset.univ := by
        ext k
        simp only [P, M, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (h | h) <;> trivial
        · intro _
          rcases ggQ2xD2_ztri (z k) with h | h | h
          · exact absurd h (hfull k)
          · exact Or.inl h
          · exact Or.inr h
      have hdisj : Disjoint P M := by
        rw [Finset.disjoint_left]
        intro k hkP hkM
        simp only [P, M, Finset.mem_filter, Finset.mem_univ, true_and] at hkP hkM
        rw [hkP] at hkM
        exact (by decide : (1 : ZMod 3) ≠ -1) hkM
      have hcard : P.card + M.card = n := by
        rw [← Finset.card_union_of_disjoint hdisj, hPM, Finset.card_univ, Fintype.card_fin]
      by_cases hM2 : 2 ≤ M.card
      · obtain ⟨a, haM, b, hbM, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < M.card)
        have ha1 : z a = -1 := (Finset.mem_filter.mp haM).2
        have hb1 : z b = -1 := (Finset.mem_filter.mp hbM).2
        obtain ⟨hmem, hsum, hwt⟩ := ggQ2xD2_flip_two Z hZroots hZcl hz hab
        exact ⟨_, hmem, by rw [hsum, ha1, hb1, hsumn1]; decide, by rw [hwt]⟩
      · have hP4 : 4 ≤ P.card := by omega
        obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hP4
        obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hS⟩ :=
          Finset.card_eq_four.mp hScard
        have ha : z a = 1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        have hb : z b = 1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        have hc : z c = 1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        have hd : z d = 1 := (Finset.mem_filter.mp (hSsub (by rw [hS]; simp))).2
        obtain ⟨hmem, hsum, hwt⟩ :=
          ggQ2xD2_flip_four Z hZroots hZcl hz hab hcd hac had hbc hbd
        exact ⟨_, hmem, by rw [hsum, ha, hb, hc, hd, hsumn1]; decide, by rw [hwt]⟩
    · push Not at hfull
      obtain ⟨m, hm⟩ := hfull
      by_cases hpos : ∃ k, z k = 1
      · obtain ⟨k, hk⟩ := hpos
        have hkm : k ≠ m := by
          rintro rfl
          rw [hk] at hm
          exact (by decide : (1 : ZMod 3) ≠ 0) hm
        obtain ⟨hmem, hsum, hwt⟩ := ggQ2xD2_flip_one Z hZroots hZcl hz hm hkm
        exact ⟨_, hmem, by rw [hsum, hk, hsumn1]; decide, by rw [hwt]⟩
      · have hsupp : 1 < (Finset.univ.filter fun k => z k ≠ 0).card := by
          have hwt : ggBCWt z = (Finset.univ.filter fun k => z k ≠ 0).card := rfl
          omega
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hsupp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        have hzi : z i = -1 := by
          rcases ggQ2xD2_ztri (z i) with h0 | h1 | h1
          · exact absurd h0 hi
          · exact absurd h1 (fun hh => hpos ⟨i, hh⟩)
          · exact h1
        have hzj : z j = -1 := by
          rcases ggQ2xD2_ztri (z j) with h0 | h1 | h1
          · exact absurd h0 hj
          · exact absurd h1 (fun hh => hpos ⟨j, hh⟩)
          · exact h1
        have him : i ≠ m := by rintro rfl; exact hi hm
        have hjm : j ≠ m := by rintro rfl; exact hj hm
        have hfirst := ggQ2xD2_flip_one Z hZroots hZcl hz hm him
        have hfirst_zero : (ggQ2xD2_negOn ({i, m} : Finset (Fin n)) z) m = 0 := by
          unfold ggQ2xD2_negOn
          rw [if_pos (by simp), hm]
          exact neg_zero
        have hsec := ggQ2xD2_flip_one Z hZroots hZcl hfirst.1 hfirst_zero hjm
        have hsecond_wt : ggBCWt (ggQ2xD2_negOn ({j, m} : Finset (Fin n))
            (ggQ2xD2_negOn ({i, m} : Finset (Fin n)) z)) = ggBCWt z := by
          rw [hsec.2.2, hfirst.2.2]
        have hj' : (ggQ2xD2_negOn ({i, m} : Finset (Fin n)) z) j = z j := by
          unfold ggQ2xD2_negOn
          rw [if_neg]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hij h.symm, hjm⟩
        exact ⟨_, hsec.1,
          by rw [hsec.2.1, hfirst.2.1, hj', hzi, hzj, hsumn1]; decide, hsecond_wt⟩

theorem ggQ2_D_Z_a1 (n : ℕ) [NeZero n] (hn : 6 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 n) :
    (∀ z ∈ Z, ggBCWt z ≤ 2 ∨ (n = 8 ∧ ggBCWt z = 8)) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, ggBCWt z = n → ggBCWt w = n →
        (Even (Finset.univ.filter fun i => z i = -1).card ↔
          Even (Finset.univ.filter fun i => w i = -1).card)) := by
  constructor
  · intro z hz
    by_cases hzero : ∃ m, z m = 0
    · left; exact ggQ2xD1_zero_coord_le_two hn Z hZ0 hZroots hZcl hHL hz hzero
    · push Not at hzero
      have hfull : ∀ i, z i ≠ 0 := hzero
      have hwt : ggBCWt z = n := ggQ2x_wt_eq_of_full hfull
      have h8 : n = 8 := ggQ2xD1_full_force_eight hn Z hZ0 hZroots hZcl hHL hz hfull
      exact Or.inr ⟨h8, by rw [hwt, h8]⟩
  · intro z hz w hw hzwt hwwt
    have hfull_z : ∀ i, z i ≠ 0 := ggQ2xD1_full_of_wt_eq hzwt
    have hfull_w : ∀ i, w i ≠ 0 := ggQ2xD1_full_of_wt_eq hwwt
    have h8 : n = 8 := ggQ2xD1_full_force_eight hn Z hZ0 hZroots hZcl hHL hz hfull_z
    exact ggQ2xD1_full_parity hn Z hZ0 hZroots hZcl hHL hz hw hfull_z hfull_w h8

theorem ggQ2_D_Z_aN (n : ℕ) (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, ∑ i, z i = 0 → ∀ ρ ∈ ggARoots n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARoots n) :
    ∀ z ∈ Z, ggBCWt z ≤ 2 := by
  intro z hz
  by_cases hle : ggBCWt z ≤ 2
  · exact hle
  · push Not at hle
    obtain ⟨z', hz'Z, hsum', hwt'⟩ := ggQ2xD2_partB hn Z hZroots hZcl z hz (by omega)
    have hpart := ggQ2xD2_partA hn Z hZ0 hHL z' hz'Z hsum'
    omega

end CFSG.StandardType

end
