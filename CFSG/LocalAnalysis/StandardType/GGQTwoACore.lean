module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2xA_sum_single {m : ℕ} (i : Fin m) (c : ZMod 3) :
    ∑ j, (Pi.single i c : GGBCV m) j = c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xA_sum_sub_single {m : ℕ} (a b : Fin m) :
    ∑ i, (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) i = 0 := by
  have h : (∑ i, (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) i)
      = (∑ i, (Pi.single a (1 : ZMod 3) : GGBCV m) i)
        - (∑ i, (Pi.single b (1 : ZMod 3) : GGBCV m) i) :=
    Finset.sum_sub_distrib _ _
  have h1 : (∑ i, (Pi.single a (1 : ZMod 3) : GGBCV m) i) = 1 :=
    ggQ2xA_sum_single a 1
  have h2 : (∑ i, (Pi.single b (1 : ZMod 3) : GGBCV m) i) = 1 :=
    ggQ2xA_sum_single b 1
  rw [h, h1, h2, sub_self]

private lemma ggQ2xA_wt_eq_one {m : ℕ} {v : GGBCV m} (hv : ggBCWt v = 1) :
    ∃ i s, s ≠ 0 ∧ v = Pi.single i s := by
  unfold ggBCWt at hv
  obtain ⟨i, h⟩ := Finset.card_eq_one.mp hv
  refine ⟨i, v i, ?_, ?_⟩
  · have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by
      rw [h]; exact Finset.mem_singleton_self i
    simpa using this
  · ext k
    by_cases hk : k = i
    · subst hk; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
      have : k ∉ Finset.univ.filter (fun l => v l ≠ 0) := by
        rw [h]; simp [hk]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using this

private lemma ggQ2xA_wt_le_union {m : ℕ} {u v w : GGBCV m}
    (h : ∀ i, u i ≠ 0 → v i ≠ 0 ∨ w i ≠ 0) : ggBCWt u ≤ ggBCWt v + ggBCWt w := by
  unfold ggBCWt
  calc (Finset.univ.filter fun i => u i ≠ 0).card
      ≤ ((Finset.univ.filter fun i => v i ≠ 0) ∪
          (Finset.univ.filter fun i => w i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
        exact h i hi
    _ ≤ (Finset.univ.filter fun i => v i ≠ 0).card +
          (Finset.univ.filter fun i => w i ≠ 0).card := Finset.card_union_le _ _

private lemma ggQ2xA_sq_eq_one {x : ZMod 3} (hx : x ≠ 0) : x * x = 1 := by
  revert hx; revert x; decide

private lemma ggQ2xA_eq_one_or_neg_one {x : ZMod 3} (hx : x ≠ 0) : x = 1 ∨ x = -1 := by
  revert hx; revert x; decide

private lemma ggQ2xA_dot_self_full {m : ℕ} {w : GGBCV m} (hfull : ∀ i, w i ≠ 0) :
    w ⬝ᵥ w = (m : ZMod 3) := by
  rw [ggQ2x_dot_self_eq_wt, ggQ2x_wt_eq_of_full hfull]

private lemma ggQ2xA_dot_self_ne_zero_of_full {m : ℕ} {w : GGBCV m}
    (hfull : ∀ i, w i ≠ 0) (hm3 : m % 3 ≠ 0) : w ⬝ᵥ w ≠ 0 := by
  rw [ggQ2xA_dot_self_full hfull]
  intro h
  apply hm3
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast] using hv

private lemma ggQ2xA_natCast_eq_one {m : ℕ} (h : m % 3 = 1) : (m : ZMod 3) = 1 := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, h]
  decide

private lemma ggQ2xA_natCast_eq_two {m : ℕ} (h : m % 3 = 2) : (m : ZMod 3) = 2 := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, h]
  decide

private lemma ggQ2xA_natCast_eq_zero {m : ℕ} (h : m % 3 = 0) : (m : ZMod 3) = 0 := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, h]
  decide

private lemma ggQ2xA_swap_mem {m : ℕ} (Z : Set (GGBCV m)) (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    {z : GGBCV m} (hz : z ∈ Z) {a b : Fin m} (hab : a ≠ b) :
    (fun i => z (Equiv.swap a b i)) ∈ Z := by
  have hrhoRoot : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m)
      ∈ ggARoots m := by
    refine ⟨?_, ?_⟩
    · rw [ggQ2x_wt_sub_single a b hab]
    · rw [ggQ2xA_sum_sub_single]
  have hrhoNe : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m)
      ⬝ᵥ (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) ≠ 0 := by
    rw [ggQ2x_sub_single_norm a b hab]; decide
  have hmem := hZcl (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3))
    (hZroots hrhoRoot) z hz hrhoNe
  rwa [ggQ2x_refl_sub_single a b hab z hrhoNe] at hmem

private lemma ggQ2xA_zero_at_zero_root (m : ℕ) [NeZero m] (hm : 6 ≤ m)
    (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0)
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m)
    {z : GGBCV m} (hz : z ∈ Z) (hz0 : z 0 = 0) : ggBCWt z = 2 := by
  have hz0ne : z ⬝ᵥ z ≠ 0 := hZ0 z hz
  have hzsum : ∑ i, z i = 0 := hZsum z hz
  have hwt_ne_zero : ggBCWt z ≠ 0 := by
    intro h0
    exact hz0ne (by rw [ggQ2x_dot_self_eq_wt, h0]; rfl)
  have hwt_ne_one : ggBCWt z ≠ 1 := by
    intro h1
    obtain ⟨i, c, hc, hzeq⟩ := ggQ2xA_wt_eq_one h1
    have hsum : ∑ j, z j = c := by rw [hzeq]; exact ggQ2xA_sum_single i c
    rw [hsum] at hzsum
    exact hc hzsum
  suffices hle : ggBCWt z ≤ 2 by omega
  by_contra hgt
  push Not at hgt
  by_cases halleq : ∀ i j, z i ≠ 0 → z j ≠ 0 → z i = z j
  · have hnonempty : (Finset.univ.filter fun i => z i ≠ 0).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have : ggBCWt z = 0 := by simp [ggBCWt, he]
      omega
    obtain ⟨i, hi⟩ := hnonempty
    have hzi : z i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hdot : z ⬝ᵥ z = (∑ k, z k) * z i := by
      rw [dotProduct, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : z k = 0
      · simp [hk]
      · rw [halleq k i hk hzi]
    rw [hzsum, zero_mul] at hdot
    exact hz0ne hdot
  · push Not at halleq
    obtain ⟨i, j, hzi, hzj, hij⟩ := halleq
    have hij_ne : i ≠ j := by rintro rfl; exact hij rfl
    have hi0 : i ≠ 0 := by intro h; rw [h] at hzi; exact hzi hz0
    have hj0 : j ≠ 0 := by intro h; rw [h] at hzj; exact hzj hz0
    have hrhoRoot : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m)
        ∈ ggARoots m := by
      refine ⟨?_, ?_⟩
      · rw [ggQ2x_wt_sub_single i j hij_ne]
      · rw [ggQ2xA_sum_sub_single]
    have hrhoLam : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m)
        ∈ ggARootsLam1 m := by
      refine ⟨hrhoRoot, ?_⟩
      rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hi0),
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hj0), sub_self]
    have hzrho : z ⬝ᵥ (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m)
        ≠ 0 := by
      rw [dotProduct_comm, ggQ2x_sub_single_dot]
      intro h; exact hij (sub_eq_zero.mp h)
    have hs := hHL z hz hz0 _ hrhoLam hz0ne
    have hrho_wt : ggBCWt (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) :
        GGBCV m) = 2 := ggQ2x_wt_sub_single i j hij_ne
    have hs_wt : ggBCWt (ggBCRefl z hz0ne
        (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m)) = 2 := hs.1.1
    have hsupp : ∀ k, z k ≠ 0 →
        (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) k ≠ 0 ∨
          (ggBCRefl z hz0ne
            (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m)) k ≠ 0 := by
      intro k hzk
      by_cases hrk : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) k = 0
      · right
        rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrk, zero_add]
        exact mul_ne_zero (mul_ne_zero hzrho hz0ne) hzk
      · exact Or.inl hrk
    have hwt_le : ggBCWt z ≤ 4 := by
      have h := ggQ2xA_wt_le_union hsupp
      rw [hrho_wt, hs_wt] at h
      omega
    have hwt3 : ggBCWt z ≠ 3 := by
      intro h3
      exact hz0ne (by rw [ggQ2x_dot_self_eq_wt, h3]; rfl)
    have hwt4 : ggBCWt z = 4 := by omega
    have hsupp_card : (Finset.univ.filter fun k => z k ≠ 0).card = 4 := hwt4
    have hErase_card : (Finset.univ.erase (0 : Fin m)).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hlt : (Finset.univ.filter fun k => z k ≠ 0).card
        < (Finset.univ.erase (0 : Fin m)).card := by
      rw [hsupp_card, hErase_card]; omega
    obtain ⟨t, htmem, htnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp htmem).1
    have hzt : z t = 0 := by
      by_contra hzt
      exact htnot (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hzt⟩)
    have hS_nonempty : (Finset.univ.filter fun k => z k ≠ 0).Nonempty :=
      Finset.card_pos.mp (by rw [hsupp_card]; omega)
    obtain ⟨a, ha⟩ := hS_nonempty
    have hza : z a ≠ 0 := (Finset.mem_filter.mp ha).2
    have ha0 : a ≠ 0 := by intro h; rw [h] at hza; exact hza hz0
    have hat : a ≠ t := by rintro rfl; exact hza hzt
    have hrho2Root : (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)
        ∈ ggARoots m := by
      refine ⟨?_, ?_⟩
      · rw [ggQ2x_wt_sub_single a t hat]
      · rw [ggQ2xA_sum_sub_single]
    have hrho2Lam : (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)
        ∈ ggARootsLam1 m := by
      refine ⟨hrho2Root, ?_⟩
      rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm ha0),
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm ht0), sub_self]
    have hs2 := hHL z hz hz0 _ hrho2Lam hz0ne
    have hs2_wt : ggBCWt (ggBCRefl z hz0ne
        (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)) = 2 := hs2.1.1
    have hzz1 : z ⬝ᵥ z = (1 : ZMod 3) := by rw [ggQ2x_dot_self_eq_wt, hwt4]; rfl
    have hzrho2 : z ⬝ᵥ (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)
        = z a := by
      rw [dotProduct_comm, ggQ2x_sub_single_dot, hzt]
      simp
    have hs2_apply : ∀ k, (ggBCRefl z hz0ne
        (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)) k
        = (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m) k + z a * z k := by
      intro k
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzrho2, hzz1,
        mul_one]
    have hsupp2 : (Finset.univ.filter fun k =>
          (ggBCRefl z hz0ne
            (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)) k ≠ 0)
        = insert t (Finset.univ.filter fun k => z k ≠ 0) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hk
        by_cases hkt : k = t
        · exact Or.inl hkt
        · right
          by_contra hzk
          have hzk0 : z k = 0 := by simpa using hzk
          have hka : k ≠ a := by intro h; rw [h] at hzk0; exact hza hzk0
          have h0 : (ggBCRefl z hz0ne
              (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)) k = 0 := by
            rw [hs2_apply k, Pi.sub_apply,
              Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkt,
              Pi.single_eq_of_ne (M := fun _ => ZMod 3) hka, hzk0, mul_zero, zero_sub]
            decide
          exact hk h0
      · intro hk
        rcases hk with hkt | hkS
        · rw [hkt, hs2_apply]
          simp only [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hat),
            Pi.single_eq_same, hzt, mul_zero, add_zero]
          decide
        · have hzk : z k ≠ 0 := hkS
          rw [hs2_apply]
          by_cases hka : k = a
          · rw [hka]
            rw [Pi.sub_apply, Pi.single_eq_same,
              Pi.single_eq_of_ne (M := fun _ => ZMod 3) hat]
            rw [ggQ2xA_sq_eq_one hza]
            decide
          · have hkt : k ≠ t := by intro h; rw [h] at hzk; exact hzk hzt
            rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hka,
              Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkt, sub_self, zero_add]
            exact mul_ne_zero hza hzk
    have hwt5 : ggBCWt (ggBCRefl z hz0ne
        (Pi.single a (1 : ZMod 3) - Pi.single t (1 : ZMod 3) : GGBCV m)) = 5 := by
      unfold ggBCWt
      rw [hsupp2, Finset.card_insert_of_notMem htnot, hsupp_card]
    omega

private lemma ggQ2xA_zero_coord_root (m : ℕ) [NeZero m] (hm : 6 ≤ m)
    (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0)
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m)
    {z : GGBCV m} (hz : z ∈ Z) (hzero : ∃ i, z i = 0) : ggBCWt z = 2 := by
  obtain ⟨i, hi⟩ := hzero
  by_cases hi0 : i = 0
  · rw [hi0] at hi
    exact ggQ2xA_zero_at_zero_root m hm Z hZ0 hZsum hZroots hZcl hHL hz hi
  · have h0i : (0 : Fin m) ≠ i := Ne.symm hi0
    have hswap := ggQ2xA_swap_mem Z hZroots hZcl hz h0i
    have hswap0 : (fun j => z (Equiv.swap 0 i j)) 0 = 0 := by
      change z (Equiv.swap 0 i 0) = 0
      rw [Equiv.swap_apply_left]
      exact hi
    have hwt := ggQ2xA_zero_at_zero_root m hm Z hZ0 hZsum hZroots hZcl hHL hswap hswap0
    rwa [ggQ2x_wt_comp_swap 0 i z] at hwt

private lemma ggQ2xA_type4_m_eq_eight {m : ℕ} {z : GGBCV m} (hz : ggAType4 z) : m = 8 := by
  obtain ⟨hfull, h1, hm1⟩ := hz
  have hpart : (Finset.univ.filter fun i => z i = 1) ∪
      (Finset.univ.filter fun i => z i = -1) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ggQ2xA_eq_one_or_neg_one (hfull i) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hdisj : Disjoint (Finset.univ.filter fun i => z i = 1)
      (Finset.univ.filter fun i => z i = -1) := by
    rw [Finset.disjoint_left]
    intro i hi1 him1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 him1
    rw [hi1] at him1
    exact (by decide : (1 : ZMod 3) ≠ -1) him1
  have hcard := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hdisj, h1, hm1, Finset.card_univ, Fintype.card_fin] at hcard
  omega

private lemma ggQ2xA_full_support_mod3 (m : ℕ) [NeZero m] (hm : 6 ≤ m) (h3 : m % 3 ≠ 0)
    (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0)
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m)
    {z : GGBCV m} (hz : z ∈ Z) (hfull : ∀ i, z i ≠ 0) : m % 3 = 2 := by
  have hcases : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcases with h1 | h2
  · exfalso
    have hex : ∃ a b, z a ≠ z b := by
      by_contra hcon
      push Not at hcon
      have hsum_eq : ∑ k, z k = (m : ZMod 3) * z 0 := by
        calc ∑ k, z k = ∑ k, z 0 := Finset.sum_congr rfl (fun k _ => hcon k 0)
          _ = (m : ZMod 3) * z 0 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hzero := hZsum z hz
      rw [hsum_eq] at hzero
      have hm0 : (m : ZMod 3) = 0 := (mul_eq_zero.mp hzero).resolve_right (hfull 0)
      apply h3
      have hv := congrArg ZMod.val hm0
      simpa [ZMod.val_natCast] using hv
    obtain ⟨a, b, hab0⟩ := hex
    have hab : a ≠ b := by rintro rfl; exact hab0 rfl
    have hzb_eq : z b = -z a := by
      have h1a := ggQ2xA_eq_one_or_neg_one (hfull a)
      have h1b := ggQ2xA_eq_one_or_neg_one (hfull b)
      rcases h1a with h1a | h1a
      · rcases h1b with h1b | h1b
        · exact absurd (by rw [h1a, h1b]) hab0
        · rw [h1a, h1b]; try decide
      · rcases h1b with h1b | h1b
        · rw [h1a, h1b]; try decide
        · exact absurd (by rw [h1a, h1b]) hab0
    have hz0ne : z ⬝ᵥ z ≠ 0 := hZ0 z hz
    set rho : GGBCV m := Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) with hrho
    have hrhoRoot : rho ∈ ggARoots m := by
      refine ⟨?_, ?_⟩
      · rw [hrho, ggQ2x_wt_sub_single a b hab]
      · rw [hrho, ggQ2xA_sum_sub_single]
    have hzrho : z ⬝ᵥ rho = 2 * z a := by
      rw [hrho, dotProduct_comm, ggQ2x_sub_single_dot, hzb_eq]
      rcases ggQ2xA_eq_one_or_neg_one (hfull a) with hza1 | hza1 <;> rw [hza1] <;> decide
    have hm1 : (m : ZMod 3) = 1 := ggQ2xA_natCast_eq_one h1
    have hzz : z ⬝ᵥ z = (1 : ZMod 3) := by rw [ggQ2xA_dot_self_full hfull, hm1]
    have hs_apply : ∀ k, (ggBCRefl z hz0ne rho) k = rho k + (2 * z a) * z k := by
      intro k
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzrho, hzz]
      ring_nf
    have hza_sq : z a * z a = 1 := ggQ2xA_sq_eq_one (hfull a)
    have hb_zero : (ggBCRefl z hz0ne rho) b = 0 := by
      rw [hs_apply b, hrho, Pi.sub_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab),
        Pi.single_eq_same, hzb_eq]
      rcases ggQ2xA_eq_one_or_neg_one (hfull a) with hza1 | hza1 <;> rw [hza1] <;> decide
    have ha_zero : (ggBCRefl z hz0ne rho) a = 0 := by
      rw [hs_apply a, hrho, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab]
      rcases ggQ2xA_eq_one_or_neg_one (hfull a) with hza1 | hza1 <;> rw [hza1] <;> decide
    have hsupp : (Finset.univ.filter fun k => (ggBCRefl z hz0ne rho) k ≠ 0)
        = (Finset.univ.erase a).erase b := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro hk
        refine ⟨fun hkb => hk (by rw [hkb]; exact hb_zero),
          fun hka => hk (by rw [hka]; exact ha_zero)⟩
      · rintro ⟨hkb, hka⟩
        rw [hs_apply]
        have hrk : rho k = 0 := by
          rw [hrho, Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hka,
            Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkb]
          simp
        rw [hrk, zero_add]
        exact mul_ne_zero (mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hfull a)) (hfull k)
    have hwt_s : ggBCWt (ggBCRefl z hz0ne rho) = m - 2 := by
      unfold ggBCWt
      rw [hsupp,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩),
        Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      omega
    have hmem : ggBCRefl z hz0ne rho ∈ Z := hZcl z hz rho (hZroots hrhoRoot) hz0ne
    have hA2 := ggQ2xA_zero_coord_root m hm Z hZ0 hZsum hZroots hZcl hHL hmem ⟨a, ha_zero⟩
    rw [hwt_s] at hA2
    omega
  · exact h2

private lemma ggQ2xA_scalar_self (c x : ZMod 3) (hc : c ≠ 0) :
    x + ((c * x * 2) * -c) = 2 * x := by
  revert c x; decide

private lemma ggQ2xA_scalar_hzw (c x : ZMod 3) : -c * x + c * (-x) = c * x := by
  revert c x; decide

private lemma ggQ2xA_scalar_other (c x y : ZMod 3) (hc : c ≠ 0) :
    y + ((c * x * 2) * c) = y - x := by
  revert c x y; decide

private lemma ggQ2xA_sub_ne_zero {a b : ZMod 3} (h : a ≠ b) : a - b ≠ 0 := by
  revert a b; decide

private lemma ggQ2xA_ne_of_sub_ne_zero {a b : ZMod 3} (h : a - b ≠ 0) : a ≠ b := by
  revert a b; decide

private lemma ggQ2xA_not_both (m : ℕ) [NeZero m] (hm : 6 ≤ m) (h3 : m % 3 ≠ 0)
    (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0)
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m) :
    ¬ ((∃ z ∈ Z, ggAType1 z) ∧ (∃ w ∈ Z, ggAType4 w)) := by
  rintro ⟨⟨z, hzZ, hzt1⟩, ⟨w, hwZ, hwt4⟩⟩
  have hm8 : m = 8 := ggQ2xA_type4_m_eq_eight hwt4
  obtain ⟨hwt4_full, hwt4_one, hwt4_neg⟩ := hwt4
  obtain ⟨c, hc, i0, hzi0, hzother⟩ := hzt1
  have hz0ne : z ⬝ᵥ z ≠ 0 := hZ0 z hzZ
  have hzfull : ∀ k, z k ≠ 0 := by
    intro k
    by_cases hk : k = i0
    · rw [hk, hzi0]; exact neg_ne_zero.mpr hc
    · rw [hzother k hk]; exact hc
  have hz_eq : z = fun k => if k = i0 then -c else c := by
    funext k
    by_cases hk : k = i0
    · rw [if_pos hk, hk]; exact hzi0
    · rw [if_neg hk]; exact hzother k hk
  have hzw : z ⬝ᵥ w = c * w i0 := by
    rw [dotProduct, hz_eq]
    change (∑ k, (if k = i0 then -c else c) * w k) = c * w i0
    rw [← Finset.add_sum_erase Finset.univ
      (fun k => (if k = i0 then -c else c) * w k) (Finset.mem_univ i0), if_pos rfl]
    have hrest : (∑ k ∈ Finset.univ.erase i0,
        (if k = i0 then -c else c) * w k) = c * (∑ k ∈ Finset.univ.erase i0, w k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_erase] at hk
      rw [if_neg hk.1]
    rw [hrest]
    have hwsum : (∑ k ∈ Finset.univ.erase i0, w k) = -w i0 := by
      have hall : ∑ k, w k = 0 := hZsum w hwZ
      have h := Finset.add_sum_erase Finset.univ (fun k => w k) (Finset.mem_univ i0)
      rw [hall] at h
      have h' : w i0 + (∑ k ∈ Finset.univ.erase i0, w k) = 0 := h
      exact eq_neg_of_add_eq_zero_right h'
    rw [hwsum]
    exact ggQ2xA_scalar_hzw c (w i0)
  have hzz : z ⬝ᵥ z = (2 : ZMod 3) := by
    rw [ggQ2xA_dot_self_full hzfull, hm8]
    decide
  have hs_apply : ∀ k, (ggBCRefl z hz0ne w) k
      = if k = i0 then 2 * w i0 else w k - w i0 := by
    intro k
    rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzw, hzz]
    by_cases hki : k = i0
    · rw [if_pos hki, hki, hzi0]
      exact ggQ2xA_scalar_self c (w i0) hc
    · rw [if_neg hki, hzother k hki]
      exact ggQ2xA_scalar_other c (w i0) (w k) hc
  have hsupp : (Finset.univ.filter fun k => (ggBCRefl z hz0ne w) k ≠ 0)
      = insert i0 (Finset.univ.filter fun k => w k ≠ w i0) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      by_cases hki : k = i0
      · exact Or.inl hki
      · right
        rw [hs_apply, if_neg hki] at hk
        exact ggQ2xA_ne_of_sub_ne_zero hk
    · intro hk
      rcases hk with hki | hkw
      · rw [hki, hs_apply, if_pos rfl]
        exact mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hwt4_full i0)
      · have hki : k ≠ i0 := by rintro rfl; exact hkw rfl
        rw [hs_apply, if_neg hki]
        exact ggQ2xA_sub_ne_zero hkw
  have hS_card : (Finset.univ.filter fun k => w k ≠ w i0).card = 4 := by
    have hwi : w i0 = 1 ∨ w i0 = -1 := ggQ2xA_eq_one_or_neg_one (hwt4_full i0)
    rcases hwi with hwi | hwi
    · have heq : (Finset.univ.filter fun k => w k ≠ w i0) =
          Finset.univ.filter fun k => w k = -1 := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hwi]
        constructor
        · intro h
          rcases ggQ2xA_eq_one_or_neg_one (hwt4_full k) with h1 | hm1
          · exact absurd h1 h
          · exact hm1
        · intro h h1; rw [h1] at h; exact (by decide : (1 : ZMod 3) ≠ -1) h
      rw [heq, hwt4_neg]
    · have heq : (Finset.univ.filter fun k => w k ≠ w i0) =
          Finset.univ.filter fun k => w k = 1 := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hwi]
        constructor
        · intro h
          rcases ggQ2xA_eq_one_or_neg_one (hwt4_full k) with h1 | hm1
          · exact h1
          · exact absurd hm1 h
        · intro h hm1; rw [hm1] at h; exact (by decide : (-1 : ZMod 3) ≠ 1) h
      rw [heq, hwt4_one]
  have hnotmem : i0 ∉ Finset.univ.filter fun k => w k ≠ w i0 := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => h rfl
  have hwt5 : ggBCWt (ggBCRefl z hz0ne w) = 5 := by
    unfold ggBCWt
    rw [hsupp, Finset.card_insert_of_notMem hnotmem, hS_card]
  have hzeros_card : (Finset.univ.filter fun k => w k = w i0).card = 4 := by
    have hwi : w i0 = 1 ∨ w i0 = -1 := ggQ2xA_eq_one_or_neg_one (hwt4_full i0)
    rcases hwi with hwi | hwi
    · have heq : (Finset.univ.filter fun k => w k = w i0) =
          Finset.univ.filter fun k => w k = 1 := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hwi]
      rw [heq, hwt4_one]
    · have heq : (Finset.univ.filter fun k => w k = w i0) =
          Finset.univ.filter fun k => w k = -1 := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hwi]
      rw [heq, hwt4_neg]
  obtain ⟨k0, hk0mem, hk0not⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i0} : Finset (Fin m))) (t := Finset.univ.filter fun k => w k = w i0)
    (by rw [Finset.card_singleton, hzeros_card]; omega)
  have hk0_eq : w k0 = w i0 := (Finset.mem_filter.mp hk0mem).2
  have hk0_ne : k0 ≠ i0 := by simpa using hk0not
  have hzero0 : (ggBCRefl z hz0ne w) k0 = 0 := by
    rw [hs_apply, if_neg hk0_ne, hk0_eq]
    exact sub_self _
  have hmem : ggBCRefl z hz0ne w ∈ Z := hZcl z hzZ w hwZ hz0ne
  have hA2 := ggQ2xA_zero_coord_root m hm Z hZ0 hZsum hZroots hZcl hHL hmem ⟨k0, hzero0⟩
  rw [hwt5] at hA2
  omega

private def ggQ2xA_flip {m : ℕ} (S : Finset (Fin m)) (w : GGBCV m) : GGBCV m :=
  fun j => if j ∈ S then -w j else w j

private lemma ggQ2xA_flip_apply_of_mem {m : ℕ} {S : Finset (Fin m)} {w : GGBCV m}
    {j : Fin m} (h : j ∈ S) : ggQ2xA_flip S w j = -w j := by
  unfold ggQ2xA_flip; rw [if_pos h]

private lemma ggQ2xA_flip_apply_of_notMem {m : ℕ} {S : Finset (Fin m)} {w : GGBCV m}
    {j : Fin m} (h : j ∉ S) : ggQ2xA_flip S w j = w j := by
  unfold ggQ2xA_flip; rw [if_neg h]

private lemma ggQ2xA_flip_full {m : ℕ} {S : Finset (Fin m)} {w : GGBCV m}
    (hw : ∀ j, w j ≠ 0) : ∀ j, ggQ2xA_flip S w j ≠ 0 := by
  intro j
  by_cases h : j ∈ S
  · rw [ggQ2xA_flip_apply_of_mem h]; exact neg_ne_zero.mpr (hw j)
  · rw [ggQ2xA_flip_apply_of_notMem h]; exact hw j

private lemma ggQ2xA_flip_flip {m : ℕ} {S T : Finset (Fin m)} {w : GGBCV m}
    (h : Disjoint S T) : ggQ2xA_flip S (ggQ2xA_flip T w) = ggQ2xA_flip (S ∪ T) w := by
  funext j
  by_cases hjS : j ∈ S
  · have hjT : j ∉ T := fun hj => (Finset.disjoint_left.mp h) hjS hj
    rw [ggQ2xA_flip_apply_of_mem hjS, ggQ2xA_flip_apply_of_notMem hjT,
      ggQ2xA_flip_apply_of_mem (Finset.mem_union_left T hjS)]
  · by_cases hjT : j ∈ T
    · rw [ggQ2xA_flip_apply_of_notMem hjS, ggQ2xA_flip_apply_of_mem hjT,
        ggQ2xA_flip_apply_of_mem (Finset.mem_union_right S hjT)]
    · rw [ggQ2xA_flip_apply_of_notMem hjS, ggQ2xA_flip_apply_of_notMem hjT,
        ggQ2xA_flip_apply_of_notMem (by
          intro hmem
          rcases Finset.mem_union.mp hmem with h' | h'
          · exact hjS h'
          · exact hjT h')]

private lemma ggQ2xA_pair_disjoint {m : ℕ} {a b c d : Fin m}
    (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c) (h4 : b ≠ d) :
    Disjoint ({a, b} : Finset (Fin m)) ({c, d} : Finset (Fin m)) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj1 hj2
  rcases hj1 with rfl | rfl <;> rcases hj2 with h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

private lemma ggQ2xA_refl_root_eq_flip {m : ℕ} (w : GGBCV m) {a b : Fin m}
    (hab : a ≠ b) (ha : w a = 1) (hb : w b = -1)
    (hrho : (Pi.single a 1 - Pi.single b 1 : GGBCV m)
      ⬝ᵥ (Pi.single a 1 - Pi.single b 1) ≠ 0) :
    ggBCRefl (Pi.single a 1 - Pi.single b 1 : GGBCV m) hrho w
      = ggQ2xA_flip ({a, b} : Finset (Fin m)) w := by
  have h1 : (Pi.single a 1 - Pi.single b 1 : GGBCV m) ⬝ᵥ w = 2 := by
    rw [ggQ2x_sub_single_dot, ha, hb]; decide
  have h2 : (Pi.single a 1 - Pi.single b 1 : GGBCV m)
      ⬝ᵥ (Pi.single a 1 - Pi.single b 1) = 2 := ggQ2x_sub_single_norm a b hab
  funext j
  rw [ggQ2x_ggBCRefl_apply, h1, h2, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
  by_cases hj : j ∈ ({a, b} : Finset (Fin m))
  · rw [ggQ2xA_flip_apply_of_mem hj]
    have hj' : j = a ∨ j = b := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
    rcases hj' with rfl | rfl
    · rw [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab, ha]
      decide
    · rw [Pi.add_apply, Pi.sub_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab),
        Pi.single_eq_same, hb]
      decide
  · rw [ggQ2xA_flip_apply_of_notMem hj]
    have hja : j ≠ a := by
      intro h; apply hj; rw [h]; exact Finset.mem_insert_self a {b}
    have hjb : j ≠ b := by
      intro h; apply hj; rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [Pi.add_apply, Pi.sub_apply,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hja,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjb]
    simp

private lemma ggQ2xA_refl_root_add {m : ℕ} (w : GGBCV m) {a b : Fin m}
    (hab : a ≠ b) (ha : w a = 1) (hb : w b = -1)
    (hrho : (Pi.single a 1 - Pi.single b 1 : GGBCV m)
      ⬝ᵥ (Pi.single a 1 - Pi.single b 1) ≠ 0) :
    ggBCRefl (Pi.single a 1 - Pi.single b 1 : GGBCV m) hrho w
      = w + (Pi.single a 1 - Pi.single b 1 : GGBCV m) := by
  have h1 : (Pi.single a 1 - Pi.single b 1 : GGBCV m) ⬝ᵥ w = 2 := by
    rw [ggQ2x_sub_single_dot, ha, hb]; decide
  have h2 : (Pi.single a 1 - Pi.single b 1 : GGBCV m)
      ⬝ᵥ (Pi.single a 1 - Pi.single b 1) = 2 := ggQ2x_sub_single_norm a b hab
  rw [ggQ2x_ggBCRefl_apply, h1, h2, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]

private lemma ggQ2xA_eq_of_add_neg_eq_zero (a b : ZMod 3) (h : a + -b = 0) : a = b := by
  revert a b; decide

private lemma ggQ2xA_mul_neg_one (x : ZMod 3) : x * -1 = -x := by revert x; decide

private lemma ggQ2xA_two_mul_eq_two (x : ZMod 3) (h : 2 * x = 2) : x = 1 := by
  revert x; decide

private lemma ggQ2xA_full_support_classify (m : ℕ) [NeZero m] (hm : 6 ≤ m) (h3 : m % 3 ≠ 0)
    (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0)
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m)
    {z : GGBCV m} (hz : z ∈ Z) (hfull : ∀ i, z i ≠ 0) :
    (m % 3 = 2 ∧ ggAType1 z) ∨ (m = 8 ∧ ggAType4 z) := by
  have hm2 : m % 3 = 2 :=
    ggQ2xA_full_support_mod3 m hm h3 Z hZ0 hZsum hZroots hZcl hHL hz hfull
  have hz0 : z ⬝ᵥ z ≠ 0 := hZ0 z hz
  let S1 : Finset (Fin m) := Finset.univ.filter fun k => z k = 1
  let S2 : Finset (Fin m) := Finset.univ.filter fun k => z k = -1
  have hS1mem : ∀ i, i ∈ S1 ↔ z i = 1 := by intro i; simp [S1]
  have hS2mem : ∀ i, i ∈ S2 ↔ z i = -1 := by intro i; simp [S2]
  have hS1v : ∀ i ∈ S1, z i = 1 := fun i hi => (hS1mem i).mp hi
  have hS2v : ∀ i ∈ S2, z i = -1 := fun i hi => (hS2mem i).mp hi
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 := hS1v i hi1
    have h2 := hS2v i hi2
    rw [h1] at h2
    exact (by decide : (1 : ZMod 3) ≠ -1) h2
  have hcover : S1 ∪ S2 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    rw [Finset.mem_union]
    rcases ggQ2xA_eq_one_or_neg_one (hfull i) with h | h
    · exact Or.inl ((hS1mem i).mpr h)
    · exact Or.inr ((hS2mem i).mpr h)
  have hcard : S1.card + S2.card = m := by
    have h := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hS1sum : (∑ i ∈ S1, z i) = (S1.card : ZMod 3) := by
    rw [Finset.sum_congr rfl (fun i hi => hS1v i hi)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hS2sum : (∑ i ∈ S2, z i) = -(S2.card : ZMod 3) := by
    rw [Finset.sum_congr rfl (fun i hi => hS2v i hi)]
    rw [Finset.sum_const, nsmul_eq_mul, ggQ2xA_mul_neg_one]
  have htotal : (∑ i ∈ S1, z i) + (∑ i ∈ S2, z i) = 0 := by
    rw [← Finset.sum_union hdisj, hcover]
    simpa using hZsum z hz
  have heq : (S1.card : ZMod 3) = (S2.card : ZMod 3) := by
    have h := htotal
    rw [hS1sum, hS2sum] at h
    exact ggQ2xA_eq_of_add_neg_eq_zero _ _ h
  have heqsum : (S1.card : ZMod 3) + (S2.card : ZMod 3) = (m : ZMod 3) := by
    rw [← Nat.cast_add, hcard]
  have hdouble : (S1.card : ZMod 3) + (S1.card : ZMod 3) = 2 := by
    have h := heqsum
    rw [← heq] at h
    rw [ggQ2xA_natCast_eq_two hm2] at h
    exact h
  have hk1 : (S1.card : ZMod 3) = 1 := by
    have h2c : (2 : ZMod 3) * (S1.card : ZMod 3) = 2 := by
      rw [two_mul]; exact hdouble
    exact ggQ2xA_two_mul_eq_two _ h2c
  have hk1mod : S1.card % 3 = 1 := by
    have hv := congrArg ZMod.val hk1
    rw [ZMod.val_natCast] at hv
    have hv1 : ZMod.val (1 : ZMod 3) = 1 := by decide
    omega
  have hS2card1 : (S2.card : ZMod 3) = 1 := by rw [← heq]; exact hk1
  have hl1mod : S2.card % 3 = 1 := by
    have hv := congrArg ZMod.val hS2card1
    rw [ZMod.val_natCast] at hv
    have hv1 : ZMod.val (1 : ZMod 3) = 1 := by decide
    omega
  by_cases hA : 4 ≤ S1.card ∧ 4 ≤ S2.card
  · obtain ⟨hk4, hl4⟩ := hA
    obtain ⟨T1, hT1sub, hT1card⟩ :=
      Finset.exists_subset_card_eq (s := S1) (n := 3) (by omega)
    obtain ⟨a1, a2, a3, ha12, ha13, ha23, hT1eq⟩ := Finset.card_eq_three.mp hT1card
    obtain ⟨T2, hT2sub, hT2card⟩ :=
      Finset.exists_subset_card_eq (s := S2) (n := 3) (by omega)
    obtain ⟨b1, b2, b3, hb12, hb13, hb23, hT2eq⟩ := Finset.card_eq_three.mp hT2card
    have ha1S1 : a1 ∈ S1 := by apply hT1sub; rw [hT1eq]; simp
    have ha2S1 : a2 ∈ S1 := by apply hT1sub; rw [hT1eq]; simp
    have ha3S1 : a3 ∈ S1 := by apply hT1sub; rw [hT1eq]; simp
    have hb1S2 : b1 ∈ S2 := by apply hT2sub; rw [hT2eq]; simp
    have hb2S2 : b2 ∈ S2 := by apply hT2sub; rw [hT2eq]; simp
    have hb3S2 : b3 ∈ S2 := by apply hT2sub; rw [hT2eq]; simp
    have ha1z : z a1 = 1 := hS1v a1 ha1S1
    have ha2z : z a2 = 1 := hS1v a2 ha2S1
    have ha3z : z a3 = 1 := hS1v a3 ha3S1
    have hb1z : z b1 = -1 := hS2v b1 hb1S2
    have hb2z : z b2 = -1 := hS2v b2 hb2S2
    have hb3z : z b3 = -1 := hS2v b3 hb3S2
    have hcross : ∀ {i j : Fin m}, i ∈ S1 → j ∈ S2 → i ≠ j := by
      intro i j hi hj hij
      have hi1 := hS1v i hi
      have hj1 := hS2v j hj
      rw [← hij, hi1] at hj1
      exact (by decide : (1 : ZMod 3) ≠ -1) hj1
    have hab1 : a1 ≠ b1 := hcross ha1S1 hb1S2
    have hab2 : a2 ≠ b2 := hcross ha2S1 hb2S2
    have hab3 : a3 ≠ b3 := hcross ha3S1 hb3S2
    have ha2a1 : a2 ≠ a1 := (ha12).symm
    have ha3a1 : a3 ≠ a1 := (ha13).symm
    have ha3a2 : a3 ≠ a2 := (ha23).symm
    have hb2b1 : b2 ≠ b1 := (hb12).symm
    have hb3b1 : b3 ≠ b1 := (hb13).symm
    have hb3b2 : b3 ≠ b2 := (hb23).symm
    have ha2b1 : a2 ≠ b1 := hcross ha2S1 hb1S2
    have ha3b1 : a3 ≠ b1 := hcross ha3S1 hb1S2
    have ha3b2 : a3 ≠ b2 := hcross ha3S1 hb2S2
    have hb2a1 : b2 ≠ a1 := (hcross ha1S1 hb2S2).symm
    have hb3a1 : b3 ≠ a1 := (hcross ha1S1 hb3S2).symm
    have hb3a2 : b3 ≠ a2 := (hcross ha2S1 hb3S2).symm
    set S1f : Finset (Fin m) := {a1, b1} with hS1f
    set S2f : Finset (Fin m) := {a2, b2} with hS2f
    set S3f : Finset (Fin m) := {a3, b3} with hS3f
    set T : Finset (Fin m) := S3f ∪ (S2f ∪ S1f) with hT
    have hdisj21 : Disjoint S2f S1f := by
      rw [hS2f, hS1f]
      exact ggQ2xA_pair_disjoint ha2a1 ha2b1 hb2a1 hb2b1
    have hdisj321 : Disjoint S3f (S2f ∪ S1f) := by
      rw [hS3f, hS2f, hS1f, Finset.disjoint_union_right]
      exact ⟨ggQ2xA_pair_disjoint ha3a2 ha3b2 hb3a2 hb3b2,
        ggQ2xA_pair_disjoint ha3a1 ha3b1 hb3a1 hb3b1⟩
    have hcard21 : (S2f ∪ S1f).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj21, hS2f, hS1f,
        Finset.card_pair hab2, Finset.card_pair hab1]
    have hTcard : T.card = 6 := by
      rw [hT, Finset.card_union_of_disjoint hdisj321, hcard21, hS3f,
        Finset.card_pair hab3]
    have hrho1ne : (Pi.single a1 1 - Pi.single b1 1 : GGBCV m)
        ⬝ᵥ (Pi.single a1 1 - Pi.single b1 1) ≠ 0 := by
      rw [ggQ2x_sub_single_norm a1 b1 hab1]; decide
    have hrho1root : (Pi.single a1 1 - Pi.single b1 1 : GGBCV m) ∈ ggARoots m := by
      refine ⟨?_, ?_⟩
      · rw [ggQ2x_wt_sub_single a1 b1 hab1]
      · rw [ggQ2xA_sum_sub_single]
    have hrho2ne : (Pi.single a2 1 - Pi.single b2 1 : GGBCV m)
        ⬝ᵥ (Pi.single a2 1 - Pi.single b2 1) ≠ 0 := by
      rw [ggQ2x_sub_single_norm a2 b2 hab2]; decide
    have hrho2root : (Pi.single a2 1 - Pi.single b2 1 : GGBCV m) ∈ ggARoots m := by
      refine ⟨?_, ?_⟩
      · rw [ggQ2x_wt_sub_single a2 b2 hab2]
      · rw [ggQ2xA_sum_sub_single]
    have hrho3ne : (Pi.single a3 1 - Pi.single b3 1 : GGBCV m)
        ⬝ᵥ (Pi.single a3 1 - Pi.single b3 1) ≠ 0 := by
      rw [ggQ2x_sub_single_norm a3 b3 hab3]; decide
    have hrho3root : (Pi.single a3 1 - Pi.single b3 1 : GGBCV m) ∈ ggARoots m := by
      refine ⟨?_, ?_⟩
      · rw [ggQ2x_wt_sub_single a3 b3 hab3]
      · rw [ggQ2xA_sum_sub_single]
    set w1 : GGBCV m :=
      ggBCRefl (Pi.single a1 1 - Pi.single b1 1 : GGBCV m) hrho1ne z with hw1
    have hz1flip : w1 = ggQ2xA_flip S1f z := by
      rw [hw1, ggQ2xA_refl_root_eq_flip z hab1 ha1z hb1z hrho1ne, hS1f]
    have hz1Z : w1 ∈ Z := by
      rw [hw1]; exact hZcl _ (hZroots hrho1root) z hz hrho1ne
    have ha2S1f : a2 ∉ S1f := by
      rw [hS1f]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha2a1, ha2b1⟩
    have hb2S1f : b2 ∉ S1f := by
      rw [hS1f]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hb2a1, hb2b1⟩
    have ha3S1f : a3 ∉ S1f := by
      rw [hS1f]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha3a1, ha3b1⟩
    have hb3S1f : b3 ∉ S1f := by
      rw [hS1f]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hb3a1, hb3b1⟩
    have hz1a2 : w1 a2 = 1 := by
      rw [hz1flip, ggQ2xA_flip_apply_of_notMem ha2S1f]; exact ha2z
    have hz1b2 : w1 b2 = -1 := by
      rw [hz1flip, ggQ2xA_flip_apply_of_notMem hb2S1f]; exact hb2z
    have hz1a3 : w1 a3 = 1 := by
      rw [hz1flip, ggQ2xA_flip_apply_of_notMem ha3S1f]; exact ha3z
    have hz1b3 : w1 b3 = -1 := by
      rw [hz1flip, ggQ2xA_flip_apply_of_notMem hb3S1f]; exact hb3z
    set w2 : GGBCV m :=
      ggBCRefl (Pi.single a2 1 - Pi.single b2 1 : GGBCV m) hrho2ne w1 with hw2
    have hz2flip : w2 = ggQ2xA_flip S2f w1 := by
      rw [hw2, ggQ2xA_refl_root_eq_flip w1 hab2 hz1a2 hz1b2 hrho2ne, hS2f]
    have hz2Z : w2 ∈ Z := by
      rw [hw2]; exact hZcl _ (hZroots hrho2root) w1 hz1Z hrho2ne
    have ha3S2f : a3 ∉ S2f := by
      rw [hS2f]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha3a2, ha3b2⟩
    have hb3S2f : b3 ∉ S2f := by
      rw [hS2f]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hb3a2, hb3b2⟩
    have hz2a3 : w2 a3 = 1 := by
      rw [hz2flip, ggQ2xA_flip_apply_of_notMem ha3S2f]; exact hz1a3
    have hz2b3 : w2 b3 = -1 := by
      rw [hz2flip, ggQ2xA_flip_apply_of_notMem hb3S2f]; exact hz1b3
    set w3 : GGBCV m :=
      ggBCRefl (Pi.single a3 1 - Pi.single b3 1 : GGBCV m) hrho3ne w2 with hw3
    have hz3flip : w3 = ggQ2xA_flip S3f w2 := by
      rw [hw3, ggQ2xA_refl_root_eq_flip w2 hab3 hz2a3 hz2b3 hrho3ne, hS3f]
    have hz3Z : w3 ∈ Z := by
      rw [hw3]; exact hZcl _ (hZroots hrho3root) w2 hz2Z hrho3ne
    have hz3T : w3 = ggQ2xA_flip T z := by
      rw [hz3flip, hz2flip, hz1flip, ggQ2xA_flip_flip hdisj21,
        ggQ2xA_flip_flip hdisj321, ← hT]
    have hz1add : w1 = z + (Pi.single a1 1 - Pi.single b1 1 : GGBCV m) := by
      rw [hw1]; exact ggQ2xA_refl_root_add z hab1 ha1z hb1z hrho1ne
    have hz2add : w2 = w1 + (Pi.single a2 1 - Pi.single b2 1 : GGBCV m) := by
      rw [hw2]; exact ggQ2xA_refl_root_add w1 hab2 hz1a2 hz1b2 hrho2ne
    have hz3add : w3 = w2 + (Pi.single a3 1 - Pi.single b3 1 : GGBCV m) := by
      rw [hw3]; exact ggQ2xA_refl_root_add w2 hab3 hz2a3 hz2b3 hrho3ne
    have hz3add' : w3 = z + (Pi.single a1 1 - Pi.single b1 1 : GGBCV m)
        + (Pi.single a2 1 - Pi.single b2 1 : GGBCV m)
        + (Pi.single a3 1 - Pi.single b3 1 : GGBCV m) := by
      rw [hz3add, hz2add, hz1add]
    have hz_e1 : z ⬝ᵥ (Pi.single a1 1 - Pi.single b1 1 : GGBCV m) = 2 := by
      rw [dotProduct_comm, ggQ2x_sub_single_dot, ha1z, hb1z]; decide
    have hz_e2 : z ⬝ᵥ (Pi.single a2 1 - Pi.single b2 1 : GGBCV m) = 2 := by
      rw [dotProduct_comm, ggQ2x_sub_single_dot, ha2z, hb2z]; decide
    have hz_e3 : z ⬝ᵥ (Pi.single a3 1 - Pi.single b3 1 : GGBCV m) = 2 := by
      rw [dotProduct_comm, ggQ2x_sub_single_dot, ha3z, hb3z]; decide
    have hz_z3 : z ⬝ᵥ w3 = 2 := by
      rw [hz3add', dotProduct_add, dotProduct_add, dotProduct_add,
        ggQ2xA_dot_self_full hfull, ggQ2xA_natCast_eq_two hm2, hz_e1, hz_e2, hz_e3]
      decide
    have hrefl : ggBCRefl z hz0 w3 = w3 + z := by
      rw [ggQ2x_ggBCRefl_apply, hz_z3, ggQ2xA_dot_self_full hfull,
        ggQ2xA_natCast_eq_two hm2, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
    have hsumZ : w3 + z ∈ Z := by
      rw [← hrefl]; exact hZcl z hz w3 hz3Z hz0
    have hsupp : (Finset.univ.filter fun j => (w3 + z) j ≠ 0) = Finset.univ \ T := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · intro hj hmem
        exact hj (by
          rw [Pi.add_apply, hz3T, ggQ2xA_flip_apply_of_mem hmem]
          exact neg_add_cancel (z j))
      · intro hmem
        rw [Pi.add_apply, hz3T, ggQ2xA_flip_apply_of_notMem hmem, ← two_mul]
        exact mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hfull j)
    have hwt : ggBCWt (w3 + z) = m - 6 := by
      unfold ggBCWt
      rw [hsupp, Finset.card_sdiff_of_subset (Finset.subset_univ T)]
      rw [Finset.card_univ, Fintype.card_fin, hTcard]
    have hzero : ∃ i, (w3 + z) i = 0 := by
      refine ⟨a1, ?_⟩
      have hmem : a1 ∈ T := by
        rw [hT]
        exact Finset.mem_union_right S3f
          (Finset.mem_union_right S2f (by rw [hS1f]; exact Finset.mem_insert_self a1 {b1}))
      rw [Pi.add_apply, hz3T, ggQ2xA_flip_apply_of_mem hmem, ha1z]
      decide
    have hwt2 := ggQ2xA_zero_coord_root m hm Z hZ0 hZsum hZroots hZcl hHL hsumZ hzero
    rw [hwt] at hwt2
    have hm8 : m = 8 := by omega
    right
    refine ⟨hm8, hfull, ?_, ?_⟩
    · have h4 : S1.card = 4 := by omega
      simpa [S1] using h4
    · have h4 : S2.card = 4 := by omega
      simpa [S2] using h4
  · push Not at hA
    left
    refine ⟨hm2, ?_⟩
    by_cases hk : S1.card ≤ 3
    · have hk1c : S1.card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hk1c
      refine ⟨-1, by decide, i, ?_, ?_⟩
      · have hi1 : z i = 1 := by
          have him : i ∈ S1 := by rw [hi]; exact Finset.mem_singleton_self i
          exact hS1v i him
        rw [hi1]; decide
      · intro j hj
        have hzj : z j ≠ 1 := by
          intro h
          have hjm : j ∈ S1 := (hS1mem j).mpr h
          rw [hi, Finset.mem_singleton] at hjm
          exact hj hjm
        rcases ggQ2xA_eq_one_or_neg_one (hfull j) with h | h
        · exact absurd h hzj
        · exact h
    · have hk4 : 4 ≤ S1.card := by omega
      have hl : S2.card ≤ 3 := by have h := hA hk4; omega
      have hl1c : S2.card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hl1c
      refine ⟨1, by decide, i, ?_, ?_⟩
      · have hi1 : z i = -1 := by
          have him : i ∈ S2 := by rw [hi]; exact Finset.mem_singleton_self i
          exact hS2v i him
        exact hi1
      · intro j hj
        have hzj : z j ≠ -1 := by
          intro h
          have hjm : j ∈ S2 := (hS2mem j).mpr h
          rw [hi, Finset.mem_singleton] at hjm
          exact hj hjm
        rcases ggQ2xA_eq_one_or_neg_one (hfull j) with h | h
        · exact h
        · exact absurd h hzj

theorem ggQ2_A_Z (m : ℕ) [NeZero m] (hm : 6 ≤ m) (h3 : m % 3 ≠ 0) (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0) (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m) :
    (∀ z ∈ Z, z ∈ ggARoots m ∨ (m % 3 = 2 ∧ ggAType1 z) ∨ (m = 8 ∧ ggAType4 z)) ∧
      ¬ ((∃ z ∈ Z, ggAType1 z) ∧ (∃ w ∈ Z, ggAType4 w)) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    by_cases hzero : ∃ i, z i = 0
    · left
      have hwt : ggBCWt z = 2 :=
        ggQ2xA_zero_coord_root m hm Z hZ0 hZsum hZroots hZcl hHL hz hzero
      exact ⟨hwt, hZsum z hz⟩
    · right
      push Not at hzero
      exact ggQ2xA_full_support_classify m hm h3 Z hZ0 hZsum hZroots hZcl hHL hz hzero
  · exact ggQ2xA_not_both m hm h3 Z hZ0 hZsum hZroots hZcl hHL

theorem ggQ2_A_Z_II (m : ℕ) [NeZero m] (hm : 6 ≤ m) (h3 : m % 3 = 0) (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZsum : ∀ z ∈ Z, ∑ i, z i = 0) (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 m) :
    ∀ z ∈ Z, z ∈ ggARoots m := by
  intro z hz
  by_cases hzero : ∃ i, z i = 0
  · exact ⟨ggQ2xA_zero_coord_root m hm Z hZ0 hZsum hZroots hZcl hHL hz hzero, hZsum z hz⟩
  · exfalso
    push Not at hzero
    exact hZ0 z hz (by rw [ggQ2xA_dot_self_full hzero, ggQ2xA_natCast_eq_zero h3])

end CFSG.StandardType

end
