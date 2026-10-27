module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

lemma ggQ2x_two_div_neg (d : ZMod 3) (hd : d ≠ 0) : (2 : ZMod 3) / d = -d := by
  have hdd : d * d = 1 := by revert d; decide
  have hinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [div_eq_mul_inv, hinv, h2]
  exact neg_one_mul d

lemma ggQ2x_scalar_refl (d x y z : ZMod 3) (hd : d ≠ 0) :
    x - ((2 / d) * y) * z = x + (y * d) * z := by
  rw [ggQ2x_two_div_neg d hd]
  exact (by decide : ∀ d x y z : ZMod 3, x - (-d * y) * z = x + (y * d) * z) d x y z

lemma ggQ2x_mul_self_eq_one (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  revert hx; revert x; decide

lemma ggQ2x_scalar_a (x y : ZMod 3) : x + (x - y) * 2 = y := by revert x y; decide

lemma ggQ2x_scalar_b (x y : ZMod 3) : y + (x - y) * 2 * (-1) = x := by revert x y; decide

lemma ggQ2x_ggBCDot_apply {n : ℕ} (c v : GGBCV n) : ggBCDot c v = c ⬝ᵥ v := by
  simp only [ggBCDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rfl

lemma ggQ2x_ggBCRefl_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  funext j
  unfold ggBCRefl
  change (v - (((2 / (c ⬝ᵥ c)) • ggBCDot c) v) • c) j
      = (v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c) j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply,
    ggQ2x_ggBCDot_apply]
  exact ggQ2x_scalar_refl (c ⬝ᵥ c) (v j) (c ⬝ᵥ v) (c j) hc

lemma ggQ2x_dot_self_eq_wt {n : ℕ} (v : GGBCV n) : v ⬝ᵥ v = (ggBCWt v : ZMod 3) := by
  have hsq : ∀ x : ZMod 3, x * x = if x = 0 then 0 else 1 := by decide
  simp only [ggBCWt]
  rw [Finset.natCast_card_filter]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsq]
  by_cases h : v i = 0 <;> simp [h]

lemma ggQ2x_wt_eq_of_full {n : ℕ} {v : GGBCV n} (hv : ∀ i, v i ≠ 0) : ggBCWt v = n := by
  unfold ggBCWt
  rw [Finset.filter_true_of_mem (fun i _ => hv i)]
  simp [Fintype.card_fin]

lemma ggQ2x_wt_single {n : ℕ} (i : Fin n) :
    ggBCWt (Pi.single i (1 : ZMod 3) : GGBCV n) = 1 := by
  unfold ggBCWt
  have hset : Finset.univ.filter (fun j => (Pi.single i (1 : ZMod 3) : GGBCV n) j ≠ 0)
      = {i} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      by_contra hji
      exact h (Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji (1 : ZMod 3))
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simp⟩
  rw [hset, Finset.card_singleton]

lemma ggQ2x_wt_sub_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ggBCWt (Pi.single a 1 - Pi.single b 1 : GGBCV n) = 2 := by
  unfold ggBCWt
  have hset : Finset.univ.filter
      (fun j => (Pi.single a 1 - Pi.single b 1 : GGBCV n) j ≠ 0) = {a, b} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨hja, hjb⟩ := hcon
      exact h (by rw [Pi.sub_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hja,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjb, sub_self])
    · rintro (rfl | rfl)
      · refine ⟨Finset.mem_univ _, ?_⟩
        rw [Pi.sub_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab]
        decide
      · refine ⟨Finset.mem_univ _, ?_⟩
        rw [Pi.sub_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab)]
        decide
  rw [hset, Finset.card_pair hab]

lemma ggQ2x_sub_single_apply_same {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (Pi.single a 1 - Pi.single b 1 : GGBCV n) a = 1 := by
  rw [Pi.sub_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab]
  decide

lemma ggQ2x_sub_single_apply_other {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (Pi.single a 1 - Pi.single b 1 : GGBCV n) b = -1 := by
  rw [Pi.sub_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab)]
  decide

lemma ggQ2x_sub_single_apply_of_ne {n : ℕ} (a b j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) :
    (Pi.single a 1 - Pi.single b 1 : GGBCV n) j = 0 := by
  rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hja,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjb, sub_self]

lemma ggQ2x_wt_single_add_single {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (c0 c1 : ZMod 3) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) :
    ggBCWt (Pi.single a c0 + Pi.single b c1 : GGBCV n) = 2 := by
  unfold ggBCWt
  have hset : Finset.univ.filter
      (fun j => (Pi.single a c0 + Pi.single b c1 : GGBCV n) j ≠ 0) = {a, b} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨hja, hjb⟩ := hcon
      exact h (by rw [Pi.add_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hja,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjb, add_zero])
    · rintro (rfl | rfl)
      · refine ⟨Finset.mem_univ _, ?_⟩
        rw [Pi.add_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab, add_zero]
        exact hc0
      · refine ⟨Finset.mem_univ _, ?_⟩
        rw [Pi.add_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab), zero_add]
        exact hc1
  rw [hset, Finset.card_pair hab]

lemma ggQ2x_wt_smul_single_add_single {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (c0 c1 : ZMod 3) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) :
    ggBCWt (c0 • (Pi.single a 1 : GGBCV n) + c1 • (Pi.single b 1 : GGBCV n)) = 2 := by
  have h : c0 • (Pi.single a 1 : GGBCV n) + c1 • (Pi.single b 1 : GGBCV n)
      = Pi.single a c0 + Pi.single b c1 := by
    rw [← Pi.single_smul, ← Pi.single_smul]; simp
  rw [h]
  exact ggQ2x_wt_single_add_single a b hab c0 c1 hc0 hc1

lemma ggQ2x_wt_comp_swap {n : ℕ} (a b : Fin n) (v : GGBCV n) :
    ggBCWt (fun j => v (Equiv.swap a b j)) = ggBCWt v := by
  unfold ggBCWt
  refine Finset.card_bij (fun j _ => Equiv.swap a b j) ?_ ?_ ?_
  · intro j hj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · intro j1 _ j2 _ heq
    exact (Equiv.swap a b).injective heq
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨Equiv.swap a b k, by simpa using hk, by simp⟩

lemma ggQ2x_sub_single_dot {n : ℕ} (a b : Fin n) (v : GGBCV n) :
    (Pi.single a 1 - Pi.single b 1 : GGBCV n) ⬝ᵥ v = v a - v b := by
  rw [sub_dotProduct, single_one_dotProduct, single_one_dotProduct]

lemma ggQ2x_sub_single_norm {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (Pi.single a 1 - Pi.single b 1 : GGBCV n) ⬝ᵥ (Pi.single a 1 - Pi.single b 1) = 2 := by
  rw [ggQ2x_sub_single_dot]
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab,
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab), sub_zero, zero_sub]
  decide

lemma ggQ2x_refl_sub_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) (v : GGBCV n)
    (hc : (Pi.single a 1 - Pi.single b 1 : GGBCV n) ⬝ᵥ (Pi.single a 1 - Pi.single b 1) ≠ 0) :
    ggBCRefl (Pi.single a 1 - Pi.single b 1) hc v = fun j => v (Equiv.swap a b j) := by
  funext j
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_sub_single_dot, ggQ2x_sub_single_norm a b hab]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hja : j = a
  · rw [hja, Equiv.swap_apply_left, ggQ2x_sub_single_apply_same a b hab, mul_one]
    exact ggQ2x_scalar_a (v a) (v b)
  · by_cases hjb : j = b
    · rw [hjb, Equiv.swap_apply_right, ggQ2x_sub_single_apply_other a b hab]
      exact ggQ2x_scalar_b (v a) (v b)
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb,
        ggQ2x_sub_single_apply_of_ne a b j hja hjb, mul_zero, add_zero]






lemma ggQ2x_zero_coord_is_root {n : ℕ} [NeZero n] (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggBCRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggBCRootsLam1 n)
    {z : GGBCV n} (hz : z ∈ Z) (hzero : ∃ m, z m = 0) :
    z ∈ ggBCRoots n := by
  obtain ⟨m, hm⟩ := hzero
  have hz' : ∃ z' ∈ Z, z' 0 = 0 ∧ ggBCWt z' = ggBCWt z := by
    by_cases hm0 : m = 0
    · exact ⟨z, hz, by simpa [hm0] using hm, rfl⟩
    · have h0m : (0 : Fin n) ≠ m := fun h => hm0 h.symm
      have hc_ne : (Pi.single 0 1 - Pi.single m 1 : GGBCV n)
          ⬝ᵥ (Pi.single 0 1 - Pi.single m 1) ≠ 0 := by
        rw [ggQ2x_sub_single_norm 0 m h0m]; decide
      have hc_root : (Pi.single 0 1 - Pi.single m 1 : GGBCV n) ∈ ggBCRoots n := by
        refine ⟨?_, ?_⟩ <;> rw [ggQ2x_wt_sub_single 0 m h0m] <;> norm_num
      have hcZ : (Pi.single 0 1 - Pi.single m 1 : GGBCV n) ∈ Z := hZroots hc_root
      refine ⟨ggBCRefl (Pi.single 0 1 - Pi.single m 1) hc_ne z,
        hZcl _ hcZ z hz hc_ne, ?_, ?_⟩
      · rw [ggQ2x_refl_sub_single 0 m h0m z hc_ne]
        change z (Equiv.swap 0 m 0) = 0
        rw [Equiv.swap_apply_left]
        exact hm
      · rw [ggQ2x_refl_sub_single 0 m h0m z hc_ne]
        exact ggQ2x_wt_comp_swap 0 m z
  obtain ⟨z', hz'Z, hz'0, hwt⟩ := hz'
  have hz_ne : ggBCWt z ≠ 0 := by
    intro h0
    have h := hZ0 z hz
    rw [ggQ2x_dot_self_eq_wt, h0] at h
    exact h rfl
  refine ⟨by omega, ?_⟩
  by_contra hle
  push Not at hle
  have hle' : 2 < ggBCWt z' := by omega
  have hz'3 : ggBCWt z' ≠ 3 := by
    intro h3
    have h := hZ0 z' hz'Z
    rw [ggQ2x_dot_self_eq_wt, h3] at h
    exact h rfl
  have hz'4 : 4 ≤ ggBCWt z' := by omega
  have hsupp : (Finset.univ.filter (fun i => z' i ≠ 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have : ggBCWt z' = 0 := by simp [ggBCWt, he]
    omega
  obtain ⟨i, hi⟩ := hsupp
  have hzi : z' i ≠ 0 := (Finset.mem_filter.mp hi).2
  have hi0 : i ≠ 0 := by
    intro h
    exact hzi (by rw [h]; exact hz'0)
  have hρroot : (Pi.single i (1 : ZMod 3) : GGBCV n) ∈ ggBCRoots n := by
    refine ⟨?_, ?_⟩ <;> rw [ggQ2x_wt_single] <;> norm_num
  have hρlam : (Pi.single i (1 : ZMod 3) : GGBCV n) ∈ ggBCRootsLam1 n :=
    ⟨hρroot, by rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hi0)]⟩
  have hz'dot : z' ⬝ᵥ z' ≠ 0 := hZ0 z' hz'Z
  have hs := hHL z' hz'Z hz'0 (Pi.single i (1 : ZMod 3)) hρlam hz'dot
  have hsle : ggBCWt (ggBCRefl z' hz'dot (Pi.single i (1 : ZMod 3))) ≤ 2 := hs.1.2
  have hlow : ggBCWt z' - 1 ≤
      ggBCWt (ggBCRefl z' hz'dot (Pi.single i (1 : ZMod 3))) := by
    have hcard : ((Finset.univ.filter (fun j => z' j ≠ 0)).erase i).card = ggBCWt z' - 1 := by
      rw [Finset.card_erase_of_mem hi]
      rfl
    have hsub : (Finset.univ.filter (fun j => z' j ≠ 0)).erase i ⊆
        Finset.univ.filter
          (fun j => (ggBCRefl z' hz'dot (Pi.single i (1 : ZMod 3))) j ≠ 0) := by
      intro j hj
      rw [Finset.mem_erase] at hj
      obtain ⟨hji, hjmem⟩ := hj
      rw [Finset.mem_filter] at hjmem ⊢
      refine ⟨Finset.mem_univ j, ?_⟩
      have hzj : z' j ≠ 0 := hjmem.2
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        dotProduct_single_one, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hji, zero_add]
      exact mul_ne_zero (mul_ne_zero hzi hz'dot) hzj
    calc ggBCWt z' - 1
        = ((Finset.univ.filter (fun j => z' j ≠ 0)).erase i).card := hcard.symm
      _ ≤ (Finset.univ.filter
            (fun j => (ggBCRefl z' hz'dot (Pi.single i (1 : ZMod 3))) j ≠ 0)).card :=
          Finset.card_le_card hsub
      _ = ggBCWt (ggBCRefl z' hz'dot (Pi.single i (1 : ZMod 3))) := rfl
  omega

private lemma ggQ2x_bad_of_support {n : ℕ} [NeZero n] (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggBCRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggBCRootsLam1 n)
    {s : GGBCV n} (hs : s ∈ Z) (hzero : ∃ m, s m = 0)
    (T : Finset (Fin n)) (hT : T ⊆ Finset.univ.filter (fun k => s k ≠ 0))
    (hTcard : 3 ≤ T.card) : False := by
  have hroot := ggQ2x_zero_coord_is_root Z hZ0 hZroots hZcl hHL hs hzero
  have hle : T.card ≤ ggBCWt s := Finset.card_le_card hT
  have hs2 : ggBCWt s ≤ 2 := hroot.2
  omega

lemma ggQ2x_full_support_false {n : ℕ} [NeZero n] (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggBCRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggBCRootsLam1 n)
    {z : GGBCV n} (hz : z ∈ Z) (hfull : ∀ i, z i ≠ 0) : False := by
  have hz0 : z ⬝ᵥ z ≠ 0 := hZ0 z hz
  have hwt : ggBCWt z = n := ggQ2x_wt_eq_of_full hfull
  have hne : (n : ZMod 3) ≠ 0 := by
    intro h0
    exact hz0 (by rw [ggQ2x_dot_self_eq_wt, hwt, h0])
  have hval := (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) (n : ZMod 3)
  rcases hval with h0 | h1 | h2
  · exact absurd h0 hne
  · obtain ⟨j, hj0⟩ :=
      Fintype.exists_ne_of_one_lt_card (α := Fin n)
        (by rw [Fintype.card_fin]; omega) (0 : Fin n)
    have h0j : (0 : Fin n) ≠ j := Ne.symm hj0
    set rho : GGBCV n := z 0 • (Pi.single 0 1 : GGBCV n)
      + z j • (Pi.single j 1 : GGBCV n) with hrho_def
    have hrhoRoot : rho ∈ ggBCRoots n := by
      have hw : ggBCWt rho = 2 := by
        rw [hrho_def]
        exact ggQ2x_wt_smul_single_add_single 0 j h0j (z 0) (z j) (hfull 0) (hfull j)
      exact ⟨by omega, by omega⟩
    have hzz : z ⬝ᵥ z = 1 := by rw [ggQ2x_dot_self_eq_wt, hwt, h1]
    have hzρ : z ⬝ᵥ rho = 2 := by
      rw [hrho_def, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_single_one,
        dotProduct_single_one, smul_eq_mul, smul_eq_mul,
        ggQ2x_mul_self_eq_one (z 0) (hfull 0), ggQ2x_mul_self_eq_one (z j) (hfull j)]
      decide
    have hs_eq : ggBCRefl z hz0 rho = fun m => rho m + 2 * z m := by
      funext m
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzρ, hzz, mul_one]
    have hr0 : rho 0 = z 0 := by
      rw [hrho_def, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hj0),
        mul_one, mul_zero, add_zero]
    have hs0 : ggBCRefl z hz0 rho 0 = 0 := by
      rw [hs_eq]
      change rho 0 + 2 * z 0 = 0
      rw [hr0]
      exact (by decide : ∀ x : ZMod 3, x + 2 * x = 0) (z 0)
    have hT : (Finset.univ.erase (0 : Fin n)).erase j ⊆
        Finset.univ.filter (fun k => (ggBCRefl z hz0 rho) k ≠ 0) := by
      intro k hk
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
      obtain ⟨hkj, hk0⟩ := hk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ k, ?_⟩
      have hrk : rho k = 0 := by
        rw [hrho_def, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk0,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj, mul_zero, mul_zero, add_zero]
      rw [hs_eq]
      change rho k + 2 * z k ≠ 0
      rw [hrk, zero_add]
      exact mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hfull k)
    have hTcard : 3 ≤ ((Finset.univ.erase (0 : Fin n)).erase j).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin n)), Finset.card_univ,
        Fintype.card_fin]
      omega
    exact ggQ2x_bad_of_support Z hZ0 hZroots hZcl hHL
      (hZcl z hz rho (hZroots hrhoRoot) hz0) ⟨0, hs0⟩ _ hT hTcard
  · have hzz : z ⬝ᵥ z = 2 := by rw [ggQ2x_dot_self_eq_wt, hwt, h2]
    have hzf : z ⬝ᵥ (Pi.single 0 1 : GGBCV n) = z 0 := dotProduct_single_one z 0
    have hs_eq : ggBCRefl z hz0 (Pi.single 0 1 : GGBCV n)
        = fun m => (Pi.single 0 1 : GGBCV n) m + (z 0 * 2) * z m := by
      funext m
      rw [ggQ2x_ggBCRefl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzf, hzz]
    have hs0 : ggBCRefl z hz0 (Pi.single 0 1 : GGBCV n) 0 = 0 := by
      rw [hs_eq]
      change (Pi.single 0 1 : GGBCV n) 0 + (z 0 * 2) * z 0 = 0
      rw [Pi.single_eq_same]
      exact (by decide : ∀ x : ZMod 3, x ≠ 0 → 1 + (x * 2) * x = 0) (z 0) (hfull 0)
    have hfRoot : (Pi.single 0 1 : GGBCV n) ∈ ggBCRoots n := by
      refine ⟨?_, ?_⟩ <;> rw [ggQ2x_wt_single] <;> norm_num
    have hT : Finset.univ.erase (0 : Fin n) ⊆
        Finset.univ.filter
          (fun k => (ggBCRefl z hz0 (Pi.single 0 1 : GGBCV n)) k ≠ 0) := by
      intro k hk
      rw [Finset.mem_erase] at hk
      obtain ⟨hk0, -⟩ := hk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ k, ?_⟩
      rw [hs_eq]
      change (Pi.single 0 1 : GGBCV n) k + (z 0 * 2) * z k ≠ 0
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk0, zero_add]
      exact mul_ne_zero (mul_ne_zero (hfull 0) (by decide : (2 : ZMod 3) ≠ 0)) (hfull k)
    have hTcard : 3 ≤ (Finset.univ.erase (0 : Fin n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin n)), Finset.card_univ,
        Fintype.card_fin]
      omega
    exact ggQ2x_bad_of_support Z hZ0 hZroots hZcl hHL
      (hZcl z hz (Pi.single 0 1) (hZroots hfRoot) hz0) ⟨0, hs0⟩ _ hT hTcard

theorem ggQ2_bc_Z_a1 (n : ℕ) [NeZero n] (hn : 5 ≤ n) (Z : Set (GGBCV n))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggBCRoots n ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggBCRootsLam1 n, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggBCRootsLam1 n) :
    Z ⊆ ggBCRoots n := by
  intro z hz
  by_cases hzero : ∃ m, z m = 0
  · exact ggQ2x_zero_coord_is_root Z hZ0 hZroots hZcl hHL hz hzero
  · exfalso
    push Not at hzero
    exact ggQ2x_full_support_false hn Z hZ0 hZroots hZcl hHL hz hzero

end CFSG.StandardType

end

