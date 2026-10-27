module

public import CFSG.RepresentationTheory.SL2NatSum.Interpolation
public import CFSG.RepresentationTheory.SL2NatSum.ChooseTwo

public section

open scoped Matrix

namespace CFSG.RepresentationTheory.SzMartineau

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {M : Type*} [AddCommGroup M]
  [Module K M]

private lemma sum_pow_smul_eq_sum_choose (x y : K) (c : ℕ → M) :
    (∑ j ∈ Finset.range (Fintype.card K), (x + y) ^ j • c j) =
      ∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k •
          (if i + k < Fintype.card K then ((i + k).choose i : K) • c (i + k) else 0) := by
  classical
  let f : ℕ → ℕ → M := fun i j => x ^ i • y ^ (j - i) • ((j.choose i : K) • c j)
  have step1 : (∑ j ∈ Finset.range (Fintype.card K), (x + y) ^ j • c j) =
      ∑ j ∈ Finset.range (Fintype.card K),
        ∑ i ∈ Finset.range (j + 1), f i j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_pow, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, smul_smul, mul_assoc]
  have step2 : (∑ j ∈ Finset.range (Fintype.card K),
        ∑ i ∈ Finset.range (j + 1), f i j) =
      ∑ i ∈ Finset.range (Fintype.card K),
        ∑ j ∈ Finset.Ico i (Fintype.card K), f i j := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (Fintype.card K) f).symm
  have step3 : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ j ∈ Finset.Ico i (Fintype.card K), f i j) =
      ∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K - i), f i (i + k) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_Ico_eq_sum_range]
  have step4 : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K - i), f i (i + k)) =
      ∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k •
          (if i + k < Fintype.card K then ((i + k).choose i : K) • c (i + k) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfilter : (Finset.range (Fintype.card K)).filter
        (fun k => k < Fintype.card K - i) = Finset.range (Fintype.card K - i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    calc
      (∑ k ∈ Finset.range (Fintype.card K - i), f i (i + k))
          = ∑ k ∈ (Finset.range (Fintype.card K)).filter
              (fun k => k < Fintype.card K - i), f i (i + k) := by
            rw [hfilter]
      _ = ∑ k ∈ Finset.range (Fintype.card K),
            (if k < Fintype.card K - i then f i (i + k) else 0) := by
            rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range (Fintype.card K),
            x ^ i • y ^ k •
              (if i + k < Fintype.card K then
                ((i + k).choose i : K) • c (i + k) else 0) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hiff : k < Fintype.card K - i ↔ i + k < Fintype.card K := by
              rw [Nat.lt_sub_iff_add_lt]
              omega
            by_cases hk : k < Fintype.card K - i
            · rw [if_pos hk, if_pos (hiff.mp hk)]
              simp only [f, Nat.add_sub_cancel_left]
            · rw [if_neg hk, if_neg (hiff.not.mp hk)]
              simp
  rw [step1, step2, step3, step4]

private lemma sum_smul_ite_eq_zero_right (c : ℕ → M) (x y : K) :
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (if k = 0 then c i else 0)) =
      ∑ i ∈ Finset.range (Fintype.card K), x ^ i • c i := by
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk])
    (fun h => absurd (Finset.mem_range.mpr hq0) h)]
  simp

private lemma sum_smul_ite_eq_zero_left (c : ℕ → M) (x y : K) :
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (if i = 0 then c k else 0)) =
      ∑ k ∈ Finset.range (Fintype.card K), y ^ k • c k := by
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi])
    (fun h => absurd (Finset.mem_range.mpr hq0) h)]
  simp

private lemma additive_coeff_two_var (f : K →+ M) (c : ℕ → M)
    (hc : ∀ x : K, f x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j)
    (hc0 : c 0 = 0) :
    ∀ i < Fintype.card K, ∀ k < Fintype.card K,
      (if i + k < Fintype.card K then ((i + k).choose i : K) • c (i + k) else 0)
        - (if k = 0 then c i else 0) - (if i = 0 then c k else 0) = 0 := by
  classical
  let e : ℕ → ℕ → M := fun i k =>
    (if i + k < Fintype.card K then ((i + k).choose i : K) • c (i + k) else 0)
      - (if k = 0 then c i else 0) - (if i = 0 then c k else 0)
  have he : ∀ x y : K,
      ∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • e i k = 0 := by
    intro x y
    have hD : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K), x ^ i • y ^ k •
          (if i + k < Fintype.card K then ((i + k).choose i : K) • c (i + k) else 0))
        = f (x + y) :=
      (sum_pow_smul_eq_sum_choose x y c).symm.trans (hc (x + y)).symm
    have hL : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K),
          x ^ i • y ^ k • (if k = 0 then c i else 0)) = f x :=
      (sum_smul_ite_eq_zero_right c x y).trans (hc x).symm
    have hR : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K),
          x ^ i • y ^ k • (if i = 0 then c k else 0)) = f y :=
      (sum_smul_ite_eq_zero_left c x y).trans (hc y).symm
    calc
      (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
          x ^ i • y ^ k • e i k)
          = (∑ i ∈ Finset.range (Fintype.card K),
                ∑ k ∈ Finset.range (Fintype.card K), x ^ i • y ^ k •
                  (if i + k < Fintype.card K then
                    ((i + k).choose i : K) • c (i + k) else 0))
            - (∑ i ∈ Finset.range (Fintype.card K),
                ∑ k ∈ Finset.range (Fintype.card K),
                  x ^ i • y ^ k • (if k = 0 then c i else 0))
            - (∑ i ∈ Finset.range (Fintype.card K),
                ∑ k ∈ Finset.range (Fintype.card K),
                  x ^ i • y ^ k • (if i = 0 then c k else 0)) := by
            simp only [e, smul_sub, Finset.sum_sub_distrib]
      _ = f (x + y) - f x - f y := by rw [hD, hL, hR]
      _ = 0 := by rw [map_add]; abel
  simpa only [e] using
    CFSG.RepresentationTheory.SL2NatSum.coeff₂_eq_zero_of_forall_sum_eq_zero e he

private lemma coeff_eq_zero_of_not_two_pow {n : ℕ} (hq : Fintype.card K = 2 ^ n)
    (f : K →+ M) (c : ℕ → M)
    (hc : ∀ x : K, f x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j)
    (hc0 : c 0 = 0) :
    ∀ j < 2 ^ n, 0 < j → (¬ ∃ b, j = 2 ^ b) → c j = 0 := by
  intro j hj2 hj0 hjpow
  have hjq : j < Fintype.card K := by rwa [hq]
  have he := additive_coeff_two_var f c hc hc0
  obtain ⟨b, m, hm_odd, hjm⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp hj0)
  obtain ⟨t, rfl⟩ := hm_odd
  have hm_ne1 : 2 * t + 1 ≠ 1 := by
    intro h
    exact hjpow ⟨b, by rw [hjm, h, mul_one]⟩
  have ht : 0 < t := by omega
  have hb_le_j : 2 ^ b ≤ j := by
    rw [hjm]
    exact Nat.le_mul_of_pos_right _ (by omega : 0 < 2 * t + 1)
  set k : ℕ := j - 2 ^ b with hk_def
  have hk_eq : k = 2 ^ (b + 1) * t := by
    rw [hk_def, Nat.sub_eq_iff_eq_add hb_le_j, hjm, pow_succ]
    ring
  have hk_pos : 0 < k := by
    rw [hk_eq]
    exact Nat.mul_pos (Nat.pow_pos (by norm_num)) ht
  have hk_lt_j : k < j := by
    rw [hk_def]
    exact Nat.sub_lt_of_pos_le (Nat.pow_pos (by norm_num)) hb_le_j
  have hk_lt_q : k < Fintype.card K := by
    rw [hq]
    exact lt_trans hk_lt_j hj2
  have h2b_lt_q : 2 ^ b < Fintype.card K := by
    rw [hq]
    exact lt_of_le_of_lt hb_le_j hj2
  have h2b_pos : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
  have hand : 2 ^ b &&& k = 0 := by
    rw [hk_eq, Nat.two_pow_and, Nat.testBit_two_pow_mul,
      decide_eq_false (by omega : ¬ b + 1 ≤ b)]
    simp
  have hjsum : 2 ^ b + k = j := by
    rw [hk_def]
    exact Nat.add_sub_of_le hb_le_j
  have hdec : ((j.choose (2 ^ b) : K) • c j) = 0 := by
    have he' := he (2 ^ b) h2b_lt_q k hk_lt_q
    have hif : (if 2 ^ b + k < Fintype.card K then
          ((2 ^ b + k).choose (2 ^ b) : K) • c (2 ^ b + k) else 0)
          - (if k = 0 then c (2 ^ b) else 0) - (if 2 ^ b = 0 then c k else 0)
          = ((j.choose (2 ^ b) : K) • c j) := by
      rw [if_pos (by rwa [hjsum]), if_neg hk_pos.ne', if_neg h2b_pos.ne', hjsum]
      simp
    rwa [hif] at he'
  have hodd : Odd (j.choose (2 ^ b)) := by
    rw [← hjsum]
    exact (CFSG.RepresentationTheory.SL2NatSum.odd_choose_add_iff (2 ^ b) k).mpr hand
  have hcoef : ((j.choose (2 ^ b) : K) = 1) := by
    rw [CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.mpr hodd)]
  simpa only [hcoef, one_smul] using hdec

private lemma sum_range_eq_sum_pow_range {n : ℕ} (hq : Fintype.card K = 2 ^ n)
    (c : ℕ → M) (hc0 : c 0 = 0)
    (hnot : ∀ j < 2 ^ n, 0 < j → (¬ ∃ b, j = 2 ^ b) → c j = 0) (x : K) :
    (∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j) =
      ∑ b ∈ Finset.range n, x ^ 2 ^ b • c (2 ^ b) := by
  have hsub : (Finset.range n).image (fun b => 2 ^ b) ⊆
      Finset.range (Fintype.card K) := by
    intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_range, hq]
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (Finset.mem_range.mp hb)
  have hzero : ∀ j ∈ Finset.range (Fintype.card K),
      j ∉ (Finset.range n).image (fun b => 2 ^ b) → x ^ j • c j = 0 := by
    intro j hjq hji
    by_cases hj0 : j = 0
    · subst hj0
      simp [hc0]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hj2 : j < 2 ^ n := by
        rw [hq] at hjq
        exact Finset.mem_range.mp hjq
      have hjpow : ¬ ∃ b, j = 2 ^ b := by
        rintro ⟨b, hb⟩
        apply hji
        refine Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr ?_, hb.symm⟩
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hb]; exact hj2)
      rw [hnot j hj2 hjpos hjpow, smul_zero]
  rw [(Finset.sum_subset hsub hzero).symm]
  exact Finset.sum_image fun a _ b _ hab =>
    Nat.pow_right_injective (le_refl 2) hab

theorem exists_linearized {n : ℕ} (hq : Fintype.card K = 2 ^ n) (f : K →+ M) :
    ∃ a : ℕ → M, ∀ x, f x = ∑ b ∈ Finset.range n, x ^ 2 ^ b • a b := by
  classical
  obtain ⟨c, hc0, hc⟩ :=
    CFSG.RepresentationTheory.SL2NatSum.exists_coeff f (map_zero f)
  refine ⟨fun b => c (2 ^ b), fun x => ?_⟩
  exact (hc x).trans (sum_range_eq_sum_pow_range hq c hc0
    (coeff_eq_zero_of_not_two_pow hq f c hc hc0) x)

theorem linearized_coeff_eq_zero {n : ℕ} (hq : Fintype.card K = 2 ^ n) (a : ℕ → M)
    (h : ∀ x : K, ∑ b ∈ Finset.range n, x ^ 2 ^ b • a b = 0) :
    ∀ b < n, a b = 0 := by
  classical
  let c : ℕ → M := fun j => ∑ b ∈ Finset.range n, if j = 2 ^ b then a b else 0
  have hc0 : c 0 = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    exact fun h => (Nat.pow_pos (by norm_num : 0 < 2)).ne' h.symm
  have hsum : ∀ x : K,
      ∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j = 0 := by
    intro x
    have hrec : (∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j) =
        ∑ b ∈ Finset.range n, x ^ 2 ^ b • a b := by
      simp only [c, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.sum_eq_single (2 ^ b)]
      · simp
      · intro j _ hjne
        rw [if_neg]
        · simp
        · exact hjne
      · intro hnot
        exact absurd (Finset.mem_range.mpr (by
          rw [hq]
          exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
            (Finset.mem_range.mp hb))) hnot
    rw [hrec, h x]
  have hc := CFSG.RepresentationTheory.SL2NatSum.coeff_eq_zero_of_forall_sum_eq_zero c hsum
  intro b hb
  have h2b_lt_q : 2 ^ b < Fintype.card K := by
    rw [hq]
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hb
  have hsingle : c (2 ^ b) = a b := by
    simp only [c]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hbne
      rw [if_neg]
      exact fun h => hbne (Nat.pow_right_injective (le_refl 2) h).symm
    · intro hnot
      exact absurd (Finset.mem_range.mpr hb) hnot
  have hz := hc (2 ^ b) h2b_lt_q
  rwa [hsingle] at hz

private noncomputable def matrixEntryHom {m : ℕ}
    (φ : (Fin m → K) →+ (Fin m → K)) (i j : Fin m) : K →+ K where
  toFun x := φ (Pi.single j x) i
  map_zero' := by simp
  map_add' x y := by simp [Pi.single_add]

theorem exists_frobenius_decomp {n m : ℕ} (hq : Fintype.card K = 2 ^ n)
    (φ : (Fin m → K) →+ (Fin m → K)) :
    ∃ A : ℕ → Matrix (Fin m) (Fin m) K,
      ∀ v, φ v = ∑ c ∈ Finset.range n, A c *ᵥ (fun i => v i ^ 2 ^ c) := by
  classical
  choose a ha using fun (i j : Fin m) =>
    exists_linearized (M := K) hq (matrixEntryHom φ i j)
  let A : ℕ → Matrix (Fin m) (Fin m) K := fun c i j => a i j c
  refine ⟨A, fun v => ?_⟩
  have hA : ∀ (i j : Fin m) (x : K),
      φ (Pi.single j x) i = ∑ c ∈ Finset.range n, x ^ 2 ^ c • a i j c := by
    intro i j x
    simpa [matrixEntryHom] using ha i j x
  have hv : v = ∑ j : Fin m, Pi.single j (v j) := by
    symm
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji.symm]
    · intro hnot
      exact absurd (Finset.mem_univ i) hnot
  have hφv : φ v = ∑ j : Fin m, φ (Pi.single j (v j)) := by
    conv_lhs => rw [hv]
    rw [map_sum]
  ext i
  calc
    φ v i = (∑ j : Fin m, φ (Pi.single j (v j))) i := by rw [hφv]
    _ = (∑ c ∈ Finset.range n, A c *ᵥ (fun i => v i ^ 2 ^ c)) i := by
            simp only [Finset.sum_apply]
            simp only [hA]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Matrix.mulVec_apply_eq_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_eq_mul, mul_comm]

theorem frobenius_decomp_eq_zero {n m : ℕ} (hq : Fintype.card K = 2 ^ n)
    (A : ℕ → Matrix (Fin m) (Fin m) K)
    (h : ∀ v : Fin m → K, ∑ c ∈ Finset.range n, A c *ᵥ (fun i => v i ^ 2 ^ c) = 0) :
    ∀ c < n, A c = 0 := by
  classical
  intro c hc
  ext i j
  have hcol : ∀ x : K, ∑ b ∈ Finset.range n, x ^ 2 ^ b • A b i j = 0 := by
    intro x
    have hv := congrFun (h (Pi.single j x)) i
    rw [Finset.sum_apply] at hv
    have hterm : ∀ b : ℕ,
        (A b *ᵥ (fun i => ((Pi.single j x : Fin m → K) i) ^ 2 ^ b)) i =
          x ^ 2 ^ b • A b i j := by
      intro b
      rw [Matrix.mulVec_apply_eq_sum]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, smul_eq_mul, mul_comm]
      · intro j' _ hjne
        have hval : (Pi.single j x : Fin m → K) j' = 0 := by
          rw [Pi.single_apply, if_neg]
          exact hjne
        rw [hval, zero_pow (Nat.two_pow_pos b).ne', mul_zero]
      · intro hnot
        exact absurd (Finset.mem_univ j) hnot
    simpa [hterm] using hv
  exact linearized_coeff_eq_zero hq (fun b => A b i j) hcol c hc

private lemma zpow_eq_pow_val {m : ℕ} [NeZero m]
    (hm : ∀ x : K, x ≠ 0 → x ^ m = 1) (w : ℤ) {x : K} (hx : x ≠ 0) :
    x ^ w = x ^ (w : ZMod m).val := by
  let u : Kˣ := Units.mk0 x hx
  have hu : (u : K) = x := Units.val_mk0 hx
  have hu_pow : u ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, Units.val_one]
    exact hm x hx
  have hz : u ^ w = u ^ (w % (m : ℤ)) := zpow_eq_zpow_emod' w (by simpa using hu_pow)
  have hval : (((w : ZMod m).val : ℤ)) = w % (m : ℤ) := ZMod.val_intCast (n := m) w
  calc
    x ^ w = ((u : K) ^ w) := by rw [hu]
    _ = ((u ^ w : Kˣ) : K) := (Units.val_zpow_eq_zpow_val u w).symm
    _ = ((u ^ (w % (m : ℤ)) : Kˣ) : K) := by rw [hz]
    _ = ((u : K) ^ (w % (m : ℤ))) := Units.val_zpow_eq_zpow_val u _
    _ = ((u : K) ^ ((w : ZMod m).val : ℤ)) := by rw [hval]
    _ = ((u : K) ^ (w : ZMod m).val) := zpow_natCast (u : K) _
    _ = x ^ (w : ZMod m).val := by rw [hu]

private lemma eq_one_of_one_add_eq_zero {y : K} (h : (1 : K) + y = 0) : y = 1 :=
  (CharTwo.add_eq_zero.mp h).symm

theorem exists_two_pow_of_zpow_add {n : ℕ} (hq : Fintype.card K = 2 ^ n) (w : ℤ)
    (h : ∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → (x + y) ^ w = x ^ w + y ^ w) :
    ∃ k : ℕ, (w : ZMod (2 ^ n - 1)) = 2 ^ k := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst n
    exfalso
    have h1 : 1 < Fintype.card K := Fintype.one_lt_card
    rw [hq] at h1
    norm_num at h1
  rcases lt_or_ge 1 n with hn2 | hnle
  ·
    let m : ℕ := 2 ^ n - 1
    have hpow2 : 1 < 2 ^ n :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hnpos
    have hmpos : 0 < m := by
      have hpow : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
      change 0 < 2 ^ n - 1
      omega
    haveI : NeZero m := ⟨hmpos.ne'⟩
    have hmq : ∀ x : K, x ≠ 0 → x ^ m = 1 := by
      intro x hx
      have hmcard : Fintype.card K - 1 = m := by
        change Fintype.card K - 1 = 2 ^ n - 1
        rw [hq]
      rw [← hmcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    have hm_lt_card : m < Fintype.card K := by
      change 2 ^ n - 1 < Fintype.card K
      rw [hq]
      have hpow : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
      omega
    let r : ℕ := (w : ZMod m).val
    have hr_lt_m : r < m := ZMod.val_lt (w : ZMod m)
    have hr_lt_card : r < Fintype.card K := lt_trans hr_lt_m hm_lt_card
    have hzw : ∀ x : K, x ≠ 0 → x ^ w = x ^ r := by
      intro x hx
      exact zpow_eq_pow_val hmq w hx
    have hq4 : 2 < Fintype.card K := by
      rw [hq]
      calc
        2 = 2 ^ 1 := by norm_num
        _ < 2 ^ n := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hn2
    by_cases hr0 : r = 0
    ·
      exfalso
      have hpair : ({0, 1} : Finset K).card = 2 := Finset.card_pair zero_ne_one
      have hcardlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
        rw [hpair, Finset.card_univ]
        exact hq4
      obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardlt
      have hy0 : y ≠ 0 := by
        intro hyy
        exact hy (by simp [hyy])
      have hy1 : y ≠ 1 := by
        intro hyy
        exact hy (by simp [hyy])
      have h1y : (1 : K) + y ≠ 0 := by
        intro h0
        exact hy1 (eq_one_of_one_add_eq_zero h0)
      have hh := h 1 y one_ne_zero hy0 h1y
      rw [hzw (1 + y) h1y, hzw 1 one_ne_zero, hzw y hy0, hr0] at hh
      simp only [pow_zero] at hh
      rw [CharTwo.add_self_eq_zero (1 : K)] at hh
      exact one_ne_zero hh
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      let g : K →+ K :=
        { toFun := fun x => x ^ r
          map_zero' := by rw [zero_pow hrpos.ne']
          map_add' := fun x y => by
            by_cases hx : x = 0
            · rw [hx, zero_add, zero_pow hrpos.ne', zero_add]
            by_cases hy : y = 0
            · rw [hy, add_zero, zero_pow hrpos.ne', add_zero]
            by_cases hxy : x + y = 0
            · have hxy' : x = y := CharTwo.add_eq_zero.mp hxy
              subst y
              rw [hxy, zero_pow hrpos.ne']
              exact (CharTwo.add_self_eq_zero (x ^ r)).symm
            · have hh := h x y hx hy hxy
              rwa [hzw x hx, hzw y hy, hzw (x + y) hxy] at hh }
      obtain ⟨a, ha⟩ := exists_linearized (M := K) hq g
      have ha' : ∀ x : K, x ^ r = ∑ b ∈ Finset.range n, x ^ 2 ^ b • a b := by
        intro x
        simpa [g] using ha x
      let c : ℕ → K := fun j => if j = r then 1 else 0
      let d : ℕ → K := fun j => ∑ b ∈ Finset.range n, if 2 ^ b = j then a b else 0
      have hcsum : ∀ x : K,
          ∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j = x ^ r := by
        intro x
        rw [Finset.sum_eq_single r]
        · simp only [c, if_pos rfl, smul_eq_mul, mul_one]
        · intro j _ hjr
          simp only [c, if_neg hjr, smul_zero]
        · intro hnot
          exact absurd (Finset.mem_range.mpr hr_lt_card) hnot
      have hdsum : ∀ x : K,
          ∑ j ∈ Finset.range (Fintype.card K), x ^ j • d j =
            ∑ b ∈ Finset.range n, x ^ 2 ^ b • a b := by
        intro x
        simp only [d, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.sum_eq_single (2 ^ b)]
        · simp
        · intro j _ hjne
          rw [if_neg]
          · simp
          · exact fun h => hjne h.symm
        · intro hnot
          exact absurd (Finset.mem_range.mpr (by
            rw [hq]
            exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
              (Finset.mem_range.mp hb))) hnot
      have hdiff : ∀ x : K,
          ∑ j ∈ Finset.range (Fintype.card K), x ^ j • (c j - d j) = 0 := by
        intro x
        calc
          (∑ j ∈ Finset.range (Fintype.card K), x ^ j • (c j - d j))
              = (∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j)
                - ∑ j ∈ Finset.range (Fintype.card K), x ^ j • d j := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [smul_sub]
          _ = x ^ r - ∑ b ∈ Finset.range n, x ^ 2 ^ b • a b := by rw [hcsum x, hdsum x]
          _ = 0 := by rw [ha' x, sub_self]
      have huniq := CFSG.RepresentationTheory.SL2NatSum.coeff_eq_zero_of_forall_sum_eq_zero
        (fun j => c j - d j) hdiff
      have hcr : c r - d r = 0 := huniq r hr_lt_card
      have hdr : d r = 1 := by
        rw [show c r = 1 by simp only [c, if_pos rfl]] at hcr
        exact (sub_eq_zero.mp hcr).symm
      by_contra hno
      have hzero : d r = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        have hne : 2 ^ b ≠ r := by
          intro hbr
          apply hno
          refine ⟨b, ?_⟩
          rw [← ZMod.natCast_zmod_val (w : ZMod m)]
          change (r : ZMod m) = 2 ^ b
          rw [← hbr, Nat.cast_pow]
          norm_num
        rw [if_neg hne]
      rw [hzero] at hdr
      exact zero_ne_one hdr
  ·
    have hn1 : n = 1 := by omega
    subst n
    haveI : Subsingleton (ZMod (2 ^ 1 - 1)) := by
      rw [show 2 ^ 1 - 1 = 1 by norm_num]
      exact ZMod.subsingleton_iff.mpr rfl
    exact ⟨0, Subsingleton.elim _ _⟩

end CFSG.RepresentationTheory.SzMartineau
