module

public import CFSG.LocalAnalysis.StandardType.GGLatticeRootsDefs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.GCD
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType

open Matrix

private theorem ggKGLi_sq_sub_one {m : ℕ} (v : Matrix (Fin m) (Fin m) ℤ) (hv2 : v * v = 1) :
    (v - 1) * (v - 1) = (-2 : ℤ) • (v - 1) := by
  have h : (v - 1) * (v - 1) = v * v - v - v + 1 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul]
    abel
  rw [h, hv2]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

private theorem ggKGLi_sub_one_ne_zero {m p : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (v : Matrix (Fin m) (Fin m) ℤ)
    (hfix : Nat.card {x : Fin m → ZMod p //
      (v.map (Int.castRingHom (ZMod p))).mulVec x = x} = p ^ (m - 1)) :
    v - 1 ≠ 0 := by
  intro h
  have hv : v = 1 := sub_eq_zero.mp h
  subst hv
  rw [Matrix.map_one (Int.castRingHom (ZMod p)) (by simp) (by simp)] at hfix
  have hcard : Nat.card {x : Fin m → ZMod p //
      (1 : Matrix (Fin m) (Fin m) (ZMod p)).mulVec x = x} = Nat.card (Fin m → ZMod p) := by
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)
    exact Matrix.one_mulVec x
  have hpm : Nat.card (Fin m → ZMod p) = p ^ m := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    rw [Nat.card_pi]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hcard, hpm] at hfix
  have hlt : p ^ (m - 1) < p ^ m :=
    Nat.pow_lt_pow_right hp.one_lt (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hm) (by norm_num))
  exact (ne_of_lt hlt) hfix.symm

private theorem ggKGLi_minors_mod_p {m p : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (v : Matrix (Fin m) (Fin m) ℤ)
    (hfix : Nat.card {x : Fin m → ZMod p //
      (v.map (Int.castRingHom (ZMod p))).mulVec x = x} = p ^ (m - 1)) :
    ∀ a b i j : Fin m,
      (p : ℤ) ∣ (v - 1) a i * (v - 1) b j - (v - 1) a j * (v - 1) b i := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let ū : Matrix (Fin m) (Fin m) (ZMod p) := (v - 1).map (Int.castRingHom (ZMod p))
  have hū : ū = v.map (Int.castRingHom (ZMod p)) - 1 := by
    simp only [ū]
    rw [Matrix.map_sub (Int.castRingHom (ZMod p)) (fun a b => by simp),
      Matrix.map_one _ (by simp) (by simp)]
  have hker_sub : Nat.card {x : Fin m → ZMod p // ū.mulVec x = 0} = p ^ (m - 1) := by
    rw [← hfix]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [hū, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_eq_zero
  have hker_card : Nat.card (LinearMap.ker ū.mulVecLin) = p ^ (m - 1) := by
    rw [← hker_sub]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hkerfin : Module.finrank (ZMod p) (LinearMap.ker ū.mulVecLin) = m - 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker ū.mulVecLin)
    rw [hker_card] at h
    have hz : Nat.card (ZMod p) = p := by
      rw [Nat.card_eq_fintype_card]; exact ZMod.card p
    rw [hz] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  have hfr : Module.finrank (ZMod p) (LinearMap.range ū.mulVecLin) ≤ 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ū.mulVecLin
    rw [Module.finrank_fin_fun, hkerfin] at hrn
    omega
  obtain ⟨v₀, hv₀⟩ :=
    (finrank_le_one_iff (K := ZMod p) (V := LinearMap.range ū.mulVecLin)).mp hfr
  have hcol : ∀ i : Fin m, ∃ c : ZMod p,
      c • (v₀ : Fin m → ZMod p) = ū.mulVec (Pi.single i 1) := by
    intro i
    let wi : LinearMap.range ū.mulVecLin :=
      ⟨ū.mulVec (Pi.single i 1), LinearMap.mem_range.mpr
        ⟨Pi.single i 1, by rw [Matrix.mulVecLin_apply]⟩⟩
    obtain ⟨c, hc⟩ := hv₀ wi
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hcol
  intro a b i j
  have h1 : c i * (v₀ : Fin m → ZMod p) a = ū a i := by
    have := congrFun (hc i) a
    simpa [Matrix.mulVec_single_one] using this
  have h2 : c j * (v₀ : Fin m → ZMod p) b = ū b j := by
    have := congrFun (hc j) b
    simpa [Matrix.mulVec_single_one] using this
  have h3 : c j * (v₀ : Fin m → ZMod p) a = ū a j := by
    have := congrFun (hc j) a
    simpa [Matrix.mulVec_single_one] using this
  have h4 : c i * (v₀ : Fin m → ZMod p) b = ū b i := by
    have := congrFun (hc i) b
    simpa [Matrix.mulVec_single_one] using this
  have hminor : ū a i * ū b j - ū a j * ū b i = 0 := by
    rw [← h1, ← h2, ← h3, ← h4]; ring
  have hcast : (((v - 1) a i * (v - 1) b j - (v - 1) a j * (v - 1) b i : ℤ) : ZMod p) = 0 := by
    push_cast
    exact hminor
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast

private theorem ggKGLi_cauchyBinet2 {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (a b i j : Fin m) :
    2 * ((A * B) a i * (A * B) b j - (A * B) a j * (A * B) b i)
      = ∑ k, ∑ l, (A a k * A b l - A a l * A b k) *
          (B k i * B l j - B k j * B l i) := by
  have h1 : (∑ k, A a k * B k i) * (∑ l, A b l * B l j)
      = ∑ k, ∑ l, A a k * A b l * (B k i * B l j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have h2 : (∑ k, A a k * B k j) * (∑ l, A b l * B l i)
      = ∑ k, ∑ l, A a k * A b l * (B k j * B l i) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hR : (∑ k, ∑ l, (A a k * A b l - A a l * A b k) *
        (B k i * B l j - B k j * B l i))
      = (∑ k, ∑ l, A a k * A b l * (B k i * B l j))
        - (∑ k, ∑ l, A a k * A b l * (B k j * B l i))
        - (∑ k, ∑ l, A a l * A b k * (B k i * B l j))
        + (∑ k, ∑ l, A a l * A b k * (B k j * B l i)) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have hS3 : (∑ k, ∑ l, A a l * A b k * (B k i * B l j))
      = (∑ k, ∑ l, A a k * A b l * (B k j * B l i)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hS4 : (∑ k, ∑ l, A a l * A b k * (B k j * B l i))
      = (∑ k, ∑ l, A a k * A b l * (B k i * B l j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  simp only [Matrix.mul_apply]
  rw [h1, h2, hR, hS3, hS4]
  ring

private theorem ggKGLi_minors_zero {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u : Matrix (Fin m) (Fin m) ℤ) (hu2 : u * u = (-2 : ℤ) • u)
    (hdiv : ∀ a b i j : Fin m, (p : ℤ) ∣ u a i * u b j - u a j * u b i) :
    ∀ a b i j : Fin m, u a i * u b j - u a j * u b i = 0 := by
  let M : Fin m → Fin m → Fin m → Fin m → ℤ := fun a b i j => u a i * u b j - u a j * u b i
  have hMval : ∀ a b i j, M a b i j = u a i * u b j - u a j * u b i := fun a b i j => rfl
  have hkey : ∀ a b i j, 8 * M a b i j = ∑ k, ∑ l, M a b k l * M k l i j := by
    intro a b i j
    have hcb := ggKGLi_cauchyBinet2 u u a b i j
    rw [hu2] at hcb
    simp only [Matrix.smul_apply, smul_eq_mul] at hcb
    have hgoal : 8 * M a b i j
        = ∑ k, ∑ l, (u a k * u b l - u a l * u b k) *
            (u k i * u l j - u k j * u l i) := by
      rw [← hcb]
      simp only [M]
      ring
    simpa only [M] using hgoal
  have hcop : IsCoprime (p : ℤ) (8 : ℤ) := by
    have hcop2 : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr (by
      intro hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact hp.ne_one h1
      · exact hp2 h2)
    have hcop8 : Nat.Coprime p 8 := by
      have h : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h]
      exact hcop2.pow_right 3
    exact hcop8.isCoprime
  have hP : ∀ n : ℕ, 1 ≤ n → ∀ a b i j, (p : ℤ) ^ n ∣ M a b i j := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        intro a b i j
        simpa [hMval] using hdiv a b i j
      · intro a b i j
        have hPn : ∀ a b i j, (p : ℤ) ^ n ∣ M a b i j := ih hnpos
        have hsum : ((p : ℤ) ^ n * (p : ℤ) ^ n) ∣
            ∑ k, ∑ l, M a b k l * M k l i j := by
          apply Finset.dvd_sum
          intro k _
          apply Finset.dvd_sum
          intro l _
          exact mul_dvd_mul (hPn a b k l) (hPn k l i j)
        have h8 : (p : ℤ) ^ (2 * n) ∣ 8 * M a b i j := by
          rw [hkey a b i j]
          have h2n : (p : ℤ) ^ (2 * n) = (p : ℤ) ^ n * (p : ℤ) ^ n := by
            rw [show 2 * n = n + n by ring, pow_add]
          rw [h2n]
          exact hsum
        have hcopn : IsCoprime ((p : ℤ) ^ (2 * n)) (8 : ℤ) :=
          IsCoprime.pow_left (m := 2 * n) hcop
        have hM : (p : ℤ) ^ (2 * n) ∣ M a b i j := hcopn.dvd_of_dvd_mul_left h8
        have hle : n + 1 ≤ 2 * n := by omega
        exact dvd_trans (pow_dvd_pow (p : ℤ) hle) hM
  intro a b i j
  have hN : 1 ≤ (M a b i j).natAbs + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hdvd := hP ((M a b i j).natAbs + 1) hN a b i j
  have hpow : ((p : ℤ) ^ ((M a b i j).natAbs + 1)).natAbs = p ^ ((M a b i j).natAbs + 1) := by
    simp [Int.natAbs_pow]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
  rw [hpow]
  exact Nat.lt_trans (Nat.lt_succ_self _)
    (Nat.lt_pow_self (n := (M a b i j).natAbs + 1) hp.one_lt)

private theorem ggKGLi_rank_rat_le_one {m : ℕ} (u : Matrix (Fin m) (Fin m) ℤ) (hu : u ≠ 0)
    (hmin : ∀ a b i j : Fin m, u a i * u b j - u a j * u b i = 0) :
    (u.map (Int.castRingHom ℚ)).rank ≤ 1 := by
  obtain ⟨a₀, i₀, hi₀⟩ : ∃ a i, u a i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (by ext a i; exact h a i)
  let TQ : Matrix (Fin m) (Fin m) ℚ := u.map (Int.castRingHom ℚ)
  have hcol : ∀ k : Fin m, ∃ c : ℚ, c • TQ.col i₀ = TQ.col k := by
    intro k
    refine ⟨(u a₀ k : ℚ) / (u a₀ i₀ : ℚ), ?_⟩
    funext a
    have hm : u a k * u a₀ i₀ = u a i₀ * u a₀ k := sub_eq_zero.mp (hmin a a₀ k i₀)
    have hcast : (u a k : ℚ) * (u a₀ i₀ : ℚ) = (u a i₀ : ℚ) * (u a₀ k : ℚ) := by
      exact_mod_cast hm
    have hne : (u a₀ i₀ : ℚ) ≠ 0 := by exact_mod_cast hi₀
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, TQ, Matrix.map_apply]
    rw [div_mul_eq_mul_div, div_eq_iff hne]
    exact (mul_comm ((Int.castRingHom ℚ) (u a₀ k)) ((Int.castRingHom ℚ) (u a i₀))).trans hcast.symm
  have hspan_le : Submodule.span ℚ (Set.range TQ.col) ≤ Submodule.span ℚ {TQ.col i₀} := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact Submodule.mem_span_singleton.mpr (hcol k)
  have hcol_ne : TQ.col i₀ ≠ 0 := by
    intro h
    have h0 : TQ.col i₀ a₀ = 0 := by rw [h]; rfl
    have : (u a₀ i₀ : ℚ) = 0 := by simpa [TQ, Matrix.col_apply, Matrix.map_apply] using h0
    exact hi₀ (by exact_mod_cast this)
  change TQ.rank ≤ 1
  rw [Matrix.rank_eq_finrank_span_cols]
  exact (Submodule.finrank_mono hspan_le).trans_eq (finrank_span_singleton hcol_ne)

private theorem ggKGLi_vecMulVec {r : ℕ} (T : Matrix (Fin r) (Fin r) ℤ)
    (hT : T ≠ 0) (hrank : (T.map (Int.castRingHom ℚ)).rank ≤ 1) :
    ∃ u c : Fin r → ℤ, u ≠ 0 ∧ c ≠ 0 ∧
      (∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1) ∧
      T = Matrix.vecMulVec u c := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, T.col j ≠ 0 := by
    by_contra h
    push Not at h
    exact hT (by ext i j; simpa using congrFun (h j) i)
  let v : Fin r → ℤ := T.col j₀
  have hv : v ≠ 0 := hj₀
  obtain ⟨u, huv, hugcd⟩ := Finset.extract_gcd (s := Finset.univ) v ⟨j₀, Finset.mem_univ j₀⟩
  let G : ℤ := Finset.univ.gcd v
  have hG : G ≠ 0 := by
    intro h0
    exact hv (funext fun j => (Finset.gcd_eq_zero_iff.mp h0) j (Finset.mem_univ j))
  have hu : u ≠ 0 := by
    intro h
    apply hv
    funext j
    rw [huv j (Finset.mem_univ j), h]
    simp
  have hprim : ∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1 := by
    intro d hd
    have h1 : d ∣ (1 : ℤ) := by
      have h := Finset.dvd_gcd (s := Finset.univ) (f := u) (fun j _ => hd j)
      rwa [hugcd] at h
    exact Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr h1)
  let TQ : Matrix (Fin r) (Fin r) ℚ := T.map (Int.castRingHom ℚ)
  let W : Submodule ℚ (Fin r → ℚ) := Submodule.span ℚ (Set.range TQ.col)
  have hWle : Module.finrank ℚ W ≤ 1 := by
    rw [show Module.finrank ℚ W = TQ.rank from (Matrix.rank_eq_finrank_span_cols TQ).symm]
    exact hrank
  obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hWle
  let w₀ : W := ⟨TQ.col j₀, Submodule.subset_span ⟨j₀, rfl⟩⟩
  have hw₀_ne : w₀ ≠ 0 := by
    intro h
    have hval : TQ.col j₀ = 0 := congrArg Subtype.val h
    apply hv
    funext a
    have hthis := congrFun hval a
    change (v a : ℚ) = 0 at hthis
    exact_mod_cast hthis
  obtain ⟨a, ha⟩ := hv₀ w₀
  have ha_ne : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at ha
    exact hw₀_ne ha.symm
  have hcol : ∀ k, ∃ q : ℚ, TQ.col k = q • TQ.col j₀ := by
    intro k
    let wk : W := ⟨TQ.col k, Submodule.subset_span ⟨k, rfl⟩⟩
    obtain ⟨b, hb⟩ := hv₀ wk
    refine ⟨b * a⁻¹, ?_⟩
    have hbval : b • (v₀ : Fin r → ℚ) = TQ.col k := congrArg Subtype.val hb
    have haval : a • (v₀ : Fin r → ℚ) = TQ.col j₀ := congrArg Subtype.val ha
    have hv0 : (v₀ : Fin r → ℚ) = a⁻¹ • TQ.col j₀ := by
      rw [← haval]
      exact (inv_smul_smul₀ ha_ne (v₀ : Fin r → ℚ)).symm
    rw [← hbval, hv0, smul_smul]
  choose q hq using hcol
  let uQ : Fin r → ℚ := fun a => (u a : ℚ)
  have huvQ : TQ.col j₀ = (G : ℚ) • uQ := by
    funext a
    change (v a : ℚ) = (G : ℚ) * (u a : ℚ)
    rw [huv a (Finset.mem_univ a)]
    push_cast
    ring
  have hcolQ : ∀ k, TQ.col k = (q k * (G : ℚ)) • uQ := by
    intro k
    rw [hq k, huvQ, smul_smul]
  have hcolQ_comp : ∀ k a, (T a k : ℚ) = (q k * (G : ℚ)) * (u a : ℚ) := by
    intro k a
    have h := congrFun (hcolQ k) a
    change (T a k : ℚ) = (q k * (G : ℚ)) * (u a : ℚ) at h
    exact h
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin r)) u
  have hg1 : ∑ a : Fin r, u a * g a = 1 := by
    have h1 : ∑ a ∈ Finset.univ, u a * g a = 1 := by rw [← hg, hugcd]
    simpa using h1
  let c : Fin r → ℤ := fun k => ∑ a, T a k * g a
  have hcQ : ∀ k, ((c k : ℤ) : ℚ) = q k * (G : ℚ) := by
    intro k
    have hsum1 : ((∑ a, T a k * g a : ℤ) : ℚ) =
        (q k * (G : ℚ)) * ((∑ a, u a * g a : ℤ) : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hcolQ_comp k a]
      ring
    change ((∑ a, T a k * g a : ℤ) : ℚ) = q k * (G : ℚ)
    rw [hsum1, hg1]
    ring
  have hTcol : ∀ k, T.col k = c k • u := by
    intro k
    funext a
    show T a k = c k * u a
    have hq_eq : ((T a k : ℤ) : ℚ) = ((c k * u a : ℤ) : ℚ) := by
      push_cast
      rw [hcolQ_comp k a, hcQ k]
    exact_mod_cast hq_eq
  refine ⟨u, c, hu, ?_, hprim, ?_⟩
  · intro hc0
    apply hT
    ext i j
    have h1 := congrFun (hTcol j) i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h1
    have hcj : c j = 0 := by simp [hc0]
    rw [h1, hcj, zero_mul]
    rfl
  · ext i j
    have h1 := congrFun (hTcol j) i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    simp [Matrix.vecMulVec_apply, mul_comm]

private theorem ggKGLi_rank_one {m : ℕ} (u : Matrix (Fin m) (Fin m) ℤ) (hu : u ≠ 0)
    (hmin : ∀ a b i j : Fin m, u a i * u b j - u a j * u b i = 0) :
    ∃ w l : Fin m → ℤ, w ≠ 0 ∧ ∀ a i, u a i = w a * l i := by
  have hrank := ggKGLi_rank_rat_le_one u hu hmin
  obtain ⟨w, l, hw, _hc, _hprim, hT⟩ := ggKGLi_vecMulVec u hu hrank
  refine ⟨w, l, hw, ?_⟩
  intro a i
  have h := congrFun (congrFun hT a) i
  simpa [Matrix.vecMulVec] using h

private theorem ggKGLi_vecMulVec_mulVec {m : ℕ} (w l y : Fin m → ℤ) :
    (Matrix.vecMulVec w l).mulVec y = (l ⬝ᵥ y) • w := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem ggKGLi_form {m : ℕ} (v : Matrix (Fin m) (Fin m) ℤ) (w l : Fin m → ℤ)
    (hfac : ∀ a i, (v - 1) a i = w a * l i) :
    ∀ y, v.mulVec y = y + (l ⬝ᵥ y) • w := by
  intro y
  have hmat : v - 1 = Matrix.vecMulVec w l := by ext a i; exact hfac a i
  have h1 : (v - 1).mulVec y = (l ⬝ᵥ y) • w := by
    rw [hmat, ggKGLi_vecMulVec_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
  calc v.mulVec y = (l ⬝ᵥ y) • w + y := eq_add_of_sub_eq h1
    _ = y + (l ⬝ᵥ y) • w := add_comm _ _

private theorem ggKGLi_lambda_w {m : ℕ} (u : Matrix (Fin m) (Fin m) ℤ) (w l : Fin m → ℤ)
    (hu_ne : u ≠ 0) (hu2 : u * u = (-2 : ℤ) • u)
    (hfac : u = Matrix.vecMulVec w l) :
    l ⬝ᵥ w = -2 := by
  have hmul : u * u = (l ⬝ᵥ w) • u := by
    rw [hfac]
    ext a i
    simp only [Matrix.mul_apply, Matrix.smul_apply, dotProduct, Matrix.vecMulVec_apply,
      smul_eq_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h0 : (l ⬝ᵥ w + 2) • u = 0 := by
    rw [add_smul, ← hmul, hu2]
    simp
  obtain ⟨a, i, hi⟩ : ∃ a i, u a i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu_ne (by ext a i; exact h a i)
  have hthis := congrFun (congrFun h0 a) i
  simp only [Matrix.smul_apply, Pi.zero_apply, smul_eq_mul] at hthis
  have hz : l ⬝ᵥ w + 2 = 0 := (mul_eq_zero.mp hthis).resolve_right hi
  linarith

private theorem ggKGLi_orth {m : ℕ} (Q v : Matrix (Fin m) (Fin m) ℤ)
    (hQsym : Q.transpose = Q) (hvQ : v.transpose * Q * v = Q)
    (w l : Fin m → ℤ) (hform : ∀ y, v.mulVec y = y + (l ⬝ᵥ y) • w)
    (hlw : l ⬝ᵥ w = -2) (y : Fin m → ℤ) :
    (w ⬝ᵥ Q.mulVec w) * (l ⬝ᵥ y) = -2 * (y ⬝ᵥ Q.mulVec w) := by
  have hisom : ∀ x y, (v.mulVec x) ⬝ᵥ Q.mulVec (v.mulVec y) = x ⬝ᵥ Q.mulVec y := by
    intro x y
    have hstep : ∀ z, x ⬝ᵥ v.transpose.mulVec z = (v.mulVec x) ⬝ᵥ z := by
      intro z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    calc (v.mulVec x) ⬝ᵥ Q.mulVec (v.mulVec y)
        = x ⬝ᵥ v.transpose.mulVec (Q.mulVec (v.mulVec y)) := (hstep _).symm
      _ = x ⬝ᵥ (v.transpose * Q).mulVec (v.mulVec y) := by
          rw [Matrix.mulVec_mulVec (v.mulVec y) v.transpose Q]
      _ = x ⬝ᵥ (v.transpose * Q * v).mulVec y := by
          rw [Matrix.mulVec_mulVec y (v.transpose * Q) v]
      _ = x ⬝ᵥ Q.mulVec y := by rw [hvQ]
  have hsym : ∀ a b, a ⬝ᵥ Q.mulVec b = b ⬝ᵥ Q.mulVec a := by
    intro a b
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose Q a, hQsym]
    exact dotProduct_comm _ _
  have hvw : v.mulVec w = -w := by
    rw [hform w, hlw]
    ext i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := hisom w y
  rw [hvw, hform y] at h
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, neg_dotProduct, dotProduct_add,
    dotProduct_smul] at h
  rw [hsym w y] at h
  simp only [smul_eq_mul] at h
  nlinarith [h]


theorem ggKGLat_involution_isRoot {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q) (v : Matrix (Fin m) (Fin m) ℤ)
    (hvQ : v.transpose * Q * v = Q) (hv2 : v * v = 1)
    (hfix : Nat.card {x : Fin m → ZMod p //
      (v.map (Int.castRingHom (ZMod p))).mulVec x = x} = p ^ (m - 1)) (hm : 1 ≤ m) :
    ∃ w : Fin m → ℤ, GGLatRoot Q w ∧ ∀ y : Fin m → ℤ, v.mulVec y = ggLatRefl Q w y := by
  have hu2 : (v - 1) * (v - 1) = (-2 : ℤ) • (v - 1) := ggKGLi_sq_sub_one v hv2
  have hue : v - 1 ≠ 0 := ggKGLi_sub_one_ne_zero hp hm v hfix
  have hdiv := ggKGLi_minors_mod_p hp hm v hfix
  have hmin := ggKGLi_minors_zero hp hp2 (v - 1) hu2 hdiv
  obtain ⟨w, l, hw, hfac⟩ := ggKGLi_rank_one (v - 1) hue hmin
  have hmat : v - 1 = Matrix.vecMulVec w l := by ext a i; exact hfac a i
  have hform : ∀ y, v.mulVec y = y + (l ⬝ᵥ y) • w := ggKGLi_form v w l hfac
  have hlw : l ⬝ᵥ w = -2 := ggKGLi_lambda_w (v - 1) w l hue hu2 hmat
  have horth : ∀ y, (w ⬝ᵥ Q.mulVec w) * (l ⬝ᵥ y) = -2 * (y ⬝ᵥ Q.mulVec w) :=
    fun y => ggKGLi_orth Q v hQ.1 hvQ w l hform hlw y
  have hB : w ⬝ᵥ Q.mulVec w ≠ 0 := ne_of_gt (hQ.2 w hw)
  refine ⟨w, ⟨hw, ?_⟩, ?_⟩
  · intro y
    have h2 : 2 * (y ⬝ᵥ Q.mulVec w) = (w ⬝ᵥ Q.mulVec w) * (-(l ⬝ᵥ y)) := by
      nlinarith [horth y]
    rw [h2]
    exact dvd_mul_right _ _
  · intro y
    have hcart : ggLatCartan Q y w = -(l ⬝ᵥ y) := by
      have h2 : 2 * (y ⬝ᵥ Q.mulVec w) = (w ⬝ᵥ Q.mulVec w) * (-(l ⬝ᵥ y)) := by
        nlinarith [horth y]
      unfold ggLatCartan
      exact Int.ediv_eq_of_eq_mul_right hB h2
    rw [ggLatRefl, hcart, hform y, neg_smul, sub_neg_eq_add]


end CFSG.StandardType

end
