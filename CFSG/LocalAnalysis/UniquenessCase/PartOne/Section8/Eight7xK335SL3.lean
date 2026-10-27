module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

open Polynomial

private theorem k335csl_not_mem_center {π : Bool} {p f : ℕ} {K : Type} [Field K] [Fintype K]
    (hPi : CFSG.RankThree.PartTwo.Sec4.PiField π p f K)
    (hq : CFSG.RankThree.PartTwo.Sec4.ModThree π (p ^ f))
    {x : CFSG.RankThree.PartTwo.Sec4.slPi π 3 (p ^ f) K}
    (hxs : ∀ c : K,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) :
    x ∉ Subgroup.center (CFSG.RankThree.PartTwo.Sec4.slPi π 3 (p ^ f) K) := by
  intro hz
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp
    (CFSG.RankThree.PartTwo.Sec13.mem_statedScalars_of_mem_center hPi hq hz)
  exact hxs u.1 (by rw [← hu, Matrix.GeneralLinearGroup.coe_scalar])

theorem k335_conj_sl3 {K : Type} [Field K] [Fintype K] (hK : Nat.card K % 3 = 1)
    {x y : ↥(CFSG.Open.StatedSL 3 K)} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxs : ∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c)
    (hys : ∀ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) :
    ∃ g : ↥(CFSG.Open.StatedSL 3 K), g⁻¹ * x * g = y := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hcharI : CharP K p := hchar
  obtain ⟨n, hpprime, hcardF⟩ := FiniteField.card K p
  have hn1 : 1 ≤ (n : ℕ) := n.2
  have hcard : Nat.card K = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardF
  have hPi : CFSG.RankThree.PartTwo.Sec4.PiField true p (n : ℕ) K :=
    ⟨hpprime, hn1,
      by rw [CFSG.RankThree.PartTwo.Sec4.piCard, Bool.cond_true]; exact hcard⟩
  have hq : CFSG.RankThree.PartTwo.Sec4.ModThree true (p ^ (n : ℕ)) := by
    show p ^ (n : ℕ) % 3 = 1
    rw [← hcard]; exact hK
  let x' : CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ (n : ℕ)) K := x
  let y' : CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ (n : ℕ)) K := y
  have hx3 : x' ^ 3 = 1 := hx
  have hy3 : y' ^ 3 = 1 := hy
  have hxnc : x' ∉ Subgroup.center
      (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ (n : ℕ)) K) :=
    k335csl_not_mem_center hPi hq hxs
  have hync : y' ∉ Subgroup.center
      (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ (n : ℕ)) K) :=
    k335csl_not_mem_center hPi hq hys
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec12.Hering129L.exists_conj_of_pow_three_slPi
    hPi hq hx3 hy3 hxnc hync
  have hgoal : ∃ g : CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ (n : ℕ)) K,
      g⁻¹ * x' * g = y' := by
    refine ⟨g⁻¹, ?_⟩
    simp only [inv_inv]
    exact hg
  exact hgoal

theorem k335_conj_su3 {K : Type} [Field K] [Fintype K] {q : ℕ} (hKq : Nat.card K = q ^ 2)
    (hq : q % 3 = 2) {x y : ↥(CFSG.Open.StatedSU 3 q K)} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxs : ∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c)
    (hys : ∀ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) :
    ∃ g : ↥(CFSG.Open.StatedSU 3 q K), g⁻¹ * x * g = y := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hcharI : CharP K p := hchar
  obtain ⟨n, hpprime, hcardF⟩ := FiniteField.card K p
  have hcard : Nat.card K = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardF
  have hqdvd : q ∣ p ^ (n : ℕ) := by
    rw [← hcard, hKq]; exact ⟨q, by ring⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hpprime).1 hqdvd
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk; omega
    · exact h0
  subst q
  have hPi : CFSG.RankThree.PartTwo.Sec4.PiField false p k K :=
    ⟨hpprime, hk1,
      by rw [CFSG.RankThree.PartTwo.Sec4.piCard, Bool.cond_false]; exact hKq⟩
  have hqmod : CFSG.RankThree.PartTwo.Sec4.ModThree false (p ^ k) := hq
  let x' : CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ k) K := x
  let y' : CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ k) K := y
  have hx3 : x' ^ 3 = 1 := hx
  have hy3 : y' ^ 3 = 1 := hy
  have hxnc : x' ∉ Subgroup.center
      (CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ k) K) :=
    k335csl_not_mem_center hPi hqmod hxs
  have hync : y' ∉ Subgroup.center
      (CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ k) K) :=
    k335csl_not_mem_center hPi hqmod hys
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec12.Hering129L.exists_conj_of_pow_three_slPi
    hPi hqmod hx3 hy3 hxnc hync
  have hgoal : ∃ g : CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ k) K,
      g⁻¹ * x' * g = y' := by
    refine ⟨g⁻¹, ?_⟩
    simp only [inv_inv]
    exact hg
  exact hgoal

private theorem k335p9_no_nine (K : Type) [Field K] [Fintype K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) {r : K}
    (hr9 : r ^ 9 = 1) (hr3 : r ^ 3 ≠ 1) : False := by
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hr9
    norm_num at hr9
  let u : Kˣ := Units.mk0 r hr0
  have hu : (u : K) = r := Units.val_mk0 hr0
  have hu9 : u ^ 9 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [hu]
    exact hr9
  have hu3 : u ^ 3 ≠ 1 := by
    intro h
    apply hr3
    have := congrArg (fun v : Kˣ => (v : K)) h
    simpa [hu, Units.val_pow_eq_pow_val] using this
  have horder : orderOf u = 9 := by
    have h := orderOf_eq_prime_pow (p := 3) (n := 1) (x := u) (by simpa using hu3)
      (by simpa using hu9)
    simpa using h
  have h9dvd : 9 ∣ Nat.card K - 1 := by
    have h := orderOf_dvd_natCard u
    rw [horder, Nat.card_units] at h
    exact h
  have hmod : Nat.card K % 9 = 1 := by
    have hNpos : 1 ≤ Nat.card K := Nat.card_pos
    have hm : (1 : ℕ) ≡ Nat.card K [MOD 9] := (Nat.modEq_iff_dvd' hNpos).mpr h9dvd
    have hs : Nat.card K ≡ 1 [MOD 9] := Nat.ModEq.symm hm
    simpa [Nat.ModEq] using hs
  rcases hK with h | h <;> omega

private theorem k335p9_exists_zeta (K : Type) [Field K] [Fintype K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) :
    ∃ ζ : K, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ 1 + ζ + ζ ^ 2 = 0 := by
  have h3 : 3 ∣ Nat.card K - 1 := by
    have hNpos : 1 ≤ Nat.card K := Nat.card_pos
    have hmod3 : Nat.card K % 3 = 1 := by rcases hK with h | h <;> omega
    have hm : (1 : ℕ) ≡ Nat.card K [MOD 3] := by
      show (1 : ℕ) % 3 = Nat.card K % 3
      rw [hmod3]
    exact (Nat.modEq_iff_dvd' hNpos).mp hm
  have hdvd : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hζ3 : (u : K) ^ 3 = 1 := by simpa using congrArg Units.val hu3
  have hζne : (u : K) ≠ 1 := by
    intro h
    have hu1 : u = 1 := Units.ext (by simpa using h)
    rw [hu1, orderOf_one] at hu
    exact (by norm_num : (1 : ℕ) ≠ 3) hu
  have hsum : 1 + (u : K) + (u : K) ^ 2 = 0 := by
    have hfac : ((u : K) - 1) * (1 + (u : K) + (u : K) ^ 2) = 0 := by
      have hpoly : ((u : K) - 1) * (1 + (u : K) + (u : K) ^ 2) = (u : K) ^ 3 - 1 := by
        ring
      rw [hpoly, hζ3]
      ring
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hζne)
  exact ⟨(u : K), hζ3, hζne, hsum⟩

private theorem k335p9_factor (K : Type) [Field K] {ζ : K} (hζ3 : ζ ^ 3 = 1)
    (hsum : 1 + ζ + ζ ^ 2 = 0) :
    (X ^ 3 - 1) * (X ^ 3 - C ζ) * (X ^ 3 - C (ζ ^ 2)) = X ^ 9 - 1 := by
  have hζsum : C ζ + C (ζ ^ 2) = (-1 : K[X]) := by
    rw [← map_add, show ζ + ζ ^ 2 = -1 by linear_combination hsum, map_neg, map_one]
  have hζprod : C ζ * C (ζ ^ 2) = (1 : K[X]) := by
    rw [← map_mul, show ζ * ζ ^ 2 = 1 by rw [← pow_succ', hζ3], map_one]
  have hmid : (X ^ 3 - C ζ) * (X ^ 3 - C (ζ ^ 2)) = (X ^ 3) ^ 2 + X ^ 3 + 1 := by
    have hexp : (X ^ 3 - C ζ) * (X ^ 3 - C (ζ ^ 2))
        = (X ^ 3) ^ 2 - X ^ 3 * (C ζ + C (ζ ^ 2)) + C ζ * C (ζ ^ 2) := by ring
    rw [hexp, hζsum, hζprod]
    ring
  rw [mul_assoc, hmid]
  ring

private theorem k335p9_pow3_sub_C_irreducible (K : Type) [Field K] [Fintype K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) {η : K} (hη3 : η ^ 3 = 1)
    (hηne : η ≠ 1) : Irreducible (X ^ 3 - C η : K[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [Polynomial.natDegree_X_pow_sub_C]
    exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  · intro r hr
    rw [Polynomial.IsRoot.def] at hr
    have hr3 : r ^ 3 = η := by
      have hz : r ^ 3 - η = 0 := by simpa using hr
      exact sub_eq_zero.mp hz
    exact k335p9_no_nine K hK (r := r)
      (by rw [show r ^ 9 = (r ^ 3) ^ 3 by ring, hr3, hη3])
      (by rw [hr3]; exact hηne)

private theorem k335p9_dvd_charpoly_false (K : Type) [Field K]
    {M : Matrix (Fin 3) (Fin 3) K} {η : K} (hηne : η ≠ 1) (hdet : M.det = 1)
    (hdvd : (X ^ 3 - C η) ∣ M.charpoly) : False := by
  have hmon : (X ^ 3 - C η : K[X]).Monic := Polynomial.monic_X_pow_sub_C η (by norm_num)
  have hdeg : M.charpoly.natDegree ≤ (X ^ 3 - C η : K[X]).natDegree := by
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_pow_sub_C]
    simp
  have heq : M.charpoly = X ^ 3 - C η :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon M.charpoly_monic hdvd hdeg
  have hcoeff : M.charpoly.coeff 0 = -η := by
    rw [heq]
    simp
  have hdetval : M.det = η := by
    rw [Matrix.det_eq_sign_charpoly_coeff M, hcoeff]
    simp only [Fintype.card_fin]
    ring
  exact hηne (hdetval.symm.trans hdet)

private theorem k335p9_coprime_case (K : Type) [Field K]
    {M : Matrix (Fin 3) (Fin 3) K} {p1 p2 : K[X]}
    (hfac : (X ^ 3 - 1) * p1 * p2 = X ^ 9 - 1)
    (hcop : IsCoprime (p1 * p2) M.charpoly) (hM9 : M ^ 9 = 1) : M ^ 3 = 1 := by
  have hχ : Polynomial.aeval M M.charpoly = 0 := Matrix.aeval_self_charpoly M
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : Polynomial.aeval M a * Polynomial.aeval M (p1 * p2)
      + Polynomial.aeval M b * Polynomial.aeval M M.charpoly = 1 := by
    have h := congrArg (Polynomial.aeval M) hab
    simpa [map_add, map_mul] using h
  have hu : Polynomial.aeval M a * Polynomial.aeval M (p1 * p2) = 1 := by
    simpa [hχ] using h1
  have hcomm : Polynomial.aeval M (p1 * p2) * Polynomial.aeval M a
      = Polynomial.aeval M a * Polynomial.aeval M (p1 * p2) := by
    have h₁ : Polynomial.aeval M (p1 * p2) * Polynomial.aeval M a
        = Polynomial.aeval M ((p1 * p2) * a) := by simp only [map_mul]
    have h₂ : Polynomial.aeval M ((p1 * p2) * a)
        = Polynomial.aeval M (a * (p1 * p2)) := by rw [mul_comm]
    have h₃ : Polynomial.aeval M (a * (p1 * p2))
        = Polynomial.aeval M a * Polynomial.aeval M (p1 * p2) := by simp only [map_mul]
    exact h₁.trans (h₂.trans h₃)
  have hv : Polynomial.aeval M (p1 * p2) * Polynomial.aeval M a = 1 := by
    rw [hcomm, hu]
  have hzero : (M ^ 3 - 1) * Polynomial.aeval M (p1 * p2) = 0 := by
    have h := congrArg (Polynomial.aeval M) hfac
    rw [map_mul, map_mul] at h
    simp only [map_sub, map_pow, aeval_X, map_one, hM9, sub_self] at h
    rw [mul_assoc, ← map_mul] at h
    exact h
  have hmul : ((M ^ 3 - 1) * Polynomial.aeval M (p1 * p2)) * Polynomial.aeval M a = 0 := by
    rw [hzero, zero_mul]
  have hM3 : M ^ 3 - 1 = 0 := by
    rwa [mul_assoc, hv, mul_one] at hmul
  exact sub_eq_zero.mp hM3

theorem k335_pow_three_gl3 {K : Type} [Field K] [Fintype K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) {x : GL (Fin 3) K}
    (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  obtain ⟨ζ, hζ3, hζne, hζsum⟩ := k335p9_exists_zeta K hK
  let M : Matrix (Fin 3) (Fin 3) K := x
  have hM9 : M ^ 9 = 1 := by
    change ((x : Matrix (Fin 3) (Fin 3) K) ^ 9) = 1
    rw [← Units.val_pow_eq_pow_val (a := x) (n := 9)]
    exact congrArg Units.val hx
  have hdetM : M.det = 1 := hdet
  have hζ2ne : ζ ^ 2 ≠ 1 := by
    intro h
    have hζ1 : ζ = 1 := by
      calc ζ = ζ * ζ ^ 2 := by rw [h, mul_one]
        _ = ζ ^ 3 := by ring
        _ = 1 := hζ3
    exact hζne hζ1
  have hζ23 : (ζ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 6 by norm_num]
    rw [show ζ ^ 6 = (ζ ^ 3) ^ 2 by ring, hζ3, one_pow]
  let p1 : K[X] := X ^ 3 - C ζ
  let p2 : K[X] := X ^ 3 - C (ζ ^ 2)
  have hp1 : Irreducible p1 := by
    show Irreducible (X ^ 3 - C ζ : K[X])
    exact k335p9_pow3_sub_C_irreducible K hK hζ3 hζne
  have hp2 : Irreducible p2 := by
    show Irreducible (X ^ 3 - C (ζ ^ 2) : K[X])
    exact k335p9_pow3_sub_C_irreducible K hK hζ23 hζ2ne
  have hfac : (X ^ 3 - 1) * p1 * p2 = X ^ 9 - 1 := by
    show (X ^ 3 - 1) * (X ^ 3 - C ζ) * (X ^ 3 - C (ζ ^ 2)) = X ^ 9 - 1
    exact k335p9_factor K hζ3 hζsum
  have hM3 : M ^ 3 = 1 := by
    by_cases hp1dvd : p1 ∣ M.charpoly
    · exact (k335p9_dvd_charpoly_false K hζne hdetM hp1dvd).elim
    · by_cases hp2dvd : p2 ∣ M.charpoly
      · exact (k335p9_dvd_charpoly_false K hζ2ne hdetM (by simpa [p2] using hp2dvd)).elim
      · have hcop1 : IsCoprime p1 M.charpoly := (hp1.coprime_iff_not_dvd).mpr hp1dvd
        have hcop2 : IsCoprime p2 M.charpoly := (hp2.coprime_iff_not_dvd).mpr hp2dvd
        have hcop : IsCoprime (p1 * p2) M.charpoly := hcop1.mul_left hcop2
        exact k335p9_coprime_case K hfac hcop hM9
  apply Units.ext
  simpa [M, Units.val_pow_eq_pow_val] using hM3

private theorem k335fsl_factorization_eq_three {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤) (hT27 : Nat.card T = 27) :
    (Nat.card G).factorization 3 = 3 := by
  have h := CFSG.ABGLocalTools.IsSylowOf.card_eq hT
  rw [Subgroup.card_top] at h
  have h' : 3 ^ (Nat.card G).factorization 3 = 3 ^ 3 := by
    rw [← h, hT27]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h'

private theorem k335fsl_sl_mod_nine {K : Type} [Field K] [Fintype K]
    (hK : Nat.card K % 3 = 1)
    {T : Subgroup ↥(CFSG.Open.StatedSL 3 K)}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤) (hT27 : Nat.card T = 27) :
    Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7 := by
  set q := Nat.card K with hq
  have horder := CFSG.Open.StatedAPI.card_statedSL_three K
  have hne1 : q % 9 ≠ 1 := by
    intro h1
    have h9 : q ≡ 1 [MOD 9] := by
      show q % 9 = 1 % 9
      simpa using h1
    have hd2 : 9 ∣ q ^ 2 - 1 := by simpa using (h9.pow 2).symm.dvd'
    have hd3 : 9 ∣ q ^ 3 - 1 := by simpa using (h9.pow 3).symm.dvd'
    have h81 : 81 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
      obtain ⟨a, ha⟩ := hd2
      obtain ⟨b, hb⟩ := hd3
      exact ⟨a * b, by rw [ha, hb]; ring⟩
    have h81N : 81 ∣ Nat.card ↥(CFSG.Open.StatedSL 3 K) := by
      rw [horder]
      exact dvd_mul_of_dvd_right h81 _
    have hle : 4 ≤ (Nat.card ↥(CFSG.Open.StatedSL 3 K)).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (Finite.card_pos.ne')).mp h81N
    have := k335fsl_factorization_eq_three hT hT27
    omega
  have hr : q % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hr3 : q % 9 % 3 = 1 := by
    rw [Nat.mod_mod_of_dvd q (by norm_num : 3 ∣ 9), hq]
    exact hK
  interval_cases q % 9 <;> simp_all

private theorem k335fsl_scalar_ncard_le_three {K : Type} [Field K] [Fintype K]
    {L : Subgroup (GL (Fin 3) K)} (hL : L ≤ CFSG.Open.StatedSL 3 K) :
    Set.ncard {x : L | ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c} ≤ 3 := by
  classical
  let S : Set L :=
    {x | ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c}
  let f : L → K := fun x => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
  have hf : Set.InjOn f S := by
    intro x hx y hy hxy
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    apply Subtype.ext
    apply Units.ext
    have hcd : c = d := by
      have := hxy
      simp only [f] at this
      rw [hc, hd] at this
      simpa [Matrix.scalar_apply] using this
    rw [hc, hd, hcd]
  have hmem : ∀ x ∈ S, f x ∈ (Polynomial.nthRootsFinset 3 (1 : K) : Set K) := by
    intro x hx
    change f x ∈ Polynomial.nthRootsFinset 3 (1 : K)
    rw [Polynomial.mem_nthRootsFinset (by norm_num)]
    obtain ⟨c, hc⟩ := hx
    have hxSL : (x : GL (Fin 3) K) ∈ CFSG.Open.StatedSL 3 K := hL x.2
    have hdet : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      CFSG.Open.StatedAPI.det_of_mem_statedSL hxSL
    have hfx : f x = c := by simp [f, hc, Matrix.scalar_apply]
    rw [hfx]
    have h1 : (Matrix.scalar (Fin 3) c).det = 1 := by rw [← hc, hdet]
    have h2 : Matrix.scalar (Fin 3) c = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    rw [h2, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  calc S.ncard ≤ (Polynomial.nthRootsFinset 3 (1 : K) : Set K).ncard :=
        Set.ncard_le_ncard_of_injOn f hmem hf
    _ = (Polynomial.nthRootsFinset 3 (1 : K)).card := Set.ncard_coe_finset _
    _ ≤ 3 := by
      rw [Polynomial.nthRootsFinset]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)

private theorem k335fsl_pow_three_gl {K : Type} [Field K] [Fintype K]
    (hpow : ∀ {x : GL (Fin 3) K},
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 → x ^ 9 = 1 → x ^ 3 = 1)
    {x : GL (Fin 3) K} (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) (hx : x ^ 27 = 1) :
    x ^ 3 = 1 := by
  have hx3det : ((x ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, hdet]
    norm_num
  have hx3_9 : (x ^ 3 : GL (Fin 3) K) ^ 9 = 1 := by
    rw [← pow_mul, show 3 * 9 = 27 by norm_num, hx]
  have h3 := hpow hx3det hx3_9
  have hx9 : x ^ 9 = 1 := by
    rw [← h3, ← pow_mul]
  exact hpow hdet hx9

private theorem k335fsl_pow_three_of_mem {K : Type} [Field K] [Fintype K]
    {H : Subgroup (GL (Fin 3) K)} (hHs : H ≤ CFSG.Open.StatedSL 3 K)
    (hpow : ∀ {x : GL (Fin 3) K},
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 → x ^ 9 = 1 → x ^ 3 = 1)
    {T : Subgroup H} (hT27 : Nat.card T = 27) {t : H} (ht : t ∈ T) : t ^ 3 = 1 := by
  have h27H : t ^ 27 = 1 := by
    have h := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
    rw [hT27] at h
    simpa using congrArg Subtype.val h
  have h27 : (t : GL (Fin 3) K) ^ 27 = 1 := by
    have := congrArg (fun z : H => (z : GL (Fin 3) K)) h27H
    simpa using this
  have hdet : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL (hHs t.2)
  have hgl := k335fsl_pow_three_gl hpow hdet h27
  exact Subtype.ext (by simpa using hgl)

private theorem k335fsl_sl3_core
    (hpow : ∀ {K : Type} [Field K] [Fintype K],
      (Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) → ∀ {x : GL (Fin 3) K},
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 → x ^ 9 = 1 → x ^ 3 = 1)
    (hconj : ∀ {K : Type} [Field K] [Fintype K], Nat.card K % 3 = 1 →
      ∀ {x y : ↥(CFSG.Open.StatedSL 3 K)}, x ^ 3 = 1 → y ^ 3 = 1 →
      (∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) →
      (∀ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) →
      ∃ g : ↥(CFSG.Open.StatedSL 3 K), g⁻¹ * x * g = y)
    {K : Type} [Field K] [Fintype K] (hK : Nat.card K % 3 = 1)
    {T A : Subgroup ↥(CFSG.Open.StatedSL 3 K)} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤)
    (hT27 : Nat.card T = 27) (hAT : A ≤ T) (hA : Nat.card A = 9)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set ↥(CFSG.Open.StatedSL 3 K)) T) : False := by
  classical
  let H := ↥(CFSG.Open.StatedSL 3 K)
  have h9 : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7 := k335fsl_sl_mod_nine hK hT hT27
  have hpowK : ∀ {x : GL (Fin 3) K},
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 → x ^ 9 = 1 → x ^ 3 = 1 :=
    fun {x} hdet hx => hpow h9 hdet hx
  let Scal : Set H :=
    {x | ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c}
  have hScal : Scal.ncard ≤ 3 :=
    k335fsl_scalar_ncard_le_three (L := CFSG.Open.StatedSL 3 K) le_rfl
  have hAncard : (A : Set H).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hA
  have hex : ∃ a ∈ A, a ∉ Scal := by
    by_contra h
    have hsub : (A : Set H) ⊆ Scal := by
      intro a ha
      by_contra hna
      exact h ⟨a, ha, hna⟩
    have := Set.ncard_le_ncard hsub
    omega
  obtain ⟨a, haA, haScal⟩ := hex
  have haScal' : ∀ c : K,
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c :=
    fun c hc => haScal ⟨c, hc⟩
  have ha3 : a ^ 3 = 1 :=
    k335fsl_pow_three_of_mem (H := CFSG.Open.StatedSL 3 K) le_rfl hpowK hT27 (hAT haA)
  have hsubT : (T : Set H) ⊆ (A : Set H) ∪ Scal := by
    intro t ht
    by_cases htScal : t ∈ Scal
    · exact Or.inr htScal
    · refine Or.inl ?_
      have htScal' : ∀ c : K,
          ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c :=
        fun c hc => htScal ⟨c, hc⟩
      have ht3 : t ^ 3 = 1 :=
        k335fsl_pow_three_of_mem (H := CFSG.Open.StatedSL 3 K) le_rfl hpowK hT27 ht
      obtain ⟨g, hg⟩ := hconj hK ha3 ht3 haScal' htScal'
      have hmem : g ⁻¹ * a * g ∈ T := by rw [hg]; exact ht
      have hcl' := hcl a haA g hmem
      rwa [hg] at hcl'
  have hTcard : (T : Set H).ncard = 27 := by
    rw [← Nat.card_coe_set_eq]
    exact hT27
  have hle := Set.ncard_le_ncard hsubT
  have hunion := Set.ncard_union_le (A : Set H) Scal
  omega

theorem k335_sl3_false {K : Type} [Field K] [Fintype K] (hK : Nat.card K % 3 = 1)
    {T A : Subgroup ↥(CFSG.Open.StatedSL 3 K)} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤)
    (hT27 : Nat.card T = 27) (hAT : A ≤ T) (hA : Nat.card A = 9)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set ↥(CFSG.Open.StatedSL 3 K)) T) : False := by
  exact k335fsl_sl3_core k335_pow_three_gl3 k335_conj_sl3 hK hT hT27 hAT hA hcl

private theorem k335fsl_su_mod_nine {K : Type} [Field K] [Fintype K] {q : ℕ}
    (hKq : Nat.card K = q ^ 2) (hq : q % 3 = 2)
    {T : Subgroup ↥(CFSG.Open.StatedSU 3 q K)}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤) (hT27 : Nat.card T = 27) :
    Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7 := by
  have hfact : (Nat.card ↥(CFSG.Open.StatedSU 3 q K)).factorization 3 = 3 :=
    k335fsl_factorization_eq_three hT hT27
  obtain ⟨p, hp⟩ := CharP.exists K
  obtain ⟨n, hpp, hn0⟩ := FiniteField.card K p
  have hn : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
  have hqd : q ∣ p ^ (n : ℕ) := by rw [← hn, hKq]; exact Dvd.intro_left q (sq q).symm
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hf; omega
    · exact h0
  have hPi : CFSG.RankThree.PartTwo.Sec4.PiField false p f K :=
    ⟨hpp, hf1, by rw [CFSG.RankThree.PartTwo.Sec4.piCard, Bool.cond_false, ← hf, hKq]⟩
  have horderSU : Nat.card ↥(CFSG.Open.StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have h1 := CFSG.RankThree.PartTwo.Sec13.card_slPi_three (π := false) (p := p) (f := f) hPi
    rw [← hf] at h1
    simpa [CFSG.RankThree.PartTwo.Sec4.slPi] using h1
  have hne8 : q % 9 ≠ 8 := by
    intro h8
    have h9 : q ≡ 8 [MOD 9] := by
      show q % 9 = 8 % 9
      simpa using h8
    have hd2 : 9 ∣ q ^ 2 - 1 := by
      have h2 : q ^ 2 ≡ 1 [MOD 9] := (h9.pow 2).trans (by decide)
      exact h2.symm.dvd'
    have hd3 : 9 ∣ q ^ 3 + 1 := by
      have h3 : q ^ 3 + 1 ≡ 0 [MOD 9] := by
        have a : q ^ 3 + 1 ≡ 8 + 1 [MOD 9] := (h9.pow 3).add (Nat.ModEq.refl 1)
        exact a.trans (by decide)
      simpa using h3.symm.dvd'
    have h81 : 81 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
      obtain ⟨a, ha⟩ := hd2
      obtain ⟨b, hb⟩ := hd3
      exact ⟨a * b, by rw [ha, hb]; ring⟩
    have h81N : 81 ∣ Nat.card ↥(CFSG.Open.StatedSU 3 q K) := by
      rw [horderSU, mul_assoc]
      obtain ⟨a, ha⟩ := h81
      exact ⟨q ^ 3 * a, by rw [ha]; ring⟩
    have hle : 4 ≤ (Nat.card ↥(CFSG.Open.StatedSU 3 q K)).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (Finite.card_pos.ne')).mp h81N
    omega
  have hmod : q % 9 = 2 ∨ q % 9 = 5 := by
    have hr : q % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have hr3 : q % 9 % 3 = 2 := by
      rw [Nat.mod_mod_of_dvd q (by norm_num : 3 ∣ 9)]; exact hq
    interval_cases q % 9 <;> simp_all
  rw [hKq]
  rcases hmod with h | h <;> rw [Nat.pow_mod, h] <;> norm_num

private theorem k335fsl_su3_core
    (hpow : ∀ {K : Type} [Field K] [Fintype K],
      (Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) → ∀ {x : GL (Fin 3) K},
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 → x ^ 9 = 1 → x ^ 3 = 1)
    (hconj : ∀ {K : Type} [Field K] [Fintype K] {q : ℕ}, Nat.card K = q ^ 2 → q % 3 = 2 →
      ∀ {x y : ↥(CFSG.Open.StatedSU 3 q K)}, x ^ 3 = 1 → y ^ 3 = 1 →
      (∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) →
      (∀ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) →
      ∃ g : ↥(CFSG.Open.StatedSU 3 q K), g⁻¹ * x * g = y)
    {K : Type} [Field K] [Fintype K] {q : ℕ} (hKq : Nat.card K = q ^ 2) (hq : q % 3 = 2)
    {T A : Subgroup ↥(CFSG.Open.StatedSU 3 q K)} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤)
    (hT27 : Nat.card T = 27) (hAT : A ≤ T) (hA : Nat.card A = 9)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set ↥(CFSG.Open.StatedSU 3 q K)) T) : False := by
  classical
  let H := ↥(CFSG.Open.StatedSU 3 q K)
  have hSL : CFSG.Open.StatedSU 3 q K ≤ CFSG.Open.StatedSL 3 K :=
    CFSG.Open.StatedAPI.statedSU_le_statedSL 3 q K
  have h9 : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7 := k335fsl_su_mod_nine hKq hq hT hT27
  have hpowK : ∀ {x : GL (Fin 3) K},
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 → x ^ 9 = 1 → x ^ 3 = 1 :=
    fun {x} hdet hx => hpow h9 hdet hx
  let Scal : Set H :=
    {x | ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c}
  have hScal : Scal.ncard ≤ 3 :=
    k335fsl_scalar_ncard_le_three (L := CFSG.Open.StatedSU 3 q K) hSL
  have hAncard : (A : Set H).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hA
  have hex : ∃ a ∈ A, a ∉ Scal := by
    by_contra h
    have hsub : (A : Set H) ⊆ Scal := by
      intro a ha
      by_contra hna
      exact h ⟨a, ha, hna⟩
    have := Set.ncard_le_ncard hsub
    omega
  obtain ⟨a, haA, haScal⟩ := hex
  have haScal' : ∀ c : K,
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c :=
    fun c hc => haScal ⟨c, hc⟩
  have ha3 : a ^ 3 = 1 :=
    k335fsl_pow_three_of_mem (H := CFSG.Open.StatedSU 3 q K) hSL hpowK hT27 (hAT haA)
  have hsubT : (T : Set H) ⊆ (A : Set H) ∪ Scal := by
    intro t ht
    by_cases htScal : t ∈ Scal
    · exact Or.inr htScal
    · refine Or.inl ?_
      have htScal' : ∀ c : K,
          ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c :=
        fun c hc => htScal ⟨c, hc⟩
      have ht3 : t ^ 3 = 1 :=
        k335fsl_pow_three_of_mem (H := CFSG.Open.StatedSU 3 q K) hSL hpowK hT27 ht
      obtain ⟨g, hg⟩ := hconj hKq hq ha3 ht3 haScal' htScal'
      have hmem : g ⁻¹ * a * g ∈ T := by rw [hg]; exact ht
      have hcl' := hcl a haA g hmem
      rwa [hg] at hcl'
  have hTcard : (T : Set H).ncard = 27 := by
    rw [← Nat.card_coe_set_eq]
    exact hT27
  have hle := Set.ncard_le_ncard hsubT
  have hunion := Set.ncard_union_le (A : Set H) Scal
  omega

theorem k335_su3_false {K : Type} [Field K] [Fintype K] {q : ℕ} (hKq : Nat.card K = q ^ 2)
    (hq : q % 3 = 2) {T A : Subgroup ↥(CFSG.Open.StatedSU 3 q K)}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤) (hT27 : Nat.card T = 27) (hAT : A ≤ T)
    (hA : Nat.card A = 9)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set ↥(CFSG.Open.StatedSU 3 q K)) T) : False := by
  exact k335fsl_su3_core k335_pow_three_gl3 k335_conj_su3 hKq hq hT hT27 hAT hA hcl


private theorem k335trf_exists_conj_map {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {S S' : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤)
    (hS' : CFSG.ABGLocalTools.IsSylowOf p S' ⊤) :
    ∃ x : X, S' = S.map (MulAut.conj x).toMonoidHom := by
  have hSi : ¬ p ∣ S.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hS'i : ¬ p ∣ S'.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS').2.2
    rwa [Subgroup.relIndex_top_right] at h
  let QS : Sylow p X := hS.isPGroup.toSylow hSi
  let QS' : Sylow p X := hS'.isPGroup.toSylow hS'i
  have hQS : (QS : Subgroup X) = S := IsPGroup.toSylow_coe _ _
  have hQS' : (QS' : Subgroup X) = S' := IsPGroup.toSylow_coe _ _
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  have : Finite (Sylow p X) :=
    Finite.of_injective (fun Q : Sylow p X => (Q : Subgroup X)) (fun P Q h => Sylow.ext h)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X QS QS'
  refine ⟨x, ?_⟩
  have hmap : ((x • QS : Sylow p X) : Subgroup X) = S.map (MulAut.conj x).toMonoidHom := by
    ext a
    change a ∈ ((x • QS : Sylow p X) : Set X) ↔ _
    rw [Sylow.coe_smul]
    rfl
  have hx' : ((x • QS : Sylow p X) : Subgroup X) = S' := by
    rw [hx, hQS']
  rw [← hx', hmap]

private theorem k335trf_comap_sylow {X H : Type} [Group X] [Finite X] [Group H]
    {φ : H →* X} (hφ : Function.Injective φ) {S' : Subgroup X}
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' ⊤) (hS'φ : S' ≤ φ.range)
    (hS'27 : Nat.card S' = 27) :
    CFSG.ABGLocalTools.IsSylowOf 3 (S'.comap φ) ⊤ ∧ Nat.card (S'.comap φ) = 27 := by
  have : Finite H := Finite.of_injective φ hφ
  have hmap : (S'.comap φ).map φ = S' := Subgroup.map_comap_eq_self hS'φ
  have hcard : Nat.card (S'.comap φ) = 27 := by
    have h := Subgroup.card_map_of_injective hφ (K := S'.comap φ)
    rw [hmap] at h
    rw [← h]; exact hS'27
  refine ⟨?_, hcard⟩
  apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
  have hHfac : (Nat.card H).factorization 3 = 3 := by
    have hdvdHX : Nat.card H ∣ Nat.card X := by
      rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card φ.range
    have hle : (Nat.card H).factorization 3 ≤ (Nat.card X).factorization 3 :=
      (Nat.factorization_le_iff_dvd (Finite.card_pos (α := H)).ne'
        (Finite.card_pos (α := X)).ne').2 hdvdHX 3
    have hX3 : (Nat.card X).factorization 3 = 3 :=
      k335fsl_factorization_eq_three hS' hS'27
    have hge : 3 ≤ (Nat.card H).factorization 3 := by
      have hdvd : 3 ^ 3 ∣ Nat.card H := by
        rw [show (3 : ℕ) ^ 3 = Nat.card (S'.comap φ) by rw [hcard]; norm_num]
        exact Subgroup.card_subgroup_dvd_card (S'.comap φ)
      exact (Nat.prime_three.pow_dvd_iff_le_factorization (Finite.card_pos (α := H)).ne').mp hdvd
    omega
  rw [Subgroup.card_top, hHfac, hcard]
  norm_num

theorem k335_transfer {X H : Type} [Group X] [Finite X] [Group H] {P S : Subgroup X}
    (hP : K335StrongE9 P S) (hS27 : Nat.card S = 27) {φ : H →* X} (hφ : Function.Injective φ)
    {S' : Subgroup X} (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' ⊤) (hS'φ : S' ≤ φ.range) :
    ∃ T A : Subgroup H, CFSG.ABGLocalTools.IsSylowOf 3 T ⊤ ∧ Nat.card T = 27 ∧ A ≤ T ∧
      Nat.card A = 9 ∧ CFSG.Open.fusionStronglyClosed (A : Set H) T := by
  have : Finite H := Finite.of_injective φ hφ
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ := hP.sylow
  have hS'27 : Nat.card S' = 27 := by
    have hfactX : (Nat.card X).factorization 3 = 3 := k335fsl_factorization_eq_three hS hS27
    have h := hS'.card_eq
    rw [Subgroup.card_top, hfactX] at h
    norm_num at h
    exact h
  obtain ⟨x, hx⟩ := k335trf_exists_conj_map hS hS'
  let P' : Subgroup X := P.map (MulAut.conj x).toMonoidHom
  have hP'le : P' ≤ S' := by
    change P.map (MulAut.conj x).toMonoidHom ≤ S'
    rw [hx]
    exact Subgroup.map_mono hP.le
  have hP'card : Nat.card P' = 9 := by
    change Nat.card (P.map (MulAut.conj x).toMonoidHom) = 9
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hP.card]
  have hP'cl : CFSG.Open.fusionStronglyClosed (P' : Set X) S' := by
    change CFSG.Open.fusionStronglyClosed
      ((P.map (MulAut.conj x).toMonoidHom : Subgroup X) : Set X) S'
    rw [hx]
    exact CFSG.Goldschmidt.LemmaX.stronglyClosed_map_conj hP.closed x
  let T : Subgroup H := S'.comap φ
  let A : Subgroup H := P'.comap φ
  obtain ⟨hTsyl', hTcard'⟩ := k335trf_comap_sylow hφ hS' hS'φ hS'27
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤ := hTsyl'
  have hTcard : Nat.card T = 27 := hTcard'
  have hAcard : Nat.card A = 9 := by
    change Nat.card (P'.comap φ) = 9
    have h := Subgroup.card_map_of_injective hφ (K := P'.comap φ)
    rw [Subgroup.map_comap_eq_self (hP'le.trans hS'φ)] at h
    rw [← h]; exact hP'card
  have hAT : A ≤ T := by
    change P'.comap φ ≤ S'.comap φ
    exact Subgroup.comap_mono hP'le
  have hclA : CFSG.Open.fusionStronglyClosed (A : Set H) T := by
    intro a ha g hg
    change a ∈ P'.comap φ at ha
    change g⁻¹ * a * g ∈ S'.comap φ at hg
    change g⁻¹ * a * g ∈ P'.comap φ
    rw [Subgroup.mem_comap] at ha hg ⊢
    rw [show φ (g⁻¹ * a * g) = (φ g)⁻¹ * φ a * φ g by simp [map_mul]] at hg ⊢
    exact hP'cl (φ a) ha (φ g) hg
  exact ⟨T, A, hTsyl, hTcard, hAT, hAcard, hclA⟩

theorem k335_g2_false (hG2 : K335G2Local) {X : Type} [Group X] [Finite X] {P S : Subgroup X}
    (hP : K335StrongE9 P S) (hS27 : Nat.card S = 27) {p f : ℕ} (h : LieModel X .G2 0 p f)
    (hp : p ≠ 3) : False := by
  obtain ⟨K, _, _, H, hH, φ, hφ, S', hS', hS'φ⟩ := hG2 X p f h hp
  obtain ⟨T, A, hT, hT27, hAT, hA, hcl⟩ := k335_transfer hP hS27 hφ hS' hS'φ
  rcases hH with ⟨hq, hK, rfl⟩ | ⟨hq, hK, rfl⟩
  · exact k335_sl3_false (by rw [hK]; exact hq) hT hT27 hAT hA hcl
  · exact k335_su3_false hK hq hT hT27 hAT hA hcl

theorem k335_ree_false (hRee : K335ReeLocal) {X : Type} [Group X] [Finite X] {P S : Subgroup X}
    (hP : K335StrongE9 P S) (hS27 : Nat.card S = 27) {f : ℕ} (h : LieModel X .twistedF4 0 2 f) :
    False := by
  obtain ⟨K, _, _, hK, φ, hφ, S', hS', hS'φ⟩ := hRee X f h
  obtain ⟨T, A, hT, hT27, hAT, hA, hcl⟩ := k335_transfer hP hS27 hφ hS' hS'φ
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, -⟩ := h.admissible
  refine k335_su3_false hK ?_ hT hT27 hAT hA hcl
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
