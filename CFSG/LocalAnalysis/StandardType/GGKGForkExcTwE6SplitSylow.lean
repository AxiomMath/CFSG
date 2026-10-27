module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6SplitOrders
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.SylowFrame

public section

namespace CFSG.StandardType

namespace ExcTwE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open scoped Matrix Polynomial

private def ggKGTz_M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
  toMat TwistTag.E6.tag.rank twE6PermList

private def ggKGTz_L : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]

private def ggKGTz_B : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0]]

private def ggKGTz_B' : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0],
   [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0]]

private lemma ggKGTz_B_mul : toMat TwistTag.E6.tag.rank ggKGTz_B *
    toMat TwistTag.E6.tag.rank ggKGTz_B' = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma ggKGTz_L_charpoly :
    (toMat TwistTag.E6.tag.rank ggKGTz_L).charpoly =
      (Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 2 := by
  have h1 := charpoly_eq_mul_of_blocks (k := 2) (m := 4) ggKGTz_L (by decide)
  rw [show (2 : ℕ) + 4 = TwistTag.E6.tag.rank from rfl] at h1
  rw [h1]
  have h2 := charpoly_eq_mul_of_blocks (k := 2) (m := 2) (lbotRight 2 4 ggKGTz_L) (by decide)
  rw [show (2 : ℕ) + 2 = 4 from rfl] at h2
  rw [h2]
  have hA : toMat 2 (ltopLeft 2 ggKGTz_L) = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hA2 : toMat 2 (ltopLeft 2 (lbotRight 2 4 ggKGTz_L)) = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hB : toMat 2 (lbotRight 2 2 (lbotRight 2 4 ggKGTz_L)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have ht : (toMat 2 (ltopLeft 2 ggKGTz_L)).charpoly =
      (Polynomial.X - 1) * (Polynomial.X + 1) := by
    rw [hA, Matrix.charpoly_fin_two, Matrix.det_fin_two]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply]
    ring
  have ht2 : (toMat 2 (ltopLeft 2 (lbotRight 2 4 ggKGTz_L))).charpoly =
      (Polynomial.X - 1) * (Polynomial.X + 1) := by
    rw [hA2, Matrix.charpoly_fin_two, Matrix.det_fin_two]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply]
    ring
  have hb2 : (toMat 2 (lbotRight 2 2 (lbotRight 2 4 ggKGTz_L))).charpoly =
      (Polynomial.X - 1) ^ 2 := by
    rw [hB, Matrix.charpoly_one]
    norm_num
  rw [ht, ht2, hb2]
  ring

private lemma ggKGTz_M_charpoly :
    ggKGTz_M.charpoly = (Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 2 := by
  have hconj : toMat TwistTag.E6.tag.rank ggKGTz_B' * ggKGTz_M *
      toMat TwistTag.E6.tag.rank ggKGTz_B = toMat TwistTag.E6.tag.rank ggKGTz_L := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [charpoly_eq_of_conj (B := toMat TwistTag.E6.tag.rank ggKGTz_B)
    (B' := toMat TwistTag.E6.tag.rank ggKGTz_B') ggKGTz_B_mul, hconj]
  exact ggKGTz_L_charpoly

private lemma ggKGTz_M_mul_self : ggKGTz_M * ggKGTz_M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma ggKGTz_M_pow : ggKGTz_M ^ 2 = 1 := by
  rw [pow_two, ggKGTz_M_mul_self]

private lemma ggKGTz_M_hv : ∀ x, (1 : WeylGroup TwistTag.E6.tag) • x =
    ggKGTz_M *ᵥ permLattice TwistTag.E6.perm x := by
  intro x
  rw [one_smul, permLattice_E6_eq]
  change x = ggKGTz_M *ᵥ (ggKGTz_M *ᵥ x)
  rw [Matrix.mulVec_mulVec, ggKGTz_M_mul_self, Matrix.one_mulVec]

private lemma ggKGTz_eval (N : ℕ) :
    Polynomial.eval ((N : ℤ)) ((Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 2) =
      (((N : ℤ) - 1) ^ 4) * (((N : ℤ) + 1) ^ 2) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]

private lemma ggKGTz_natAbs_eval (N : ℕ) (hN : 1 ≤ N) :
    ((Polynomial.eval ((N : ℤ))
        ((Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 2)).natAbs) =
      (N - 1) ^ 4 * (N + 1) ^ 2 := by
  rw [ggKGTz_eval]
  have h1 : ((N : ℤ) - 1) = ((N - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hN]
    norm_num
  have h2 : ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) := by norm_num
  rw [h1, h2, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast,
    Int.natAbs_natCast]

private lemma ggKGTz_factorization {N p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 2 ≤ N)
    (hpq : p ∣ N - 1) :
    ((N - 1) ^ 4 * (N + 1) ^ 2).factorization p = 4 * padicValNat p (N - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNdvd : ¬ p ∣ N + 1 := by
    intro h
    have h2 : p ∣ (N + 1) - (N - 1) := Nat.dvd_sub h hpq
    have hsub : (N + 1) - (N - 1) = 2 := by omega
    rw [hsub] at h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hN1 : N - 1 ≠ 0 := by omega
  have hN1' : N + 1 ≠ 0 := by omega
  rw [Nat.factorization_def _ hp]
  rw [padicValNat.mul (pow_ne_zero _ hN1) (pow_ne_zero _ hN1')]
  rw [padicValNat.pow, padicValNat.pow]
  rw [padicValNat.eq_zero_of_not_dvd hNdvd]
  ring

private lemma ggKGTz_M_hev {n : ℕ} (hn0 : n ≠ 0) :
    ggKGTz_M.charpoly.eval (((2 ^ n : ℕ) : ℤ)) ≠ 0 := by
  rw [ggKGTz_M_charpoly, ggKGTz_eval]
  have hq2 : 2 ≤ 2 ^ n := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have h1 : (((2 ^ n : ℕ) : ℤ) - 1) ≠ 0 := by
    have hcast : (2 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast hq2
    omega
  have h2 : (((2 ^ n : ℕ) : ℤ) + 1) ≠ 0 := by positivity
  exact mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)

private lemma ggKGTz_M_factorization {n p : ℕ} (hn0 : n ≠ 0) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n - 1) :
    (((ggKGTz_M.charpoly.eval (((2 ^ n : ℕ) : ℤ))).natAbs).factorization p) =
      4 * padicValNat p (2 ^ n - 1) := by
  have hq2 : 2 ≤ 2 ^ n := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hN : 1 ≤ 2 ^ n := by omega
  rw [ggKGTz_M_charpoly, ggKGTz_natAbs_eval (2 ^ n) hN]
  exact ggKGTz_factorization hp hp5 hq2 hpq

private theorem ggKGTz_torus_commute
    {L : Type} [Field L] (n : ModGL TwistTag.E6.tag L)
    (Φ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L)
    {h h' : ModGL TwistTag.E6.tag L} (hh : h ∈ twistedTorusOf n Φ)
    (hh' : h' ∈ twistedTorusOf n Φ) : Commute h h' := by
  have h1 : h ∈ torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

private theorem ggKGTz_twistHom_baseChange_eq_self
    {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (y : twistedE6RootGroup K σ) :
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K))
          (y : ModGL TwistTag.E6.tag K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (y : ModGL TwistTag.E6.tag K) := by
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      Fr.comp (algebraMap K (AlgebraicClosure K)) := by
    ext c
    change algebraMap K (AlgebraicClosure K) (σ c) =
      Fr (algebraMap K (AlgebraicClosure K) c)
    rw [hσ, hFr, map_pow]
  rw [twistHom_baseChangeGL (algebraMap K (AlgebraicClosure K)) hcomm,
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom y.2)).2]

theorem twE6SCTorusInput_split
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n - 1) :
    TwE6SCTorusInput K σ n p 4 := by
  intro E hE h3 h4 hsc
  haveI : Fintype K := Fintype.ofFinite K
  have hn0 : n ≠ 0 := by
    intro hn
    have h2 : 2 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [hK, hn] at h2
    norm_num at h2
  have hf : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
  have hp3 : 3 < p := by omega
  have hord : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
      ((ggKGTz_M.charpoly.eval (((2 ^ n : ℕ) : ℤ))).natAbs).factorization p := by
    rw [Nat.factorization_def _ hp, padicValNat_card_twE6_split σ hp hp5 hK hσ hpq]
    exact le_of_eq (ggKGTz_M_factorization hn0 hp hp5 hpq).symm
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
    exists_langFrame_twistedE6_sylow (ℓ := 2) (f := n) (n := 2) Nat.prime_two hf K hK σ hσ
      hp hp3 (1 : WeylGroup TwistTag.E6.tag) ggKGTz_M_hv (by norm_num) ggKGTz_M_pow
      (ggKGTz_M_hev hn0) hord
  obtain ⟨c, hc⟩ := hconj E hE.2
  let g0' : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) * g0
  have hg0'C : g0' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    dsimp only [g0']
    refine (adjointGroup TwistTag.E6.tag (AlgebraicClosure K)).mul_mem ?_ hg0C
    exact baseChangeGL_mem_adjointGroup _
      (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom
        (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom (inv_mem c.2)))
  have hg0'Lang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0' =
      g0' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
        (1 : WeylGroup TwistTag.E6.tag) := by
    dsimp only [g0']
    rw [map_mul, ggKGTz_twistHom_baseChange_eq_self hσ Fr hFr c⁻¹, hg0]
    group
  let T : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
      (1 : WeylGroup TwistTag.E6.tag)) (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
  have hET : ∀ x ∈ E, g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0' ∈ T := by
    intro x hx
    obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.1 (hc x hx)
    have hconj : g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0' =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((c * x * c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
      dsimp only [g0']
      rw [show ((c * x * c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
          (c : ModGL TwistTag.E6.tag K) * (x : ModGL TwistTag.E6.tag K) *
            (c⁻¹ : ModGL TwistTag.E6.tag K) by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]]
      rw [Subgroup.coe_inv, map_mul, map_mul, map_inv]
      group
    rw [hconj]
    have ht' : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((c * x * c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 = t := by
      rw [← ht]
      change g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t
      group
    rw [ht']
    exact htT
  have hiff : ∀ x : twistedE6RootGroup K σ, x ∈ E ↔ x ^ p = 1 ∧
      g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0' ∈ T := by
    intro x
    constructor
    · intro hx
      exact ⟨hE.2 x hx, hET x hx⟩
    · rintro ⟨hxpow, hxT⟩
      refine hsc x ?_ hxpow
      intro e he
      have heT := hET e he
      have hcommT : (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) * g0') *
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0') =
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0') *
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) * g0') :=
        (ggKGTz_torus_commute _ _ heT hxT).eq
      have hcommB : baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) := by
        have h := congrArg (fun t => g0' * t * g0'⁻¹) hcommT
        calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)
            = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (e : ModGL TwistTag.E6.tag K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (x : ModGL TwistTag.E6.tag K) * g0')) * g0'⁻¹ := by group
          _ = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (x : ModGL TwistTag.E6.tag K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (e : ModGL TwistTag.E6.tag K) * g0')) * g0'⁻¹ := by rw [hcommT]
          _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) := by
                group
      apply Subtype.ext
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommB.symm
  refine ⟨{
    Fr := Fr
    v := 1
    g0 := g0'
    fr_eq := hFr
    g0_mem := hg0'C
    lang := hg0'Lang
    mem_iff := hiff }, ?_, ?_⟩
  · intro _
    rfl
  · intro hpm1
    exfalso
    have hsub : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
      have h1 : 0 < 2 ^ n := pow_pos (by norm_num) n
      omega
    have hdvd2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpm1 hpq
      rwa [hsub] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end ExcTwE6Split

end CFSG.StandardType

end
