module

public import CFSG.RankThree.PartTwo.Sec8.Hering88LCLift
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open scoped commutatorElement

namespace SU3Two

variable {F : Type} [Field F]

@[expose] def yMat (ω : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![ω, ω ^ 2, 1]

@[expose] def pMat : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem yMat_mul (ω ω' : F) :
    yMat ω * yMat ω' = Matrix.diagonal ![ω * ω', ω ^ 2 * ω' ^ 2, 1] := by
  rw [yMat, yMat, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem diagonal_ones : Matrix.diagonal ![(1 : F), 1, 1] = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem mul_sq_eq_one {ω : F} (hω3 : ω ^ 3 = 1) : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω3]

theorem sq_mul_eq_one {ω : F} (hω3 : ω ^ 3 = 1) : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω3]

theorem sq_mul_sq_sq_eq_one {ω : F} (hω3 : ω ^ 3 = 1) : ω ^ 2 * (ω ^ 2) ^ 2 = 1 := by
  rw [← pow_mul, ← pow_add, show 2 + 2 * 2 = 3 * 2 by rfl, pow_mul, hω3, one_pow]

theorem sq_sq_mul_sq_eq_one {ω : F} (hω3 : ω ^ 3 = 1) : (ω ^ 2) ^ 2 * ω ^ 2 = 1 := by
  rw [mul_comm, sq_mul_sq_sq_eq_one hω3]

theorem yMat_mul_yMat_sq {ω : F} (hω3 : ω ^ 3 = 1) :
    yMat ω * yMat (ω ^ 2) = (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [yMat_mul, mul_sq_eq_one hω3, show (ω ^ 2) ^ 2 = (ω ^ 2) ^ 2 from rfl,
    sq_mul_sq_sq_eq_one hω3, diagonal_ones]

theorem yMat_sq_mul_yMat {ω : F} (hω3 : ω ^ 3 = 1) :
    yMat (ω ^ 2) * yMat ω = (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [yMat_mul, sq_mul_eq_one hω3, sq_sq_mul_sq_eq_one hω3, diagonal_ones]

theorem pMat_mul_self : pMat * pMat = (1 : Matrix (Fin 3) (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def Y {ω : F} (hω3 : ω ^ 3 = 1) : GL (Fin 3) F :=
  ⟨yMat ω, yMat (ω ^ 2), yMat_mul_yMat_sq hω3, yMat_sq_mul_yMat hω3⟩

@[expose] def P : GL (Fin 3) F := ⟨pMat, pMat, pMat_mul_self, pMat_mul_self⟩

theorem Y_pow_three {ω : F} (hω3 : ω ^ 3 = 1) : Y hω3 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change yMat ω ^ 3 = 1
  rw [yMat, Matrix.diagonal_pow, ← diagonal_ones]
  congr 1
  ext i
  fin_cases i <;> simp [hω3]
  rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]

theorem P_mul_Y_ne {ω : F} (hω3 : ω ^ 3 = 1) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    P * Y hω3 ≠ Y hω3 * P := by
  intro h
  have e := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 1) h
  simp [P, Y, pMat, yMat, Matrix.mul_apply, Fin.sum_univ_three] at e
  apply hω1
  have h2 : ω * (ω - 1) = 0 := by linear_combination e
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hω0
  · exact sub_eq_zero.mp h

variable [CharP F 2]

theorem Y_mem {ω : F} (hω3 : ω ^ 3 = 1) :
    Y hω3 ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 2 F := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (yMat ω).det = 1
    rw [yMat, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    exact mul_sq_eq_one hω3
  · change ((yMat ω).map (· ^ 2))ᵀ * yMat ω = 1
    have hmap : (yMat ω).map (· ^ 2) = yMat (ω ^ 2) := by
      rw [yMat, yMat, Matrix.diagonal_map (by simp)]
      congr 1
      ext i
      fin_cases i <;> simp
    rw [hmap, yMat, Matrix.diagonal_transpose, ← yMat, yMat_sq_mul_yMat hω3]

theorem P_mem : P ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 2 F := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (pMat : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [pMat, Matrix.det_fin_three]
    simp
    exact CharTwo.neg_eq (1 : F)
  · change ((pMat : Matrix (Fin 3) (Fin 3) F).map (· ^ 2))ᵀ * pMat = 1
    have hmap : (pMat : Matrix (Fin 3) (Fin 3) F).map (· ^ 2) = pMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pMat]
    have htr : (pMat : Matrix (Fin 3) (Fin 3) F)ᵀ = pMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hmap, htr, pMat_mul_self]

end SU3Two

theorem exists_cube_root_of_card_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    ∃ ω : F, ω ^ 3 = 1 ∧ ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  have hlt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hc]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hω0 : ω ≠ 0 := fun h => hω (by simp [h])
  have hω1 : ω ≠ 1 := fun h => hω (by simp [h])
  refine ⟨ω, ?_, hω0, hω1⟩
  have h := FiniteField.pow_card_sub_one_eq_one ω hω0
  rwa [hc] at h

variable {G : Type} [Group G] [Finite G]

theorem exists_inverting_pair {K : Subgroup G} {a : G} (ha3 : a ^ 3 = 1)
    (ha : KFacts.InducesStdKind K a .field)
    (hK : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 (3 * 1)))) :
    ∃ t u : K, (t : G) ∈ Subgroup.centralizer ({a} : Set G) ∧
      (u : G) ∈ Subgroup.centralizer ({a} : Set G) ∧ (∃ e : ℕ, t ^ 2 ^ e = 1) ∧ u ^ 3 = 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) u ≠ 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) t *
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) u *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) t)⁻¹ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) u)⁻¹ := by
  obtain ⟨haN, hout⟩ := KFacts.InducesStdKind.inducesOuterTheta K ha (by decide)
  obtain ⟨e⟩ := hK
  obtain ⟨t₀, w₀, ht₀, hw₀, ht2, hw3, hw1, hconj⟩ :=
    exists_inverting_pair_of_projSL haN ha3 hout e
  exact lift_inverting_pair haN ha3 ht₀ hw₀ ht2 hw3 hw1 hconj

theorem exists_noncomm_three {K : Subgroup G} {a : G} (ha3 : a ^ 3 = 1)
    (ha : KFacts.InducesStdKind K a .field)
    (hK : IsoSUThree (K ⧸ aschbacherSolvableCore 3 K) (2 ^ (3 * 1)) ∨
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 (3 * 1)))) :
    ∃ u p : K, (u : G) ∈ Subgroup.centralizer ({a} : Set G) ∧ u ^ 3 = 1 ∧
      ⁅(u : G), (p : G)⁆ ∉ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨haN, hout⟩ := KFacts.InducesStdKind.inducesOuterTheta K ha (by decide)
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hq
  obtain ⟨w₀, p₀, hw₀, hw3, hwp⟩ : ∃ w₀ p₀ : K ⧸ aschbacherSolvableCore 3 K,
      w₀ ∈ barCentralizer (Subgroup.zpowers a) K ∧ w₀ ^ 3 = 1 ∧ w₀ * p₀ ≠ p₀ * w₀ := by
    rcases hK with hSU | he
    · obtain ⟨F, _, _, hF, ⟨φ⟩⟩ :=
        KFacts.isoSUThree_barCentralizer_of_inducesStdKind odd_one hSU ha3 ha
      have e1 : (2 : ℕ) ^ 1 = 2 := pow_one 2
      rw [e1] at hF φ
      have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
      haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (k := 2) (by norm_num) (by rw [hF4]; norm_num)
      obtain ⟨ω, hω3, hω0, hω1⟩ := exists_cube_root_of_card_four hF4
      set y : CFSG.Assembly.LowTwoRank.StatedSU 3 2 F := ⟨SU3Two.Y hω3, SU3Two.Y_mem hω3⟩
      set p : CFSG.Assembly.LowTwoRank.StatedSU 3 2 F := ⟨SU3Two.P, SU3Two.P_mem⟩
      refine ⟨(φ.symm y : _), (φ.symm p : _), (φ.symm y).2, ?_, ?_⟩
      · rw [← Subgroup.coe_pow, ← map_pow]
        have : y ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact SU3Two.Y_pow_three hω3)
        rw [this, map_one, Subgroup.coe_one]
      · intro h
        apply SU3Two.P_mul_Y_ne hω3 hω0 hω1
        have h' : φ.symm y * φ.symm p = φ.symm p * φ.symm y := Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h)
        rw [← map_mul, ← map_mul] at h'
        have := congrArg Subtype.val (φ.symm.injective h')
        exact this.symm
    · obtain ⟨e⟩ := he
      obtain ⟨t₀, w₀, ht₀, hw₀, -, hw3, hw1, hconj⟩ :=
        exists_inverting_pair_of_projSL haN ha3 hout e
      refine ⟨w₀, t₀, hw₀, hw3, fun h => hw1 ?_⟩
      have h1 : w₀ = w₀⁻¹ := by
        rw [← hconj, ← h, mul_inv_cancel_right]
      have h2 : w₀ ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [h1]
        exact mul_inv_cancel w₀
      calc w₀ = w₀ ^ 3 * (w₀ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hw3, h2, inv_one, mul_one]
  obtain ⟨u, hua, hu3, hup⟩ := lift_noncomm_three haN ha3 hw₀ hw3 hwp
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) p₀
  exact ⟨u, p, hua, hu3, commutator_not_mem_theta hup⟩

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
