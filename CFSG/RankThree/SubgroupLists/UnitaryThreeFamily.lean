module

public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import Certificates.Certificate43
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section SUTwo

variable {K : Type} [Field K] [Finite K] {r f : ℕ} [Fact r.Prime] [CharP K r]

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg in
theorem nonempty_sl2_mulEquiv_statedSU_two (hK : Nat.card K = (r ^ f) ^ 2) :
    Nonempty (SL(2, fixedSubfield K r f) ≃* StatedSU 2 (r ^ f) K) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  exact ⟨((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 2))⟩

open CFSG.LieType.Steinberg in
theorem card_statedSU_two (hK : Nat.card K = (r ^ f) ^ 2) :
    Nat.card (StatedSU 2 (r ^ f) K) = r ^ f * ((r ^ f) ^ 2 - 1) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_statedSU_two hK
  rw [← Nat.card_congr e.toEquiv, card_specialLinearGroup_fin_two, card_fixedSubfield hK]

theorem isPerfect_statedSU_two (hK : Nat.card K = (r ^ f) ^ 2) (hq : 4 ≤ r ^ f) :
    Group.IsPerfect (StatedSU 2 (r ^ f) K) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_statedSU_two hK
  have : Group.IsPerfect SL(2, CFSG.LieType.Steinberg.fixedSubfield K r f) := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    classical
    have : Fintype (CFSG.LieType.Steinberg.fixedSubfield K r f) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (CFSG.LieType.Steinberg.fixedSubfield K r f))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        CFSG.LieType.Steinberg.card_fixedSubfield hK]; exact hq)
    exact ⟨s, hs⟩
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end SUTwo

section Levi

variable {K : Type} [Field K]

@[expose] noncomputable def blockGL3 : GL (Fin 2) K →* GL (Fin 3) K where
  toFun A := ⟨leviMat (A : Matrix (Fin 2) (Fin 2) K), leviMat ((A⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), by
    rw [← leviMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, leviMat_one], by
    rw [← leviMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, leviMat_one]⟩
  map_one' := Units.ext (by simp [leviMat_one])
  map_mul' A B := Units.ext (by simp [leviMat_mul])

theorem coe_blockGL3 (A : GL (Fin 2) K) :
    ((blockGL3 A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      leviMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem map_blockGL3_statedSU_le {q : ℕ} (hq : 1 ≤ q) :
    (StatedSU 2 q K).map blockGL3 ≤ StatedSU 3 q K := by
  rw [StatedSU, MonoidHom.map_closure, StatedSU]
  apply Subgroup.closure_mono
  rintro _ ⟨A, ⟨hdet, hu⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [coe_blockGL3, det_leviMat, hdet]
  · rw [coe_blockGL3]
    have hq0 : (0 : K) ^ q = 0 := zero_pow (by omega)
    have e := fun i j => congrFun (congrFun hu i) j
    have e00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 0 0
    have e01 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 0 1
    have e10 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 1 0
    have e11 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 1 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leviMat, Matrix.mul_apply, Fin.sum_univ_three, hq0, e00, e01, e10, e11]

theorem negDiag3_mem_statedSU {q : ℕ} (hq : Odd q) : negDiag3 K ∈ StatedSU 3 q K := by
  apply Subgroup.subset_closure
  refine ⟨by simp [coe_negDiag3, det_diagonal, Fin.prod_univ_three], ?_⟩
  rw [coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, diagonal, hq.neg_one_pow, hq.pos.ne']

theorem blockGL3_commute_negDiag3 (A : GL (Fin 2) K) :
    blockGL3 A * negDiag3 K = negDiag3 K * blockGL3 A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blockGL3, coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat, Matrix.mul_apply, diagonal]

theorem negDiag3_not_scalar (h2 : (2 : K) ≠ 0) : negDiag3 K ∉ StatedScalars (Fin 3) K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  have h0 := congrFun (congrFun h 0) 0
  have h2' := congrFun (congrFun h 2) 2
  simp [coe_negDiag3, Matrix.GeneralLinearGroup.coe_scalar, diagonal] at h0 h2'
  have h1 := congrArg Units.val (h0.symm.trans h2')
  simp only [Units.val_neg, Units.val_one] at h1
  apply h2
  linear_combination -h1

theorem blockGL3_eq_one_of_scalar {A : GL (Fin 2) K} (hA : blockGL3 A ∈ StatedScalars (Fin 3) K) :
    A = 1 := by
  obtain ⟨c, hc⟩ := hA
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  have e := fun i j => congrFun (congrFun h i) j
  have e22 := e 2 2
  simp [coe_blockGL3, leviMat, Matrix.GeneralLinearGroup.coe_scalar] at e22
  apply Units.ext
  ext i j
  have := e (Fin.castSucc i) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;>
    simp [coe_blockGL3, leviMat, e22] at this ⊢ <;>
    simp_all

end Levi

section PSU3

variable {K : Type} [Field K]

@[expose] noncomputable def negDiagSU3 {q : ℕ} (hq : Odd q) : StatedSU 3 q K :=
  ⟨negDiag3 K, negDiag3_mem_statedSU hq⟩

@[expose] noncomputable def leviSU3 (q : ℕ) : Subgroup (StatedSU 3 q K) :=
  ((StatedSU 2 q K).map blockGL3).subgroupOf (StatedSU 3 q K)

theorem leviSU3_commute {q : ℕ} (hq : Odd q) (x : StatedSU 3 q K)
    (hx : x ∈ leviSU3 q) : x * negDiagSU3 hq = negDiagSU3 hq * x := by
  obtain ⟨A, -, hA⟩ := hx
  apply Subtype.ext
  change (x : GL (Fin 3) K) * negDiag3 K = negDiag3 K * x
  have hA' : (x : GL (Fin 3) K) = blockGL3 A := hA.symm
  rw [hA']
  exact blockGL3_commute_negDiag3 _

@[expose] noncomputable def leviPSU3 (q : ℕ) : Subgroup (StatedProj (StatedSU 3 q K)) :=
  (leviSU3 q).map (QuotientGroup.mk' _)

theorem nonempty_mulEquiv_leviPSU3 (q : ℕ) (hq : 1 ≤ q) :
    Nonempty (StatedSU 2 q K ≃* leviPSU3 (K := K) q) := by
  classical
  let φ : StatedSU 2 q K →* StatedProj (StatedSU 3 q K) :=
    (QuotientGroup.mk' _).comp
      ((blockGL3.comp (StatedSU 2 q K).subtype).codRestrict (StatedSU 3 q K) fun A =>
        map_blockGL3_statedSU_le hq ⟨A, A.2, rfl⟩)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro A hA
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hA
    exact Subtype.ext (blockGL3_eq_one_of_scalar hA)
  have hrange : φ.range = leviPSU3 q := by
    ext y
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨A, A.2, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨A, hA, hAx⟩, rfl⟩
      refine ⟨⟨A, hA⟩, ?_⟩
      change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ x
      congr 1
      exact Subtype.ext hAx
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)⟩

@[expose] noncomputable def negDiagPSU3 {q : ℕ} (hq : Odd q) : StatedProj (StatedSU 3 q K) :=
  QuotientGroup.mk' _ (negDiagSU3 (K := K) hq)

theorem negDiagPSU3_sq {q : ℕ} (hq : Odd q) : negDiagPSU3 (K := K) hq ^ 2 = 1 := by
  rw [negDiagPSU3, ← map_pow]
  rw [show negDiagSU3 (K := K) hq ^ 2 = 1 from Subtype.ext (by
    change negDiag3 K ^ 2 = 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_negDiag3, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, diagonal]), map_one]

theorem negDiagPSU3_ne_one (h2 : (2 : K) ≠ 0) {q : ℕ} (hq : Odd q) :
    negDiagPSU3 (K := K) hq ≠ 1 := by
  intro h
  rw [negDiagPSU3, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  exact negDiag3_not_scalar h2 h

theorem leviPSU3_commute {q : ℕ} (hq : Odd q) (y : StatedProj (StatedSU 3 q K))
    (hy : y ∈ leviPSU3 q) : y * negDiagPSU3 hq = negDiagPSU3 hq * y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [negDiagPSU3, ← map_mul, ← map_mul, leviSU3_commute hq x hx]

end PSU3

theorem not_dvd_cube_add_one {p d : ℕ} (hp : 3 ≤ p) (hd : d ≤ 3) (hd0 : 0 < d) :
    ¬ p ^ 3 + 1 ∣ d * ((p ^ 3 - 1) * (p - 1)) := by
  intro h
  have h1 : d * ((p ^ 3 - 1) * (p - 1)) + 2 * d * (p - 1) = d * (p - 1) * (p ^ 3 + 1) := by
    have : p ^ 3 - 1 + 2 = p ^ 3 + 1 := by
      have : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    calc d * ((p ^ 3 - 1) * (p - 1)) + 2 * d * (p - 1)
        = d * (p - 1) * (p ^ 3 - 1 + 2) := by ring
      _ = d * (p - 1) * (p ^ 3 + 1) := by rw [this]
  have h2 : p ^ 3 + 1 ∣ 2 * d * (p - 1) := by
    have h3 : p ^ 3 + 1 ∣ d * (p - 1) * (p ^ 3 + 1) := dvd_mul_left _ _
    rw [← h1] at h3
    exact (Nat.dvd_add_right h).mp h3
  have hpos : 0 < 2 * d * (p - 1) := by
    apply Nat.mul_pos (Nat.mul_pos (by norm_num) hd0)
    omega
  have hle := Nat.le_of_dvd hpos h2
  have : 2 * d * (p - 1) ≤ 6 * p := by
    calc 2 * d * (p - 1) ≤ 2 * 3 * p := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd) (Nat.sub_le p 1)
      _ = 6 * p := by ring
  have hp3 : 9 * p ≤ p ^ 3 := by
    have : 9 ≤ p ^ 2 := by nlinarith
    calc 9 * p ≤ p ^ 2 * p := Nat.mul_le_mul_right p this
      _ = p ^ 3 := by ring
  omega

theorem card_GL_three_zmod {p : ℕ} [Fact p.Prime] :
    Nat.card (GL (Fin 3) (ZMod p)) = p ^ 3 * ((p ^ 3 - 1) * (p ^ 2 - 1) * (p - 1)) := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  have e1 : p ^ 3 - p = p * (p ^ 2 - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ']
  have e2 : p ^ 3 - p ^ 2 = p ^ 2 * (p - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ]
  rw [e1, e2]
  ring

theorem not_dvd_card_GL_of_psu3 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K]
    (hK : Nat.card K = (p ^ 1) ^ 2) :
    ¬ Nat.card (StatedProj (StatedSU 3 (p ^ 1) K)) ∣ Nat.card (GL (Fin 3) (ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  intro h
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp le_rfl hK (by norm_num)] at h
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  have h3 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_singleton, pow_one, h3] at h
  have hp2le : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hA : ((p : ℤ) ^ 2 - (-1) ^ 2).toNat = p ^ 2 - 1 := by
    have : ((p : ℤ) ^ 2 - (-1) ^ 2) = ((p ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hp2le]
      ring
    rw [this, Int.toNat_natCast]
  have hB : ((p : ℤ) ^ 3 - (-1) ^ 3).toNat = p ^ 3 + 1 := by
    have : ((p : ℤ) ^ 3 - (-1) ^ 3) = ((p ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [hA, hB] at h
  set d := Nat.gcd 3 (p + 1) with hd
  have hd3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (p + 1))
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
  set N := p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) with hNdef
  have hddvd : d ∣ N := by
    have h1 : p + 1 ∣ p ^ 3 + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow p 1 (by decide : Odd 3)
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left
      (Nat.dvd_trans (Nat.gcd_dvd_right 3 (p + 1)) h1) _) _
  obtain ⟨m, hm⟩ := h
  have hNd : d * (N / d) = N := Nat.mul_div_cancel' hddvd
  rw [card_GL_three_zmod] at hm
  have key : N ∣ d * (p ^ 3 * ((p ^ 3 - 1) * (p ^ 2 - 1) * (p - 1))) := by
    refine ⟨m, ?_⟩
    rw [hm]
    calc d * (N / d * m) = d * (N / d) * m := by ring
      _ = N * m := by rw [hNd]
  have hpos : 0 < p ^ 3 * (p ^ 2 - 1) := by
    apply Nat.mul_pos (pow_pos hp.pos 3)
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  apply not_dvd_cube_add_one hp3 hd3 hd0
  have : p ^ 3 * (p ^ 2 - 1) * (p ^ 3 + 1) ∣
      p ^ 3 * (p ^ 2 - 1) * (d * ((p ^ 3 - 1) * (p - 1))) := by
    have e1 : N = p ^ 3 * (p ^ 2 - 1) * (p ^ 3 + 1) := by rw [hNdef]; ring
    have e2 : d * (p ^ 3 * ((p ^ 3 - 1) * (p ^ 2 - 1) * (p - 1))) =
        p ^ 3 * (p ^ 2 - 1) * (d * ((p ^ 3 - 1) * (p - 1))) := by ring
    rw [← e1, ← e2]
    exact key
  exact (Nat.mul_dvd_mul_iff_left hpos).mp this

section RationalFive

@[expose] def so3FiveX : Matrix (Fin 3) (Fin 3) (ZMod 5) := !![1, 1, 2; 4, 3, 4; 3, 4, 4]

@[expose] def so3FiveG : Matrix (Fin 3) (Fin 3) (ZMod 5) := !![1, 0, 0; 0, 0, 1; 0, 4, 0]

theorem so3FiveX_orth : so3FiveXᵀ * so3FiveX = 1 := by decide

theorem so3FiveX_det : so3FiveX.det = 1 := by rw [Matrix.det_fin_three]; decide

theorem so3FiveX_pow : so3FiveX ^ 5 = 1 := by decide

theorem so3FiveG_orth : so3FiveGᵀ * so3FiveG = 1 := by decide

theorem so3FiveG_det : so3FiveG.det = 1 := by rw [Matrix.det_fin_three]; decide

theorem so3FiveG_conj : so3FiveG * so3FiveX = so3FiveX ^ 2 * so3FiveG := by decide

variable {K : Type} [Field K] [CharP K 5]

theorem mem_statedSU_of_orth (A : Matrix (Fin 3) (Fin 3) (ZMod 5)) (hA : Aᵀ * A = 1)
    (hdet : A.det = 1) (hu : IsUnit (A.map (ZMod.castHom (dvd_refl 5) K)).det) :
    Matrix.GeneralLinearGroup.mk'' (A.map (ZMod.castHom (dvd_refl 5) K)) hu ∈
      StatedSU 3 5 K := by
  apply Subgroup.subset_closure
  set φ := ZMod.castHom (dvd_refl 5) K
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfrob : (A.map φ).map (· ^ 5) = A.map φ := by
    ext i j
    simp only [Matrix.map_apply]
    rw [← map_pow, ZMod.pow_card]
  refine ⟨?_, ?_⟩
  · change (A.map φ).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · change ((A.map φ).map (· ^ 5))ᵀ * A.map φ = 1
    rw [hfrob, ← Matrix.transpose_map, ← Matrix.map_mul, hA, Matrix.map_one φ (map_zero φ)
      (map_one φ)]

theorem isUnit_det_map_of_det_eq_one (A : Matrix (Fin 3) (Fin 3) (ZMod 5)) (hdet : A.det = 1) :
    IsUnit (A.map (ZMod.castHom (dvd_refl 5) K)).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  exact isUnit_one

theorem exists_rational_five_psu3 :
    ∃ s g : StatedProj (StatedSU 3 5 K), s ^ 5 = 1 ∧ s ≠ 1 ∧ g * s * g⁻¹ = s ^ 2 := by
  classical
  set φ := ZMod.castHom (dvd_refl 5) K
  set X : GL (Fin 3) K := Matrix.GeneralLinearGroup.mk'' (so3FiveX.map φ)
    (isUnit_det_map_of_det_eq_one _ so3FiveX_det)
  set Y : GL (Fin 3) K := Matrix.GeneralLinearGroup.mk'' (so3FiveG.map φ)
    (isUnit_det_map_of_det_eq_one _ so3FiveG_det)
  have hX : X ∈ StatedSU 3 5 K := mem_statedSU_of_orth _ so3FiveX_orth so3FiveX_det _
  have hY : Y ∈ StatedSU 3 5 K := mem_statedSU_of_orth _ so3FiveG_orth so3FiveG_det _
  set π := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 5 K))
  have hXv : (X : Matrix (Fin 3) (Fin 3) K) = so3FiveX.map φ := rfl
  have hYv : (Y : Matrix (Fin 3) (Fin 3) K) = so3FiveG.map φ := rfl
  refine ⟨π ⟨X, hX⟩, π ⟨Y, hY⟩, ?_, ?_, ?_⟩
  · rw [← map_pow]
    rw [show (⟨X, hX⟩ : StatedSU 3 5 K) ^ 5 = 1 from Subtype.ext (Units.ext (by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hXv, ← Matrix.map_pow, so3FiveX_pow,
        Matrix.map_one φ (map_zero φ) (map_one φ), Subgroup.coe_one, Units.val_one])), map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := h
    have h01 := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hc) 0) 1
    simp [Matrix.GeneralLinearGroup.coe_scalar, hXv, so3FiveX, φ] at h01
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    congr 1
    apply Subtype.ext
    apply Units.ext
    have hconj : (Y : Matrix (Fin 3) (Fin 3) K) * X = (X : Matrix (Fin 3) (Fin 3) K) ^ 2 * Y := by
      rw [hXv, hYv, ← Matrix.map_mul, ← Matrix.map_pow, ← Matrix.map_mul, so3FiveG_conj]
    have : Y * X * Y⁻¹ = X ^ 2 := by
      have h2 : Y * X = X ^ 2 * Y := Units.ext (by
        rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hconj])
      rw [h2, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, this]

end RationalFive

theorem false_of_psu3 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {K : Type} [Field K] [Finite K] {r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (r ^ f) ^ 2)
    (hq4 : 4 ≤ r ^ f) (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSU 3 (r ^ f) K)) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  have : CharP K r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr
    (by rw [hK, ← pow_mul])
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hqodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K r] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
  obtain ⟨eL⟩ := nonempty_mulEquiv_leviPSU3 (K := K) (r ^ f) (by omega)
  set L := (leviPSU3 (K := K) (r ^ f)).map e.symm.toMonoidHom with hLdef
  have : Group.IsPerfect (StatedSU 2 (r ^ f) K) := isPerfect_statedSU_two hK hq4
  have : Group.IsPerfect (leviPSU3 (K := K) (r ^ f)) :=
    Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  have hLp : Group.IsPerfect L := Group.IsPerfect.map _
  have hLcard : Nat.card L = r ^ f * ((r ^ f) ^ 2 - 1) := by
    rw [← card_statedSU_two hK, Nat.card_congr eL.toEquiv]
    exact (Nat.card_congr ((leviPSU3 (K := K) (r ^ f)).equivMapOfInjective _
      e.symm.injective).toEquiv).symm
  have hL : L ≠ ⊥ := by
    intro h
    have h1 : Nat.card L = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hLcard] at h1
    have : 4 * (4 ^ 2 - 1) ≤ r ^ f * ((r ^ f) ^ 2 - 1) := Nat.mul_le_mul hq4
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq4 2) 1)
    omega
  set t := e.symm (negDiagPSU3 (K := K) hqodd) with ht
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, negDiagPSU3_sq, map_one]
  have ht1 : t ≠ 1 := fun h =>
    negDiagPSU3_ne_one hK2 hqodd (e.symm.injective (by rw [← ht, h, map_one]))
  have hLt : ∀ x ∈ L, x * t = t * x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ht, ← map_mul, leviPSU3_commute hqodd y hy]
  have hcard := card_perfect_of_le_centralizer hp2 hdet hZ ht2 ht1 L hL hLt
  rw [hLcard] at hcard
  have hqp : r ^ f ≠ p := by
    intro hqp
    obtain ⟨rfl, rfl⟩ := ((Fact.out : p.Prime).pow_eq_iff).mp hqp
    apply not_dvd_card_GL_of_psu3 hp2 hK
    rw [← Nat.card_congr e.toEquiv]
    exact Nat.dvd_trans (Subgroup.card_quotient_dvd_card _) (Subgroup.card_subgroup_dvd_card H)
  rcases eq_five_or_eq_of_card_sl2 (by omega) hp1 hcard with h5 | hp
  ·
    obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).mp h5
    obtain ⟨s, g, hs5, hs1, hg⟩ := exists_rational_five_psu3 (K := K)
    have h5p := five_eq_zero_of_rational_five hdet hZ3
      (s := e.symm s) (g := e.symm g) (by rw [← map_pow, hs5, map_one])
      (fun h => hs1 (e.symm.injective (by rw [h, map_one])))
      (by rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow])
    have hdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h5p)
    exact hqp (by
      rw [pow_one]
      exact ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd).symm)
  · exact hqp hp

end CFSG.RankThree.SubgroupLists
