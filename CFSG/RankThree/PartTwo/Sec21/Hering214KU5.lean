module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine
public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
public import CFSG.RankThree.PartTwo.Sec8.Hering418Orders
public import CFSG.Models.PGLSimple
public import CFSG.Models.PGLOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.R6Levi
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU StatedLieAdmissible)
open CFSG.Assembly.RankThreeEven (projSU)

namespace KU5

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def xr (c : K) : GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.transvection 0 4 (by decide) c

theorem xr_val (c : K) : ((xr c : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 + single 0 4 c :=
  rfl

theorem xr_mul (c d : K) : xr c * xr d = xr (c + d) := by
  apply Units.ext
  simp only [Units.val_mul, xr_val]
  have := Matrix.transvection_mul_transvection_same (n := Fin 5) (0 : Fin 5) 4 (by decide) c d
  simpa [Matrix.transvection] using this

theorem xr_zero : xr (0 : K) = 1 := by
  apply Units.ext
  simp [xr_val]

theorem xr_mem_SU {c : K} (hc : c + σ c = 0) : xr c ∈ SU σ 5 := by
  refine mem_SU.mpr ⟨?_, ?_⟩
  · exact Matrix.det_transvection_of_ne (0 : Fin 5) 4 (by decide) c
  · rw [xr_val]
    have h1 : conjTr σ (1 + single (0 : Fin 5) (4 : Fin 5) c) =
        1 + single (4 : Fin 5) (0 : Fin 5) (σ c) := by
      simp [conjTr, Matrix.transpose_add, Matrix.map_add, Matrix.transpose_single,
        Matrix.map_single]
    rw [h1]
    have h2 : antidiag 5 * single (0 : Fin 5) (4 : Fin 5) c = single (4 : Fin 5) (4 : Fin 5) c := by
      rw [antidiag_mul_single]; rfl
    have h3 : single (4 : Fin 5) (0 : Fin 5) (σ c) * antidiag 5 =
        single (4 : Fin 5) (4 : Fin 5) (σ c) := by
      rw [single_mul_antidiag]; rfl
    have h4 : single (4 : Fin 5) (4 : Fin 5) (σ c) * single (0 : Fin 5) (4 : Fin 5) c = 0 :=
      Matrix.single_mul_single_of_ne _ _ _ 0 (by decide) _
    calc (1 + single (4 : Fin 5) (0 : Fin 5) (σ c)) * antidiag 5 *
          (1 + single (0 : Fin 5) (4 : Fin 5) c)
        = antidiag 5 + antidiag 5 * single (0 : Fin 5) (4 : Fin 5) c +
            single (4 : Fin 5) (0 : Fin 5) (σ c) * antidiag 5 +
            single (4 : Fin 5) (0 : Fin 5) (σ c) * antidiag 5 *
              single (0 : Fin 5) (4 : Fin 5) c := by
          noncomm_ring
      _ = antidiag 5 := by
          rw [h2, h3, h4, add_zero, add_assoc, ← single_add, hc]
          simp

theorem diagU_mul_xr (d : Fin 5 → Kˣ) (c : K) :
    (diagU d : GL (Fin 5) K) * xr c = xr ((d 0 : K) * ((d 4)⁻¹ : Kˣ) * c) * diagU d := by
  apply Units.ext
  simp only [Units.val_mul, diagU_val, xr_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply,
      Fin.sum_univ_five] <;> field_simp

theorem xr_eq_one_iff {c : K} : xr c = 1 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) 0 4) h
    simpa [xr_val] using this
  · rintro rfl
    exact xr_zero

theorem xr_inj {c d : K} (h : xr c = xr d) : c = d := by
  have := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) 0 4) h
  simpa [xr_val] using this

theorem xr_mul_self {c : K} (hc : c + c = 0) : xr c * xr c = 1 := by
  rw [xr_mul, hc, xr_zero]

theorem xr_comm (c d : K) : xr c * xr d = xr d * xr c := by
  rw [xr_mul, xr_mul, add_comm]

end KU5

section Torus

variable {K : Type} [Field K]

theorem diagU_pow {m : ℕ} (d : Fin m → Kˣ) (n : ℕ) :
    (diagU d : GL (Fin m) K) ^ n = diagU (d ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, diagU_one]
  | succ n ih => rw [pow_succ, ih, diagU_mul, pow_succ]

end Torus

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_cube_root (hK : Nat.card K = (2 ^ 2) ^ 2) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  have hc : Nat.card Kˣ = 15 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    norm_num
  have h3 : 3 ∣ Nat.card Kˣ := by rw [hc]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  refine ⟨ω, ?_, ?_⟩
  · rw [← hω]; exact pow_orderOf_eq_one ω
  · intro h
    rw [h, orderOf_one] at hω
    norm_num at hω

theorem sigma_eq_self [Fact (Nat.Prime 2)] {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    CFSG.LieType.BorelTits.unitaryInvolution K 2 2 (ω : K) = ω := by
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have h : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val h3
    simpa using this
  have h4 : (ω : K) ^ 2 ^ 2 = (ω : K) ^ 3 * (ω : K) := by
    rw [show 2 ^ 2 = 3 + 1 by norm_num, pow_succ]
  rw [h4, h, one_mul]

open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open KU5

theorem eInvNine_statedSU_five (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hZ : Subgroup.center (StatedProj (StatedSU 5 (2 ^ 2) K)) = ⊥)
    (hout : ∀ α : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)), α ^ 3 = 1 →
      ∃ y, α = MulAut.conj y)
    (hsyl : ∀ P : Sylow 3 (StatedProj (StatedSU 5 (2 ^ 2) K)), Nat.card P = 9) :
    EInvNine (StatedProj (StatedSU 5 (2 ^ 2) K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root hK
  have hσω : CFSG.LieType.BorelTits.unitaryInvolution K 2 2 (ω : K) = ω := sigma_eq_self hω3
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K 2 2 with hσdef
  have hσ1 : σ ((1 : Kˣ) : K) = ((1 : Kˣ) : K) := by simp
  have hω3K : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have hω1K : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have hωsq : (ω : K) ^ 2 = 1 + ω := Hering214.sq_eq_one_add hω3K hω1K
  have hc1 : ((1 : Kˣ) : K) + σ ((1 : Kˣ) : K) = 0 := by
    rw [hσ1]; exact CharTwo.add_self_eq_zero _
  have hcω : (ω : K) + σ (ω : K) = 0 := by
    rw [hσω]; exact CharTwo.add_self_eq_zero _
  let aS : ↥(SU σ 5) := ⟨diagU (dvec5 ω 1), diagU_dvec5_mem_SU σ hσω hσ1⟩
  let bS : ↥(SU σ 5) := ⟨diagU (dvec5 1 ω), diagU_dvec5_mem_SU σ hσ1 hσω⟩
  let u1S : ↥(SU σ 5) := ⟨xr 1, xr_mem_SU σ (by simpa using hc1)⟩
  let u2S : ↥(SU σ 5) := ⟨xr (ω : K), xr_mem_SU σ hcω⟩
  have hd3a : (dvec5 ω 1 : Fin 5 → Kˣ) ^ 3 = 1 := by
    funext i; fin_cases i <;> simp [dvec5, Pi.pow_apply, inv_pow, hω3]
  have hd3b : (dvec5 1 ω : Fin 5 → Kˣ) ^ 3 = 1 := by
    funext i; fin_cases i <;> simp [dvec5, Pi.pow_apply, inv_pow, hω3]
  have ha3 : aS ^ 3 = 1 := by
    apply Subtype.ext
    show (diagU (dvec5 ω 1) : GL (Fin 5) K) ^ 3 = 1
    rw [diagU_pow, hd3a, diagU_one]
  have hb3 : bS ^ 3 = 1 := by
    apply Subtype.ext
    show (diagU (dvec5 1 ω) : GL (Fin 5) K) ^ 3 = 1
    rw [diagU_pow, hd3b, diagU_one]
  have hab : aS * bS = bS * aS := by
    apply Subtype.ext
    show diagU (dvec5 ω 1) * diagU (dvec5 1 ω) = diagU (dvec5 1 ω) * diagU (dvec5 ω 1)
    rw [diagU_mul, diagU_mul, mul_comm]
  have hu1sq : u1S * u1S = 1 :=
    Subtype.ext (KU5.xr_mul_self (c := ((1 : Kˣ) : K)) (CharTwo.add_self_eq_zero _))
  have hu2sq : u2S * u2S = 1 := Subtype.ext (KU5.xr_mul_self (CharTwo.add_self_eq_zero _))
  have hu12 : u1S * u2S = u2S * u1S := Subtype.ext (KU5.xr_comm _ _)
  have ha1 : aS * u1S = (u1S * u2S) * aS := by
    apply Subtype.ext
    show diagU (dvec5 ω 1) * xr ((1 : Kˣ) : K) =
      (xr ((1 : Kˣ) : K) * xr (ω : K)) * diagU (dvec5 ω 1)
    rw [KU5.diagU_mul_xr, KU5.xr_mul]
    congr 2
    simp [dvec5]
    rw [← sq]
    simpa [add_comm] using hωsq
  have ha2 : aS * u2S = u1S * aS := by
    apply Subtype.ext
    show diagU (dvec5 ω 1) * xr (ω : K) = xr ((1 : Kˣ) : K) * diagU (dvec5 ω 1)
    rw [KU5.diagU_mul_xr]
    congr 2
    simp [dvec5]
    calc (ω : K) * ω * ω = (ω : K) ^ 3 := by ring
      _ = 1 := hω3K
  have hb1 : bS * u1S = u1S * bS := by
    apply Subtype.ext
    show diagU (dvec5 1 ω) * xr ((1 : Kˣ) : K) = xr ((1 : Kˣ) : K) * diagU (dvec5 1 ω)
    rw [KU5.diagU_mul_xr]
    simp [dvec5]
  have hb2 : bS * u2S = u2S * bS := by
    apply Subtype.ext
    show diagU (dvec5 1 ω) * xr (ω : K) = xr (ω : K) * diagU (dvec5 1 ω)
    rw [KU5.diagU_mul_xr]
    simp [dvec5]
  have hQ : IsCentralPQuot 3 (suQ 5 hK) :=
    isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK
  set q := suQ 5 hK with hqdef
  have hcomm_of_ker : ∀ x : ↥(SU σ 5), q x = 1 → ∀ y : ↥(SU σ 5), y * x = x * y := fun x hx y =>
    Subgroup.mem_center_iff.mp (hQ.central (MonoidHom.mem_ker.mpr hx)) y
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hu1ne : q u1S ≠ 1 := by
    intro h
    have hc := hcomm_of_ker u1S h aS
    rw [ha1] at hc
    have h2 : u1S * u2S = u1S := mul_right_cancel hc
    have h3 : u2S = 1 := mul_left_cancel (a := u1S) (h2.trans (mul_one u1S).symm)
    exact hω0 (xr_eq_one_iff.1 (congrArg Subtype.val h3))
  have hu2ne : q u2S ≠ 1 := by
    intro h
    have hc := hcomm_of_ker u2S h aS
    rw [ha2] at hc
    have h2 : u1S = u2S := mul_right_cancel hc
    have h3 := xr_inj (congrArg Subtype.val h2)
    exact hω1K (by simpa using h3.symm)
  have hu12ne : q u1S ≠ q u2S := by
    intro h
    have h1 : q (u1S * u2S) = 1 := by
      rw [map_mul, h, ← map_mul, hu2sq, map_one]
    have hc := hcomm_of_ker _ h1 aS
    have e : aS * (u1S * u2S) = u2S * aS := by
      calc aS * (u1S * u2S) = (aS * u1S) * u2S := by rw [mul_assoc]
        _ = (u1S * u2S) * aS * u2S := by rw [ha1]
        _ = (u1S * u2S) * (aS * u2S) := by rw [mul_assoc]
        _ = (u1S * u2S) * (u1S * aS) := by rw [ha2]
        _ = ((u1S * u2S) * u1S) * aS := by rw [mul_assoc (u1S * u2S)]
        _ = (u1S * (u2S * u1S)) * aS := by rw [mul_assoc u1S u2S u1S]
        _ = (u1S * (u1S * u2S)) * aS := by rw [← hu12]
        _ = (u1S * u1S * u2S) * aS := by simp only [mul_assoc]
        _ = u2S * aS := by rw [hu1sq, one_mul]
    rw [e] at hc
    have h2 : u2S = u1S * u2S := mul_right_cancel hc
    have h3 : u1S = 1 := mul_right_cancel (b := u2S) (h2.symm.trans (one_mul u2S).symm)
    exact h10 (xr_eq_one_iff.1 (congrArg Subtype.val h3))
  have hdist : ∀ i j k l : Fin 3,
      q aS ^ (i : ℕ) * q bS ^ (j : ℕ) = q aS ^ (k : ℕ) * q bS ^ (l : ℕ) → i = k ∧ j = l := by
    intro i j k l h
    have hord : ∀ i j : ℕ, (aS ^ i * bS ^ j) ^ 3 = 1 := by
      intro i j
      have hcm : Commute aS bS := hab
      rw [Commute.mul_pow (Commute.pow_pow hcm i j), ← pow_mul, ← pow_mul,
        mul_comm i 3, mul_comm j 3, pow_mul, pow_mul, ha3, hb3, one_pow, one_pow, one_mul]
    have h' : q (aS ^ (i : ℕ) * bS ^ (j : ℕ)) = q (aS ^ (k : ℕ) * bS ^ (l : ℕ)) := by
      simpa only [map_mul, map_pow] using h
    have heq := hQ.eq_of_map_eq (hord i j) (hord k l) h'
    have hgl : (diagU (dvec5 ω 1) : GL (Fin 5) K) ^ (i : ℕ) * diagU (dvec5 1 ω) ^ (j : ℕ) =
        diagU (dvec5 ω 1) ^ (k : ℕ) * diagU (dvec5 1 ω) ^ (l : ℕ) := congrArg Subtype.val heq
    rw [diagU_pow, diagU_pow, diagU_pow, diagU_pow, diagU_mul, diagU_mul] at hgl
    have e0 := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) 0 0) hgl
    have e1 := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) 1 1) hgl
    simp only [diagU_val, Matrix.diagonal_apply_eq, Pi.mul_apply, Pi.pow_apply, dvec5,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one, one_mul] at e0 e1
    have hωo : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    have e0' : ω ^ (i : ℕ) = ω ^ (k : ℕ) := Units.ext e0
    have e1' : ω ^ (j : ℕ) = ω ^ (l : ℕ) := Units.ext e1
    rw [pow_eq_pow_iff_modEq, hωo] at e0' e1'
    exact ⟨Fin.ext (Nat.ModEq.eq_of_lt_of_lt e0' i.2 k.2),
      Fin.ext (Nat.ModEq.eq_of_lt_of_lt e1' j.2 l.2)⟩
  have hab' : q aS * q bS = q bS * q aS := by simpa only [map_mul] using congrArg q hab
  have ha1' : q aS * q u1S = (q u1S * q u2S) * q aS := by
    simpa only [map_mul] using congrArg q ha1
  have ha2' : q aS * q u2S = q u1S * q aS := by simpa only [map_mul] using congrArg q ha2
  have hb1' : q bS * q u1S = q u1S * q bS := by simpa only [map_mul] using congrArg q hb1
  have hb2' : q bS * q u2S = q u2S * q bS := by simpa only [map_mul] using congrArg q hb2
  refine eInvNine_of_explicit_hout hZ hout hsyl (a := q aS) (b := q bS) (u₁ := q u1S)
    (u₂ := q u2S) (va₁ := q u1S * q u2S) (va₂ := q u1S) (vb₁ := q u1S) (vb₂ := q u2S)
    (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one]) hab' hdist
    (by rw [← map_mul, hu1sq, map_one]) (by rw [← map_mul, hu2sq, map_one])
    (by simpa only [map_mul] using congrArg q hu12) hu1ne hu2ne hu12ne
    (Four4.mul _ _) (Four4.left _ _) (Four4.left _ _) (Four4.right _ _)
    ha1' ha2' hb1' hb2' ?_
  intro h
  have h2 : q u1S * q u2S = q u1S := mul_right_cancel (ha1'.symm.trans h)
  exact hu2ne (mul_left_cancel (a := q u1S) (h2.trans (mul_one _).symm))

end Main

section Final

open CFSG.PGLModel (projSUEquivStatedProj isSimpleGroup_projSU_of_admissible)

theorem eInvNine_projSU_five_four : EInvNine (projSU 5 2 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 (2 * 2) with hKdef
  have hK : Nat.card K = (2 ^ 2) ^ 2 := U4Lines.card_galoisField_two_mul 2 (by norm_num)
  have hadm : StatedLieAdmissible .PSU 5 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩
  set e : projSU 5 2 2 ≃* StatedProj (StatedSU 5 (2 ^ 2) K) := projSUEquivStatedProj 5 2 2
    with he
  have hcard : Nat.card (projSU 5 2 2) = 53443952640000 := CFSG.PGLModel.card_projSU_five_four
  have hZ : Subgroup.center (projSU 5 2 2) = ⊥ :=
    center_eq_bot_of_simple_of_not_prime (isSimpleGroup_projSU_of_admissible hadm)
      (by rw [hcard]; norm_num)
  have hY : EInvNine (StatedProj (StatedSU 5 (2 ^ 2) K)) := by
    refine eInvNine_statedSU_five hK (center_eq_bot_of_mulEquiv e hZ) ?_ ?_
    · intro α hα
      obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Sec8.Hering418.inner_projSU hadm (by decide)
        (by decide) e.symm hα
      exact ⟨y, hy.symm⟩
    · intro P
      have hc : Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K)) = 53443952640000 := by
        rw [← Nat.card_congr e.toEquiv, hcard]
      exact card_sylow_three_of_padicValNat hc (by decide +kernel) P
  exact EInvNine.of_mulEquiv e hY

end Final

end CFSG.RankThree.PartTwo.Sec21.Hering214
