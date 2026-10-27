module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix
open scoped MatrixGroups

namespace Item812Res10

section Field

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem exists_cube_add_add_one_eq_zero (hF : Fintype.card F = 8) :
    ∃ t : F, t ^ 3 + t + 1 = 0 := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ)
    (by rw [Finset.card_univ, hF]; exact (Finset.card_le_two).trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx0, hx1⟩ := hx
  have h7 : x ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x hx0
    rwa [hF] at this
  have key : (x - 1) * ((x ^ 3 + x + 1) * (x ^ 3 + x ^ 2 + 1)) = 0 := by
    linear_combination h7 + (x ^ 4 - x ^ 3) * h2
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hx1') with h | h
  · exact ⟨x, h⟩
  · refine ⟨x⁻¹, ?_⟩
    have e : x⁻¹ ^ 3 + x⁻¹ + 1 = x⁻¹ ^ 3 * (x ^ 3 + x ^ 2 + 1) := by
      field_simp
      ring
    rw [e, h, mul_zero]

end Field

section Nine

variable {F : Type} [Field F] [CharP F 2]

@[expose] def matNine (t : F) : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, t]

theorem det_matNine (t : F) : (matNine t).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [matNine, Matrix.det_fin_two_of]
  linear_combination -h2

@[expose] def slNine (t : F) : SL(2, F) := ⟨matNine t, det_matNine t⟩

theorem matNine_pow_three {t : F} (ht : t ^ 3 + t + 1 = 0) :
    matNine t ^ 3 = !![t, 1 + t ^ 2; 1 + t ^ 2, 1 + t] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matNine, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination ht - h2

theorem matNineCube_pow_three {t : F} (ht : t ^ 3 + t + 1 = 0) :
    (!![t, 1 + t ^ 2; 1 + t ^ 2, 1 + t] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination (3 * t ^ 2 + t + 4) * ht + (-t ^ 2 - t - 2) * h2
      | linear_combination (t ^ 3 + 5 * t + 2) * ht + (t ^ 2 - 2 * t) * h2
      | linear_combination (3 * t ^ 2 + 2 * t + 4) * ht + (t ^ 2 - 1) * h2

theorem orderOf_slNine {t : F} (ht : t ^ 3 + t + 1 = 0) : orderOf (slNine t) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_
  · intro h
    have h01 := congrArg (fun g : SL(2, F) => g.val 0 1) h
    change (matNine t ^ 3 ^ 1) 0 1 = (1 : Matrix (Fin 2) (Fin 2) F) 0 1 at h01
    rw [pow_one, matNine_pow_three ht] at h01
    simp at h01
    have e1 : (t + 1) ^ 2 = 0 := by linear_combination h01 + t * h2
    have e2 : t + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp e1
    have e3 : (1 : F) = 0 := by linear_combination -ht + (t ^ 2 - t + 2) * e2
    exact one_ne_zero e3
  · apply Subtype.ext
    change matNine t ^ 3 ^ (1 + 1) = 1
    rw [show 3 ^ (1 + 1) = 3 * 3 by norm_num, pow_mul, matNine_pow_three ht,
      matNineCube_pow_three ht]

end Nine

section Torus

variable {F : Type} [Field F] [CharP F 2]

open CFSG.RankThree.PartTwo.KFacts (planeSp planeSp_commute planeSp_injective coe_planeSp
  planeBlock)

omit [CharP F 2] in
private theorem eq_one_of_planeSp_eq {B B' : SL(2, F)} (h : planeSp 0 B = planeSp 1 B') :
    B = 1 := by
  have h1 := congrArg (fun g : StatedSp 2 F =>
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [coe_planeSp, planeBlock] at h1
  have h2 := congrFun (CFSG.LieType.SteinbergBR.EvenSp.planeMat_injective h1) 0
  simp at h2
  exact Subtype.ext h2

omit [CharP F 2] in
private theorem zpowers_inf_zpowers_eq_bot (B : SL(2, F)) :
    Subgroup.zpowers (planeSp 0 B) ⊓ Subgroup.zpowers (planeSp 1 B) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx0, hx1⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx0
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx1
  rw [← map_zpow, ← map_zpow] at hj
  rw [Subgroup.mem_bot, ← map_zpow, eq_one_of_planeSp_eq hj.symm, map_one]

private theorem exists_injective_torusHom {t : F} (ht : t ^ 3 + t + 1 = 0) :
    ∃ ψ : Multiplicative (ZMod 9 × ZMod 9) →* StatedSp 2 F, Function.Injective ψ := by
  set u := planeSp 0 (slNine t) with hu
  set v := planeSp 1 (slNine t) with hv
  have hou : orderOf u = 9 := by
    rw [hu, orderOf_injective _ (planeSp_injective 0), orderOf_slNine ht]
  have hov : orderOf v = 9 := by
    rw [hv, orderOf_injective _ (planeSp_injective 1), orderOf_slNine ht]
  have hcu : Nat.card (Subgroup.zpowers u) = 9 := by rw [Nat.card_zpowers, hou]
  have hcv : Nat.card (Subgroup.zpowers v) = 9 := by rw [Nat.card_zpowers, hov]
  let eU : Multiplicative (ZMod 9) ≃* Subgroup.zpowers u :=
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcu.symm).toAddEquiv).trans
      (zmodCyclicMulEquiv (Subgroup.isCyclic_zpowers u))
  let eV : Multiplicative (ZMod 9) ≃* Subgroup.zpowers v :=
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcv.symm).toAddEquiv).trans
      (zmodCyclicMulEquiv (Subgroup.isCyclic_zpowers v))
  let fU : Multiplicative (ZMod 9) →* StatedSp 2 F := (Subgroup.zpowers u).subtype.comp eU
  let fV : Multiplicative (ZMod 9) →* StatedSp 2 F := (Subgroup.zpowers v).subtype.comp eV
  have huv : Commute u v := planeSp_commute _ _
  have hcomm : ∀ m n, Commute (fU m) (fV n) := by
    intro m n
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (eU m).2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (eV n).2
    change Commute ((eU m : Subgroup.zpowers u) : StatedSp 2 F)
      ((eV n : Subgroup.zpowers v) : StatedSp 2 F)
    rw [← hi, ← hj]
    exact huv.zpow_zpow i j
  set φ := MonoidHom.noncommCoprod fU fV hcomm with hφ
  refine ⟨φ.comp (MulEquiv.prodMultiplicative (ZMod 9) (ZMod 9)).toMonoidHom, ?_⟩
  rw [injective_iff_map_eq_one]
  intro z hz
  set p := MulEquiv.prodMultiplicative (ZMod 9) (ZMod 9) z with hp
  have hz' : fU p.1 * fV p.2 = 1 := hz
  have hmem : fU p.1 ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
    refine ⟨(eU p.1).2, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hz']
    exact Subgroup.inv_mem _ (eV p.2).2
  rw [hu, hv, zpowers_inf_zpowers_eq_bot, Subgroup.mem_bot] at hmem
  have h1 : p.1 = 1 := by
    apply eU.injective
    rw [map_one]
    exact Subtype.ext hmem
  have h2 : fV p.2 = 1 := by rw [hmem, one_mul] at hz'; exact hz'
  have h2' : p.2 = 1 := by
    apply eV.injective
    rw [map_one]
    exact Subtype.ext h2
  have hp1 : p = 1 := Prod.ext h1 h2'
  rw [hp] at hp1
  exact (MulEquiv.prodMultiplicative (ZMod 9) (ZMod 9)).injective (by rw [hp1, map_one])

end Torus

theorem factorization_card_sp48_three : (1056706560 : ℕ).factorization 3 = 4 := by
  rw [show (1056706560 : ℕ) = 3 ^ 4 * 13045760 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

end Item812Res10

open Item812Res10 in
theorem kFSp48SylowThree_holds :
    ∀ S : Subgroup ↥(projSp 2 (GaloisField 2 3)), Nat.card S = 81 →
      Nonempty (↥S ≃* Multiplicative (ZMod 9 × ZMod 9)) := by
  intro S hS
  classical
  set F := GaloisField 2 3 with hFdef
  have : Fintype F := Fintype.ofFinite F
  have hK : Fintype.card F = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num
  have : CharP F 2 := inferInstance
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht⟩ := exists_cube_add_add_one_eq_zero hK
  obtain ⟨ψ, hψ⟩ := exists_injective_torusHom ht
  set ι := CFSG.RankThree.PartTwo.KFacts.statedSpEquivProjSpOfCharTwo F with hι
  set T : Subgroup ↥(projSp 2 F) := (ψ.range).map ι.toMonoidHom with hT
  have eT : ↥T ≃* Multiplicative (ZMod 9 × ZMod 9) :=
    (ι.subgroupMap ψ.range).symm.trans (MonoidHom.ofInjective hψ).symm
  have hcardG : Nat.card ↥(projSp 2 F) = 1056706560 := Item812Res2.card_projSp_two_three
  have hTcard : Nat.card T = 81 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have h81 : (81 : ℕ) = 3 ^ (Nat.card ↥(projSp 2 F)).factorization 3 := by
    rw [hcardG, factorization_card_sp48_three]
    norm_num
  have : Finite ↥(projSp 2 F) := Nat.finite_of_card_ne_zero (by rw [hcardG]; norm_num)
  set PS : Sylow 3 ↥(projSp 2 F) := Sylow.ofCard S (by rw [hS]; exact h81) with hPS
  set PT : Sylow 3 ↥(projSp 2 F) := Sylow.ofCard T (by rw [hTcard]; exact h81) with hPT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(projSp 2 F) PS PT
  have e1 : ↥S ≃* ↥T :=
    ((MulEquiv.subgroupCongr (Sylow.coe_ofCard S _).symm).trans (Sylow.equivSMul PS g)).trans
      (MulEquiv.subgroupCongr ((congrArg (fun P : Sylow 3 ↥(projSp 2 F) =>
        (P : Subgroup ↥(projSp 2 F))) hg).trans (Sylow.coe_ofCard T _)))
  exact ⟨e1.trans eT⟩

end CFSG.RankThree.PartTwo.Sec8
