module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSU
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLFixed
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag longRootHom rootHom traceZero rootMatrix)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (gramSUToSL coe_gramSUToSL gramSUToSL_injective)

namespace AutPSU

section Equiv

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {n : ℕ}

noncomputable abbrev suEquiv : SU (unitaryInvolution K 2 f) n ≃* XJ h n :=
  MulEquiv.subgroupCongr (RootDetectSU.SU_eq_gramSU_antidiag h)

theorem coe_suEquiv (x : SU (unitaryInvolution K 2 f) n) :
    ((suEquiv h x : XJ h n) : GL (Fin n) K) = x :=
  rfl

noncomputable abbrev projU : SU (unitaryInvolution K 2 f) n →* PJ h n :=
  (QuotientGroup.mk' _).comp (suEquiv h).toMonoidHom

theorem projU_apply (x : SU (unitaryInvolution K 2 f) n) :
    projU h x = ((suEquiv h x : XJ h n) : PJ h n) :=
  rfl

include h in
theorem sigma_involutive :
    ∀ c : K, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
  unitaryInvolution_involutive h.card_eq_sq

end Equiv

section Roots

variable {K : Type} [Field K] [CharP K 2] {n : ℕ} (σ : K ≃+* K)

theorem one_mem_traceZero : (1 : K) ∈ traceZero σ := by
  rw [CFSG.LieType.Universal.Unitary.mem_traceZero, map_one]
  exact CharTwo.add_self_eq_zero 1

noncomputable abbrev lroot {i : Fin n} (hi : i ≠ Fin.rev i) : SU σ n :=
  longRootHom σ hi (Multiplicative.ofAdd ⟨1, one_mem_traceZero σ⟩)

theorem coe_lroot {i : Fin n} (hi : i ≠ Fin.rev i) :
    (((lroot σ hi : SU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + single i (Fin.rev i) 1 :=
  rfl

noncomputable abbrev sroot (hσ : ∀ c, σ (σ c) = c) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) : SU σ n :=
  rootHom σ hσ hij hi hj (Multiplicative.ofAdd 1)

theorem coe_sroot (hσ : ∀ c, σ (σ c) = c) {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) :
    (((sroot σ hσ hij hi hj : SU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + single i j 1 + single (Fin.rev j) (Fin.rev i) 1 := by
  rw [CFSG.LieType.Universal.Unitary.coe_rootHom, toAdd_ofAdd, rootMatrix, map_one,
    sub_eq_add_neg, Matrix.single_neg, CharTwo.neg_eq]

theorem map_lroot (φ : K ≃+* K) {i : Fin n} (hi : i ≠ Fin.rev i) :
    ((((lroot σ hi : SU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      ((lroot σ hi : SU σ n) : GL (Fin n) K) := by
  rw [coe_lroot, Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    Matrix.map_single, map_one]

theorem map_sroot (hσ : ∀ c, σ (σ c) = c) (φ : K ≃+* K) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) :
    ((((sroot σ hσ hij hi hj : SU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      ((sroot σ hσ hij hi hj : SU σ n) : GL (Fin n) K) := by
  rw [coe_sroot, Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ),
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_single, Matrix.map_single, map_one]

end Roots

section SL

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {n : ℕ}

theorem gramSUToSL_lroot {i : Fin n} (hi : i ≠ Fin.rev i) :
    gramSUToSL h _ (suEquiv h (lroot (unitaryInvolution K 2 f) hi)) =
      SpecialLinearGroup.transvection hi 1 :=
  Subtype.ext (by rw [coe_gramSUToSL, coe_suEquiv, coe_lroot]; rfl)

theorem gramSUToSL_sroot {a b : Fin n} (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b)
    (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) :
    gramSUToSL h _ (suEquiv h (sroot (unitaryInvolution K 2 f) (sigma_involutive h) hba hb ha)) =
      SpecialLinearGroup.transvection hba 1 * SpecialLinearGroup.transvection hrab 1 := by
  apply Subtype.ext
  change (((sroot (unitaryInvolution K 2 f) (sigma_involutive h) hba hb ha :
      SU (unitaryInvolution K 2 f) n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((SpecialLinearGroup.transvection hba (1 : K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *
    ((SpecialLinearGroup.transvection hrab (1 : K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
  rw [coe_sroot, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, single_mul_single_of_ne _ _ _ _ ha, add_zero]
  abel

end SL

section Fixed

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem compl_fixes_of_map {c : MulAut (PJ h n)} (hc : c ∈ compl h) (x : XJ h n)
    (hx : ∀ φ : K ≃+* K,
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ = (x : GL (Fin n) K)) :
    c (x : PJ h n) = x := by
  obtain ⟨φ, rfl⟩ := hc
  change primeFormFieldAut h isPrimeFormGram_gramJ φ (x : PJ h n) = _
  rw [primeFormFieldAut_mk]
  congr 1
  exact Subtype.ext (Units.ext (hx φ))

end Fixed

end AutPSU

end CFSG.StandardType
