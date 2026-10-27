module

public import CFSG.ClassicalGroups.Unitary.RankTwoNormOneTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj
public import CFSG.Permutation.FiveTransitive.SylowThreeFixedOrbits
public import CFSG.GroupTheory.OddInvariantSubgroupFamily
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutInvolution

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG CFSG.Open CFSG.ClassicalGroups.Unitary
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Phan CFSG.RankThree.CentralCover
open Subgroup

variable {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime] [CharP K p]

private abbrev PSU3 (p f : ℕ) (K : Type) [Field K] : Type :=
  StatedProj (StatedSU 3 (p ^ f) K)

private noncomputable def suNormOneTorus (hK : Nat.card K = (p ^ f) ^ 2)
    (h2 : (2 : K) ≠ 0) :
    normOne (unitaryInvolution K p f) →* StatedSU 3 (p ^ f) K :=
  (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).toMonoidHom.comp
    (normOneTorusHom (unitaryInvolution_involutive hK) h2)

private noncomputable def psuNormOneTorus (hK : Nat.card K = (p ^ f) ^ 2)
    (h2 : (2 : K) ≠ 0) :
    normOne (unitaryInvolution K p f) →* PSU3 p f K :=
  (statedProjMk (StatedSU 3 (p ^ f) K)).comp (suNormOneTorus hK h2)

private theorem suNormOneTorus_coe (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (u : normOne (unitaryInvolution K p f)) :
    (((suNormOneTorus hK h2 u : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = normOneTorusMat u := by
  change ((((normOneTorusHom (unitaryInvolution_involutive hK) h2 u :
    SUid (unitaryInvolution K p f) 3) : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) = _
  exact coe_coe_normOneTorusHom (unitaryInvolution_involutive hK) h2 u

private theorem psuNormOneTorus_eq (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (u : normOne (unitaryInvolution K p f)) :
    psuNormOneTorus hK h2 u =
      statedProjMk (StatedSU 3 (p ^ f) K) (suNormOneTorus hK h2 u) := rfl

private theorem psuNormOneTorus_injective (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) :
    Function.Injective (psuNormOneTorus (p := p) (f := f) hK h2) := by
  classical
  intro u v h
  let eSU : SUid (unitaryInvolution K p f) 3 ≃* StatedSU 3 (p ^ f) K :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)
  let R : normOne (unitaryInvolution K p f) →* StatedSU 3 (p ^ f) K :=
    eSU.toMonoidHom.comp (normOneTorusHom (unitaryInvolution_involutive hK) h2)
  have hcoe : ∀ w : normOne (unitaryInvolution K p f),
      (((R w : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        normOneTorusMat w := by
    intro w
    change ((((normOneTorusHom (unitaryInvolution_involutive hK) h2 w :
      SUid (unitaryInvolution K p f) 3) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) = _
    exact coe_coe_normOneTorusHom (unitaryInvolution_involutive hK) h2 w
  have hRinj : Function.Injective R := by
    intro a b hab
    exact normOneTorusHom_injective (unitaryInvolution_involutive hK) h2
      (eSU.injective hab)
  have hquot : statedProjMk (StatedSU 3 (p ^ f) K) (R u) =
      statedProjMk (StatedSU 3 (p ^ f) K) (R v) := h
  have hmem : (R u)⁻¹ * (R v) ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.eq (s := (StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (p ^ f) K))).mp hquot
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have h11 : c = 1 := by
    have h1 := congrArg (fun g : GL (Fin 3) K =>
      (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 1 1) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    have hentry : (((((R u : StatedSU 3 (p ^ f) K) : GL (Fin 3) K))⁻¹ *
        ((R v : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
      have hinv : (((R u : StatedSU 3 (p ^ f) K) : GL (Fin 3) K))⁻¹ =
          ((R (u⁻¹) : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) := by
        rw [← Subgroup.coe_inv]
        congr 1
        exact (map_inv R u).symm
      rw [hinv]
      change (((↑(R (u⁻¹)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((↑(R v) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 1 1 = 1
      rw [hcoe (u⁻¹), hcoe v, Matrix.mul_apply]
      simp [normOneTorusMat, Fin.sum_univ_three]
    simpa [hentry, Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hGL : (((R u)⁻¹ * (R v) : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) = 1 := by
    rw [← hc, h11]
    exact map_one _
  have hSU : (R u)⁻¹ * (R v) = 1 := Subtype.ext hGL
  have huv : R u = R v := by
    have := congrArg (fun z : StatedSU 3 (p ^ f) K => R u * z) hSU
    simpa [mul_assoc] using this.symm
  exact hRinj huv

section Diagonal

variable (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)

private noncomputable def normOneDiagTuple (δ : normOne (unitaryInvolution K p f)) :
    Fin 3 → normOne (unitaryInvolution K p f) :=
  ![δ, δ⁻¹, 1]

private theorem normOneDiagTuple_mem_detKer (δ : normOne (unitaryInvolution K p f)) :
    normOneDiagTuple δ ∈ detKer (unitaryInvolution K p f) 3 := by
  rw [mem_detKer]
  simp [normOneDiagTuple, Fin.prod_univ_three]

private noncomputable def normOneDiagTupleHom :
    normOne (unitaryInvolution K p f) →* detKer (unitaryInvolution K p f) 3 where
  toFun δ := ⟨normOneDiagTuple δ, normOneDiagTuple_mem_detKer δ⟩
  map_one' := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [normOneDiagTuple]
  map_mul' δ ε := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [normOneDiagTuple, Pi.mul_apply, mul_comm]

private noncomputable def normOneDiagHom :
    normOne (unitaryInvolution K p f) →* SUid (unitaryInvolution K p f) 3 :=
  (diagSUHom (unitaryInvolution K p f) 3).comp normOneDiagTupleHom

private theorem coe_coe_normOneDiagHom (δ : normOne (unitaryInvolution K p f)) :
    ((((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![((δ : Kˣ) : K), (((δ : Kˣ) : K))⁻¹, 1] := by
  rw [normOneDiagHom, MonoidHom.comp_apply, diagSUHom_apply, coe_coe_diagSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normOneDiagTuple, normOneDiagTupleHom, Matrix.diagonal]

private theorem normOneDiagHom_injective :
    Function.Injective (normOneDiagHom (K := K) (p := p) (f := f)) := by
  intro δ ε h
  have hmat := congrArg (fun w : SUid (unitaryInvolution K p f) 3 =>
    (((w : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) h
  rw [coe_coe_normOneDiagHom, coe_coe_normOneDiagHom] at hmat
  have h00 := congrFun (congrFun hmat 0) 0
  simp [Matrix.diagonal_apply_eq] at h00
  exact Subtype.ext (Units.ext h00)

private noncomputable def psuNormOneDiagonalHom :
    normOne (unitaryInvolution K p f) →* PSU3 p f K :=
  (statedProjMk (StatedSU 3 (p ^ f) K)).comp
    ((MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).toMonoidHom.comp normOneDiagHom)

private noncomputable def psuNormOneDiagonal : Subgroup (PSU3 p f K) :=
  (psuNormOneDiagonalHom hK).range

private theorem psuNormOneDiagonalHom_injective :
    Function.Injective (psuNormOneDiagonalHom hK) := by
  classical
  intro δ ε h
  let eSU : SUid (unitaryInvolution K p f) 3 ≃* StatedSU 3 (p ^ f) K :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)
  have hquot : statedProjMk (StatedSU 3 (p ^ f) K) (eSU (normOneDiagHom δ)) =
      statedProjMk (StatedSU 3 (p ^ f) K) (eSU (normOneDiagHom ε)) := h
  have hmem : (eSU (normOneDiagHom δ))⁻¹ * eSU (normOneDiagHom ε) ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.eq (s := (StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (p ^ f) K))).mp hquot
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have hcoe : ∀ w : normOne (unitaryInvolution K p f),
      ((((eSU (normOneDiagHom w) : StatedSU 3 (p ^ f) K) :
        GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal ![((w : Kˣ) : K), (((w : Kˣ) : K))⁻¹, 1] := by
    intro w
    change ((((normOneDiagHom w :
      SUid (unitaryInvolution K p f) 3) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) = _
    exact coe_coe_normOneDiagHom w
  have hc1 : c = 1 := by
    have h1 := congrArg (fun g : GL (Fin 3) K =>
      (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 2 2) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    have hentry : (((((eSU (normOneDiagHom δ) : StatedSU 3 (p ^ f) K) :
        GL (Fin 3) K))⁻¹ * ((eSU (normOneDiagHom ε) :
          StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      have hinv : (((eSU (normOneDiagHom δ) : StatedSU 3 (p ^ f) K) :
          GL (Fin 3) K))⁻¹ =
          ((eSU (normOneDiagHom (δ⁻¹)) : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) := by
        rw [← Subgroup.coe_inv]
        congr 1
        rw [← map_inv, ← map_inv]
      rw [hinv]
      change (((↑(eSU (normOneDiagHom (δ⁻¹))) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * ((↑(eSU (normOneDiagHom ε)) :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 2 2 = 1
      rw [hcoe (δ⁻¹), hcoe ε, Matrix.mul_apply]
      simp [Fin.sum_univ_three]
    simpa [hentry, Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hGL : (((eSU (normOneDiagHom δ))⁻¹ * eSU (normOneDiagHom ε) :
      StatedSU 3 (p ^ f) K) : GL (Fin 3) K) = 1 := by
    rw [← hc, hc1]
    exact map_one _
  have hSU : (eSU (normOneDiagHom δ))⁻¹ * eSU (normOneDiagHom ε) = 1 :=
    Subtype.ext hGL
  have heq : eSU (normOneDiagHom δ) = eSU (normOneDiagHom ε) := by
    have := congrArg (fun z : StatedSU 3 (p ^ f) K =>
      eSU (normOneDiagHom δ) * z) hSU
    simpa [mul_assoc] using this.symm
  exact normOneDiagHom_injective (eSU.injective heq)

private theorem card_psuNormOneDiagonal :
    Nat.card (psuNormOneDiagonal hK) = p ^ f + 1 := by
  rw [psuNormOneDiagonal, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (psuNormOneDiagonalHom_injective hK)]
  calc Nat.card (⊤ : Subgroup (normOne (unitaryInvolution K p f))) =
        Nat.card (normOne (unitaryInvolution K p f)) :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = p ^ f + 1 := card_normOne hK

private theorem suOdd₃_mul_self (hq : Odd (p ^ f)) :
    suOdd₃ K hq * suOdd₃ K hq = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suOdd₃, oddDiag₃, Matrix.mul_apply, Fin.sum_univ_three]

private theorem suOdd₃_inv (hq : Odd (p ^ f)) : (suOdd₃ K hq)⁻¹ = suOdd₃ K hq :=
  inv_eq_of_mul_eq_one_left (suOdd₃_mul_self (p := p) (f := f) hq)

private theorem suOdd₃_coe (hq : Odd (p ^ f)) :
    (((suOdd₃ K hq : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(-1 : K), -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suOdd₃, oddDiag₃, Matrix.diagonal]

private theorem psuNormOneDiagonalHom_negOne (hq : Odd (p ^ f)) :
    psuNormOneDiagonalHom hK CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.negOneN = uniU₀ K hq := by
  rw [psuNormOneDiagonalHom, MonoidHom.comp_apply, uniU₀]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change (((normOneDiagHom CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.negOneN : SUid (unitaryInvolution K p f) 3) :
    GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (oddDiag₃ K : Matrix (Fin 3) (Fin 3) K)
  rw [coe_coe_normOneDiagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.negOneN, normOneDiagTuple, oddDiag₃, Matrix.diagonal]

private theorem suOdd₃_conj_suNormOneTorus (hq : Odd (p ^ f))
    (u : normOne (unitaryInvolution K p f)) :
    suOdd₃ K hq * suNormOneTorus hK h2 u * suOdd₃ K hq =
      suNormOneTorus hK h2 (u⁻¹) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [suOdd₃_coe, suNormOneTorus_coe, suNormOneTorus_coe]
  exact normOneTorusMat_conj_sign₃ u (unitaryInvolution_involutive hK)

private theorem uniU₀_conj_psuNormOneTorus (hq : Odd (p ^ f))
    (u : normOne (unitaryInvolution K p f)) :
    uniU₀ K hq * psuNormOneTorus hK h2 u *
        (uniU₀ K hq)⁻¹ =
      (psuNormOneTorus hK h2 u)⁻¹ := by
  have huni : uniU₀ K hq =
      statedProjMk (StatedSU 3 (p ^ f) K) (suOdd₃ K hq) := rfl
  have hpsu : psuNormOneTorus hK h2 u =
      statedProjMk (StatedSU 3 (p ^ f) K) (suNormOneTorus hK h2 u) := rfl
  calc
    uniU₀ K hq * psuNormOneTorus hK h2 u * (uniU₀ K hq)⁻¹
        = statedProjMk (StatedSU 3 (p ^ f) K)
            (suOdd₃ K hq * suNormOneTorus hK h2 u * suOdd₃ K hq) := by
          rw [huni, hpsu, ← map_inv,
            show (suOdd₃ K hq)⁻¹ = suOdd₃ K hq from suOdd₃_inv hq,
            ← map_mul, ← map_mul]
    _ = statedProjMk (StatedSU 3 (p ^ f) K)
          ((suNormOneTorus hK h2 u)⁻¹) := by
          rw [suOdd₃_conj_suNormOneTorus hK h2 hq u, map_inv]
    _ = (psuNormOneTorus hK h2 u)⁻¹ := by
          rw [hpsu, map_inv]

private theorem odd_half_add_one (hq4 : p ^ f % 4 = 1) : Odd ((p ^ f + 1) / 2) := by
  have hq : p ^ f = 4 * (p ^ f / 4) + 1 := by
    have := Nat.div_add_mod (p ^ f) 4
    omega
  have hdvd : 2 ∣ p ^ f + 1 := by omega
  refine ⟨p ^ f / 4, ?_⟩
  refine Nat.mul_left_cancel (by norm_num : 0 < 2) ?_
  rw [Nat.mul_div_cancel' hdvd]
  have hq' : p ^ f + 1 = 2 * (2 * (p ^ f / 4) + 1) := by omega
  rw [hq']

private theorem exists_odd_prime_torus_member (hq4 : p ^ f % 4 = 1) (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ lam : normOne (unitaryInvolution K p f),
      orderOf (psuNormOneTorus hK h2 lam) = r := by
  have hp2 : p ≠ 2 := by
    intro hp
    have hdiv : 4 ∣ p ^ f := by
      rw [hp]
      refine ⟨2 ^ (f - 2), ?_⟩
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have hmod : p ^ f % 4 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hp3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hq9 : 9 ≤ p ^ f := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega : 0 < p) hf
  have hm1 : 1 < (p ^ f + 1) / 2 := by omega
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : (p ^ f + 1) / 2 ≠ 1)
  letI : Fact r.Prime := ⟨hrprime⟩
  have hrod : r ≠ 2 := by
    intro hr2
    have hm_odd := odd_half_add_one (p := p) (f := f) hq4
    rw [hr2] at hrdvd
    exact (Nat.not_even_iff_odd.mpr hm_odd) (even_iff_two_dvd.mpr hrdvd)
  have hrdvd' : r ∣ p ^ f + 1 := by
    have := Nat.dvd_trans hrdvd (Nat.div_dvd_of_dvd (by omega : 2 ∣ p ^ f + 1))
    exact this
  obtain ⟨lam, hlam⟩ := exists_prime_orderOf_dvd_card'
    (G := normOne (unitaryInvolution K p f)) r (by
      rw [card_normOne hK]
      exact hrdvd')
  refine ⟨r, hrprime, hrod, lam, ?_⟩
  rw [orderOf_injective (psuNormOneTorus hK h2) (psuNormOneTorus_injective hK h2) lam, hlam]

end Diagonal

private theorem suOdd₂_coe (hq : Odd (p ^ f)) :
    (((suOdd₂ K hq : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(-1 : K), 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suOdd₂, oddDiag₂, Matrix.diagonal]

private theorem offdiag_eq_zero_of_commutes_signs (h : UnitaryFieldData p f K)
    (A : uU h 3) (Z Z' : StatedSU 3 (p ^ f) K)
    (hZmat : ((((Z : StatedSU 3 (p ^ f) K) : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(-1 : K), -1, 1])
    (hZ'mat : ((((Z' : StatedSU 3 (p ^ f) K) : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(-1 : K), 1, -1])
    (hZ : (A : GL (Fin 3) K) * (Z : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      (Z : GL (Fin 3) K))
    (hZ' : (A : GL (Fin 3) K) * (Z' : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      (Z' : GL (Fin 3) K))
    (h2 : (2 : K) ≠ 0) :
    ∀ i j : Fin 3, i ≠ j → (((A : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hZmulGL : (A : GL (Fin 3) K) * (Z : GL (Fin 3) K) =
      (Z : GL (Fin 3) K) * (A : GL (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => g * (A : GL (Fin 3) K)) hZ
    simpa [mul_assoc] using this
  have hZ'mulGL : (A : GL (Fin 3) K) * (Z' : GL (Fin 3) K) =
      (Z' : GL (Fin 3) K) * (A : GL (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => g * (A : GL (Fin 3) K)) hZ'
    simpa [mul_assoc] using this
  have hZmul : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
      (((Z : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((Z : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) hZmulGL
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using this
  have hZ'mul : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
      (((Z' : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((Z' : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) hZ'mulGL
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using this
  have hZmulD : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal ![(-1 : K), -1, 1] =
      Matrix.diagonal ![(-1 : K), -1, 1] *
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
    rwa [← hZmat]
  have hZ'mulD : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal ![(-1 : K), 1, -1] =
      Matrix.diagonal ![(-1 : K), 1, -1] *
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
    rwa [← hZ'mat]
  have zero_of_eq_neg : ∀ {x : K}, x = -x → x = 0 := by
    intro x hx
    have h2x : (2 : K) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp h2x).resolve_left h2
  have hA02 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    apply zero_of_eq_neg
    have h := congrFun (congrFun hZmulD 0) 2
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h
  have hA12 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    apply zero_of_eq_neg
    have h := congrFun (congrFun hZmulD 1) 2
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h
  have hA20 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    apply zero_of_eq_neg
    have h := congrFun (congrFun hZmulD 2) 0
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h.symm
  have hA21 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    apply zero_of_eq_neg
    have h := congrFun (congrFun hZmulD 2) 1
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h.symm
  have hA01 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    apply zero_of_eq_neg
    have h := congrFun (congrFun hZ'mulD 0) 1
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h
  have hA10 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    apply zero_of_eq_neg
    have h := congrFun (congrFun hZ'mulD 1) 0
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h.symm
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hA01
  · exact hA02
  · exact hA10
  · exact absurd rfl hij
  · exact hA12
  · exact hA20
  · exact hA21
  · exact absurd rfl hij

private theorem uU_diagonal_entry_normOne (h : UnitaryFieldData p f K)
    (A : uU h 3) (hdiag : ∀ i j : Fin 3, i ≠ j →
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (i : Fin 3) :
    h.bar ((((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i i) *
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
  have hU := (mem_uU h).1 A.2
  have hii := congrFun (congrFun hU i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at hii
  · simpa [Matrix.transpose_apply, Matrix.map_apply] using hii
  · intro k _ hki
    simp [hdiag k i hki]
  · simp

private theorem conj_diag_normOneTorusMat (h : UnitaryFieldData p f K)
    (A : uU h 3)
    (hdiag : ∀ i j : Fin 3, i ≠ j →
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (δ : normOne (unitaryInvolution K p f))
    (hδ : ((δ : Kˣ) : K) =
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0 /
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2)
    (h2 : (2 : K) ≠ 0)
    (u : normOne (unitaryInvolution K p f)) :
    (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
        normOneTorusMat u *
        ((((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K))⁻¹ =
      (((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *
        normOneTorusMat u *
        ((((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K))⁻¹ := by
  classical
  let Am : Matrix (Fin 3) (Fin 3) K := (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
  let a : Fin 3 → K := fun i => Am i i
  let d : Fin 3 → K := ![((δ : Kˣ) : K), (((δ : Kˣ) : K))⁻¹, 1]
  have hAeq : Am = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      simpa [Am] using hdiag i j hij
  have hAne : ∀ i, a i ≠ 0 := by
    intro i
    have hi := (mem_uU h).1 A.2
    have hii := congrFun (congrFun hi i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at hii
    · intro h0
      have h0' : Am i i = 0 := by simpa [a] using h0
      have hii' : ((((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ i i *
          Am i i = 1 := by simpa using hii
      rw [h0', mul_zero] at hii'
      exact zero_ne_one hii'
    · intro k _ hki
      simp [hdiag k i hki]
    · simp
  have hAinv : (Matrix.diagonal a)⁻¹ = Matrix.diagonal (fun i => (a i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hAne i)
  have hDeq : (((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d :=
    coe_coe_normOneDiagHom δ
  have hDne : ∀ i, d i ≠ 0 := by
    intro i
    fin_cases i <;> simp [d, Units.ne_zero]
  have hDinv : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hDne i)
  have hA00 : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      ((δ : Kˣ) : K) * (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    have h2ne : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
      simpa [Am] using hAne 2
    rw [hδ]
    field_simp [h2ne]
  change Am * normOneTorusMat u * Am⁻¹ =
    (((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * normOneTorusMat u *
      ((((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))⁻¹
  rw [hAeq, hAinv, hDeq, hDinv]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [normOneTorusMat, normOneTorusA, normOneTorusB, a, d, hδ, h2, Am,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] <;>
    field_simp [show (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 by
        simpa [a, Am] using hAne 0,
      show (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 by
        simpa [a, Am] using hAne 1,
      show (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 by
        simpa [a, Am] using hAne 2] <;> ring

private theorem uniU₀_mul_self (hq : Odd (p ^ f)) :
    uniU₀ K hq * uniU₀ K hq = 1 := by
  have huni : uniU₀ K hq =
      statedProjMk (StatedSU 3 (p ^ f) K) (suOdd₃ K hq) := rfl
  rw [huni, ← map_mul, suOdd₃_mul_self hq, map_one]

private theorem uniU₀_ne_one (hq : Odd (p ^ f)) (h2 : (2 : K) ≠ 0) :
    uniU₀ K hq ≠ 1 := by
  intro h1
  have huni : uniU₀ K hq =
      statedProjMk (StatedSU 3 (p ^ f) K) (suOdd₃ K hq) := rfl
  have hq1 : statedProjMk (StatedSU 3 (p ^ f) K) (suOdd₃ K hq) = 1 := by
    rw [← huni]
    exact h1
  have hmem : suOdd₃ K hq ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.eq_one_iff _).mp hq1
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have h00 := congrArg (fun g : GL (Fin 3) K =>
    ((((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) 0 0) hc
  have h22 := congrArg (fun g : GL (Fin 3) K =>
    ((((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) 2 2) hc
  rw [suOdd₃_coe] at h00 h22
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal] at h00 h22
  have hcnegK : (c : K) = -1 := by
    rw [h00]
    norm_num
  have hc1K : (c : K) = 1 := by
    rw [h22]
    norm_num
  have hneg : (-1 : K) = 1 := by
    rw [← hcnegK, hc1K]
  have h2zero : (2 : K) = 0 := by linear_combination -hneg
  exact h2 h2zero

private theorem orderOf_uniU₀ (hq : Odd (p ^ f)) (h2 : (2 : K) ≠ 0) :
    orderOf (uniU₀ K hq) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact uniU₀_mul_self hq) (uniU₀_ne_one hq h2)

private theorem uFieldAut_psuNormOneTorus (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hq : Odd (p ^ f)) (φ : K ≃+* K)
    (hφσ : ∀ c, φ (unitaryInvolution K p f c) =
      unitaryInvolution K p f (φ c))
    (u : normOne (unitaryInvolution K p f)) :
    uFieldAut h (by omega : 1 ≤ 3) φ (psuNormOneTorus hK h2 u) =
      psuNormOneTorus hK h2 (normOneMap φ hφσ u) := by
  rw [psuNormOneTorus_eq, psuNormOneTorus_eq]
  change uFieldAut h (by omega : 1 ≤ 3) φ
      (projH (StatedSU 3 (p ^ f) K) (suNormOneTorus hK h2 u)) =
    projH (StatedSU 3 (p ^ f) K) (suNormOneTorus hK h2 (normOneMap φ hφσ u))
  rw [uFieldAut_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_glAut, suNormOneTorus_coe, normOneTorusMat, normOneTorusA,
      normOneTorusB, Matrix.map_apply, coe_coe_normOneMap, map_ofNat]

private theorem uFieldAut_psuNormOneDiagonal (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hq : Odd (p ^ f)) (φ : K ≃+* K)
    (hφσ : ∀ c, φ (unitaryInvolution K p f c) =
      unitaryInvolution K p f (φ c))
    (δ : normOne (unitaryInvolution K p f)) :
    uFieldAut h (by omega : 1 ≤ 3) φ (psuNormOneDiagonalHom hK δ) =
      psuNormOneDiagonalHom hK (normOneMap φ hφσ δ) := by
  dsimp only [psuNormOneDiagonalHom, MonoidHom.comp_apply]
  change uFieldAut h (by omega : 1 ≤ 3) φ
      (projH (StatedSU 3 (p ^ f) K)
        ((MulEquiv.subgroupCongr
          (SUid_eq_statedSU (p := p) (f := f) hK 3)) (normOneDiagHom δ))) = _
  rw [uFieldAut_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_glAut, coe_coe_normOneDiagHom, normOneDiagTuple,
      Matrix.map_apply, coe_coe_normOneMap, map_ofNat, map_div₀, map_inv₀]

private theorem uConjAut_psuNormOneDiagonal_of_diagonal (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (A : uU h 3)
    (hdiag : ∀ i j : Fin 3, i ≠ j →
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (δ : normOne (unitaryInvolution K p f)) :
    uConjAut h (by omega : 1 ≤ 3) A (psuNormOneDiagonalHom hK δ) =
      psuNormOneDiagonalHom hK δ := by
  dsimp only [psuNormOneDiagonalHom, MonoidHom.comp_apply]
  let D : StatedSU 3 (p ^ f) K :=
    (MulEquiv.subgroupCongr
      (SUid_eq_statedSU (p := p) (f := f) hK 3)) (normOneDiagHom δ)
  change uConjAut h (by omega : 1 ≤ 3) A
      (projH (StatedSU 3 (p ^ f) K) D) =
    projH (StatedSU 3 (p ^ f) K) D
  rw [uConjAut_proj]
  have hAeq : (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i => (((A : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hdiag i j hij
  have hDmat : (((D : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![((δ : Kˣ) : K), (((δ : Kˣ) : K))⁻¹, 1] := by
    change ((((normOneDiagHom δ : SUid (unitaryInvolution K p f) 3) :
      GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = _
    exact coe_coe_normOneDiagHom δ
  have hcomm : (A : GL (Fin 3) K) * (D : GL (Fin 3) K) =
      (D : GL (Fin 3) K) * (A : GL (Fin 3) K) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      hAeq, hDmat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hconj : (A : GL (Fin 3) K) * (D : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      (D : GL (Fin 3) K) := by
    calc
      (A : GL (Fin 3) K) * (D : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
          (D : GL (Fin 3) K) * (A : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ := by
            rw [hcomm]
      _ = (D : GL (Fin 3) K) := by group
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (((A : GL (Fin 3) K) * (D : GL (Fin 3) K) *
    (A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (((D : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j
  rw [hconj]

private theorem uConjAut_psuNormOneTorus (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (A : uU h 3)
    (hdiag : ∀ i j : Fin 3, i ≠ j →
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (δ : normOne (unitaryInvolution K p f))
    (hδ : ((δ : Kˣ) : K) =
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0 /
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2)
    (u : normOne (unitaryInvolution K p f)) :
    uConjAut h (by omega : 1 ≤ 3) A (psuNormOneTorus hK h2 u) =
      psuNormOneDiagonalHom hK δ * psuNormOneTorus hK h2 u *
        (psuNormOneDiagonalHom hK δ)⁻¹ := by
  rw [psuNormOneTorus_eq, psuNormOneDiagonalHom, MonoidHom.comp_apply]
  change uConjAut h (by omega : 1 ≤ 3) A
      (projH (StatedSU 3 (p ^ f) K) (suNormOneTorus hK h2 u)) =
    projH (StatedSU 3 (p ^ f) K)
        ((MulEquiv.subgroupCongr
          (SUid_eq_statedSU (p := p) (f := f) hK 3)) (normOneDiagHom δ)) *
      projH (StatedSU 3 (p ^ f) K) (suNormOneTorus hK h2 u) *
      (projH (StatedSU 3 (p ^ f) K)
        ((MulEquiv.subgroupCongr
          (SUid_eq_statedSU (p := p) (f := f) hK 3)) (normOneDiagHom δ)))⁻¹
  rw [uConjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  have hmat := conj_diag_normOneTorusMat h A hdiag δ hδ h2 u
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
    suNormOneTorus_coe, coe_coe_normOneDiagHom] using hmat

private theorem uFieldAut_fixes_psuNormOneTorus_zpowers (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hq : Odd (p ^ f)) (φ : K ≃+* K)
    (hφσ : ∀ c, φ (unitaryInvolution K p f c) =
      unitaryInvolution K p f (φ c))
    (r : ℕ) [Fact r.Prime] (hrdvd : r ∣ p ^ f + 1)
    (lam : normOne (unitaryInvolution K p f))
    (hlam : orderOf (psuNormOneTorus hK h2 lam) = r) :
    (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
        (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom =
      Subgroup.zpowers (psuNormOneTorus hK h2 lam) := by
  classical
  let gen := psuNormOneTorus hK h2 lam
  let T : Subgroup (PSU3 p f K) := (psuNormOneTorus hK h2).range
  have hTcard : Nat.card T = p ^ f + 1 := by
    rw [show T = (psuNormOneTorus hK h2).range from rfl, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (psuNormOneTorus_injective hK h2)]
    calc Nat.card (⊤ : Subgroup (normOne (unitaryInvolution K p f))) =
          Nat.card (normOne (unitaryInvolution K p f)) :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = p ^ f + 1 := card_normOne hK
  haveI hcyc : IsCyclic T := by
    haveI hN : IsCyclic (normOne (unitaryInvolution K p f)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective ((psuNormOneTorus hK h2).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨H0, hH0, huniq⟩ :=
    CFSG.GorensteinWalter.secondCase_unique_order_p_subgroup_of_cyclic
      (G := PSU3 p f K) (T := T) (k := p ^ f + 1) (p := r) hcyc hTcard hrdvd
  have hgenT : gen ∈ T := ⟨lam, rfl⟩
  have hP0le : Subgroup.zpowers gen ≤ T := Subgroup.zpowers_le.mpr hgenT
  have hP0card : Nat.card (Subgroup.zpowers gen) = r := by
    rw [Nat.card_zpowers, hlam]
  have hfgen : (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom gen =
      psuNormOneTorus hK h2 (normOneMap φ hφσ lam) :=
    uFieldAut_psuNormOneTorus h hK h2 hq φ hφσ lam
  have hfgenT : (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom gen ∈ T :=
    ⟨normOneMap φ hφσ lam, hfgen.symm⟩
  have hfP0le : (Subgroup.zpowers gen).map
      (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom ≤ T := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hfgenT
  have hfP0card : Nat.card ((Subgroup.zpowers gen).map
      (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom) = r := by
    rw [Subgroup.card_map_of_injective (uFieldAut h (by omega : 1 ≤ 3) φ).injective,
      hP0card]
  exact (huniq _ ⟨hfP0le, hfP0card⟩).trans
    (huniq _ ⟨hP0le, hP0card⟩).symm

private noncomputable def psuD0Orbit (hK : Nat.card K = (p ^ f) ^ 2)
    (P0 : Subgroup (PSU3 p f K)) : Set (Subgroup (PSU3 p f K)) :=
  {Q | ∃ d : psuNormOneDiagonal hK,
    Q = P0.map (MulAut.conj (d : PSU3 p f K)).toMonoidHom}

private theorem odd_card_psuD0Orbit (hK : Nat.card K = (p ^ f) ^ 2)
    (hq4 : p ^ f % 4 = 1) (hq : Odd (p ^ f)) (h2 : (2 : K) ≠ 0)
    (lam : normOne (unitaryInvolution K p f))
    (hinv : uniU₀ K hq * psuNormOneTorus hK h2 lam * (uniU₀ K hq)⁻¹ =
      (psuNormOneTorus hK h2 lam)⁻¹) :
    Odd (Nat.card (psuD0Orbit (p := p) (f := f) (K := K) hK
      (Subgroup.zpowers (psuNormOneTorus hK h2 lam)))) := by
  classical
  let D0 : Subgroup (PSU3 p f K) := psuNormOneDiagonal hK
  let P0 : Subgroup (PSU3 p f K) := Subgroup.zpowers (psuNormOneTorus hK h2 lam)
  let act : MulAction D0 (Subgroup (PSU3 p f K)) :=
    { smul := fun d P => P.map (MulAut.conj ((d : D0) : PSU3 p f K)).toMonoidHom
      one_smul := fun P => by
        change P.map (MulAut.conj (((1 : D0) : PSU3 p f K))).toMonoidHom = P
        rw [Subgroup.coe_one, map_one]
        exact Subgroup.map_id P
      mul_smul := fun d e P => by
        change P.map (MulAut.conj (((d * e : D0) : PSU3 p f K))).toMonoidHom =
          (P.map (MulAut.conj (((e : D0) : PSU3 p f K))).toMonoidHom).map
            (MulAut.conj (((d : D0) : PSU3 p f K))).toMonoidHom
        rw [Subgroup.coe_mul, map_mul, Subgroup.map_map]
        rfl }
  letI := act
  have horbit : MulAction.orbit D0 P0 =
      psuD0Orbit (p := p) (f := f) (K := K) hK P0 := by
    ext Q
    simp only [MulAction.mem_orbit_iff,
      psuD0Orbit, Set.mem_setOf_eq]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, hd.symm⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, hd.symm⟩
  have hx0D : uniU₀ K hq ∈ D0 := by
    rw [show D0 = psuNormOneDiagonal hK from rfl, psuNormOneDiagonal]
    exact ⟨CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.negOneN, psuNormOneDiagonalHom_negOne (p := p) (f := f) hK hq⟩
  let x0D : D0 := ⟨uniU₀ K hq, hx0D⟩
  have hx0gen : (MulAut.conj (x0D : PSU3 p f K)).toMonoidHom
      (psuNormOneTorus hK h2 lam) = (psuNormOneTorus hK h2 lam)⁻¹ := by
    simpa [x0D, MulAut.conj_apply] using hinv
  have hmap : P0.map (MulAut.conj (x0D : PSU3 p f K)).toMonoidHom = P0 := by
    rw [show P0 = Subgroup.zpowers (psuNormOneTorus hK h2 lam) from rfl,
      MonoidHom.map_zpowers, hx0gen, Subgroup.zpowers_inv]
  have hstab : x0D ∈ MulAction.stabilizer D0 P0 := by
    rw [MulAction.mem_stabilizer_iff]
    exact hmap
  let S : Subgroup D0 := Subgroup.zpowers x0D
  have hS_card : Nat.card S = 2 := by
    rw [show S = Subgroup.zpowers x0D from rfl, Nat.card_zpowers]
    simpa [x0D] using orderOf_uniU₀ (p := p) (f := f) (K := K) hq h2
  have hD0_card : Nat.card D0 = p ^ f + 1 := by
    simpa [D0] using card_psuNormOneDiagonal hK
  have hS_index : S.index = (p ^ f + 1) / 2 := by
    have hcard := Subgroup.card_mul_index S
    rw [hS_card, hD0_card] at hcard
    omega
  have hnot2 : ¬ 2 ∣ S.index := by
    rw [hS_index]
    simpa [even_iff_two_dvd] using
      (Nat.not_even_iff_odd.mpr (odd_half_add_one hq4))
  let Ssyl : Sylow 2 D0 :=
    (IsPGroup.of_card (show Nat.card S = 2 ^ 1 by rw [hS_card]; norm_num)).toSylow hnot2
  have hScoe : (Ssyl : Subgroup D0) = S := IsPGroup.toSylow_coe _ _
  have hle : (Ssyl : Subgroup D0) ≤ MulAction.stabilizer D0 P0 := by
    rw [hScoe]
    exact Subgroup.zpowers_le.mpr hstab
  have hfix : P0 ∈ MulAction.fixedPoints Ssyl (Subgroup (PSU3 p f K)) :=
    MulAction.mem_fixedPoints.mpr fun s =>
      MulAction.mem_stabilizer_iff.mp (hle s.2)
  have hnotdvd :=
    CFSG.FiveTransitive.SylowThreeFixedOrbits.odd_orbit_of_sylow_fixed P0 Ssyl hfix
  rw [horbit] at hnotdvd
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnotdvd)

private theorem uFieldAut_fixes_uniU₀ (h : UnitaryFieldData p f K) (hq : Odd (p ^ f))
    (φ : K ≃+* K) :
    uFieldAut h (by omega : 1 ≤ 3) φ (uniU₀ K hq) = uniU₀ K hq := by
  rw [show uniU₀ K hq = projH (StatedSU 3 (p ^ f) K) (suOdd₃ K hq) from rfl]
  rw [uFieldAut_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_glAut]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suOdd₃, oddDiag₃, Matrix.map_apply]

private theorem uFieldAut_fixes_uniU₀' (h : UnitaryFieldData p f K) (hq : Odd (p ^ f))
    (φ : K ≃+* K) :
    uFieldAut h (by omega : 1 ≤ 3) φ (uniU₀' K hq) = uniU₀' K hq := by
  rw [show uniU₀' K hq = projH (StatedSU 3 (p ^ f) K) (⟨oddDiag₂ K,
    Subgroup.subset_closure ⟨det_oddDiag₂ K, unitary_oddDiag₂ hq⟩⟩ :
      StatedSU 3 (p ^ f) K) from rfl]
  rw [uFieldAut_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_glAut]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oddDiag₂, Matrix.map_apply]

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG CFSG.Open CFSG.ClassicalGroups.Unitary
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Phan CFSG.RankThree.CentralCover
open Subgroup

variable {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime] [CharP K p]

private theorem eq_conj_of_uConjAut_proj_fixes (h : UnitaryFieldData p f K)
    (A : uU h 3) (Z : StatedSU 3 (p ^ f) K)
    (htrace : Matrix.trace (((Z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) ≠ 0)
    (hfix : uConjAut h (by omega : 1 ≤ 3) A
      (projH (StatedSU 3 (p ^ f) K) Z) =
      projH (StatedSU 3 (p ^ f) K) Z) :
    (A : GL (Fin 3) K) * (Z : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      (Z : GL (Fin 3) K) := by
  classical
  let W : StatedSU 3 (p ^ f) K := ⟨(A : GL (Fin 3) K) * (Z : GL (Fin 3) K) *
    (A : GL (Fin 3) K)⁻¹, uConjSU_mem h A Z⟩
  have hWdef : ((W : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) =
      (A : GL (Fin 3) K) * (Z : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ := rfl
  have hfixW : projH (StatedSU 3 (p ^ f) K) W =
      projH (StatedSU 3 (p ^ f) K) Z := by
    rw [uConjAut_proj] at hfix
    simpa [W] using hfix
  have hmem : (W)⁻¹ * Z ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.eq (s := (StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (p ^ f) K))).mp hfixW
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have hc' : ((W : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      (Z : GL (Fin 3) K)) := by
    calc
      (W : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c =
          (W : GL (Fin 3) K) * ((W⁻¹ * Z : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) := by
            rw [hc]
      _ = ((W * (W⁻¹ * Z) : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) := by
            rw [← Subgroup.coe_mul]
      _ = (Z : GL (Fin 3) K) := by
            congr 1
            group
  have hW : ((W : GL (Fin 3) K)) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ * (Z : GL (Fin 3) K) := by
    have h1 : (W : GL (Fin 3) K) =
        (Z : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ := by
      calc
        (W : GL (Fin 3) K) = (W : GL (Fin 3) K) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) c *
            Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ := by
              rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
        _ = (Z : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ := by
              rw [hc']
    rw [h1, Matrix.GeneralLinearGroup.scalar_commute c⁻¹ (Z : GL (Fin 3) K)]
  have hWmat : (((W : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
        (((Z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
        (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)⁻¹ := by
    rw [hWdef, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  have hunit : IsUnit ((((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) :=
    (A : GL (Fin 3) K).isUnit
  have hdet : IsUnit ((((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hAA : ((((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K))⁻¹ *
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have htraceW : Matrix.trace (((W : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.trace (((Z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hWmat, Matrix.trace_mul_cycle, hAA, one_mul]
  have hc1 : c⁻¹ = 1 := by
    have h1 : Matrix.trace (((W : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        ((c⁻¹ : Kˣ) : K) * Matrix.trace (((Z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hW, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul]
      rfl
    rw [htraceW] at h1
    have h1' : ((c⁻¹ : Kˣ) : K) * Matrix.trace (((Z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        (1 : K) * Matrix.trace (((Z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← h1, one_mul]
    have := mul_right_cancel₀ htrace h1'
    simpa using this
  have hWZ : ((W : GL (Fin 3) K)) = (Z : GL (Fin 3) K) := by
    rw [hW, hc1, map_one, one_mul]
  simpa [hWdef] using hWZ

private theorem psuD0Orbit_invariant_of_fixes (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hq : Odd (p ^ f)) (hq4 : p ^ f % 4 = 1)
    (r : ℕ) [Fact r.Prime] (hrdvd : r ∣ p ^ f + 1)
    (lam : normOne (unitaryInvolution K p f))
    (hlam : orderOf (psuNormOneTorus hK h2 lam) = r)
    (α : MulAut (PSU3 p f K))
    (hα0 : α (uniU₀ K hq) = uniU₀ K hq)
    (hα1 : α (uniU₀' K hq) = uniU₀' K hq) :
    ∀ P ∈ psuD0Orbit (p := p) (f := f) (K := K) hK
        (Subgroup.zpowers (psuNormOneTorus hK h2 lam)),
      P.map α.toMonoidHom ∈ psuD0Orbit (p := p) (f := f) (K := K) hK
        (Subgroup.zpowers (psuNormOneTorus hK h2 lam)) := by
  classical
  intro P hP
  obtain ⟨A, φ, hα⟩ :=
    CFSG.ComponentClassification.Burgoyne.U.exists_uConjAut_mul_uFieldAut h
      (n := 3) (by omega) (by omega) α
  have hφσ : ∀ c, φ (unitaryInvolution K p f c) =
      unitaryInvolution K p f (φ c) := by
    intro c
    rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  have hf0 : uFieldAut h (by omega : 1 ≤ 3) φ (uniU₀ K hq) = uniU₀ K hq :=
    uFieldAut_fixes_uniU₀ h hq φ
  have hf1 : uFieldAut h (by omega : 1 ≤ 3) φ (uniU₀' K hq) = uniU₀' K hq :=
    uFieldAut_fixes_uniU₀' h hq φ
  have hA0 : uConjAut h (by omega : 1 ≤ 3) A (uniU₀ K hq) = uniU₀ K hq := by
    have := hα0
    rw [hα, MulAut.mul_apply, hf0] at this
    exact this
  have hA1 : uConjAut h (by omega : 1 ≤ 3) A (uniU₀' K hq) = uniU₀' K hq := by
    have := hα1
    rw [hα, MulAut.mul_apply, hf1] at this
    exact this
  have htraceZ : Matrix.trace (((suOdd₃ K hq : StatedSU 3 (p ^ f) K) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    rw [suOdd₃_coe]
    simp [Matrix.trace, Fin.sum_univ_three]
  have htraceZ' : Matrix.trace (((suOdd₂ K hq : StatedSU 3 (p ^ f) K) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    rw [suOdd₂_coe]
    simp [Matrix.trace, Fin.sum_univ_three]
  have hAZ : (A : GL (Fin 3) K) * (suOdd₃ K hq : GL (Fin 3) K) *
      (A : GL (Fin 3) K)⁻¹ = (suOdd₃ K hq : GL (Fin 3) K) :=
    eq_conj_of_uConjAut_proj_fixes h A (suOdd₃ K hq) htraceZ hA0
  have hAZ' : (A : GL (Fin 3) K) * (suOdd₂ K hq : GL (Fin 3) K) *
      (A : GL (Fin 3) K)⁻¹ = (suOdd₂ K hq : GL (Fin 3) K) :=
    eq_conj_of_uConjAut_proj_fixes h A (suOdd₂ K hq) htraceZ' hA1
  have hdiag : ∀ i j : Fin 3, i ≠ j →
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
    offdiag_eq_zero_of_commutes_signs h A (suOdd₃ K hq) (suOdd₂ K hq)
      (suOdd₃_coe hq) (suOdd₂_coe hq) hAZ hAZ' h2
  let a0 : K := (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0
  let a2 : K := (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2
  have ha0 : a0 ≠ 0 := by
    have hnorm : h.bar a0 * a0 = 1 := by
      simpa [a0] using uU_diagonal_entry_normOne h A hdiag 0
    intro h0
    rw [h0, mul_zero] at hnorm
    exact zero_ne_one hnorm
  have ha2 : a2 ≠ 0 := by
    have hnorm : h.bar a2 * a2 = 1 := by
      simpa [a2] using uU_diagonal_entry_normOne h A hdiag 2
    intro h0
    rw [h0, mul_zero] at hnorm
    exact zero_ne_one hnorm
  let δ : Kˣ := Units.mk0 (a0 / a2) (div_ne_zero ha0 ha2)
  have hδnorm : δ ∈ normOne (unitaryInvolution K p f) := by
    rw [mem_normOne]
    change unitaryInvolution K p f (a0 / a2) * (a0 / a2) = 1
    have hσbar : unitaryInvolution K p f = h.bar := by
      ext c
      change c ^ (p ^ f) = h.bar c
      rw [h.bar_apply]
    have hσbar' : unitaryInvolution K p f (a0 / a2) = h.bar (a0 / a2) :=
      DFunLike.congr_fun hσbar (a0 / a2)
    rw [hσbar', map_div₀]
    have h0 : h.bar a0 * a0 = 1 := by
      simpa [a0] using uU_diagonal_entry_normOne h A hdiag 0
    have h2' : h.bar a2 * a2 = 1 := by
      simpa [a2] using uU_diagonal_entry_normOne h A hdiag 2
    field_simp [ha0, ha2]
    rw [h0, h2']
  let δn : normOne (unitaryInvolution K p f) := ⟨δ, hδnorm⟩
  let dA : psuNormOneDiagonal hK :=
    ⟨psuNormOneDiagonalHom hK δn, ⟨δn, rfl⟩⟩
  have hδeq : ((δn : Kˣ) : K) = a0 / a2 := rfl
  have hfP0 : (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
      (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom =
      Subgroup.zpowers (psuNormOneTorus hK h2 lam) :=
    uFieldAut_fixes_psuNormOneTorus_zpowers h hK h2 hq φ hφσ r hrdvd lam hlam
  have hcAgen : uConjAut h (by omega : 1 ≤ 3) A (psuNormOneTorus hK h2 lam) =
      psuNormOneDiagonalHom hK δn * psuNormOneTorus hK h2 lam *
        (psuNormOneDiagonalHom hK δn)⁻¹ :=
    uConjAut_psuNormOneTorus h hK h2 A hdiag δn hδeq lam
  have hαP0 : (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map α.toMonoidHom =
      (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
        (MulAut.conj (dA : PSU3 p f K)).toMonoidHom := by
    calc
      (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map α.toMonoidHom =
          ((Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
            (uFieldAut h (by omega : 1 ≤ 3) φ).toMonoidHom).map
              (uConjAut h (by omega : 1 ≤ 3) A).toMonoidHom := by
            rw [hα]
            rw [Subgroup.map_map]
            rfl
      _ = (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
            (uConjAut h (by omega : 1 ≤ 3) A).toMonoidHom := by rw [hfP0]
      _ = (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
            (MulAut.conj (dA : PSU3 p f K)).toMonoidHom := by
            rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
            change Subgroup.zpowers ((uConjAut h (by omega : 1 ≤ 3) A)
                (psuNormOneTorus hK h2 lam)) =
              Subgroup.zpowers ((MulAut.conj (dA : PSU3 p f K))
                (psuNormOneTorus hK h2 lam))
            rw [hcAgen]
            change Subgroup.zpowers (psuNormOneDiagonalHom hK δn *
                psuNormOneTorus hK h2 lam * (psuNormOneDiagonalHom hK δn)⁻¹) =
              Subgroup.zpowers ((dA : PSU3 p f K) *
                psuNormOneTorus hK h2 lam * (dA : PSU3 p f K)⁻¹)
            rw [show (dA : PSU3 p f K) = psuNormOneDiagonalHom hK δn from rfl]
  have hαd : ∀ ε : normOne (unitaryInvolution K p f),
      α (psuNormOneDiagonalHom hK ε) =
        psuNormOneDiagonalHom hK (normOneMap φ hφσ ε) := by
    intro ε
    rw [hα, MulAut.mul_apply,
      uFieldAut_psuNormOneDiagonal h hK h2 hq φ hφσ ε,
      uConjAut_psuNormOneDiagonal_of_diagonal h hK h2 A hdiag
        (normOneMap φ hφσ ε)]
  obtain ⟨d, rfl⟩ := hP
  obtain ⟨ε, hε⟩ := d.2
  have hd : (d : PSU3 p f K) = psuNormOneDiagonalHom hK ε := by
    rw [← hε]
  refine ⟨⟨psuNormOneDiagonalHom hK (normOneMap φ hφσ ε * δn), ⟨_, rfl⟩⟩, ?_⟩
  calc
    ((Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
        (MulAut.conj (d : PSU3 p f K)).toMonoidHom).map α.toMonoidHom =
        (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
          (α.toMonoidHom.comp (MulAut.conj (d : PSU3 p f K)).toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
          ((MulAut.conj (α (d : PSU3 p f K))).toMonoidHom.comp α.toMonoidHom) := by
          congr 1
          ext x
          simp [MulAut.conj_apply, map_mul]
    _ = ((Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map α.toMonoidHom).map
          (MulAut.conj (α (d : PSU3 p f K))).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = ((Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
          (MulAut.conj (dA : PSU3 p f K)).toMonoidHom).map
            (MulAut.conj (α (d : PSU3 p f K))).toMonoidHom := by rw [hαP0]
    _ = (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
          ((MulAut.conj (α (d : PSU3 p f K))).toMonoidHom.comp
            (MulAut.conj (dA : PSU3 p f K)).toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
          (MulAut.conj (α (d : PSU3 p f K) * (dA : PSU3 p f K))).toMonoidHom := by
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
    _ = (Subgroup.zpowers (psuNormOneTorus hK h2 lam)).map
          (MulAut.conj (psuNormOneDiagonalHom hK
            (normOneMap φ hφσ ε * δn) : PSU3 p f K)).toMonoidHom := by
          rw [hd, hαd ε]
          rw [show (dA : PSU3 p f K) = psuNormOneDiagonalHom hK δn from rfl]
          rw [show psuNormOneDiagonalHom hK (normOneMap φ hφσ ε * δn) =
            psuNormOneDiagonalHom hK (normOneMap φ hφσ ε) *
              psuNormOneDiagonalHom hK δn from
            map_mul (psuNormOneDiagonalHom hK) ((normOneMap φ hφσ) ε) δn]

private theorem card_of_mem_psuD0Orbit (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    {r : ℕ} (lam : normOne (unitaryInvolution K p f))
    (hlam : orderOf (psuNormOneTorus hK h2 lam) = r)
    {P : Subgroup (PSU3 p f K)}
    (hP : P ∈ psuD0Orbit (p := p) (f := f) (K := K) hK
      (Subgroup.zpowers (psuNormOneTorus hK h2 lam))) :
    Nat.card P = r := by
  obtain ⟨d, rfl⟩ := hP
  rw [Subgroup.card_map_of_injective (MulAut.conj (d : PSU3 p f K)).injective,
    Nat.card_zpowers, hlam]

private theorem uniU₀_comm_psuNormOneDiagonal (hK : Nat.card K = (p ^ f) ^ 2)
    (h2 : (2 : K) ≠ 0) (hq : Odd (p ^ f)) (d : psuNormOneDiagonal hK) :
    uniU₀ K hq * (d : PSU3 p f K) = (d : PSU3 p f K) * uniU₀ K hq := by
  obtain ⟨ε, hε⟩ := d.2
  rw [← hε]
  rw [← psuNormOneDiagonalHom_negOne (p := p) (f := f) hK hq]
  rw [← map_mul, ← map_mul, mul_comm]

private theorem uniU₀_inv_of_mem_psuD0Orbit (hK : Nat.card K = (p ^ f) ^ 2)
    (h2 : (2 : K) ≠ 0) (hq : Odd (p ^ f))
    (lam : normOne (unitaryInvolution K p f))
    (hinv : uniU₀ K hq * psuNormOneTorus hK h2 lam * (uniU₀ K hq)⁻¹ =
      (psuNormOneTorus hK h2 lam)⁻¹)
    {P : Subgroup (PSU3 p f K)}
    (hP : P ∈ psuD0Orbit (p := p) (f := f) (K := K) hK
      (Subgroup.zpowers (psuNormOneTorus hK h2 lam)))
    {p : PSU3 p f K} (hp : p ∈ P) :
    uniU₀ K hq * p * (uniU₀ K hq)⁻¹ = p⁻¹ := by
  obtain ⟨d, rfl⟩ := hP
  obtain ⟨p0, hp0, rfl⟩ := hp
  have hx0p0 : uniU₀ K hq * p0 * (uniU₀ K hq)⁻¹ = p0⁻¹ := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp0
    calc
      uniU₀ K hq * psuNormOneTorus hK h2 lam ^ n * (uniU₀ K hq)⁻¹ =
          (uniU₀ K hq * psuNormOneTorus hK h2 lam * (uniU₀ K hq)⁻¹) ^ n := by
            rw [conj_zpow]
      _ = ((psuNormOneTorus hK h2 lam)⁻¹) ^ n := by rw [hinv]
      _ = (psuNormOneTorus hK h2 lam ^ n)⁻¹ := by rw [_root_.inv_zpow]
  have hcomm := uniU₀_comm_psuNormOneDiagonal hK h2 hq d
  have hcomm_inv : (d : PSU3 p f K)⁻¹ * (uniU₀ K hq)⁻¹ =
      (uniU₀ K hq)⁻¹ * (d : PSU3 p f K)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hcomm]
  calc
    uniU₀ K hq * ((d : PSU3 p f K) * p0 * (d : PSU3 p f K)⁻¹) * (uniU₀ K hq)⁻¹ =
        (uniU₀ K hq * (d : PSU3 p f K)) * p0 *
          ((d : PSU3 p f K)⁻¹ * (uniU₀ K hq)⁻¹) := by group
    _ = ((d : PSU3 p f K) * uniU₀ K hq) * p0 *
          ((uniU₀ K hq)⁻¹ * (d : PSU3 p f K)⁻¹) := by rw [hcomm, hcomm_inv]
    _ = (d : PSU3 p f K) * (uniU₀ K hq * p0 * (uniU₀ K hq)⁻¹) *
          (d : PSU3 p f K)⁻¹ := by group
    _ = (d : PSU3 p f K) * p0⁻¹ * (d : PSU3 p f K)⁻¹ := by rw [hx0p0]
    _ = ((d : PSU3 p f K) * p0 * (d : PSU3 p f K)⁻¹)⁻¹ := by group

private theorem not_le_centralizer_uniU₀_of_mem_psuD0Orbit (hK : Nat.card K = (p ^ f) ^ 2)
    (h2 : (2 : K) ≠ 0) (hq : Odd (p ^ f)) {r : ℕ} [Fact r.Prime]
    (hr_odd : Odd r) (lam : normOne (unitaryInvolution K p f))
    (hlam : orderOf (psuNormOneTorus hK h2 lam) = r)
    (hinv : uniU₀ K hq * psuNormOneTorus hK h2 lam * (uniU₀ K hq)⁻¹ =
      (psuNormOneTorus hK h2 lam)⁻¹)
    {P : Subgroup (PSU3 p f K)}
    (hP : P ∈ psuD0Orbit (p := p) (f := f) (K := K) hK
      (Subgroup.zpowers (psuNormOneTorus hK h2 lam))) :
    ¬ P ≤ Subgroup.centralizer ({uniU₀ K hq} : Set (PSU3 p f K)) := by
  intro hle
  have hcard : Nat.card P = r :=
    card_of_mem_psuD0Orbit hK h2 lam hlam hP
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Fact.out : r.Prime).ne_one hcard.symm
  obtain ⟨pel, hpel1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let pval : PSU3 p f K := (pel : PSU3 p f K)
  have hpP : pval ∈ P := pel.2
  have hp1' : pval ≠ 1 := fun h => hpel1 (Subtype.ext h)
  have hcentral' : pval * uniU₀ K hq = uniU₀ K hq * pval :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hpP)
  have hcentral : uniU₀ K hq * pval * (uniU₀ K hq)⁻¹ = pval := by
    rw [← hcentral']
    group
  have hinv' : uniU₀ K hq * pval * (uniU₀ K hq)⁻¹ = pval⁻¹ :=
    uniU₀_inv_of_mem_psuD0Orbit hK h2 hq lam hinv hP hpP
  have hsq : pval * pval = 1 := by
    have hp_eq : pval = pval⁻¹ := hcentral.symm.trans hinv'
    nth_rewrite 1 [hp_eq]
    exact inv_mul_cancel pval
  have hdvd : orderOf pval ∣ r := by
    rw [← hcard]
    exact Subgroup.orderOf_dvd_natCard P hpP
  have hord : orderOf pval = r := by
    have hd : orderOf pval = 1 ∨ orderOf pval = r :=
      (Nat.dvd_prime (Fact.out : r.Prime)).mp hdvd
    cases hd with
    | inl h1 => exact absurd (orderOf_eq_one_iff.mp h1) hp1'
    | inr hr => exact hr
  have hdvd2 : orderOf pval ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hr2 : r ∣ 2 := by rwa [hord] at hdvd2
  have hr_ne_two : r ≠ 2 := by
    have := Nat.odd_iff.mp hr_odd
    omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hr2 with h1 | h2
  · exact (Fact.out : r.Prime).ne_one h1
  · exact hr_ne_two h2

private theorem card_range_psuNormOneTorus (hK : Nat.card K = (p ^ f) ^ 2)
    (h2 : (2 : K) ≠ 0) :
    Nat.card (psuNormOneTorus hK h2).range = p ^ f + 1 := by
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (psuNormOneTorus_injective hK h2)]
  calc Nat.card (⊤ : Subgroup (normOne (unitaryInvolution K p f))) =
        Nat.card (normOne (unitaryInvolution K p f)) :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = p ^ f + 1 := card_normOne hK

private theorem exists_inner_torus_standard_psu3 (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hq4 : p ^ f % 4 = 1) (hf : 2 ≤ f) (hq : Odd (p ^ f))
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLn : L.Normal) (e : L ≃* PSU3 p f K) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hx_std : e ⟨x, hxL⟩ = uniU₀ K hq)
    (hy_std : e ⟨y, hyL⟩ = uniU₀' K hq)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQle : Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∃ P : Subgroup G, P ≤ L ∧ (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({x} : Set G) := by
  classical
  obtain ⟨r, hrprime, hrne2, lam, hlam⟩ :=
    exists_odd_prime_torus_member (p := p) (f := f) (K := K) hK h2 hq4 hf
  letI : Fact r.Prime := ⟨hrprime⟩
  have hr_odd : Odd r := hrprime.odd_of_ne_two hrne2
  have hrdvd : r ∣ p ^ f + 1 := by
    rw [← hlam]
    have h := Subgroup.orderOf_dvd_natCard _
      (show psuNormOneTorus hK h2 lam ∈ (psuNormOneTorus hK h2).range from ⟨lam, rfl⟩)
    rwa [card_range_psuNormOneTorus hK h2] at h
  let P0 : Subgroup (PSU3 p f K) := Subgroup.zpowers (psuNormOneTorus hK h2 lam)
  let Ω : Set (Subgroup (PSU3 p f K)) := psuD0Orbit (p := p) (f := f) (K := K) hK P0
  have hfin : Ω.Finite := Set.finite_univ.subset (Set.subset_univ Ω)
  have hinvP0 : uniU₀ K hq * psuNormOneTorus hK h2 lam * (uniU₀ K hq)⁻¹ =
      (psuNormOneTorus hK h2 lam)⁻¹ :=
    uniU₀_conj_psuNormOneTorus (p := p) (f := f) (K := K) hK h2 hq lam
  have hodd : Odd Ω.ncard := by
    have h := odd_card_psuD0Orbit (p := p) (f := f) (K := K) hK hq4 hq h2 lam hinvP0
    rwa [Nat.card_coe_set_eq] at h
  have hβx : ∀ q ∈ Q, MulAut.congr e (MulAut.conjNormal (H := L) q) (uniU₀ K hq) =
      uniU₀ K hq := by
    intro q hqQ
    rw [← hx_std]
    rw [show MulAut.congr e (MulAut.conjNormal (H := L) q) (e ⟨x, hxL⟩) =
        e (MulAut.conjNormal (H := L) q ⟨x, hxL⟩) by
      simp [MulAut.congr_apply]]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hqcx : q * x = x * q := Subgroup.mem_centralizer_singleton_iff.mp (hQle hqQ).1
    change q * x * q⁻¹ = x
    calc
      q * x * q⁻¹ = x * q * q⁻¹ := by rw [hqcx]
      _ = x := by group
  have hβy : ∀ q ∈ Q, MulAut.congr e (MulAut.conjNormal (H := L) q) (uniU₀' K hq) =
      uniU₀' K hq := by
    intro q hqQ
    rw [← hy_std]
    rw [show MulAut.congr e (MulAut.conjNormal (H := L) q) (e ⟨y, hyL⟩) =
        e (MulAut.conjNormal (H := L) q ⟨y, hyL⟩) by
      simp [MulAut.congr_apply]]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hqcy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.mp (hQle hqQ).2
    change q * y * q⁻¹ = y
    calc
      q * y * q⁻¹ = y * q * q⁻¹ := by rw [hqcy]
      _ = y := by group
  have hinv : ∀ q ∈ Q, ∀ P ∈ Ω,
      P.map (MulAut.congr e (MulAut.conjNormal (H := L) q)).toMonoidHom ∈ Ω := by
    intro q hqQ P hP
    exact psuD0Orbit_invariant_of_fixes h hK h2 hq hq4 r hrdvd lam hlam _
      (hβx q hqQ) (hβy q hqQ) P hP
  obtain ⟨P, hPΩ, hPN⟩ :=
    CFSG.exists_le_normalizer_of_odd_ncard e Q hQ Ω hfin hodd hinv
  let PG : Subgroup G := P.map (L.subtype.comp e.symm.toMonoidHom)
  have hPG_le : PG ≤ L := by
    intro pg hpg
    obtain ⟨p, hp, rfl⟩ := hpg
    exact (e.symm p).2
  have hmap_inj : Function.Injective (L.subtype.comp e.symm.toMonoidHom) :=
    L.subtype_injective.comp e.symm.injective
  have hcardPG : Nat.card PG = r := by
    rw [Subgroup.card_map_of_injective hmap_inj,
      card_of_mem_psuD0Orbit hK h2 lam hlam hPΩ]
  have hPG_prime : (Nat.card PG).Prime := by
    rw [hcardPG]; exact hrprime
  have hPG_ne_two : Nat.card PG ≠ 2 := by
    rw [hcardPG]; exact hrne2
  have hPG_not_central_x : ¬ PG ≤ Subgroup.centralizer ({x} : Set G) := by
    intro hle
    have hcent : P ≤ Subgroup.centralizer ({uniU₀ K hq} : Set (PSU3 p f K)) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpG : (e.symm p : G) ∈ PG := ⟨p, hp, rfl⟩
      have hcommG : (e.symm p : G) * x = x * (e.symm p : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hle hpG)
      have hcommL : e.symm p * ⟨x, hxL⟩ = ⟨x, hxL⟩ * e.symm p := by
        apply Subtype.ext
        simpa using hcommG
      have hcommPSU := congrArg e hcommL
      simpa [hx_std] using hcommPSU
    exact not_le_centralizer_uniU₀_of_mem_psuD0Orbit hK h2 hq hr_odd lam hlam
      hinvP0 hPΩ hcent
  exact ⟨PG, hPG_le, hPG_prime, hPG_ne_two, hPN, hPG_not_central_x⟩

private theorem inner_torus_psu3 (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hp2 : p ≠ 2) (hf : 2 ≤ f) (hq4 : p ^ f % 4 = 1)
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLn : L.Normal) (e : L ≃* PSU3 p f K) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQle : Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∃ P : Subgroup G, P ≤ L ∧ (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({x} : Set G) := by
  classical
  have hq : Odd (p ^ f) := by
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with hp | hp
    · exact absurd hp hp2
    · have hpodd : Odd p := Nat.odd_iff.mpr hp
      exact hpodd.pow
  let v : PSU3 p f K := e ⟨x, hxL⟩
  let v' : PSU3 p f K := e ⟨y, hyL⟩
  have hordv : orderOf v = 2 := by
    rw [show v = e ⟨x, hxL⟩ from rfl, MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe ⟨x, hxL⟩).symm.trans hx2
  have hordv' : orderOf v' = 2 := by
    rw [show v' = e ⟨y, hyL⟩ from rfl, MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe ⟨y, hyL⟩).symm.trans hy2
  have hnev : v ≠ v' := by
    intro hv
    have hL : (⟨x, hxL⟩ : L) = ⟨y, hyL⟩ := e.injective (by simpa [v, v'] using hv)
    exact hxy (congrArg Subtype.val hL)
  have hcommv : v * v' = v' * v := by
    have h1 : (⟨x, hxL⟩ : L) * ⟨y, hyL⟩ = ⟨y, hyL⟩ * ⟨x, hxL⟩ := by
      apply Subtype.ext
      exact hcomm
    change e ⟨x, hxL⟩ * e ⟨y, hyL⟩ = e ⟨y, hyL⟩ * e ⟨x, hxL⟩
    rw [← map_mul, ← map_mul]
    exact congrArg e h1
  obtain ⟨g, hgx, hgy⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.uniConj K hq hK v v' hordv hordv' hnev hcommv
  let e' : L ≃* PSU3 p f K := e.trans (MulAut.conj g)
  have hx_std : e' ⟨x, hxL⟩ = uniU₀ K hq := by
    change (MulAut.conj g) (e ⟨x, hxL⟩) = uniU₀ K hq
    simpa [v, MulAut.conj_apply] using hgx
  have hy_std : e' ⟨y, hyL⟩ = uniU₀' K hq := by
    change (MulAut.conj g) (e ⟨y, hyL⟩) = uniU₀' K hq
    simpa [v', MulAut.conj_apply] using hgy
  exact exists_inner_torus_standard_psu3 h hK h2 hq4 hf hq hLn e' hxL hyL hx_std hy_std
    Q hQ hQle

theorem inner_torus_psu3_model (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hf : 2 ≤ f) (hq4 : p ^ f % 4 = 1)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (e : L ≃* StatedProj (StatedSU 3 (p ^ f) K)) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQle : Q ≤ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) :
    ∃ P : Subgroup G, P ≤ L ∧ (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({x} : Set G) := by
  have hK : Nat.card K = (p ^ f) ^ 2 := by
    have h2f : 2 * f = f * 2 := by omega
    rw [h.card, ← pow_mul, h2f]
  have h2 : (2 : K) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hp2
  exact inner_torus_psu3 h hK h2 hp2 hf hq4 inferInstance e hxL hyL hx2 hy2 hxy hcomm
    Q hQ hQle

end CFSG.LocalAnalysis.WeakClosure81
