module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Tools
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37Words
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryFixed
import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofSymForm

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Classical

variable {K : Type} [Field K]

theorem exists_sq_eq_three_of_unitary_seven (h : UnitaryFieldData 7 1 K) :
    (7 : K) = 0 ∧ ∃ z : K, z ^ 2 = 3 ∧ h.bar z = -z := by
  have := h.finite
  have := Fintype.ofFinite K
  have : CharP K 7 := h.charP
  have h7 : (7 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 7
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 7]; norm_num
  have h30 : (3 : K) ≠ 0 := fun h3 => one_ne_zero (α := K) (by linear_combination h7 - 2 * h3)
  obtain ⟨y, hy⟩ := (FiniteField.isSquare_iff hK2 h30).mpr (by
    rw [Fintype.card_eq_nat_card, h.card]
    norm_num
    grind)
  have hy3 : y ^ 2 = 3 := by rw [sq, ← hy]
  refine ⟨h7, y, hy3, ?_⟩
  rw [h.bar_apply, pow_one]
  grind

theorem unitaryScalars_seven_eq_bot (h : UnitaryFieldData 7 1 K) : unitaryScalars h 3 = ⊥ := by
  rw [← Subgroup.card_eq_one, card_unitaryScalars h (by norm_num)]
  norm_num

theorem unitaryProj_seven_injective (h : UnitaryFieldData 7 1 K) :
    Function.Injective (unitaryProj h 3) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj, unitaryScalars_seven_eq_bot]

theorem center_unitaryPSU_seven (h : UnitaryFieldData 7 1 K) :
    Subgroup.center (unitaryPSU h 3) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  have hg : g ∈ Subgroup.center (unitarySU 7 1 K 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.mp hx (unitaryProj h 3 y)
    rw [← map_mul, ← map_mul] at this
    exact unitaryProj_seven_injective h this
  rw [center_unitarySU_three (h := h) (by norm_num), unitaryScalars_seven_eq_bot,
    Subgroup.mem_bot] at hg
  rw [hg, map_one]
  exact Subgroup.one_mem _

theorem exists_antiunitary_normalForm_unitary3 {p f : ℕ} (h : UnitaryFieldData p f K)
    (hp : p ≠ 2) {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h)
    (hAA : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K).map h.bar = 1) :
    ∃ (C : GL (Fin 3) K) (d : K),
      (A : Matrix (Fin 3) (Fin 3) K) * (C : Matrix (Fin 3) (Fin 3) K).map h.bar = C ∧
      ((C : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * 1 * C = d • 1 := by
  classical
  have := h.finite
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
  set A' : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hA'
  have hU : (A'.map h.bar)ᵀ * A' = 1 := mem_unitaryIsom3.mp hA
  set τ := antiunitaryMap h A' with hτ
  have hττ : ∀ v, τ (τ v) = v := by
    intro v
    rw [hτ, antiunitaryMap_apply, antiunitaryMap_apply]
    have hv : (⇑h.bar ∘ fun j => h.bar (v j)) = v := funext fun j => h.bar_bar (v j)
    have e : (fun i => h.bar ((A' *ᵥ fun j => h.bar (v j)) i)) = A'.map h.bar *ᵥ v := by
      funext i
      rw [RingHom.map_mulVec, hv]
    rw [e, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hfin : finrank h.fixedField (conjFixed h τ) = 3 := by
    rw [finrank_conjFixed_of_ne hττ hc, Module.finrank_fin_fun]
  set b : Basis (Fin 3) h.fixedField (conjFixed h τ) := Module.finBasisOfFinrankEq _ _ hfin
  set B : Basis (Fin 3) K (Fin 3 → K) := conjFixedBasisOfNe hττ hc b with hB
  set C₀ : Matrix (Fin 3) (Fin 3) K := (Pi.basisFun K (Fin 3)).toMatrix B with hC₀
  have hC₀ij : ∀ i j, C₀ i j = (b j : Fin 3 → K) i := by
    intro i j
    rw [hC₀, Basis.toMatrix_apply, Pi.basisFun_repr, hB, conjFixedBasisOfNe_apply]
  have hC₀det : C₀.det ≠ 0 := by
    intro h0
    have e := congrArg det (Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun K (Fin 3)) B)
    rw [det_mul, ← hC₀, h0, zero_mul, det_one] at e
    exact zero_ne_one e
  have hAC₀ : A' * C₀.map h.bar = C₀ := by
    ext i j
    have hfix : antiunitaryMap h A' (b j : Fin 3 → K) = b j := (b j).2
    rw [antiunitaryMap_apply] at hfix
    have e := congrFun hfix i
    simp only [Matrix.mulVec, dotProduct] at e
    rw [Matrix.mul_apply, hC₀ij i j, ← e]
    simp only [Matrix.map_apply, hC₀ij]
  have hAbarT : (A'.map h.bar)ᵀ = A'.map h.bar := by
    calc (A'.map h.bar)ᵀ = (A'.map h.bar)ᵀ * (A' * A'.map h.bar) := by rw [hAA, Matrix.mul_one]
      _ = (A'.map h.bar)ᵀ * A' * A'.map h.bar := by rw [Matrix.mul_assoc]
      _ = A'.map h.bar := by rw [hU, Matrix.one_mul]
  have hC₀bar : C₀.map h.bar = (A'.map h.bar)ᵀ * C₀ := by
    calc C₀.map h.bar = (A'.map h.bar)ᵀ * A' * C₀.map h.bar := by rw [hU, Matrix.one_mul]
      _ = (A'.map h.bar)ᵀ * C₀ := by rw [Matrix.mul_assoc, hAC₀]
  set M : Matrix (Fin 3) (Fin 3) K := (C₀.map h.bar)ᵀ * C₀ with hM
  have hMT : Mᵀ = M := by
    rw [hM, transpose_mul, transpose_transpose, hC₀bar, transpose_mul, transpose_transpose,
      hAbarT, Matrix.mul_assoc]
  have hMbar : M.map h.bar = M := by
    have e : M.map h.bar = Mᵀ := by
      rw [hM, Matrix.map_mul, transpose_mul, transpose_transpose]
      congr 1
      ext i j
      simp [h.bar_bar]
    rw [e, hMT]
  have hMdet : M.det ≠ 0 := by
    rw [hM, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hC₀det) hC₀det
  set M₀ : Matrix (Fin 3) (Fin 3) h.fixedField :=
    Matrix.of fun i j => ⟨M i j, h.mem_fixedField.mpr (congrFun (congrFun hMbar i) j)⟩ with hM₀
  have hM₀map : M₀.map h.fixedField.subtype = M := by
    ext i j
    rfl
  have hM₀T : M₀ᵀ = M₀ := by
    ext i j
    exact congrFun (congrFun hMT i) j
  have hM₀det : M₀.det ≠ 0 := by
    intro h0
    apply hMdet
    rw [← hM₀map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2F : (2 : h.fixedField) ≠ 0 := fun h0 => h2 (by
    have e := congrArg h.fixedField.subtype h0
    rwa [map_ofNat, map_zero] at e)
  obtain ⟨c₀, N₀, -, hN₀, hM₀eq⟩ :=
    Sec21.Item211Res6Proof.exists_eq_smul_mul_transpose h2F M₀ hM₀T hM₀det
  have hN₀u : IsUnit N₀.det := isUnit_iff_ne_zero.mpr hN₀
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Matrix (Fin 3) (Fin 3) h.fixedField, P₀ = (N₀⁻¹)ᵀ := ⟨_, rfl⟩
  have hP₀M : P₀ᵀ * M₀ * P₀ = c₀ • 1 := by
    rw [hM₀eq, hP₀, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul N₀ hN₀u, Matrix.one_mul, ← transpose_mul,
      Matrix.nonsing_inv_mul N₀ hN₀u, transpose_one]
  have hP₀det : P₀.det ≠ 0 := by
    rw [hP₀, det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det N₀ hN₀u).ne_zero
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3) (Fin 3) K, P = P₀.map h.fixedField.subtype := ⟨_, rfl⟩
  have hPbar : P.map h.bar = P := by
    rw [hP]
    ext i j
    exact h.mem_fixedField.mp (P₀ i j).2
  have hPdet : P.det ≠ 0 := by
    rw [hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h0 => hP₀det (Subtype.ext (by simpa using h0))
  have hPMP : Pᵀ * M * P = (c₀ : K) • 1 := by
    have e := congrArg (fun Q => Q.map h.fixedField.subtype) hP₀M
    simp only [Matrix.map_mul, hM₀map, Matrix.transpose_map, ← hP] at e
    rw [e]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hCdet : (C₀ * P).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hC₀det hPdet
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (C₀ * P) hCdet, (c₀ : K), ?_, ?_⟩
  · rw [GeneralLinearGroup.val_mkOfDetNeZero, Matrix.map_mul, hPbar, ← Matrix.mul_assoc, hAC₀]
  · rw [GeneralLinearGroup.val_mkOfDetNeZero, Matrix.mul_one, Matrix.map_mul, hPbar,
      transpose_mul, ← hPMP, hM]
    simp only [Matrix.mul_assoc]

variable {p f : ℕ}

@[expose] def u37YGL {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : GL (Fin 3) K :=
  ⟨u37Y z, u37YBar z, u37Y_mul_u37YBar h7 hz, u37YBar_mul_u37Y h7 hz⟩

@[expose] def u37WGL {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : GL (Fin 3) K :=
  ⟨u37W z, u37WInv z, u37W_mul_u37WInv h7 hz, u37WInv_mul_u37W h7 hz⟩

@[expose] def u37C₁GL : GL (Fin 3) K := ⟨u37C₁, u37C₁, u37C₁_mul_self, u37C₁_mul_self⟩

@[expose] def u37C₂GL : GL (Fin 3) K := ⟨u37C₂, u37C₂, u37C₂_mul_self, u37C₂_mul_self⟩

@[expose] def u37C₃GL {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : GL (Fin 3) K :=
  ⟨u37C₃ z, u37C₃ z, u37C₃_mul_self h7 hz, u37C₃_mul_self h7 hz⟩

theorem u37YGL_mem (h : UnitaryFieldData p f K) {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3)
    (hbar : h.bar z = -z) : u37YGL h7 hz ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨det_u37Y h7 hz, ?_⟩
  change ((u37Y z).map h.bar)ᵀ * u37Y z = 1
  rw [map_u37Y h.bar hbar, transpose_u37YBar, u37YBar_mul_u37Y h7 hz]

theorem u37WGL_mem (h : UnitaryFieldData p f K) {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3)
    (hbar : h.bar z = -z) : u37WGL h7 hz ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨det_u37W h7 hz, ?_⟩
  change ((u37W z).map h.bar)ᵀ * u37W z = 1
  rw [map_u37W h.bar hbar, u37WInv_mul_u37W h7 hz]

theorem u37C₁GL_mem (h : UnitaryFieldData p f K) : u37C₁GL ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨det_u37C₁, ?_⟩
  change ((u37C₁ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * u37C₁ = 1
  rw [map_u37C₁, transpose_u37C₁, u37C₁_mul_self]

theorem u37C₂GL_mem (h : UnitaryFieldData p f K) : u37C₂GL ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨det_u37C₂, ?_⟩
  change ((u37C₂ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * u37C₂ = 1
  rw [map_u37C₂, transpose_u37C₂, u37C₂_mul_self]

theorem u37C₃GL_mem (h : UnitaryFieldData p f K) {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3)
    (hbar : h.bar z = -z) : u37C₃GL h7 hz ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨det_u37C₃ h7 hz, ?_⟩
  change ((u37C₃ z).map h.bar)ᵀ * u37C₃ z = 1
  rw [map_u37C₃ h.bar hbar, transpose_transpose, u37C₃_mul_self h7 hz]

private theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {g : G} (hg : g * g = 1)
    (h1 : g ≠ 1) : orderOf g = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hg) h1

theorem exists_word1411_conj_unitaryInvT_seven (h : UnitaryFieldData 7 1 K) :
    ∃ x₁ x₂ x₃ : unitaryPSU h 3,
      orderOf (word1411 (MulAut.conj (unitaryProj h 3 (unitaryInvT h))) x₁ x₂ x₃) = 43 := by
  obtain ⟨h7, z, hz, hbar⟩ := exists_sq_eq_three_of_unitary_seven h
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have hp : (7 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : K) ≠ 0 := fun h3 => one_ne_zero (α := K) (by linear_combination h7 - 2 * h3)
  set π := unitaryProj h 3
  set t : unitarySU 7 1 K 3 := unitaryInvT h
  have hT : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u37T := by
    change negNegOneDiag K = u37T
    ext i j
    fin_cases i <;> fin_cases j <;> simp [negNegOneDiag, u37T]
  set c₁ : unitarySU 7 1 K 3 := ⟨u37C₁GL, u37C₁GL_mem h⟩
  set c₂ : unitarySU 7 1 K 3 := ⟨u37C₂GL, u37C₂GL_mem h⟩
  set c₃ : unitarySU 7 1 K 3 := ⟨u37C₃GL h7 hz, u37C₃GL_mem h h7 hz hbar⟩
  set w : unitarySU 7 1 K 3 := ⟨u37WGL h7 hz, u37WGL_mem h h7 hz hbar⟩
  have hc1 : orderOf c₁ = 2 := by
    refine orderOf_eq_two_of_mul_self (Subtype.ext (Units.ext u37C₁_mul_self)) fun h1 => ?_
    have e := congrArg (fun g : unitarySU 7 1 K 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [c₁, u37C₁GL, u37C₁] at e
  have hc2 : orderOf c₂ = 2 := by
    refine orderOf_eq_two_of_mul_self (Subtype.ext (Units.ext u37C₂_mul_self)) fun h1 => ?_
    have e := congrArg (fun g : unitarySU 7 1 K 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [c₂, u37C₂GL, u37C₂] at e
  have hc3 : orderOf c₃ = 2 := by
    refine orderOf_eq_two_of_mul_self (Subtype.ext (Units.ext (u37C₃_mul_self h7 hz))) fun h1 => ?_
    have e := congrArg (fun g : unitarySU 7 1 K 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    have e' : (2 : K) = 1 := by simpa [c₃, u37C₃GL, u37C₃] using e
    exact one_ne_zero (α := K) (by linear_combination e')
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp hc1)
  obtain ⟨g₂, hg₂⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp hc2)
  obtain ⟨g₃, hg₃⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp hc3)
  have htt : π t * π t = 1 := by
    rw [← map_mul, ← sq, unitaryInvT_sq, map_one]
  have hw : t * c₁ * c₂ * c₃ = w := by
    apply Subtype.ext
    apply Units.ext
    change ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * u37C₁ * u37C₂ * u37C₃ z = u37W z
    rw [hT, u37T_mul_u37C]
  refine ⟨π g₁, π g₂, π g₃, ?_⟩
  rw [word1411_conj_eq htt]
  have e : π t * (π g₁ * π t * (π g₁)⁻¹) * (π g₂ * π t * (π g₂)⁻¹) * (π g₃ * π t * (π g₃)⁻¹) =
      π w := by
    rw [← hw, ← hg₁, ← hg₂, ← hg₃]
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · have : w ^ 43 = 1 := Subtype.ext (Units.ext (by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
      exact u37W_pow_fortyThree h7 hz))
    rw [← map_pow, this, map_one]
  · have hw1 : w = 1 := unitaryProj_seven_injective h (h1.trans (map_one π).symm)
    have e0 : u37W z 0 0 = 1 := by
      have := congrArg (fun g : unitarySU 7 1 K 3 =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) hw1
      simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq] at this
      exact this
    have e1 : u37W z 1 1 = 1 := by
      have := congrArg (fun g : unitarySU 7 1 K 3 =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) hw1
      simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq] at this
      exact this
    exact u37W_zero_zero_ne hz h3 (by rw [e0, e1])

theorem exists_word1411_U3_7 (h : UnitaryFieldData 7 1 K) (α : MulAut (unitaryPSU h 3))
    (hα : orderOf α = 2) : ∃ x₁ x₂ x₃ : unitaryPSU h 3, 43 ∣ orderOf (word1411 α x₁ x₂ x₃) := by
  obtain ⟨h7, z, hz, hbar⟩ := exists_sq_eq_three_of_unitary_seven h
  have hp : (7 : ℕ) ≠ 2 := by norm_num
  have hq : 2 < 7 ^ 1 := by norm_num
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  have key :
      psuConj h (A * ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩) * psuField h (σ * σ) = 1 := by
    rw [map_mul, map_mul, ← psuField_mul_psuConj_mul_inv σ A, ← hα2, sq]
    simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨hσσ, c, hcN, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ key
  rcases ringEquiv_eq_refl_or_bar h hσσ with rfl | hσbar
  ·
    have hα' : psuConj h A * psuField h (RingEquiv.refl K) = psuConj h A := by
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    rw [hα'] at hα hα2 ⊢
    obtain ⟨s, hs⟩ := mem_range_conj_of_mem_psuConj_range_of_coprime ⟨A, rfl⟩
      (m := 2) (by norm_num) hα2
    have hZ := center_unitaryPSU_seven h
    have hs2 : orderOf s = 2 := by
      refine orderOf_eq_prime ?_ fun h1 => ?_
      · have hc : MulAut.conj (s ^ 2) = 1 := by rw [map_pow, hs, hα2]
        have : s ^ 2 ∈ Subgroup.center (unitaryPSU h 3) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have e := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ y) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at e
          calc y * s ^ 2 = s ^ 2 * y * (s ^ 2)⁻¹ * s ^ 2 := by rw [e]
            _ = s ^ 2 * y := by group
        rw [hZ, Subgroup.mem_bot] at this
        exact this
      · rw [h1, map_one] at hs
        rw [← hs, orderOf_one] at hα
        exact absurd hα (by norm_num)
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_unitaryProj_unitaryInvT h hp hs2)
    obtain ⟨y₁, y₂, y₃, hy⟩ := exists_word1411_conj_unitaryInvT_seven h
    set β : MulAut (unitaryPSU h 3) := MulAut.conj g⁻¹
    have hβ : MulAut.conj s = β * MulAut.conj (unitaryProj h 3 (unitaryInvT h)) * β⁻¹ := by
      rw [← hg]
      simp only [β, map_mul, map_inv]
      group
    refine ⟨β y₁, β y₂, β y₃, dvd_of_eq ?_⟩
    rw [← hs, hβ, word1411_conj, MulEquiv.orderOf_eq, hy]
  ·
    have hσmat : ∀ M : Matrix (Fin 3) (Fin 3) K, M.map σ = M.map h.bar := fun M => by
      ext i j
      exact hσbar _
    have hAA : (A : GL (Fin 3) K) * glAut σ A = 1 := by
      have hc1 : c = 1 := by
        have hmat := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).det) hcA
        simp only [Subgroup.coe_mul, Units.val_mul, coe_glAut, det_mul,
          GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmat
        have hσdet : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).det =
            h.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
          rw [hσmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        have hN := norm_det_of_mem_unitaryIsom3 A.2
        rw [UnitaryFieldData.norm] at hN
        have hc3 : (c : K) ^ 3 = 1 := by rw [← hmat, hσdet, hN]
        have hc8 : (c : K) ^ 8 = 1 := by
          rw [UnitaryFieldData.norm, h.bar_apply] at hcN
          rw [← hcN]
          ring
        apply Units.ext
        rw [Units.val_one]
        calc (c : K) = (c : K) * (c : K) ^ 8 := by rw [hc8, mul_one]
          _ = ((c : K) ^ 3) ^ 3 := by ring
          _ = 1 := by rw [hc3, one_pow]
      have e := hcA
      rw [hc1, map_one] at e
      exact e
    have hAAm : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1 := by
      have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hAA
      simpa [coe_glAut, hσmat] using this
    obtain ⟨C, d, hAC, hCC⟩ := exists_antiunitary_normalForm_unitary3 h hp A.2 hAAm
    set y : GL (Fin 3) K := u37YGL h7 hz
    have hyS : y ∈ gramSU h (d • (1 : Matrix (Fin 3) (Fin 3) K)) := by
      have hy := (mem_unitarySU_iff h).mp (u37YGL_mem h h7 hz hbar)
      refine mem_gramSU.mpr ⟨?_, hy.1⟩
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hy.2]
    have hxS : C * y * C⁻¹ ∈ unitarySU 7 1 K 3 := by
      rw [unitarySU_eq_gramSU h 3]
      exact conj_mem_gramSU_of_gram h hCC hyS
    set x : unitarySU 7 1 K 3 := ⟨C * y * C⁻¹, hxS⟩
    have hyσ : glAut σ y = y⁻¹ := by
      apply Units.ext
      rw [coe_glAut, hσmat]
      change (u37Y z).map h.bar = u37YBar z
      exact map_u37Y h.bar hbar
    have hCσ : glAut σ C = (A : GL (Fin 3) K)⁻¹ * C := by
      rw [eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, coe_glAut, hσmat]
      exact hAC
    have hαx : (psuConj h A * psuField h σ) (unitaryProj h 3 x) = (unitaryProj h 3 x)⁻¹ := by
      rw [MulAut.mul_apply, ← map_inv]
      change psuConj h A (psuField h σ (x : unitaryPSU h 3)) = ((x⁻¹ : unitarySU 7 1 K 3) :
        unitaryPSU h 3)
      rw [psuField_mk, psuConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suConj, coe_suField, Subgroup.coe_inv]
      change (A : GL (Fin 3) K) * glAut σ (C * y * C⁻¹) * (A : GL (Fin 3) K)⁻¹ = (C * y * C⁻¹)⁻¹
      rw [map_mul, map_mul, map_inv, hyσ, hCσ]
      group
    have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    have hx43 : orderOf (unitaryProj h 3 x) = 43 := by
      refine orderOf_eq_prime ?_ fun h1 => ?_
      · have : x ^ 43 = 1 := by
          apply Subtype.ext
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
          change (C * y * C⁻¹) ^ 43 = 1
          rw [conj_pow]
          have : y ^ 43 = 1 := Units.ext (by
            rw [Units.val_pow_eq_pow_val]
            exact u37Y_pow_fortyThree h7 hz)
          rw [this, mul_one, mul_inv_cancel]
        rw [← map_pow, this, map_one]
      · have hx1 : x = 1 := unitaryProj_seven_injective h (h1.trans (map_one _).symm)
        have hy1 : y = 1 := by
          have e : C * y * C⁻¹ = 1 := congrArg Subtype.val hx1
          calc y = C⁻¹ * (C * y * C⁻¹) * C := by group
            _ = 1 := by rw [e, mul_one, inv_mul_cancel]
        have e := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 1) hy1
        exact u37Y_zero_one_ne_zero h7 hz (by simpa [y, u37YGL] using e)
    refine ⟨unitaryProj h 3 x, 1, 1, ?_⟩
    have hw : word1411 (psuConj h A * psuField h σ) (unitaryProj h 3 x) 1 1 =
        ((unitaryProj h 3 x) ^ 2)⁻¹ := by
      simp only [word1411, inv_one, mul_one, one_mul, map_one, hαx]
      group
    refine dvd_of_eq ?_
    rw [hw, orderOf_inv, Nat.Coprime.orderOf_pow (by rw [hx43]; norm_num), hx43]

end CFSG.RankThree.PartTwo.Sec20
