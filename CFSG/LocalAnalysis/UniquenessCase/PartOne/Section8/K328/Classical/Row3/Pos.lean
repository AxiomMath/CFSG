module

import CFSG.ClassicalGroups.Orthogonal.MinusLeviBlocks
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
import CFSG.Adapters.StatedQuasisimple
import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LieType.Universal.Spin.Twisted.Short
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open Matrix
open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal.Spin (coe_quadMinus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL map_center_eq_statedScalars)
open scoped commutatorElement


private noncomputable abbrev k328r3p_ι {F : Type} [Field F] (b c : F) :
    GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
  (HypForm.tail 3 (Fin 2) (planeNorm b c)).rho

private theorem k328r3p_ι_isometry {F : Type} [Field F] (b c : F) (A : GL (Fin 3) F)
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    StatedQuadMinus 4 F b c ((k328r3p_ι b c A : Matrix _ _ F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
  have h := (HypForm.tail 3 (Fin 2) (planeNorm b c)).rho_isometry A v
  have hQ : ∀ w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      (HypForm.tail 3 (Fin 2) (planeNorm b c)).Q w = StatedQuadMinus 4 F b c w := by
    intro w
    rw [statedQuadMinus_eq_sum_planeNorm (n := 4)]
    simp [HypForm.Q, HypForm.tail, Matrix.fromCols_mulVec, dotProduct]
    rfl
  rw [← hQ, ← hQ]
  exact h

private noncomputable abbrev k328r3p_Y {F : Type} [Field F] (b c : F) :
    Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :=
  (StatedSL 3 F).map (k328r3p_ι b c)

private theorem k328r3p_Y_perfect {F : Type} [Field F] (b c : F) :
    ⁅k328r3p_Y b c, k328r3p_Y b c⁆ = k328r3p_Y b c := by
  rw [← Subgroup.map_commutator,
    commutator_self_of_perfect
      (StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) F).1.1]

private theorem k328r3p_Y_le {F : Type} [Field F] (b c : F) :
    k328r3p_Y b c ≤ StatedOmega (StatedQuadMinus 4 F b c) := by
  have hY : ∀ g ∈ k328r3p_Y b c, ∀ v, StatedQuadMinus 4 F b c ((g : Matrix _ _ F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
    rintro _ ⟨A, -, rfl⟩ v
    exact k328r3p_ι_isometry b c A v
  have hle : k328r3p_Y b c ≤ Subgroup.closure
      {A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F |
        ∀ v, StatedQuadMinus 4 F b c ((A : Matrix _ _ F) *ᵥ v) = StatedQuadMinus 4 F b c v} :=
    fun g hg => Subgroup.subset_closure (hY g hg)
  rw [← k328r3p_Y_perfect b c]
  exact Subgroup.commutator_mono hle hle

private noncomputable abbrev k328r3p_Qa {F : Type} [Field F] (b c : F) :
    QuadraticForm F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  CFSG.LieType.Universal.Spin.quadMinus 4 F b c

private noncomputable abbrev k328r3p_O {F : Type} [Field F] (b c : F) :
    Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :=
  (TauCeti.QuadraticMap.orthogonalGroup (k328r3p_Qa b c)).comap
    (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).toMonoidHom

private theorem k328r3p_mem_O {F : Type} [Field F] (b c : F)
    (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    g ∈ k328r3p_O b c ↔ ∀ v, StatedQuadMinus 4 F b c ((g : Matrix _ _ F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
  rw [Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact forall_congr' fun v => by
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, coe_quadMinus]

private theorem k328r3p_exists_chi {F : Type} [Field F] [Fintype F]
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ χ : k328r3p_O b c →* ℤˣ,
      (∀ g : k328r3p_O b c, (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) ∈
        StatedOmega (StatedQuadMinus 4 F b c) → χ g = 1) ∧
      ∀ v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F, k328r3p_Qa b c v ≠ 0 →
        ∀ g : k328r3p_O b c,
          toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
            reflect (k328r3p_Qa b c) v → χ g = -1 := by
  obtain ⟨hnd, hT⟩ := regular_quadMinus (n := 4) (by norm_num) hbc
  obtain ⟨-, -, -, -, -, -, -, ⟨χ, hχ1, hχ2⟩, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  refine ⟨χ.comp ((toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).toMonoidHom.subgroupComap _),
    fun g hg => ?_, fun v hv g hg => ?_⟩
  · rw [statedOmega_eq_comap (coe_quadMinus 4 F b c), Subgroup.mem_comap] at hg
    exact hχ1 _ hg
  · exact (congrArg χ (Subtype.ext hg)).trans (hχ2 v hv)

private noncomputable abbrev k328r3p_OD {F : Type} [Field F] (b c : F) :
    Subgroup (GL (Fin 2) F) :=
  (TauCeti.QuadraticMap.orthogonalGroup (minusTailForm F b c)).comap
    (toLinEquiv (Fin 2) F).toMonoidHom

private theorem k328r3p_mem_OD {F : Type} [Field F] (b c : F) (D : GL (Fin 2) F) :
    D ∈ k328r3p_OD b c ↔
      ∀ p : Fin 2 → F, planeNorm b c ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) = planeNorm b c p := by
  rw [Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact forall_congr' fun p => by
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, minusTailForm_apply, minusTailForm_apply]
    rfl

private theorem k328r3p_charTwo {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)

private theorem k328r3p_card_OD {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : Nat.card (k328r3p_OD b c) = 10 := by
  have := k328r3p_charTwo hF
  have h := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
    (Q := minusTailForm F b c) finrank_fin_two_fun
    (fun x hx hq => hx (anisotropic_minusTailForm hbc x hq))
  rw [Nat.card_eq_fintype_card (α := F), hF] at h
  have key : (TauCeti.QuadraticMap.orthogonalGroup (minusTailForm F b c)).comap
      (toLinEquiv (Fin 2) F).toMonoidHom = (TauCeti.QuadraticMap.orthogonalGroup
        (minusTailForm F b c)).map (toLinEquiv (Fin 2) F).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm (toLinEquiv (Fin 2) F) _
  unfold k328r3p_OD
  rw [key, Subgroup.card_map_of_injective (toLinEquiv (Fin 2) F).symm.injective, h]

private theorem k328r3p_plane_comm {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (φ : k328r3p_OD b c →* ℤˣ)
    (h : ∃ D, φ D = -1) {D₁ D₂ : k328r3p_OD b c} (h₁ : φ D₁ = 1) (h₂ : φ D₂ = 1) :
    D₁ * D₂ = D₂ * D₁ := by
  have hrange : φ.range = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    rcases Int.units_eq_one_or x with rfl | rfl
    · exact one_mem _
    · obtain ⟨D, hD⟩ := h
      exact ⟨D, hD⟩
  have hidx : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hk : Nat.card φ.ker = 5 := by
    have := Subgroup.card_mul_index φ.ker
    rw [hidx, k328r3p_card_OD hF b c hbc] at this
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := isCyclic_of_prime_card hk
  have hcomm := (IsCyclic.commGroup (α := φ.ker)).mul_comm ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
  exact congrArg Subtype.val hcomm

private noncomputable def k328r3p_D0 {F : Type} [Field F] (b : F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by simp)

private theorem k328r3p_D0_mulVec {F : Type} [Field F] (b : F) (p : Fin 2 → F) :
    ((k328r3p_D0 b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ p =
      ![p 0 + b * p 1, p 1] := by
  funext i
  fin_cases i <;> simp [k328r3p_D0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem k328r3p_D0_mem {F : Type} [Field F] (h2 : (2 : F) = 0) (b c : F) :
    k328r3p_D0 b ∈ k328r3p_OD b c := by
  rw [k328r3p_mem_OD]
  intro p
  rw [k328r3p_D0_mulVec]
  simp only [planeNorm, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (b * p 0 * p 1 + b ^ 2 * p 1 ^ 2) * h2

private theorem k328r3p_reflect_D0 {F : Type} [Field F] (h2 : (2 : F) = 0) (b c : F) :
    toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F (planeBlockHom 3 (k328r3p_D0 b)) =
      reflect (k328r3p_Qa b c) (planeVec 4 (![1, 0] : Fin 2 → F)) := by
  have hQ : k328r3p_Qa b c (planeVec 4 (![1, 0] : Fin 2 → F)) = 1 := by
    rw [quadMinus_planeVec' 4 b c]
    simp [planeNorm]
  have hv : k328r3p_Qa b c (planeVec 4 (![1, 0] : Fin 2 → F)) ≠ 0 := by
    rw [hQ]
    exact one_ne_zero
  refine LinearEquiv.ext fun w => ?_
  have hpol : QuadraticMap.polar (k328r3p_Qa b c) (planeVec 4 (![1, 0] : Fin 2 → F)) w =
      b * w (Sum.inr (Sum.inr 1)) := by
    rw [CFSG.LieType.Universal.Spin.polar_quadMinus]
    simp [planeVec, h2]
  rw [reflect_apply hv, toLinEquiv_apply, planeBlockHom_mulVec, hpol, hQ, div_one,
    k328r3p_D0_mulVec]
  funext i
  rcases i with i | i | i
  · simp [planeVec]
  · simp [planeVec]
  · fin_cases i
    · simp [planeVec]
      linear_combination (b * w (Sum.inr (Sum.inr 1))) * h2
    · simp [planeVec]

private theorem k328r3p_blocks_iso {F : Type} [Field F] {b c : F}
    {Mm Nm : Matrix (Fin 3) (Fin 3) F} {Pm : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ v, StatedQuadMinus 4 F b c
      ((fromBlocks Mm 0 0 (fromBlocks Nm 0 0 Pm) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
        (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ v) = StatedQuadMinus 4 F b c v) :
    Mmᵀ * Nm = 1 ∧ ∀ p : Fin 2 → F, planeNorm b c (Pm *ᵥ p) = planeNorm b c p := by
  refine ⟨?_, fun p => ?_⟩
  · refine Matrix.ext fun i j => ?_
    have := h (Sum.elim (Pi.single i 1) (Sum.elim (Pi.single j 1) 0))
    simp [statedQuadMinus_eq_sum_planeNorm (n := 4), fromBlocks_mulVec, Matrix.mul_apply,
      Matrix.one_apply, Pi.single_apply] at this ⊢
    rw [this]
    exact if_congr eq_comm rfl rfl
  · have := h (Sum.elim 0 (Sum.elim 0 p))
    simpa [statedQuadMinus_eq_sum_planeNorm (n := 4), fromBlocks_mulVec] using this

private theorem k328r3p_inv_transpose_eq {F : Type} [Field F] (M : GL (Fin 3) F)
    {N : Matrix (Fin 3) (Fin 3) F} (h : (M : Matrix (Fin 3) (Fin 3) F)ᵀ * N = 1) :
    ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = N := by
  calc ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ
      = ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *
          ((M : Matrix (Fin 3) (Fin 3) F)ᵀ * N) := by rw [h, Matrix.mul_one]
    _ = (((M : Matrix (Fin 3) (Fin 3) F) * ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
          N := by rw [← Matrix.mul_assoc, ← Matrix.transpose_mul]
    _ = N := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mul]

private theorem k328r3p_zero_of {F : Type} [Field F] {x p q : F} (h : x * p = q * x)
    (hpq : p ≠ q) : x = 0 := by
  by_contra hx
  exact hpq (mul_left_cancel₀ hx (h.trans (mul_comm q x)))

private theorem k328r3p_block_diag {F : Type} [Field F] {ω : F} (h21 : ω ^ 2 ≠ ω) (h10 : ω ≠ 1)
    (h20 : ω ^ 2 ≠ 1)
    {g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hg : g * Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])) * g) :
    g = fromBlocks (Matrix.of fun a b => g (Sum.inl a) (Sum.inl b)) 0 0
      (fromBlocks (Matrix.of fun a b => g (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))) 0 0
        (Matrix.of fun a b => g (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)))) := by
  have hd : (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]) :
      Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => 1) := by
    funext i
    rcases i with i | i | i <;> fin_cases i <;> rfl
  rw [hd] at hg
  have hent : ∀ i j, g i j * (Sum.elim (fun _ : Fin 3 => ω) (Sum.elim (fun _ : Fin 3 => ω ^ 2)
      fun _ : Fin 2 => (1 : F)) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) j =
      (Sum.elim (fun _ : Fin 3 => ω) (Sum.elim (fun _ : Fin 3 => ω ^ 2)
        fun _ : Fin 2 => (1 : F)) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) i * g i j := fun i j => by
    have := congrFun (congrFun hg i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  ext i j
  rcases i with a | a | a <;> rcases j with b | b | b
  · simp
  · simpa using k328r3p_zero_of (hent (Sum.inl a) (Sum.inr (Sum.inl b))) h21
  · simpa using k328r3p_zero_of (hent (Sum.inl a) (Sum.inr (Sum.inr b))) h10.symm
  · simpa using k328r3p_zero_of (hent (Sum.inr (Sum.inl a)) (Sum.inl b)) h21.symm
  · simp
  · simpa using k328r3p_zero_of (hent (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))) h20.symm
  · simpa using k328r3p_zero_of (hent (Sum.inr (Sum.inr a)) (Sum.inl b)) h10
  · simpa using k328r3p_zero_of (hent (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b))) h20
  · simp

private theorem k328r3p_of_blocks {F : Type} [Field F] (b c : F)
    {Mm Nm : Matrix (Fin 3) (Fin 3) F} {Pm : Matrix (Fin 2) (Fin 2) F}
    (hdet : IsUnit (fromBlocks Mm 0 0 (fromBlocks Nm 0 0 Pm) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).det)
    (hMN : Mmᵀ * Nm = 1) (hP : ∀ p : Fin 2 → F, planeNorm b c (Pm *ᵥ p) = planeNorm b c p) :
    ∃ (M : GL (Fin 3) F) (D : GL (Fin 2) F), D ∈ k328r3p_OD b c ∧
      ((k328r3p_ι b c M * planeBlockHom 3 D : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
        fromBlocks Mm 0 0 (fromBlocks Nm 0 0 Pm) := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hMu : IsUnit Mm := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have hPu : IsUnit Pm := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hdet))
  refine ⟨hMu.unit, hPu.unit, (k328r3p_mem_OD b c _).2 fun p => ?_, ?_⟩
  · rw [hPu.unit_spec]
    exact hP p
  · have hN := k328r3p_inv_transpose_eq hMu.unit (N := Nm) (by rw [hMu.unit_spec]; exact hMN)
    rw [Units.val_mul, HypForm.coe_rho, coe_tail_sigma, coe_planeBlockHom, coe_invTranspose, hN,
      hMu.unit_spec, hPu.unit_spec]
    simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]

private theorem k328r3p_decomp {F : Type} [Field F] (b c : F) {ω : F} (h21 : ω ^ 2 ≠ ω)
    (h10 : ω ≠ 1) (h20 : ω ^ 2 ≠ 1) {z₀ g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])))
    (hg : g * z₀ = z₀ * g) (hiso : g ∈ k328r3p_O b c) :
    ∃ (M : GL (Fin 3) F) (D : GL (Fin 2) F), D ∈ k328r3p_OD b c ∧
      g = k328r3p_ι b c M * planeBlockHom 3 D := by
  have hg' : (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])) *
        (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) := by
    rw [← hz, ← Units.val_mul, ← Units.val_mul, hg]
  have hblock := k328r3p_block_diag h21 h10 h20 hg'
  have hiso' := (k328r3p_mem_O b c g).1 hiso
  rw [hblock] at hiso'
  obtain ⟨hMN, hP⟩ := k328r3p_blocks_iso hiso'
  have hdet := (Matrix.isUnit_iff_isUnit_det
    (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)).1 g.isUnit
  rw [hblock] at hdet
  obtain ⟨M, D, hD, hMD⟩ := k328r3p_of_blocks b c hdet hMN hP
  exact ⟨M, D, hD, Units.ext (hblock.trans hMD.symm)⟩

private theorem k328r3p_mem_SL {F : Type} [Field F] (M : GL (Fin 3) F)
    (h : Matrix.GeneralLinearGroup.det M = 1) : M ∈ StatedSL 3 F := by
  refine Subgroup.subset_closure ?_
  have h' := congrArg (fun u : Fˣ => (u : F)) h
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using h'

private theorem k328r3p_cube_mem {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (M : GL (Fin 3) F) : M ^ 3 ∈ StatedSL 3 F := by
  refine k328r3p_mem_SL _ ?_
  have h3 : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
  have h := pow_card_eq_one' (G := Fˣ) (x := Matrix.GeneralLinearGroup.det M)
  rw [h3] at h
  rw [map_pow, h]

private theorem k328r3p_commutator_mem_SL {F : Type} [Field F] (M₁ M₂ : GL (Fin 3) F) :
    ⁅M₁, M₂⁆ ∈ StatedSL 3 F := by
  refine k328r3p_mem_SL _ ?_
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

private noncomputable def k328r3p_ιO {F : Type} [Field F] (b c : F) :
    GL (Fin 3) F →* k328r3p_O b c :=
  (k328r3p_ι b c).codRestrict (k328r3p_O b c) fun M =>
    (k328r3p_mem_O b c _).2 (k328r3p_ι_isometry b c M)

private noncomputable def k328r3p_δO {F : Type} [Field F] (b c : F) :
    k328r3p_OD b c →* k328r3p_O b c :=
  ((planeBlockHom 3 : GL (Fin 2) F →* GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).comp
    (k328r3p_OD b c).subtype).codRestrict (k328r3p_O b c) fun D =>
    (k328r3p_mem_O b c _).2 fun v =>
      planeBlockHom_isometry (n := 4) _ ((k328r3p_mem_OD b c _).1 D.2) v

private theorem k328r3p_chi_iota {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (b c : F) (χ : k328r3p_O b c →* ℤˣ)
    (hχ : ∀ g : k328r3p_O b c, (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) ∈
      StatedOmega (StatedQuadMinus 4 F b c) → χ g = 1) (M : GL (Fin 3) F) :
    χ (k328r3p_ιO b c M) = 1 := by
  have h3 : χ (k328r3p_ιO b c M) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    exact hχ _ (k328r3p_Y_le b c ⟨M ^ 3, k328r3p_cube_mem hF M, by simp [k328r3p_ιO]⟩)
  rcases Int.units_eq_one_or (χ (k328r3p_ιO b c M)) with h | h
  · exact h
  · rw [h] at h3
    exact absurd h3 (by decide)

private theorem k328r3p_commutator {F : Type} [Field F] (b c : F) (M₁ M₂ : GL (Fin 3) F)
    (D₁ D₂ : GL (Fin 2) F) (hD : D₁ * D₂ = D₂ * D₁) :
    ⁅k328r3p_ι b c M₁ * planeBlockHom 3 D₁, k328r3p_ι b c M₂ * planeBlockHom 3 D₂⁆ =
      k328r3p_ι b c ⁅M₁, M₂⁆ := by
  let Φ : GL (Fin 3) F × GL (Fin 2) F →* GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    (k328r3p_ι b c).noncommCoprod (planeBlockHom 3) fun M D =>
      planeBlockHom_commute_rho (planeNorm b c) M D
  have h1 : ∀ (M : GL (Fin 3) F) (D : GL (Fin 2) F),
      k328r3p_ι b c M * planeBlockHom 3 D = Φ (M, D) := fun M D => rfl
  have h2 : ⁅((M₁, D₁) : GL (Fin 3) F × GL (Fin 2) F), (M₂, D₂)⁆ = (⁅M₁, M₂⁆, 1) :=
    Prod.ext rfl (commutatorElement_eq_one_iff_mul_comm.2 hD)
  rw [h1, h1, ← map_commutatorElement, h2]
  show k328r3p_ι b c ⁅M₁, M₂⁆ * planeBlockHom 3 1 = _
  rw [map_one, mul_one]

private theorem k328r3p_Omega_le_O {F : Type} [Field F] (b c : F) :
    StatedOmega (StatedQuadMinus 4 F b c) ≤ k328r3p_O b c := by
  rw [statedOmega_eq_comap (coe_quadMinus 4 F b c)]
  refine Subgroup.comap_mono (Subgroup.commutator_le.2 fun x hx y hy => ?_)
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
    (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)

private theorem k328r3p_two_eq_zero {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    (2 : F) = 0 := by
  have := k328r3p_charTwo hF
  exact_mod_cast CharP.cast_eq_zero F 2

private theorem k328r3p_Q_planeVec {F : Type} [Field F] (b c : F) :
    k328r3p_Qa b c (planeVec 4 (![1, 0] : Fin 2 → F)) ≠ 0 := by
  rw [quadMinus_planeVec' 4 b c]
  simp [planeNorm]

private theorem k328r3p_comm_le {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {ω : F} (h21 : ω ^ 2 ≠ ω)
    (h10 : ω ≠ 1) (h20 : ω ^ 2 ≠ 1) {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]))) :
    stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ ≤ k328r3p_Y b c := by
  obtain ⟨χ, hχΩ, hχr⟩ := k328r3p_exists_chi b c hbc
  have h2 := k328r3p_two_eq_zero hF
  have hneg : ∃ D, (χ.comp (k328r3p_δO b c)) D = -1 :=
    ⟨⟨k328r3p_D0 b, k328r3p_D0_mem h2 b c⟩,
      hχr _ (k328r3p_Q_planeVec b c) _ (k328r3p_reflect_D0 h2 b c)⟩
  have key : ∀ g ∈ StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {z₀},
      ∃ (M : GL (Fin 3) F) (D : k328r3p_OD b c), (χ.comp (k328r3p_δO b c)) D = 1 ∧
        g = k328r3p_ι b c M * planeBlockHom 3 (D : GL (Fin 2) F) := by
    rintro g ⟨hgΩ, hgC⟩
    have hgO : g ∈ k328r3p_O b c := k328r3p_Omega_le_O b c hgΩ
    obtain ⟨M, D, hD, rfl⟩ := k328r3p_decomp b c h21 h10 h20 hz
      (Subgroup.mem_centralizer_singleton_iff.1 hgC) hgO
    refine ⟨M, ⟨D, hD⟩, ?_, rfl⟩
    have h1 : χ ⟨k328r3p_ι b c M * planeBlockHom 3 D, hgO⟩ = 1 := hχΩ _ hgΩ
    have e : (⟨k328r3p_ι b c M * planeBlockHom 3 D, hgO⟩ : k328r3p_O b c) =
        k328r3p_ιO b c M * k328r3p_δO b c ⟨D, hD⟩ := Subtype.ext rfl
    rw [e, map_mul, k328r3p_chi_iota hF b c χ hχΩ M, one_mul] at h1
    exact h1
  refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
  obtain ⟨M₁, D₁, hφ₁, rfl⟩ := key g₁ hg₁
  obtain ⟨M₂, D₂, hφ₂, rfl⟩ := key g₂ hg₂
  have hcomm := k328r3p_plane_comm hF b c hbc (χ.comp (k328r3p_δO b c)) hneg hφ₁ hφ₂
  rw [k328r3p_commutator b c M₁ M₂ D₁ D₂ (congrArg Subtype.val hcomm)]
  exact ⟨⁅M₁, M₂⁆, k328r3p_commutator_mem_SL M₁ M₂, rfl⟩

private theorem k328r3p_ι_injective {F : Type} [Field F] (b c : F) :
    Function.Injective (k328r3p_ι b c) := by
  intro M N h
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F =>
    (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl i) (Sum.inl j)) h
  simpa [HypForm.coe_rho, coe_tail_sigma] using this

private theorem k328r3p_diag_mem_Y {F : Type} [Field F] (b c : F) (d : Fin 3 → Fˣ)
    (hd : d 0 * d 1 * d 2 = 1) : diagGL (torusEntMinus 3 F d) ∈ k328r3p_Y b c := by
  refine ⟨diagGL d, Subgroup.subset_closure ?_, rho_diagGL (planeNorm b c) d⟩
  show ((diagGL d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
  rw [coe_diagGL, Matrix.det_diagonal, Fin.prod_univ_three]
  simpa using congrArg Units.val hd

private theorem k328r3p_z_eq {F : Type} [Field F] {ω : F} (hω0 : ω ≠ 0) (h3 : ω ^ 3 = 1)
    {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]))) :
    z₀ = diagGL (torusEntMinus 3 F fun _ => Units.mk0 ω hω0) := by
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h3)
  apply Units.ext
  rw [hz, coe_diagGL]
  congr 1
  funext i
  rcases i with i | i | i <;> fin_cases i <;> simp [torusEntMinus, hinv]

private theorem k328r3p_pow_three {F : Type} [Field F] (d : Fin 3 → Fˣ) (h : ∀ i, d i ^ 3 = 1) :
    (diagGL (torusEntMinus 3 F d) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) ^ 3 = 1 := by
  rw [← map_pow, ← map_one (diagGL (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2) (K := F))]
  congr 1
  funext j
  rcases j with i | i | i <;> simp [torusEntMinus, inv_pow, h]

private theorem k328r3p_orderOf_three {F : Type} [Field F] {ω : F} (hω1 : ω ≠ 1)
    {g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F} (h3 : g ^ 3 = 1)
    (h : (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0) =
      ω) :
    orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime h3 fun h1 => hω1 ?_
  rw [h1] at h
  simpa using h.symm

private theorem k328r3p_Y_le_stdComp {F : Type} [Field F] (b c : F) {ω : F} (hω0 : ω ≠ 0)
    {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : z₀ = diagGL (torusEntMinus 3 F fun _ => Units.mk0 ω hω0)) :
    k328r3p_Y b c ≤ stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  have hzι : z₀ = k328r3p_ι b c (diagGL fun _ : Fin 3 => Units.mk0 ω hω0) :=
    hz.trans (rho_diagGL (planeNorm b c) _).symm
  have hYC : k328r3p_Y b c ≤
      StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {z₀} := by
    refine le_inf (k328r3p_Y_le b c) ?_
    rintro _ ⟨A, -, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzι, ← map_mul, ← map_mul]
    congr 1
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagGL]
    show (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal (fun _ => ω) =
      Matrix.diagonal (fun _ => ω) * (A : Matrix (Fin 3) (Fin 3) F)
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  have h := Subgroup.commutator_mono hYC hYC
  rwa [k328r3p_Y_perfect] at h

private theorem k328r3p_omega_facts {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (ω : F) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ ω ∧ ω ^ 2 ≠ 1 ∧ ω ^ 3 = 1 := by
  have h2 := k328r3p_two_eq_zero hF
  have hω0 : ω ≠ 0 := fun h => by
    rw [h] at hω
    exact one_ne_zero (by linear_combination hω)
  refine ⟨hω0, fun h => ?_, fun h => ?_, fun h => ?_, by linear_combination (ω - 1) * hω⟩
  · rw [h] at hω
    exact one_ne_zero (by linear_combination hω - h2)
  · exact one_ne_zero (by linear_combination hω - h - ω * h2)
  · exact hω0 (by linear_combination hω - h - h2)

private theorem k328r3p_stdComp_eq {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]))) :
    stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ = k328r3p_Y b c := by
  obtain ⟨hω0, h10, h21, h20, hω3⟩ := k328r3p_omega_facts hF ω hω
  exact le_antisymm (k328r3p_comm_le hF b c hbc h21 h10 h20 hz)
    (k328r3p_Y_le_stdComp b c hω0 (k328r3p_z_eq hω0 hω3 hz))

private theorem k328r3p_model {G : Type} [Group G] {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {S : Subgroup G} (e : S ≃* StatedSL 3 F) :
    CFSG.Open.IsQuasisimple ↥S ∧ Nat.card (Subgroup.center ↥S) = 3 ∧
      LieModel (↥S ⧸ Subgroup.center ↥S) .PSL 3 2 2 := by
  have hq := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) F
  have hcenter : (Subgroup.center ↥S).map (e : ↥S →* ↥(StatedSL 3 F)) =
      (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) :=
    (Subgroup.map_center_eq e).trans
      ((Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 3 F)).symm.trans
        (map_center_eq_statedScalars 3 F))
  have hadm : StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hlie : LieModel (↥S ⧸ Subgroup.center ↥S) .PSL 3 2 2 :=
    Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance,
      by rw [Nat.card_eq_fintype_card, hF]; norm_num,
      ⟨QuotientGroup.congr _ _ e hcenter⟩⟩
  have hcardS : Nat.card ↥S = 60480 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three,
      Nat.card_eq_fintype_card (α := F), hF]
    norm_num
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥S)
  rw [hcardS, hlie.card_psl_three_four] at hmul
  exact ⟨isQuasisimple_of_mulEquiv' e.symm ⟨hq.1.1, hq.2.1⟩, by omega, hlie⟩

private theorem k328r3p_subgroupOf_eq {M : Type} [Group M] {H : Subgroup M} {z₀ : M}
    (hz₀ : z₀ ∈ H) :
    (stdComp H z₀).subgroupOf H =
      ⁅Subgroup.centralizer {(⟨z₀, hz₀⟩ : H)}, Subgroup.centralizer {(⟨z₀, hz₀⟩ : H)}⁆ := by
  have hC : (Subgroup.centralizer {(⟨z₀, hz₀⟩ : H)}).map H.subtype =
      H ⊓ Subgroup.centralizer {z₀} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    · rintro ⟨hyH, hyc⟩
      exact ⟨⟨y, hyH⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyc)), rfl⟩
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, hC, Subgroup.map_subgroupOf_eq_of_le (stdComp_le H z₀), stdComp]

private theorem k328r3p_subnormal {M : Type} [Group M] (C : Subgroup M) :
    ((⁅C, C⁆ : Subgroup M).subgroupOf C).IsSubnormal := by
  have h : (⁅C, C⁆ : Subgroup M).subgroupOf C = _root_.commutator ↥C := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [h]
  exact Subgroup.Normal.isSubnormal inferInstance

private theorem k328r3p_pos_of {M : Type} [Group M] [Finite M] {H : Subgroup M} {z₀ : M}
    (hz₀ : z₀ ∈ H) (hord : orderOf z₀ = 3) (hzX : z₀ ∈ stdComp H z₀)
    (hqs : CFSG.Open.IsQuasisimple ↥(stdComp H z₀))
    (hcen : Nat.card (Subgroup.center ↥(stdComp H z₀)) = 3)
    (hlie : LieModel (↥(stdComp H z₀) ⧸ Subgroup.center ↥(stdComp H z₀)) .PSL 3 2 2) :
    Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) ((stdComp H z₀).subgroupOf H) := by
  let eX : ↥((stdComp H z₀).subgroupOf H) ≃* ↥(stdComp H z₀) :=
    Subgroup.subgroupOfEquivOfLe (stdComp_le H z₀)
  refine ⟨?_, Subgroup.zpowers_le.2 hzX, ?_, ?_, isQuasisimple_of_mulEquiv' eX.symm hqs, ?_,
    Or.inl (LieModel.of_mulEquiv (QuotientGroup.congr (Subgroup.center ↥(stdComp H z₀))
      (Subgroup.center ↥((stdComp H z₀).subgroupOf H)) eX.symm
      (Subgroup.map_center_eq eX.symm)) hlie)⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hord
  · rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, k328r3p_subgroupOf_eq hz₀]
    exact Subgroup.commutator_le_self _
  · rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, k328r3p_subgroupOf_eq hz₀]
    exact k328r3p_subnormal _
  · rw [← hcen]
    exact Nat.card_congr (Subgroup.centerCongr eX).toEquiv

theorem row3_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])))
    (ht : (t₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))) :
    PosLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  have _ := ht
  intro hz₀
  obtain ⟨hω0, h10, -, -, hω3⟩ := k328r3p_omega_facts hF ω hω
  have hzE := k328r3p_z_eq hω0 hω3 hz
  have hS := k328r3p_stdComp_eq hF b c hbc hω hz
  have hz3 : z₀ ^ 3 = 1 := by
    rw [hzE]
    exact k328r3p_pow_three _ fun i => Units.ext (by simpa using hω3)
  have hzY : z₀ ∈ k328r3p_Y b c := by
    rw [hzE]
    exact k328r3p_diag_mem_Y b c _ (Units.ext (by simpa [pow_succ] using hω3))
  let e : stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ ≃* StatedSL 3 F :=
    (MulEquiv.subgroupCongr hS).trans
      ((StatedSL 3 F).equivMapOfInjective (k328r3p_ι b c) (k328r3p_ι_injective b c)).symm
  obtain ⟨hqs, hcen, hlie⟩ := k328r3p_model hF e
  exact k328r3p_pos_of hz₀ (k328r3p_orderOf_three h10 hz3 (by simp [hz])) (hS ▸ hzY) hqs hcen hlie

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
