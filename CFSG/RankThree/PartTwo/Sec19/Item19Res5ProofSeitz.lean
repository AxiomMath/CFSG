module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSeitzField
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

@[expose] def Seitz199OuterUnitary : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup (MulAut X)),
    (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 → CFSG.IsQuasisimple X →
    (∃ (q : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 q K)) →
    ¬ D ≤ (MulAut.conj : X →* MulAut X).range →
    (∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) →
    Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x = x} = ⊤

namespace Item19Res5Proof

theorem le_range_conj_of_mapAut {X S : Type*} [Group X] [Group S] (ψ : X ≃* S)
    {D : Subgroup (MulAut X)} (h : mapAut ψ D ≤ (MulAut.conj : S →* MulAut S).range) :
    D ≤ (MulAut.conj : X →* MulAut X).range := by
  intro φ hφ
  obtain ⟨y, hy⟩ := h ⟨φ, hφ, rfl⟩
  refine ⟨ψ.symm y, ?_⟩
  have h1 := congr_conj ψ.symm y
  have h2 : MulAut.conj y = MulAut.congr ψ φ := hy
  rw [h2, congr_symm_congr] at h1
  exact h1.symm

theorem exists_moved_mapAut {X S : Type*} [Group X] [Group S] (ψ : X ≃* S)
    {D : Subgroup (MulAut X)} (h : ∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) :
    ∃ e ∈ mapAut ψ D, ∃ s : S, s ^ 3 = 1 ∧ MulAut.conj s ∈ mapAut ψ D ∧ e s ≠ s := by
  obtain ⟨e, he, s, hs3, hsD, hes⟩ := h
  refine ⟨MulAut.congr ψ e, ⟨e, he, rfl⟩, ψ s, by rw [← map_pow, hs3, map_one], ?_, ?_⟩
  · rw [← congr_conj]
    exact ⟨_, hsD, rfl⟩
  · intro h'
    apply hes
    apply ψ.injective
    rw [congr_apply', MulEquiv.symm_apply_apply] at h'
    exact h'

theorem mem_center_map {X S : Type*} [Group X] [Group S] (ψ : X ≃* S) {x : X}
    (hx : x ∈ Subgroup.center X) : ψ x ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  obtain ⟨y', rfl⟩ := ψ.surjective y
  rw [← map_mul, ← map_mul, hx]

theorem isConjBy_conj_zpow {k : Type} [Field k] (s : Matrix.SpecialLinearGroup (Fin 3) k)
    (n : ℤ) : ∃ g : GL (Fin 3) k, IsConjBy (MulAut.conj s ^ n) g := by
  rw [← map_zpow]
  exact ⟨_, isConjBy_conj _⟩

theorem apply_eq_self_of_conj_eq_one {k : Type} [Field k] [Finite k]
    {β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} (hβ3 : β ^ 3 = 1)
    {s : Matrix.SpecialLinearGroup (Fin 3) k} (hs : MulAut.conj s = 1) : β s = s := by
  have hcomm : ∀ t : Matrix.SpecialLinearGroup (Fin 3) k,
      ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        (t : Matrix (Fin 3) (Fin 3) k) = (t : Matrix (Fin 3) (Fin 3) k) *
          ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    intro t
    have ht : MulAut.conj s t = t := by rw [hs]; rfl
    rw [MulAut.conj_apply] at ht
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [ht]
  obtain ⟨c, hc⟩ := eq_scalar_of_forall_commute _ hcomm
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hc
  have hc3 : (c : k) ^ 3 = 1 := by
    have h1 := s.det_coe
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  apply Subtype.ext
  rcases exists_isConjBy_or_semiBy β hβ3 with ⟨g, hg⟩ | ⟨σ, g, hσ, hg⟩
  · rw [hg s, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]
  · have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have h1 := congrArg (fun x : GL (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k)) (hg s)
    simp only [Units.val_mul, coe_map_ringEquiv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      at h1
    rw [h1, hc]
    have h2 : ((c : k) • (1 : Matrix (Fin 3) (Fin 3) k)).map σ = (c : k) • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      split_ifs
      · exact ringEquiv_apply_eq_of_pow_three hσ3 hc3
      · simp
    rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

end Item19Res5Proof

end CFSG.RankThree.PartTwo.Sec19
