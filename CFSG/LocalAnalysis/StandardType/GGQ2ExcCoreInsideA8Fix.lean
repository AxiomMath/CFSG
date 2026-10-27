module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASuConj
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups commutatorElement


variable {τ : Tag}

section Kernel

variable {L : Type} [Field L]

theorem ker_le_center_of_isSLFrame {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) :
    ψ.ker ≤ Subgroup.center SL(ν, L) := by
  have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
  refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hν)
    ⟨Matrix.SpecialLinearGroup.transvection h01 1, fun h => ?_⟩
  rw [hε, mul_one] at h
  exact Units.ne_zero ε (pinnedX_injective τ L _ (h.trans (pinnedX_zero τ L _).symm))

end Kernel

section Lift

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}

theorem commutator_le_map_eqLocus_of_frame {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : Ψ ⊆ frameRoots σ) (hker : ψ.ker ≤ Subgroup.center SL(ν, L))
    (F' : SL(ν, L) →* SL(ν, L)) (hcomm : ∀ X, S.D.step (ψ X) = ψ (F' X)) :
    ⁅rootSpan τ L Ψ ⊓ S.Γ, rootSpan τ L Ψ ⊓ S.Γ⁆ ≤ (F'.eqLocus (MonoidHom.id _)).map ψ := by
  have hΓ : S.Γ ≤ S.D.model := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hlift : ∀ g ∈ rootSpan τ L Ψ ⊓ S.Γ,
      ∃ X z, ψ X = g ∧ z ∈ Subgroup.center SL(ν, L) ∧ F' X = z * X := by
    intro g hg
    have hg' : g ∈ ψ.range := by
      rw [hψ.range]
      exact rootSpan_mono hΨ (Subgroup.mem_inf.1 hg).1
    obtain ⟨X, rfl⟩ := MonoidHom.mem_range.1 hg'
    have hfix : S.D.step (ψ X) = ψ X := (S.D.mem_model.1 (hΓ (Subgroup.mem_inf.1 hg).2)).2
    refine ⟨X, F' X * X⁻¹, rfl, hker ?_, (inv_mul_cancel_right _ _).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hcomm, hfix, mul_inv_cancel]
  have hcl : ∀ {a b c : SL(ν, L)}, c ∈ Subgroup.center SL(ν, L) → ⁅c * a, b⁆ = ⁅a, b⁆ := by
    intro a b c hc
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
      show c * a * b * (a⁻¹ * c⁻¹) * b⁻¹ = c * (a * b * a⁻¹) * c⁻¹ * b⁻¹ by group,
      ← Subgroup.mem_center_iff.mp hc (a * b * a⁻¹), mul_inv_cancel_right]
  refine Subgroup.commutator_le.2 fun g hg h hh => ?_
  obtain ⟨X, z, rfl, hz, hXz⟩ := hlift g hg
  obtain ⟨Y, w, rfl, hw, hYw⟩ := hlift h hh
  refine Subgroup.mem_map.2 ⟨⁅X, Y⁆, ?_, map_commutatorElement ψ X Y⟩
  show F' ⁅X, Y⁆ = ⁅X, Y⁆
  rw [map_commutatorElement, hXz, hYw, hcl hz, ← commutatorElement_inv, hcl hw,
    commutatorElement_inv]

theorem exists_unitaryLift_of_frame (hS : NegLangTwo S) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) :
    ∃ F' : SL(ν, L) →* SL(ν, L), (∀ X, S.D.step (ψ X) = ψ (F' X)) ∧
      ∀ (μ : L) (X : SL(ν, L)), (X : Matrix (Fin ν) (Fin ν) L) = Matrix.scalar (Fin ν) μ →
        (F' X : Matrix (Fin ν) (Fin ν) L) = Matrix.scalar (Fin ν) (μ ^ 2)⁻¹ := by
  obtain ⟨hq, -, hρ⟩ := hS
  have : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq, pow_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) 2 1
  have hσc : ∀ c, σQ c = c ^ 2 := fun c => by
    rw [show σQ c = iterateFrobenius L 2 1 c by rw [← hσQ]; rfl, iterateFrobenius_def, pow_one]
  obtain ⟨B, hB⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_exists_pin S
    (s := 1) hν hψ (Equiv.refl _)
    (fun a b hab => by
      rw [Function.iterate_one, hρ _ (hψ.isRoot a b hab)]
      exact (hψ.neg a b).symm)
    (r := 2) (e := 1) (by rw [hq, pow_one]) (fun c => by rw [hσc]; norm_num)
  refine ⟨(MulAut.conj B⁻¹).toMonoidHom.comp (stdUnitary σQ.toRingHom), fun X => ?_,
    fun μ X hX => ?_⟩
  · have h : ψ B * S.D.step (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
      simpa [iterHom_eq_iterate] using hB X
    calc S.D.step (ψ X) = (ψ B)⁻¹ * (ψ B * S.D.step (ψ X) * (ψ B)⁻¹) * ψ B := by group
      _ = ψ (B⁻¹ * stdUnitary σQ.toRingHom X * B⁻¹⁻¹) := by
        rw [h, inv_inv, map_mul, map_mul, map_inv]
      _ = _ := rfl
  · have hμ : μ ≠ 0 := by
      rintro rfl
      have : Nonempty (Fin ν) := ⟨⟨0, by omega⟩⟩
      have h1 := Matrix.SpecialLinearGroup.det_coe X
      rw [hX, map_zero, Matrix.det_zero] at h1
      exact zero_ne_one h1
    have hinv : (Matrix.scalar (Fin ν) (μ ^ 2))⁻¹ = Matrix.scalar (Fin ν) (μ ^ 2)⁻¹ :=
      Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero 2 hμ), map_one])
    have hU : (stdUnitary σQ.toRingHom X : Matrix (Fin ν) (Fin ν) L) =
        Matrix.scalar (Fin ν) (μ ^ 2)⁻¹ := by
      rw [coe_stdUnitary, hX, CFSG.RankThree.Classical2.scalar_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, hσc, hinv, Matrix.scalar_apply, Matrix.diagonal_transpose]
    exact CFSG.RankThree.Classical2.coe_conj_eq_scalar B⁻¹ _ hU

end Lift

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
