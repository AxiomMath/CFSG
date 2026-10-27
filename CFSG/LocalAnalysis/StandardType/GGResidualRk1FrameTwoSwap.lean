module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
import CFSG.LocalAnalysis.StandardType.GGOrthRk1FieldTwo
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Iso
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Theta
import CFSG.LocalAnalysis.StandardType.GGOrthFrameConcl
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

open Module Multiplicative

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open SpCoord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem TBJOmData.exists_theta_rankOne_of_card_two {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ}
    (Δ : TBJOmData Q p A r) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (hK : Nat.card K = 2) {i j : Fin r} (hij : i ≠ j) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
      Function.Injective θ ∧ θ.range = Δ.rankOne i j := by
  classical
  obtain ⟨φ, hφinj, hφrange, hφQ, hφτ⟩ := Δ.exists_rk1_isometry hp2 hAΩ i j hij
  obtain ⟨θ, -, -, hθinj, -, -, hθuniq⟩ :=
    Δ.exists_rk1_theta hfix i j hij φ hφinj hφrange hφQ hφτ
  have hle : Δ.rankOne i j ≤ θ.range :=
    Δ.rankOne_le_range hp2 hfix i j φ hφinj hφrange hφQ hφτ θ hθuniq
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
    have : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rwa [Nat.card_eq_fintype_card] at hK
    rw [Matrix.card_SL_field (𝔽 := K) 2, hK', Fin.prod_univ_two]
    norm_num
  have hrange : Nat.card ↥θ.range = 6 :=
    (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm.trans hSL
  have hcard : Nat.card ↥(Δ.rankOne i j) = 6 :=
    Δ.card_rankOne_of_card_two hp2 hAΩ hfix hK hij
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  refine ⟨θ, hθinj, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hrange])).symm

section Proofs


theorem OrthFrameCore.rk1Ex_of_swapElt_two (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hK : Nat.card Φ.F = 2)
    (hlab : GGHasLabel ⟨.D, Φ.r, 1⟩ (↥X ⧸ Subgroup.center ↥X) ∨
      GGHasLabel ⟨.twD, Φ.r, 1⟩ (↥X ⧸ Subgroup.center ↥X))
    (hXns : ¬ GGSplitLie p X) {i j : Fin Φ.r} (hij : i ≠ j) {w : ↥(orthDerived Φ.Q)}
    (hw : ∀ f : Fin Φ.r → Multiplicative (ZMod p), (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (SpCoord.permAut (Equiv.swap i j) f))
    {a : MulAut ↥Bs} (haA : a ∈ ggAutomizer X Bs) (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) :
    GGIsReflection p a ∧ GGRk1ConclEx p Bs X a := by
  haveI := Φ.finite_linearEquiv
  have haR : GGIsReflection p a :=
    isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj (Fact.out : p.Prime).one_lt ha
      (fun t ht => Φ.Δ.swap_sq_comm hw t ht) (fun t => Φ.Δ.mem_reflFixed_iff hw t) (Φ.Δ.card_reflFixed hij)
  have haS : ggRankOneIn X Bs a = ((Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
    have h := ggRankOneIn_eq_map_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj ha
      (fun t => Φ.Δ.mem_reflFixed_iff hw t)
    rw [Φ.hrange] at h
    exact h
  obtain ⟨θm, hθinj, hθrange⟩ := Φ.Δ.exists_theta_rankOne_of_card_two hp2 Φ.hA Φ.hfix hK hij
  have hθΩ : ∀ x, θm x ∈ orthDerived Φ.Q := by
    intro x
    have hx : θm x ∈ θm.range := ⟨x, rfl⟩
    rw [hθrange] at hx
    exact (ggOTwoPrime_le _ hx).2
  let θΩ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* ↥(orthDerived Φ.Q) :=
    θm.codRestrict (orthDerived Φ.Q) hθΩ
  let θ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* G := Φ.ψ.comp θΩ
  have hθΩinj : Function.Injective θΩ := fun x y h => hθinj (congrArg Subtype.val h)
  have hΩrange : θΩ.range = (Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q) := by
    ext y
    rw [Subgroup.mem_subgroupOf, ← hθrange]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hrange : θ.range = ggRankOneIn X Bs a := by
    rw [haS]
    change (Φ.ψ.comp θΩ).range = _
    rw [MonoidHom.range_comp, hΩrange]
  refine ⟨haR, Φ.F, inferInstance, inferInstance, θ, inferInstance, ?_, hrange, ?_, ?_, ?_, ?_, ?_⟩
  · exact Φ.hinj.comp hθΩinj
  · have hr2 : a * a = 1 := by simpa [pow_two] using haR.1
    exact ggExists_weylElt_of_mem_ggAutomizer haA hr2
  · intro hs
    exact absurd hs hXns
  · intro _
    exact Φ.hpq
  · intro lab' hlam' hl'
    have hnn : lab'.n = 1 := by
      rcases hlab with hl | hl
      · exact ggLabel_n_eq_of_D hRig Φ.hr (le_refl 1) hl hlam' hl'
      · exact ggLabel_n_eq_of_twD hRig Φ.hr (le_refl 1) hl hlam' hl'
    rw [hnn, hK]
    norm_num
  · rcases hlab with hl | hl
    · exact ⟨⟨.D, Φ.r, 1⟩, ⟨le_refl 1, show 3 ≤ Φ.r by have := Φ.hr; omega⟩, hl,
        by rw [hK]; norm_num⟩
    · exact ⟨⟨.twD, Φ.r, 1⟩, ⟨le_refl 1, show 2 ≤ Φ.r by have := Φ.hr; omega⟩, hl,
        by rw [hK]; norm_num⟩

end Proofs

end OrthTorus

end CFSG.StandardType

end
