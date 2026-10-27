module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.ClassicalGroups.Orthogonal.RingEquivDerived
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public section

namespace CFSG.StandardType

open Module QuadraticMap CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
open CFSG.RankThree.Classical2 (orthDerived)

theorem exists_ggU_POmegaMinus_of_injective_quadMinus {G : Type} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {m f : ℕ} (hm : 4 ≤ m) (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f) {Φ : orthDerived (quadMinus m F b c) →* G}
    (hΦ : Function.Injective Φ) :
    ∃ ψ : (ggU .POmegaMinus m f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .POmegaMinus m f).K ∧ ψ.range = Φ.range := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F
  let K := GaloisField 2 f
  let e : K ≃+* F :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f hf hF).symm
  let : Module K V := Module.compHom V e.toRingHom
  have hsmul : ∀ (a : K) (v : V), a • v = e a • v := fun _ _ => rfl
  let : Finite V := Module.finite_of_finite F
  let : FiniteDimensional K V := Module.Finite.of_finite
  let Q₀ := formOfRingEquiv e hsmul (quadMinus m F b c)
  have hQ₀ : (polarBilin Q₀).Nondegenerate :=
    nondegenerate_formOfRingEquiv (nondegenerate_polarBilin_quadMinus_of_finite m F hirr)
  have hdimF : finrank F V = 2 * m := by
    dsimp [V]
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdim : finrank K V = 2 * m := (finrank_eq_of_finiteFields_ringEquiv e).trans hdimF
  have hminus : ¬ IsPlusType Q₀ := fun h =>
    not_isPlusType_quadMinus (by omega) hirr ((isPlusType_formOfRingEquiv e hsmul _).mp h)
  have hirr0 := minusCoeffs_irr 2 f
  obtain ⟨iso⟩ := nonempty_isometry_of_not_isPlusType hQ₀ (by omega) hdim hminus hirr0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let N : spinGroup (quadMinus m K (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) ≃*
      orthDerived (quadMinus m F b c) :=
    (commutatorEquivSpinMinusOfIsometry iso hm hirr0 h2).symm.trans
      (derivedFieldEquiv e hsmul (quadMinus m F b c))
  have hU : ggU .POmegaMinus m f =
      ⟨spinGroup (quadMinus m K (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        Twisted.minusDatum m hirr0⟩ := rfl
  rw [hU]
  refine ⟨Φ.comp N.toMonoidHom, ?_, ?_⟩
  · have hker : (Φ.comp N.toMonoidHom).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (hΦ.comp N.injective)
    rw [hker]
    exact bot_le
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr N.surjective, Subgroup.map_top]

theorem ggSecFiveData_of_injective_quadMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {m f : ℕ} (hm : 4 ≤ m) (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f) {Φ : orthDerived (quadMinus m F b c) →* G}
    (hΦ : Function.Injective Φ) (hrange : Φ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J := by
  obtain ⟨ψ, hker, hψ⟩ := exists_ggU_POmegaMinus_of_injective_quadMinus hirr hm hf hF hΦ
  exact ggSecFiveData_of_psi_POmegaMinus ⟨Nat.prime_two, hf, hm⟩
    (by rw [bnRank]; omega) ψ hker (hψ.trans hrange)

end CFSG.StandardType

end
