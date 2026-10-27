module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.ClassicalGroups.Orthogonal.RingEquivDerived
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.StandardType

open Module QuadraticMap CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
  CFSG.GroupTheory.WeirSylow

theorem exists_ggU_POmegaPlus_of_injective_normOmega_of_card {G : Type} [Group G] {f m : ℕ}
    (hm : 2 ≤ m) (hmo : Odd m) (hf : 0 < f) {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] (hF : Nat.card F = 2 ^ f)
    {E : QuadExt F K (unitaryInvolution K 2 f)} {Ψ : normOmega E (m + 1) →* G}
    (hΨ : Function.Injective Ψ) :
    ∃ ψ : (ggU .POmegaPlus (m + 1 + 1) f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (m + 1 + 1) f).K ∧ ψ.range = Ψ.range := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  let V := (F × F) × (Fin (m + 1) → K)
  let e : GaloisField 2 f ≃+* F :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f hf hF).symm
  let : Module (GaloisField 2 f) V := Module.compHom V e.toRingHom
  have hsmul : ∀ (a : GaloisField 2 f) (v : V), a • v = e a • v := fun _ _ => rfl
  let : FiniteDimensional (GaloisField 2 f) V := Module.Finite.of_finite
  let Q₀ := formOfRingEquiv e hsmul (normHypForm E (m + 1))
  have hQ₀ : (polarBilin Q₀).Nondegenerate :=
    nondegenerate_formOfRingEquiv (normHypForm_polarBilin_nondegenerate E (m + 1))
  have hdim : finrank (GaloisField 2 f) V = 2 * (m + 1 + 1) :=
    (finrank_eq_of_finiteFields_ringEquiv e).trans (finrank_normHypForm E (m + 1))
  have hplus : IsPlusType Q₀ := (isPlusType_formOfRingEquiv e hsmul _).mpr
    ((isPlusType_normHypForm_iff E (m + 1)).mpr hmo.add_one)
  obtain ⟨iso⟩ := nonempty_isometry_quadPlus hQ₀ hdim hplus
  have h2 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
  let N : spinGroup (quadPlus (m + 1 + 1) (GaloisField 2 f)) ≃* normOmega E (m + 1) :=
    (commutatorEquivSpinPlusOfIsometry iso (by omega) h2).symm.trans
      (derivedFieldEquiv e hsmul (normHypForm E (m + 1)))
  have hU : ggU .POmegaPlus (m + 1 + 1) f =
      ⟨spinGroup (quadPlus (m + 1 + 1) (GaloisField 2 f)),
        plusDatum (m + 1 + 1) (GaloisField 2 f) (by omega)⟩ := by
    simp only [ggU, lieUniversal, show 3 ≤ m + 1 + 1 by omega, ↓reduceDIte]
  rw [hU]
  refine ⟨Ψ.comp N.toMonoidHom, ?_, ?_⟩
  · have hker : (Ψ.comp N.toMonoidHom).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (hΨ.comp N.injective)
    rw [hker]
    exact bot_le
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr N.surjective, Subgroup.map_top]

theorem ggSecFiveData_POmegaPlus_of_injective_normOmega_of_card {G : Type} [Group G] [Finite G]
    {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} {f m : ℕ} (hm : 2 ≤ m) (hmo : Odd m)
    (hf : 0 < f) {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (hF : Nat.card F = 2 ^ f) {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Ψ : normOmega E (m + 1) →* G} (hΨ : Function.Injective Ψ)
    (hrange : Ψ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J := by
  obtain ⟨ψ, hker, hψ⟩ := exists_ggU_POmegaPlus_of_injective_normOmega_of_card hm hmo hf hF hΨ
  exact ggSecFiveData_of_psi_POmegaPlus ⟨Nat.prime_two, hf, by omega⟩
    (by rw [bnRank]; omega) ψ hker (hψ.trans hrange)

end CFSG.StandardType

end
