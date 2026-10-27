module

public import CFSG.RankThree.GroupTheory.SteinbergBYAutCentralizerTheta
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusRootPair
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory.SteinbergBY EvenF4QPlus

namespace EvenF4Actors

theorem transport_derived {G₀ M : Type*} [Group G₀] [Group M] {ι : G₀ →* M} {ψ : M →* M}
    (hι : Function.Injective ι) (hψ : Function.Injective ψ) {X : Subgroup G₀} {D : Subgroup M}
    (hXD : X.map ι = D.map ψ) :
    ⁅X, X⁆.map ι = ⁅D, D⁆.map ψ ∧
    (CFSG.IsQuasisimple (⁅D, D⁆ : Subgroup M) → CFSG.IsQuasisimple (⁅X, X⁆ : Subgroup G₀) ∧
      CFSG.layer (⁅X, X⁆ : Subgroup G₀) = ⊤) ∧
    (D ⊓ Subgroup.centralizer ((⁅D, D⁆ : Subgroup M) : Set M) =
        (Subgroup.center D).map D.subtype →
      X ⊓ Subgroup.centralizer ((⁅X, X⁆ : Subgroup G₀) : Set G₀) =
        (Subgroup.center X).map X.subtype) ∧
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center D) := by
  have hR : ⁅X, X⁆.map ι = ⁅D, D⁆.map ψ := by
    rw [Subgroup.map_commutator, hXD, ← Subgroup.map_commutator]
  have eR : (⁅X, X⁆ : Subgroup G₀) ≃* (⁅D, D⁆ : Subgroup M) :=
    ((Subgroup.equivMapOfInjective _ ι hι).trans (MulEquiv.subgroupCongr hR)).trans
      (Subgroup.equivMapOfInjective _ ψ hψ).symm
  have eX : X ≃* D :=
    ((Subgroup.equivMapOfInjective _ ι hι).trans (MulEquiv.subgroupCongr hXD)).trans
      (Subgroup.equivMapOfInjective D ψ hψ).symm
  refine ⟨hR, fun hq => ?_, fun hc => ?_, Nat.card_congr (Subgroup.centerCongr eX).toEquiv⟩
  · have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hq
    exact ⟨hq', CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hq'⟩
  · apply Subgroup.map_injective hι
    rw [map_inf_centralizer_of_injective hι, hXD, ← Subgroup.coe_map, hR,
      map_map_center_subtype_of_injective hι, hXD, ← map_map_center_subtype_of_injective hψ,
      ← hc, map_inf_centralizer_of_injective hψ, Subgroup.coe_map]

theorem exists_intermediateField_finrank (K : Type) [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    [CharP K r] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (d : ℕ) [NeZero d] :
    ∃ L : IntermediateField K Ω, Module.finrank K L = d := by
  let e : FiniteField.Extension K r d →ₐ[K] Ω := IsAlgClosed.lift
  refine ⟨e.fieldRange, ?_⟩
  rw [← e.equivFieldRange.toLinearEquiv.finrank_eq]
  exact FiniteField.finrank_extension K r d

end EvenF4Actors

end CFSG.RankThree.Chevalley
