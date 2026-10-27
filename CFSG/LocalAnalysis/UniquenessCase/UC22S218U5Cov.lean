module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import Certificates.Certificate117
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S1414Defs
import CFSG.Quasithin.EmptyFaithful.S1417Sylow
import CFSG.Quasithin.EmptyFaithful.S141Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Steinberg.CentralExt.SUOdd

theorem uc22s218_u5_exists_cover
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    {n : ℕ} (hX : IsU5 (X ⧸ Subgroup.center X) n) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 n K) (α : hypSU h 2 1 →* X),
      Function.Surjective α ∧ ∀ s, α s ∈ Subgroup.center X ↔ s ∈ hypScalars h 2 1 := by
  obtain ⟨K, hK, h, ⟨e⟩⟩ := uc22s218_u5_exists_model hX
  have := h.finite
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  have hF : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq5 : ((5 : ℕ), 2 ^ n) ≠ (3, 2) := fun h' => absurd (Prod.mk.inj h').1 (by norm_num)
  let ψ : hypSU h 2 1 ≃* StatedSU 5 (2 ^ n) K := hypTransport h hR
  have hclosed : ∀ (E : Type) [Group E] [Finite E] (π : E →* hypSU h 2 1),
      Function.Surjective π → π.ker ≤ center E →
        ∃ s : hypSU h 2 1 →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hc
    have hker : (ψ.toMonoidHom.comp π).ker ≤ center E := by
      refine le_trans (fun x hx => ?_) hc
      rw [MonoidHom.mem_ker] at hx ⊢
      exact (map_eq_one_iff _ ψ.injective).1 hx
    obtain ⟨s, hs⟩ := statedSU_odd_exists_section_of_central (p := 2) (f := n) hF h.one_le
      (n := 5) (by norm_num) (by decide) hq5 (π := ψ.toMonoidHom.comp π)
      (ψ.surjective.comp hπ) hker
    refine ⟨s.comp ψ.toMonoidHom, fun g => ?_⟩
    apply ψ.injective
    simpa using hs (ψ g)
  have hperf : commutator (hypSU h 2 1) = ⊤ := by
    have := isPerfect_statedSU_odd (p := 2) (f := n) hF (n := 5) (by norm_num) hq5
    have : Group.IsPerfect (hypSU h 2 1) :=
      Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  let ρ : hypSU h 2 1 →* X ⧸ center X := e.toMonoidHom.comp (hypProj h 2 1)
  have hρ : Function.Surjective ρ := e.surjective.comp (hypProj_surjective h 2 1)
  have hρk : ∀ s, ρ s = 1 ↔ s ∈ hypScalars h 2 1 := fun s => by
    rw [← ker_hypProj, MonoidHom.mem_ker]
    exact ⟨fun h1 => e.injective (by simpa [ρ] using h1), fun h1 => by simp [ρ, h1]⟩
  have hρc : ρ.ker ≤ center (hypSU h 2 1) := fun s hs =>
    normOneScalars_le_center h _ _ ((hρk s).1 hs)
  obtain ⟨α, hα, -, hαπ⟩ := uc22pwlie_exists_cover_of_closed_fin hclosed hq.1
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) ρ hρ hρc
  refine ⟨K, hK, h, α, hα, fun s => ?_⟩
  rw [← QuotientGroup.eq_one_iff, ← hρk s, ← hαπ]
  rfl

theorem uc22s218_u5_scalars_le_ker {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    {X : Type} [Group X] (α : hypSU h 2 1 →* X)
    (hαc : ∀ s, α s ∈ Subgroup.center X ↔ s ∈ hypScalars h 2 1) (h5 : 5 ∣ 2 ^ n + 1)
    (hinj : ¬ Function.Injective α) : hypScalars h 2 1 ≤ α.ker := by
  have hZ : Nat.card (hypScalars h 2 1) = 5 := by
    rw [card_hypScalars h (by norm_num)]
    exact Nat.gcd_eq_left h5
  have hkZ : α.ker ≤ hypScalars h 2 1 := fun s hs =>
    (hαc s).1 (by rw [MonoidHom.mem_ker.1 hs]; exact Subgroup.one_mem _)
  have hne : α.ker ≠ ⊥ := fun h' => hinj ((MonoidHom.ker_eq_bot_iff α).1 h')
  have hdvd : Nat.card α.ker ∣ 5 := hZ ▸ Subgroup.card_dvd_of_le hkZ
  have h1 : Nat.card α.ker ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.1 h1)
  have h5' : Nat.card α.ker = 5 := ((Nat.dvd_prime (by norm_num)).1 hdvd).resolve_left h1
  have := h.finite
  exact (Subgroup.eq_of_le_of_card_ge hkZ (by rw [h5', hZ])).ge

theorem uc22s218_u5_center_eq_bot {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    {X : Type} [Group X] (α : hypSU h 2 1 →* X) (hα : Function.Surjective α)
    (hαc : ∀ s, α s ∈ Subgroup.center X ↔ s ∈ hypScalars h 2 1) (h5 : 5 ∣ 2 ^ n + 1)
    (hinj : ¬ Function.Injective α) : Subgroup.center X = ⊥ := by
  have hle := uc22s218_u5_scalars_le_ker h α hαc h5 hinj
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨s, rfl⟩ := hα z
  rw [Subgroup.mem_bot]
  exact MonoidHom.mem_ker.1 (hle ((hαc s).1 hz))

end CFSG.LocalAnalysis.UniquenessCase.UC22
