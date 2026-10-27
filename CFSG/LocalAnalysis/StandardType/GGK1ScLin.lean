module

public import CFSG.LocalAnalysis.StandardType.GGK1ScCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem ggCenterPrime_linear_gcd
    {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hd : 1 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ (p ∣ d ∧ p ∣ Nat.card K - 1)) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hF⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* LargeEvenSLGroup (Fin (m + 1)) K), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSLGroup (Fin (m + 1)) K →* E, ∀ h, π (s h) = h := by
    have hOC : OddCentralSplit ↥(LargeEvenSLGroup (Fin (m + 1)) K) :=
      (CFSG.SeitzReduction.LinearPilot.oddCentralSplit_specialLinearGroup (m := m)
        (F := K)).of_mulEquiv (TypeA.slKerEquiv (m + 1) K).symm
    intro E _ _ π hπ hcen hC
    exact hOC E π hπ hcen (Nat.coprime_two_left.mp hC)
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin (m + 1)) K)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : TypeA.recipeEquiv (m + 1) K z ∈ Subgroup.center (projectiveSL (m + 1) K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := (TypeA.recipeEquiv (m + 1) K).surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
    rw [SlNsRootGen.center_projectiveSL_eq_bot_charTwo, Subgroup.mem_bot] at hz'
    exact (TypeA.recipeEquiv (m + 1) K).injective (by simpa using hz')
  haveI : Finite (LargeEvenSLGroup (Fin (m + 1)) K) := Finite.of_injective
    (fun x : LargeEvenSLGroup (Fin (m + 1)) K =>
      ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  refine ggCenterPrime_of_coprime_card_ker
    (q := LargeEvenProjMk (LargeEvenSLGroup (Fin (m + 1)) K))
    (QuotientGroup.mk'_surjective _) hZ hsplit hp hp2 ?_
  let Z0 := (LargeEvenScalars (Fin (m + 1)) K).subgroupOf (LargeEvenSLGroup (Fin (m + 1)) K)
  have hker_eq : (LargeEvenProjMk (LargeEvenSLGroup (Fin (m + 1)) K)).ker = Z0 :=
    QuotientGroup.ker_mk' _
  rw [hker_eq]
  have hHS : LargeEvenSLGroup (Fin (m + 1)) K = StatedSL (m + 1) K := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]; rfl
  have hdivN : Nat.card Z0 ∣ m + 1 :=
    CFSG.QuasithinUnique.Ch1.card_scalars_dvd_dim (n := m + 1) (p := 2) (f := f) (by omega)
      (Or.inl ⟨hF, hHS⟩)
  have hdivQ : Nat.card Z0 ∣ Nat.card K - 1 :=
    CFSG.StandardType.SporadicShape.card_statedScalars_subgroupOf_dvd
      (LargeEvenSLGroup (Fin (m + 1)) K)
  have hdiv : Nat.card Z0 ∣ Nat.gcd (m + 1) (Nat.card K - 1) := Nat.dvd_gcd hdivN hdivQ
  have hpg : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card K - 1)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hpd ⟨hd.trans (Nat.gcd_dvd_left _ _), hd.trans (Nat.gcd_dvd_right _ _)⟩
  exact (Nat.Coprime.of_dvd_right hdiv hpg).symm

end CFSG.StandardType

end
