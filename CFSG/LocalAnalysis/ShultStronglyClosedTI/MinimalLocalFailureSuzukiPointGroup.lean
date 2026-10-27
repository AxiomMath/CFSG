module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupCases
public import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.ProperPairModel
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_central_involution {J : Subgroup G} (P : Sylow 2 J) (hJ : 2 ∣ Nat.card J) :
    ∃ u ∈ (P : Subgroup J).map J.subtype,
      (∀ y ∈ (P : Subgroup J).map J.subtype, u * y = y * u) ∧ orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : 2 ∣ Nat.card (P : Subgroup J) := by
    rw [P.card_eq_multiplicity]
    exact dvd_pow_self 2 (Nat.Prime.factorization_pos_of_dvd Nat.prime_two
      Nat.card_pos.ne' hJ).ne'
  have : Nontrivial (P : Subgroup J) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos hP2
    omega
  have hZ := P.isPGroup'.center_nontrivial
  have hZ2 : 2 ∣ Nat.card (Subgroup.center (P : Subgroup J)) := by
    rcases (P.isPGroup'.to_subgroup (Subgroup.center _)).card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  refine ⟨(((x : (P : Subgroup J)) : J) : G),
    ⟨((x : (P : Subgroup J)) : J), (x : (P : Subgroup J)).2, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
    exact congrArg (fun w : (P : Subgroup J) => ((w : J) : G)) h1.symm
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

theorem minimalLocalFailure_suzuki_point_group_action_odd_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    let B := pairPointStabilizer H beta
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    let J₀ := Subgroup.centralizer (K : Set G)
    ∃ T : Subgroup G, T ≤ H ⊓ K ∧ IsPGroup 2 T ∧
      (∀ S : Sylow 2 ↥(H ⊓ K), (S : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype = T) ∧
      J₀ = B ⊓ Subgroup.centralizer (Q : Set G) ∧
      C ⊓ Subgroup.normalizer (K : Set G) = T ⊔ J₀ ∧ T ⊓ J₀ = ⊥ ∧
      T ≤ Subgroup.centralizer (J₀ : Set G) ∧
      (∃ _ : (C.subgroupOf H).Normal, Odd (Nat.card (↥H ⧸ C.subgroupOf H)) ∧
        Group.IsSolvable (↥H ⧸ C.subgroupOf H)) ∧
      ∀ P : Sylow 2 ↥J₀, ∀ u ∈ (P : Subgroup ↥J₀).map J₀.subtype,
        (∀ y ∈ (P : Subgroup ↥J₀).map J₀.subtype, u * y = y * u) → orderOf u = 2 →
        let Pg := (P : Subgroup ↥J₀).map J₀.subtype
        let NS := C ⊓ Subgroup.normalizer (u • (Q : Set G))
        (∀ c ∈ NS, ∃ y ∈ Q, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ * y) ∧
        (((∀ y ∈ Q, ∃ c ∈ NS, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ * y) ∧
            ∃ S : Sylow 2 ↥H, (S : Subgroup ↥H).map H.subtype ≤ C) ∨
          ((∀ c ∈ NS, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ) ∧
            (∃ S : Sylow 2 ↥C, (S : Subgroup ↥C).map C.subtype = T ⊔ Pg) ∧
            Odd (C.relIndex (H ⊓ Subgroup.normalizer ((T ⊔ Pg : Subgroup G) : Set G))))) := by
  intro B K Q C J₀
  obtain ⟨-, -, _, _, -, -, -, -, -, -, -, -, -, -, T, hTM, hT2, hall, -, hBT, hNeq, hTB, -, -,
    -, hTQ, -⟩ := proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  have hJ : J₀ = B ⊓ Subgroup.centralizer (Q : Set G) :=
    hull_centralizer_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have hTK : T ≤ K := fun x hx => (hTM hx).2
  obtain ⟨hNCK, hTJ, hTJc⟩ := point_centralizer_normalizer_eq hNeq hBT hTB hTQ hTK hJ
  have hcases := fun P u huP huZ hu =>
    suzuki_point_action_cases_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
      hall P (u := u) huP huZ hu
  have hJB : J₀ ≤ B := by rw [hJ]; exact inf_le_left
  have hBodd := odd_relIndex_hull_centralizer_of_exclusion h hcomm hsmallerR1 hbeta ht hproper
    hBinv hSz hexcl
  have hJ2 : 2 ∣ Nat.card J₀ := by
    obtain ⟨u₀, hu₀B, hu₀⟩ := hBinv
    have h1 : 2 ∣ Nat.card B := hu₀ ▸ Subgroup.orderOf_dvd_natCard B hu₀B
    rw [card_eq_relIndex_mul_card hJB] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h1 with h2 | h2
    · exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hBodd)
    · exact h2
  obtain ⟨u, huP, huZ, hu⟩ := exists_central_involution (default : Sylow 2 J₀) hJ2
  have hCodd : Odd (C.relIndex H) := (hcases default u huP huZ hu).2.2
  obtain ⟨-, -, hHC⟩ := point_root_conj_mem h hcomm hbeta ht hproper
  have hnormal : (C.subgroupOf H).Normal := ⟨fun n hn g => hHC g g.2 n hn⟩
  refine ⟨T, hTM, hT2, hall, hJ, hNCK, hTJ, hTJc,
    ⟨hnormal, hCodd, CFSG.FeitThompson.isSolvable_of_odd_natCard _ hCodd⟩, fun P u huP huZ hu => ?_⟩
  obtain ⟨h1, h2, -⟩ := hcases P u huP huZ hu
  exact ⟨h1, h2⟩

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
