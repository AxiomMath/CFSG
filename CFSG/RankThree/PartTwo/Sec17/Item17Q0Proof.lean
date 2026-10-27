module

public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofComm
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofW
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofQ0
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof17Q0

variable {G : Type} [Group G] [Finite G]

section Std14

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem pCoreOf_mem_scriptQ_of_cover (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : Concl142 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A))
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∨ c ∈ Y) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have hA : IsE27 A := h.isE27
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.2
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  refine pCoreOf_mem_scriptQ_of_scriptY4 hA h146 hY
    (commutator_pCoreOf_mem_scriptQ hA h1444 h146 hbot hY) hcA ?_
    (inf_centralizer_mem_scriptQ_of_concl142 hA h142 h.toSec13Data.zpowers_mem_omegaA
      (isPiSubgroup_piCompl_pCoreOf Y) hAV)
  rcases hcov with hcov | hcY
  · exact Or.inr (commutatorElement_mem_of_eq_sup hcov
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) (hAV hcA)
      (inf_le_right.trans h.toSec13Data.le_centralizer))
  · exact Or.inl hcY

end Std14

section Std17

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem inf_centralizer_mem_scriptQ_of_std (h : Sec17Std G A c L Y₀) :
    CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  have hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer_y0.trans hMV
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcop : ∀ X : Subgroup G, X ≤ V → Nat.Coprime 3 (Nat.card X) := fun X hX => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hV2.to_le hX)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have key : ∀ K : Subgroup G, K ≤ Subgroup.normalizer (Y₀ : Set G) →
      V ⊓ K ≤ pPrimeCoreOf 3 K := fun K hK =>
    le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hK.trans hMV) Subgroup.le_normalizer)
      (hcop _ inf_le_left)
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hcop _ inf_le_left)),
    le_normalizer_inf hAV (h.toSec13Data.A_le_centralizer.trans Subgroup.le_normalizer),
    fun B hB => ?_⟩
  by_cases hcB : c ∈ B
  ·
    have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)).trans
        (HeadProof.centralizer_c_le_M h)
    exact ((inf_le_inf_right _ inf_le_left).trans (key _ hCB)).trans
      (le_sup_left.trans le_sup_left)
  ·
    have hAcB := Proof169.le_zpowers_sup_of_not_mem hB hcA hcB
    have hCA : Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer (A : Set G) := by
      rintro x ⟨hxc, hxB⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hsub : Subgroup.zpowers c ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
        · intro z hz
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hxB z hz)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub (hAcB hy))
    have hle : V ⊓ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
        V ⊓ Subgroup.centralizer (A : Set G) := by
      rw [inf_assoc]
      exact inf_le_inf_left V hCA
    exact (hle.trans (key _ (HeadProof.centralizer_le_M h))).trans
      (le_sup_right.trans le_sup_left)

theorem eq_sup_of_omega (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) :
    Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  rcases h1514 Y₀ h.mem_y0Star hMeets with ⟨hY, -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, -, -, hno, -⟩
  · rwa [inf_of_le_right h.le_y0] at hY
  · have h3 := hT.1
    rw [hΩ, Set.ncard_singleton] at h3
    omega
  · exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

theorem pCoreOf_mem_scriptQ_of_std (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (hN : ⁅CFSG.Open.pCoreOf 2 Y₀, Y₀⁆ ∈ scriptQ A (lB A))
    (hcov : omegaA A = {Subgroup.zpowers c} → Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A) := by
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have hY : Y₀ ∈ scriptY4 A (lB A) := h.mem_y0Star.prop.1
  have hcA : c ∈ A := h.toSec13Data.mem_A
  refine pCoreOf_mem_scriptQ_of_scriptY4 hA h146 hY hN hcA ?_
    (inf_centralizer_mem_scriptQ_of_std h)
  rcases h.a10_or_omega with hA10 | hΩ
  · exact Or.inl (h.le_y0_of_alternating_ten hA10 hcA)
  · refine Or.inr (commutatorElement_mem_of_eq_sup (hcov hΩ)
      (h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)) ?_
      h.toSec13Data.le_centralizer)
    exact (h.le_normalizer_y0.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)) hcA

end Std17

end Proof17Q0

theorem claim17Q0_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS17)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Claim17Q0 := by
  intro G _ _ A c L Y₀ h
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have h146' := h146 G A c L h.toSec14Std
  exact Proof17Q0.pCoreOf_mem_scriptQ_of_std h h146'
    (Proof17Q0.commutator_pCoreOf_mem_scriptQ hA (h1444 G A c L h.toSec14Std) h146'
      (hbot G A c L Y₀ h) h.mem_y0Star.prop.1)
    (Proof17Q0.eq_sup_of_omega h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h))

theorem claim17Q0_of_step171CommQ (hQ : Step171CommQ) : Claim17Q0 :=
  fun _ _ _ _ _ _ _ h => Steps165.pCoreOf_mem_scriptQ hQ h

theorem step171CommQ_of_claim17Q0 (hQ0 : Claim17Q0) : Step171CommQ := by
  intro G _ _ A c L Y₀ h b hb _ _ B hB _ _
  have hV := hQ0 G A c L Y₀ h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hAb : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    (show A ≤ Subgroup.centralizer ({b} : Set G) from fun _ hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx hb)).trans
      Subgroup.le_normalizer
  have hW : A ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hV.1.2.2 hAb
  have hle : ⁅CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G),
      Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 Y₀ :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hW hcA))).trans
      inf_le_left
  exact (inf_le_inf_right _ hle).trans (hV.2 B hB)

theorem step171CommQ_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS17)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Step171CommQ :=
  step171CommQ_of_claim17Q0 (claim17Q0_of h1444 h146 hbot h1514 hMeets)

end CFSG.RankThree.PartTwo.Sec17

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

theorem Proof162.pCoreOf_le_of_mem_scriptQ {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsE27 A) (h146 : Item146 A (lB A)) {Y S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2))
    (hV : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A)) : CFSG.Open.pCoreOf 2 Y ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 Y with hVdef
  have hSN : S ≤ Subgroup.normalizer (Y : Set G) := hS.prop.1.2
  have hSV : S ≤ Subgroup.normalizer (V : Set G) :=
    hSN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hVSQ : V ⊔ S ∈ scriptQ A (lB A) := by
    rw [sup_comm]
    exact sup_mem_scriptQ_of_item146 hA h146 hS.prop.1.1 hV hSV
  have hmem : V ⊔ S ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2) :=
    ⟨⟨hVSQ, sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans Subgroup.le_normalizer) hSN⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hV2.to_sup_of_normal_left' hS2 hSV)⟩
  exact le_sup_left.trans (hS.2 hmem le_sup_right)

theorem step162WO2_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h142 : Concl142S14) : Step162WO2 := by
  intro G _ _ A c L Y₁ Y₂ S hR hconf _ hcov
  have h14 := hR.toSec14Std
  have h146' := h146 G A c L h14
  have hV := Proof17Q0.pCoreOf_mem_scriptQ_of_cover h14 (h1444 G A c L h14) h146'
    (hbot G A c L h14) (h142 G A c L h14) hconf.maxCE.1.mem₂.prop.1 (Or.inl hcov)
  exact (Proof162.pCoreOf_le_of_mem_scriptQ h14.isE27 h146' hconf.maxCE.1.s₂ hV).trans
    le_sup_right

theorem step162WR_of_items (h1514 : Item1514R) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) : Step162WR :=
  step162WR_of h1514 (step162WO2_of h1444 h146 hbot h142)

end CFSG.RankThree.PartTwo.Sec16
