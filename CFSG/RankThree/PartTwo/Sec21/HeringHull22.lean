module

public import CFSG.RankThree.PartTwo.Sec21.HeringHullChain4
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofAll
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofBlocks
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec21.Item223ListProof
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

theorem item233HullStarK_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h222 : Item222)
    (hKW : KOfWellDefinedAll) :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
        ∀ φ ∈ dStar A, ∀ X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)),
          kOf A φ ≤ X₀ → ∃ Z ∈ lStar A, ∀ ψ ∈ dStar A, kOf A ψ ≤ X₀ → kOf A ψ ≤ Z := by
  intro G _ _ A E U c L hpair B hBA hB3 φ hφ X₀ hX₀ hKX₀
  have hG := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAn := Sec6.exists_card_eq_of_mem_partTwoF hpair.mem_S.1
  have hK := hKW G A E U c L hpair
  obtain ⟨b, hbB, hb1, rfl⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three hB3
  have hbA : b ∈ A := hBA hbB
  have hX₀b : X₀ ∈ thetaComponentsAt 3 b := by
    rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq]
    exact hX₀
  have hZ₀ : X₀ ∈ thetaComponentFamily 3 A :=
    mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, hX₀b⟩
  set 𝓟 : Set (Subgroup G) := {P | ∃ ψ ∈ dStar A, P = kOf A ψ ∧ kOf A ψ ≤ X₀} with h𝓟
  have hq : ∀ P ∈ 𝓟, IsQuasisimple P ∧ A ≤ Subgroup.normalizer (P : Set G) := by
    rintro P ⟨ψ, hψ, rfl, -⟩
    obtain ⟨n, hn, ⟨e⟩⟩ := Item233One.exists_two_le_mulEquiv_kOf h222 hpair hψ
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (Sec8.Item87Proof.isQuasisimple_projSL_two hn), le_normalizer_kOf hAe.1 hK hψ⟩
  obtain ⟨Z, hZ, hPZ⟩ := HeringHull.exists_mem_lStar_le h45 h48 hG hAe hAn 𝓟 hq hZ₀
    (by rintro P ⟨ψ, -, rfl, hψX⟩; exact hψX)
  exact ⟨Z, hZ, fun ψ hψ hψX => hPZ _ ⟨ψ, hψ, rfl, hψX⟩⟩

namespace Item223PrintProof

variable {G : Type} [Group G]

theorem commute_or_le_lStar_k [Finite G] (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h222 : Item222) (hKW : KOfWellDefinedAll) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : φ ≠ ψ) :
    ⁅kOf A φ, kOf A ψ⁆ = ⊥ ∨ ∃ Z ∈ lStar A, kOf A φ ≤ Z ∧ kOf A ψ ≤ Z := by
  have hK := hKW G A E U c L hpair
  have hcard9 := card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK hφ hψ hne
  rw [hA81] at hcard9
  set D := A ⊓ Subgroup.centralizer ((kOf A φ ⊔ kOf A ψ : Subgroup G) : Set G) with hD
  have hD1 : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard9
    omega
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdK : d ∈ Subgroup.centralizer (kOf A φ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hdD.2
  have hdJ : d ∈ Subgroup.centralizer (kOf A ψ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hdD.2
  set B := Subgroup.zpowers d with hB
  have hBA : B ≤ A := Subgroup.zpowers_le.mpr hdD.1
  have hd3 : d ^ 3 = 1 := hpair.mem_S.1.1.2 d hdD.1
  have hB3 : Nat.card B = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1']
  have hB1 : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hB3
    omega
  have hKB : kOf A φ ≤ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hdK
  have hJB : kOf A ψ ≤ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hdJ
  obtain ⟨Kd, hKd, hKKd⟩ :=
    Item233One.exists_mem_thetaComponentsIn_kOf_le h48 h222 hpair hK hBA hB1 hφ hKB
  obtain ⟨Jd, hJd, hJJd⟩ :=
    Item233One.exists_mem_thetaComponentsIn_kOf_le h48 h222 hpair hK hBA hB1 hψ hJB
  by_cases hKJd : Kd = Jd
  · right
    obtain ⟨Z, hZ, hKdZ⟩ :=
      item233HullStarK_of h45 h48 h222 hKW G A E U c L hpair B hBA hB3 φ hφ Kd hKd hKKd
    exact ⟨Z, hZ, hKdZ φ hφ hKKd, hKdZ ψ hψ (hKJd ▸ hJJd)⟩
  · left
    obtain ⟨n, hn1, -, eK⟩ := exists_mulEquiv_kOf_odd h222 hpair hA81 hφ
    obtain ⟨n', hn1', -, eJ⟩ := exists_mulEquiv_kOf_odd h222 hpair hA81 hψ
    have hdφ : d ∈ fixedInG A φ := by
      rw [← inf_centralizer_kOf_eq h222 hpair hK hφ]
      exact ⟨hdD.1, hdK⟩
    have hdψ : d ∈ fixedInG A ψ := by
      rw [← inf_centralizer_kOf_eq h222 hpair hK hψ]
      exact ⟨hdD.1, hdJ⟩
    have hCB : Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({d} : Set G) :=
      Sec6.centralizer_zpowers_eq d
    rw [hCB] at hKd hJd
    exact commute33 G A E U c L hpair hK φ hφ ψ hψ hne n n' (by omega) (by omega) eK eJ d
      ⟨hdφ, hdψ⟩ hd1' Kd (by rw [thetaComponentsAt_eq_thetaComponentsIn]; exact hKd) Jd
      (by rw [thetaComponentsAt_eq_thetaComponentsIn]; exact hJd) hKKd hJJd hKJd

end Item223PrintProof

namespace Item228Proof

variable {G : Type} [Group G]

theorem commute_or_le_lStar_three_k [Finite G] (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h222 : Item222) (hKW : KOfWellDefinedAll) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : φ ≠ ψ) :
    ⁅kOf A φ, kOf A ψ⁆ = ⊥ ∨ ∃ X ∈ lStar A, kOf A φ ≤ X ∧ kOf A ψ ≤ X := by
  have hK := hKW G A E U c L hpair
  have hcard := card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK hφ hψ hne
  rw [hA27] at hcard
  set D := A ⊓ Subgroup.centralizer ((kOf A φ ⊔ kOf A ψ : Subgroup G) : Set G) with hD
  have hD1 : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdK : d ∈ Subgroup.centralizer (kOf A φ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hdD.2
  have hdJ : d ∈ Subgroup.centralizer (kOf A ψ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hdD.2
  set B := Subgroup.zpowers d with hB
  have hBA : B ≤ A := Subgroup.zpowers_le.mpr hdD.1
  have hd3 : d ^ 3 = 1 := hpair.mem_S.1.1.2 d hdD.1
  have hB3 : Nat.card B = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1']
  have hB1 : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hB3
    omega
  have hKB : kOf A φ ≤ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hdK
  have hJB : kOf A ψ ≤ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hdJ
  obtain ⟨Kd, hKd, hKKd⟩ :=
    Item233One.exists_mem_thetaComponentsIn_kOf_le h48 h222 hpair hK hBA hB1 hφ hKB
  obtain ⟨Jd, hJd, hJJd⟩ :=
    Item233One.exists_mem_thetaComponentsIn_kOf_le h48 h222 hpair hK hBA hB1 hψ hJB
  by_cases hKJd : Kd = Jd
  · right
    obtain ⟨X, hX, hKdX⟩ :=
      item233HullStarK_of h45 h48 h222 hKW G A E U c L hpair B hBA hB3 φ hφ Kd hKd hKKd
    exact ⟨X, hX, hKdX φ hφ hKKd, hKdX ψ hψ (hKJd ▸ hJJd)⟩
  · left
    obtain ⟨n, hn, eK⟩ := Item233One.exists_two_le_mulEquiv_kOf h222 hpair hφ
    obtain ⟨n', hn', eJ⟩ := Item233One.exists_two_le_mulEquiv_kOf h222 hpair hψ
    have hdφ : d ∈ fixedInG A φ := by
      rw [← inf_centralizer_kOf_eq h222 hpair hK hφ]
      exact ⟨hdD.1, hdK⟩
    have hdψ : d ∈ fixedInG A ψ := by
      rw [← inf_centralizer_kOf_eq h222 hpair hK hψ]
      exact ⟨hdD.1, hdJ⟩
    have hCB : Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({d} : Set G) :=
      Sec6.centralizer_zpowers_eq d
    rw [hCB] at hKd hJd
    exact commute33 G A E U c L hpair hK φ hφ ψ hψ hne n n' hn hn' eK eJ d
      ⟨hdφ, hdψ⟩ hd1' Kd (by rw [thetaComponentsAt_eq_thetaComponentsIn]; exact hKd) Jd
      (by rw [thetaComponentsAt_eq_thetaComponentsIn]; exact hJd) hKKd hJJd hKJd

end Item228Proof

open Item223PrintProof Item223ListProof Item228Proof

theorem item228_of_k (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h2131 : Item2131One)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hList : Item228OneList)
    (hPSp : Item228NotPSp45) (hInsp : Item228Inspection) : Item228 := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne
  have hK := hKW G A E U c L hpair
  have hne' : φ ≠ ψ := fun h => hne h.symm
  refine ⟨fun X hX hKX => item228One h2131 h222 hList hPSp hpair hA27 hφ hX hKX, fun hc => ?_,
    fun hnc => ?_⟩
  · rcases commute_or_le_lStar_three_k h45 h48 h222 hKW hpair hA27 hφ hψ hne' with h |
      ⟨X, hX, hKX, hJX⟩
    · exact Or.inl h
    · exact (hInsp G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX
        (item228One h2131 h222 hList hPSp hpair hA27 hφ hX hKX)
        (item228One h2131 h222 hList hPSp hpair hA27 hψ hX hJX)).1 hc
  · rcases commute_or_le_lStar_three_k h45 h48 h222 hKW hpair hA27 hφ hψ hne' with h |
      ⟨X, hX, hKX, hJX⟩
    · exact (hnc (Item223PrintProof.mul_comm_of_commutator_eq_bot h222 hpair hK hφ hψ h)).elim
    · exact (hInsp G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX
        (item228One h2131 h222 hList hPSp hpair hA27 hφ hX hKX)
        (item228One h2131 h222 hList hPSp hpair hA27 hψ hX hJX)).2 hnc

section Census

theorem item223Print_of_gaps_of_list_k (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6)
    (h47 : Sec4.Item4_7W) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6) (h1134 : Item1134Four)
    (hList : Inspection223List) (hBlocks : U4TorusBlocks) (hθ : Item223ThetaTrivial)
    (h222 : Item222) (hKW : KOfWellDefinedAll) : Item223Print := by
  intro G _ _ A E U c L hpair hA81 φ hφ ψ hψ
  have hone : ∀ ξ ∈ dStar A, ∀ Z ∈ lStar A, kOf A ξ ≤ Z → ∃ m : ℕ, OneData A ξ Z m :=
    fun ξ hξ Z hZ hKZ =>
      item223Print_one_of_list h45 h46 h47 h66 h1134 hList hθ h222 hKW hpair hA81 hξ hZ hKZ
  refine ⟨fun X hX hKX => ?_, fun hne hc => ?_, fun hnc => ?_⟩
  · obtain ⟨m, hm⟩ := hone φ hφ X hX hKX
    exact ⟨m, hm.one_lt, hm.odd, hm.equiv, hm.kOf_equiv⟩
  · have hne' : φ ≠ ψ := fun h => hne h.symm
    rcases commute_or_le_lStar_k h45 h48 h222 hKW hpair hA81 hφ hψ hne' with h |
      ⟨Z, hZ, hKZ, hJZ⟩
    · exact h
    · obtain ⟨m, hm⟩ := hone φ hφ Z hZ hKZ
      obtain ⟨m', hm'⟩ := hone ψ hψ Z hZ hJZ
      exact (blocks_of_oneData hBlocks h222 hKW hpair hφ hψ hne' hKZ hJZ hm hm').1 hc
  · have hne' : φ ≠ ψ := by
      rintro rfl
      exact hnc rfl
    rcases commute_or_le_lStar_k h45 h48 h222 hKW hpair hA81 hφ hψ hne' with h |
      ⟨Z, hZ, hKZ, hJZ⟩
    · exact (hnc (mul_comm_of_commutator_eq_bot h222 hpair (hKW G A E U c L hpair) hφ hψ
        h)).elim
    · obtain ⟨m, hm⟩ := hone φ hφ Z hZ hKZ
      obtain ⟨m', hm'⟩ := hone ψ hψ Z hZ hJZ
      exact (blocks_of_oneData hBlocks h222 hKW hpair hφ hψ hne' hKZ hJZ hm hm').2 hnc

end Census

end CFSG.RankThree.PartTwo.Sec21
