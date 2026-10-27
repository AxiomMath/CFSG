module

import CFSG.RankThree.PartTwo.Sec17.Item1713
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item166ResProofDeltaSz
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace Proof17Res12

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem ne_top_of_not_three_dvd (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX3 : ¬ 3 ∣ Nat.card X) : X ≠ ⊤ := by
  intro htop
  apply hX3
  rw [htop, Subgroup.card_top, ← h.toSec13Data.orderOf_eq]
  exact orderOf_dvd_natCard c

theorem suzukiModel_quot_of_eq {H : Type} [Group H] {N₁ N₂ : Subgroup H} [N₁.Normal] [N₂.Normal]
    (hN : N₁ = N₂) {p f : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (H ⧸ N₁) p f) :
    CFSG.Blueprint.SuzukiModel (H ⧸ N₂) p f := by
  subst hN
  exact hSz

theorem centralizer_ne_top (h : Sec17Std G A c L Y₀) {b : G} (hb1 : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := h.isSimpleGroup
  have hcen : b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({b} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hbot | htop'
  · exact hb1 (by rw [hbot] at hcen; exact hcen)
  · obtain ⟨x, y, hxy⟩ := h.nonabelian
    apply hxy
    have hx : x ∈ Subgroup.center G := htop' ▸ Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hx y).symm

theorem delta_centralizer_mem_scriptY3 (h : Sec17Std G A c L Y₀) {b : G} (hb1 : b ≠ 1)
    (hO2 : CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) ≠ ⊥) :
    delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ∈ scriptY3 A (lB A) :=
  ⟨⟨⟨fun htop => centralizer_ne_top h hb1 (eq_top_iff.mpr (htop ▸ delta_le _)),
    Sec14.le_normalizer_delta _⟩, hO2⟩, (delta_delta _).symm⟩

theorem delta_normalizer_mem_scriptY3 (h : Sec17Std G A c L Y₀) {S X : Subgroup G}
    (hSQ : S ∈ scriptQ A (lB A)) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hSX : S ≤ X)
    (hXtop : X ≠ ⊤) :
    delta A (lB A) (Subgroup.normalizer (S : Set G)) ∈ scriptY3 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDN : delta A (lB A) (Subgroup.normalizer (S : Set G)) ≤ Subgroup.normalizer (S : Set G) :=
    delta_le _
  have hSD : S ≤ delta A (lB A) (Subgroup.normalizer (S : Set G)) :=
    le_delta hSQ Subgroup.le_normalizer
  have hNtop : Subgroup.normalizer (S : Set G) ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with h0 | h1
    · exact hS1 h0
    · exact hXtop (eq_top_iff.mpr (h1 ▸ hSX))
  refine ⟨⟨⟨fun htop => hNtop (eq_top_iff.mpr (htop ▸ hDN)), Sec14.le_normalizer_delta _⟩, ?_⟩,
    (delta_delta _).symm⟩
  intro hbot
  apply hS1
  rw [eq_bot_iff, ← hbot]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSD hDN hS2

theorem false_of_mem_thetaComponentsIn_le {X K N : Subgroup G} (hK : K ∈ thetaComponentsIn X)
    (hKN : K ≤ N) (hN : Group.IsSolvable N) : False := by
  obtain ⟨hKX, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  obtain ⟨hK'perf, -, hq⟩ := hK'
  have eK : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  have hKperf : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKN)
      (Subgroup.inclusion_injective hKN)
  have hKnt : Nontrivial K := by
    obtain ⟨-, hsimp, -⟩ := hq
    have hQ : Nontrivial (↥(K.subgroupOf X) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf X)) := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hsimp.toNontrivial
    have : Nontrivial ↥(K.subgroupOf X) := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hQ
    exact eK.symm.toEquiv.nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)).ne
    hKperf.commutator_eq_top

theorem le_M_of_mem_scriptY3 (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L) (hC : Claim174)
    {X : Subgroup G} (hXΔ : X = delta A (lB A) X) (hX3 : ¬ 3 ∣ Nat.card X)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn X)
    (hSz : ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n)
    {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A)) : Y ≤ Subgroup.normalizer (Y₀ : Set G) := by
  by_contra hYM
  obtain ⟨hY1, -⟩ := mem_scriptY1_of_not_le_M h h166 hbot hY hYM
  obtain ⟨Y₁, hYY₁, hY₁⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY1 A (lB A))) hY1
  have hY₁M : ¬ Y₁ ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle => hYM (hYY₁.trans hle)
  obtain ⟨-, hY₁s⟩ := mem_scriptY1_of_not_le_M h h166 hbot hY₁.prop.1 hY₁M
  obtain ⟨S, hS⟩ := exists_mem_scriptQPiStar (A := A) (LB := lB A) Y₁ (piOf 2)
  obtain ⟨V, hV, hVY₁⟩ := exists_omega168_le h h166 hbot hY₁.prop.1 hY₁M
  obtain ⟨N, hN, hY₁N, hNS⟩ := h168 (item168_premise h) V hV Y₁ hY₁.prop.1 hVY₁
  have hNY₁ : N = Y₁ := le_antisymm (hY₁.2 hN.prop (hY₁N Y₁ hY₁.prop.1 le_rfl))
    (hY₁N Y₁ hY₁.prop.1 le_rfl)
  subst hNY₁
  obtain ⟨Y', hY', hKY', hSY'⟩ := hC G A c L Y₀ h X hXΔ hX3 K hK hSz N hY₁ hY₁M S hS
  exact false_of_mem_thetaComponentsIn_le hK (hKY'.trans ((hNS S hS).2.1 Y' hY' hSY')) hY₁s

theorem two_dvd_card_perfectResidual {K : Subgroup G}
    (hcen : (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀)) {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 n) {b : G} (hbY : b ∈ Y₀)
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hb : orderOf b = 3) :
    2 ∣ Nat.card (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQ
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := fun k hk =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ (hcen hk).1
  have hle : Q.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup ⟨fun n hn g => ?_⟩
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀).comap_subtype (K := K))
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hKQ g.2) n).mp hn
    simpa using this
  refine Proof1619.two_dvd_of_conjQuot_eq_one hbK hb hSz ?_
  ext z
  induction z using QuotientGroup.induction_on with
  | H k =>
    rw [Proof1619.conjQuot_mk, MulAut.one_apply, QuotientGroup.eq]
    apply hle
    rw [Subgroup.mem_subgroupOf]
    have h1 := Q.inv_mem ((hcen (K.inv_mem k.2)).2 b hbY)
    have h2 : ((((⟨b * k * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbK k).mp k.2⟩ : K)⁻¹ * k : K) :
        G)) = ((k : G)⁻¹ * b * (k : G)⁻¹⁻¹ * b⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact h1

theorem false_of_delta_le (h : Sec17Std G A c L Y₀)
    (h166 : Item166 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h168 : Item168 A (lB A) c L) (h146 : Item146 A (lB A)) (h172 : Item172 A (lB A))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hC : Claim174) {X : Subgroup G}
    (hXΔ : X = delta A (lB A) X) (hX3 : ¬ 3 ∣ Nat.card X) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn X) {n : ℕ}
    (hn : CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n)
    (hΔb : X ∈ scriptQ A (lB A) → CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K →
      (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀) → A ≤ Subgroup.normalizer (K : Set G) →
      (∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) →
      ∀ b ∈ A ⊓ L, b ≠ 1 →
        CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G)) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  have hXtop : X ≠ ⊤ := ne_top_of_not_three_dvd h hX3
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    have := Sec14.le_normalizer_delta (A := A) (LB := lB A) X
    rwa [← hXΔ] at this
  have hXQ : X ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146
      ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
    rwa [← hXΔ] at this
  obtain ⟨hθ, hcen⟩ := (h166 Y₀ h.mem_y0Star).1 X ⟨hXtop, hAX⟩ hXΔ K hK ⟨n, hn⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    ProofDeltaSz166.mem_normalizer_of_suzukiModel h.toTheoremFourHyp.localRank_lt hK hn hθ
      (hAX ha) (hA.1.2 a ha)
  have hY3 : ∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G) := fun Y hY =>
    le_M_of_mem_scriptY3 h h166 hbot h168 hC hXΔ hX3 hK ⟨n, hn⟩ hY
  have hΔb' : ∀ b ∈ A ⊓ L, b ≠ 1 → delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G) := by
    intro b hb hb1
    by_cases hO2 :
        CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥
    · exact hΔb hXQ hθ hcen hAK hY3 b hb hb1 hO2
    · exact hY3 _ (delta_centralizer_mem_scriptY3 h hb1 hO2)
  have hB : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9]⟩
  obtain ⟨Q, hQ, hQM⟩ := h172 Y₀ h.mem_y0Star
  exact hQM (le_of_forall_inf_centralizer_le hA hB hQ fun b hb hb1 =>
    (le_delta (inf_centralizer_mem_scriptQ hA.1.1 (Set.singleton_subset_iff.mpr (hB.1 hb)) hQ)
      inf_le_right).trans (hΔb' b hb hb1))

end Proof17Res12

end CFSG.RankThree.PartTwo.Sec17
