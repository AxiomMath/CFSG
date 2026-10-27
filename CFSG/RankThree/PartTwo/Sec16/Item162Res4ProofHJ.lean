module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res3ProofA5
import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofChoice
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162UJHJSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      CFSG.Open.pCoreOf 2 L = ⊥ →
      ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      S₁ ⊓ S₂ ⊓ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) →
        Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
        (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ J) ⊔ CFSG.Open.pCoreOf 2 L') →
        (Y₁ = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₁ ∧ L = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) →
        (Y₂ = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₂ ∧ L = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) →
        oPrimeResidualOf 3
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) = ⊥

namespace Res162d

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_normalizer_sup {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A))
    (hL4 : L ∈ scriptY4 A (lB A)) {Q : Subgroup G} (hQQ : Q ∈ scriptQ A (lB A))
    (hQ2 : IsPGroup 2 Q) (hQc : Q ≤ Subgroup.centralizer ({c} : Set G))
    (hQL : Q ≤ Subgroup.centralizer (L : Set G)) (hne : CFSG.Open.pCoreOf 2 L ≠ ⊥ ∨ Q ≠ ⊥)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ scriptY0Star A (lB A)) (hK₂ : K₂ ∈ scriptY0Star A (lB A))
    (hLK₁ : L ≤ K₁) (hLK₂ : L ≤ K₂) (hQK₁ : Q ≤ Subgroup.normalizer (K₁ : Set G))
    (hQK₂ : Q ≤ Subgroup.normalizer (K₂ : Set G)) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set Y' := L ⊔ Q with hY'def
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff.mp hQL).trans (Subgroup.centralizer_le_normalizer _)
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) :=
    hQL.trans (Subgroup.centralizer_le_normalizer _)
  have hY'Q : Y' ≤ Subgroup.normalizer (Q : Set G) := sup_le hLQ Subgroup.le_normalizer
  have hY'L : Y' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hQN
  have hQO : Q ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'Q hQ2
  have hOLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (hY'L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
  have hO2 : CFSG.Open.pCoreOf 2 Y' ≠ ⊥ := by
    rcases hne with h1 | h1
    · exact fun h0 => h1 (le_bot_iff.mp (h0 ▸ hOLO))
    · exact fun h0 => h1 (le_bot_iff.mp (h0 ▸ hQO))
  have hY'Δ : Y' = delta A (lB A) Y' :=
    le_antisymm (sup_le (hL4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hQQ le_sup_right))
      (delta_le _)
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) := sup_le hD.le_centralizer hQc
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hY'c))
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, le_normalizer_sup hD.le_normalizer hQQ.1.2.2⟩, hO2⟩, hY'Δ⟩
  have hres : oPrimeResidualOf 3 Y' = L :=
    ((oPrimeResidualOf_eq_of_le le_sup_left fun x hx k hk =>
      mem_of_pow_three_of_mem_sup hQN hQ2 hx hk).symm.trans hL4.2.1.symm)
  have hX4 : oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) := by
    rw [hres]
    exact hL4
  have hY'eq : Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' := by
    rw [hres]
    exact le_antisymm (sup_le le_sup_left (hQO.trans le_sup_right))
      (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hΩ : omg155 A (oPrimeResidualOf 3 Y') := by
    rw [hres]
    exact Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, by
      rw [inf_idem, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]⟩
  have hΓ₁ : K₁ ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') :=
    ⟨hK₁, by rw [hres]; exact hLK₁, sup_le (hLK₁.trans Subgroup.le_normalizer) hQK₁⟩
  have hΓ₂ : K₂ ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') :=
    ⟨hK₂, by rw [hres]; exact hLK₂, sup_le (hLK₂.trans Subgroup.le_normalizer) hQK₂⟩
  exact Proof162.eq_of_mem_gam155 h155 h153 hY'3 hX4 hY'eq hΓ₁ hΓ₂ (Or.inl hΩ)

end Res162d

open Res162d in
theorem step162UJHJ_of_simple
    (h1514 : Item1514HJR) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (h1411 : Item1411_1R) (h155 : Item155R) (hS : Step162UJHJSimple) : Step162UJHJ := by
  intro G _ _ A c L h hJ Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J hJ0 hJK hφ hnc hc₁ hc₂
  have hD := h.toSec13Data
  set Q := S₁ ⊓ S₂ ⊓ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (L : Set G)
    with hQdef
  by_cases hcase : CFSG.Open.pCoreOf 2 L ≠ ⊥ ∨ Q ≠ ⊥
  · exfalso
    have hY₁ := hmax.1.mem₁
    have hY₂ := hmax.1.mem₂
    have hLY : ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y := fun Y hY =>
      le_of_j2 h hJ (fun c' L' hR' hJ' => h1514 G A c' L' hR' hJ') (h1523 G A c L h)
        (h153 G A c L h) (hobs G A c L h) (h1411 G A c L h) hY
    have hL4 := mem_scriptY4_of_j2 h hJ (h1523 G A c L h) hY₁ (hLY Y₁ hY₁)
    have hS₁ := hmax.1.s₁.prop
    have hS₂ := hmax.1.s₂.prop
    have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hD.mem_A)
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
      (le_inf (le_inf (le_inf hS₁.1.1.1.2.2 hS₂.1.1.1.2.2 |>.trans
        Subgroup.inf_normalizer_le_normalizer_inf) (hAc.trans Subgroup.le_normalizer) |>.trans
        Subgroup.inf_normalizer_le_normalizer_inf)
        (hD.le_normalizer.trans (normalizer_le_normalizer_centralizer' L))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hQS₁ : Q ≤ S₁ := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hQS₂ : Q ≤ S₂ := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hQQ : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_le hS₁.1.1 hQS₁ hAQ
    have hQ2 : IsPGroup 2 Q := (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁).to_le hQS₁
    have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) := inf_le_left.trans inf_le_right
    have hQL : Q ≤ Subgroup.centralizer (L : Set G) := inf_le_right
    have hYY := eq_of_le_normalizer_sup h (h155 G A c L h) (h153 G A c L h) hL4 hQQ hQ2 hQc hQL
      hcase hY₁ hY₂ (hLY Y₁ hY₁) (hLY Y₂ hY₂) (hQS₁.trans hS₁.1.2) (hQS₂.trans hS₂.1.2)
    exact hmax.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, hYY]⟩
  · push Not at hcase
    exact hS G A c L h hJ hcase.1 Y₁ Y₂ S₁ S₂ hmax hcase.2 h12 h21 hnt J hJ0 hJK hφ hnc hc₁ hc₂

end CFSG.RankThree.PartTwo.Sec16
