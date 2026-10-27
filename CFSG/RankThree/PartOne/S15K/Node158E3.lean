module

import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.S12.Sec158
public import CFSG.RankThree.PartOne.S15K.Defs

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def Node158D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card ↥D = p ^ 2 ∧
      ∀ b ∈ D, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ lieNormalizer p E

@[expose] def Node158E3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ U : Subgroup G, U ≤ E → p ^ 3 ≤ Nat.card ↥U →
      Subgroup.normalizer (U : Set G) ≤ lieNormalizer p E

theorem node158D_of_inputs_c (h155 : Node155) (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hA : KF158A) (hL0 : KF158L0c)
    (hComm : KF158Commc) (h157 : KF157c) (hCov : KF158CovAt) (h156 : KF156') : Node158D := by
  classical
  intro G _ _ p A c L E h15 hF hout
  have h := h15.h12
  have hp := h.prime
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have : Fact p.Prime := ⟨hp⟩
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout hEQ hQW hQ
  have hI : ∀ Y ∈ thetaCompZeroE p E, Y ≤ lieGenerated p E := fun Y hY =>
    h156 G p A c L E h15 hF hout Y hY
  have hc : Sec158.Ctx158 p E :=
    { prime := hp
      elem := hE
      hJ := hJ
      layer_le := fun b => Sec158.zeroLayer_le_lieGenerated h156 h15 hF hout b
      L0 := fun b hbE hb1 z hz Y hY0 hYb =>
        hL0 G p A c L E h15 hF hout b hbE hb1 z hz Y hY0 hYb (hI Y hY0)
      B2 := fun b hbE hb1 => Sec158.E_le_layer_mul_centralizer hbE hEab
        (fun Y hY e he => (h157 G p A c L E h15 hF hout Y hY (hI Y hY)).1 e he)
        (fun Y₁ hY₁0 hY₁b Y₂ hY₂0 hY₂b hne =>
          hComm G p A c L E h15 hF hout b hbE hb1 Y₁ hY₁0 hY₁b (hI Y₁ hY₁0) Y₂ hY₂0 hY₂b
            (hI Y₂ hY₂0) hne) }
  obtain ⟨t, ht, K, J, hKt, hKJ, hmov, hcardD, hJθ, hS2⟩ := hA G p A c L E h15 hF hout
  have hcardM : Nat.card ↥(autMovedInG E t) = p := by
    unfold autMovedInG
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact ht.1.2
  have hcycM : IsCyclic ↥(autMovedInG E t) := isCyclic_of_prime_card hcardM
  obtain ⟨a, haz⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (autMovedInG E t)).1 hcycM
  have haM : a ∈ autMovedInG E t := haz ▸ Subgroup.mem_zpowers a
  have haE : a ∈ E := (Subgroup.map_subtype_le _) haM
  have ha1 : a ≠ 1 := by
    intro h1
    have : Nat.card ↥(Subgroup.zpowers a) = 1 := by rw [h1]; simp
    rw [haz, hcardM] at this
    exact hp.one_lt.ne' this
  have hcov := hCov G p A c L E h15 hF hout t ht K J hKt hKJ hmov hcardD hJθ hS2 a haz
  have hcov' : (E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a) ∨
      (∃ d ∈ E, d ≠ 1 ∧ d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧
        E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d) ∨
      (∃ w ∈ torusNormalizer E, w * a * w⁻¹ ∈ zeroLayer p E a ∧
        zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) = lieGenerated p E) :=
    hcov.imp id (Or.imp (fun h => h.2) (fun h => h.2))
  have hCa := Sec158.root_centralizer_le hc haE ha1 hcov'
  have haJ : a ∈ J := hKJ (hmov haM)
  refine ⟨A ⊓ Subgroup.centralizer (J : Set G), inf_le_left, ?_, ?_⟩
  · have h1 : p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = p * p ^ 2 := by
      rw [hcardD, h.A_card]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  · intro b hbD hb1
    have hbE : b ∈ E := h.A_le_E hbD.1
    have hJX := Sec158.layer_ge_of_KF158A hS h82 h15 hcardD hJθ hS2 hbD hb1
    exact Sec158.hyperplane_centralizer_le hc hbE hb1 haJ hJX hCa

theorem exists_ne_one_mem_inf_of_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E U D : Subgroup G} (hEcard : Nat.card ↥E = p ^ 4) (hUE : U ≤ E) (hDE : D ≤ E)
    (hU : p ^ 3 ≤ Nat.card ↥U) (hD : Nat.card ↥D = p ^ 2) : ∃ b ∈ U ⊓ D, b ≠ 1 := by
  classical
  by_contra hcon
  have hbot : U ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact hcon ⟨x, hx, fun h1 => hx1 (by rw [h1]; exact Subgroup.one_mem _)⟩
  have hidx : ∀ H : Subgroup G, H ≤ E → H.relIndex E * Nat.card ↥H = Nat.card ↥E := by
    intro H hHE
    have h1 := (H.subgroupOf E).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHE).toEquiv] at h1
    exact h1
  have hU1 := hidx U hUE
  have hD1 := hidx D hDE
  have hbotE := hidx (U ⊓ D) (inf_le_left.trans hUE)
  have hcbot : Nat.card ↥(U ⊓ D) = 1 := by
    rw [hbot]; exact Subgroup.card_bot
  rw [hcbot, mul_one, hEcard] at hbotE
  have hle : (U ⊓ D).relIndex E ≤ U.relIndex E * D.relIndex E := Subgroup.relIndex_inf_le
  rw [hbotE] at hle
  have hUi : U.relIndex E ≤ p := by
    by_contra hlt
    have h2 : p + 1 ≤ U.relIndex E := by omega
    have h3 : (p + 1) * p ^ 3 ≤ U.relIndex E * Nat.card ↥U := Nat.mul_le_mul h2 hU
    rw [hU1, hEcard] at h3
    nlinarith [pow_pos hp.pos 3, pow_pos hp.pos 4]
  have hDi : D.relIndex E = p ^ 2 := by
    rw [hD, hEcard] at hD1
    have : D.relIndex E * p ^ 2 = p ^ 2 * p ^ 2 := by rw [hD1]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) this
  rw [hDi] at hle
  have h4 : U.relIndex E * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hUi
  have h5 : p ^ 4 ≤ p * p ^ 2 := le_trans hle h4
  have h6 : p * p ^ 2 < p ^ 4 := by
    have := hp.two_le
    nlinarith [pow_pos hp.pos 2]
  omega

theorem node158E3_of_D (h155 : Node155) (hD : Node158D) : Node158E3 := by
  classical
  intro G _ _ p A c L E h15 hF hout U hUE hU3
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  obtain ⟨D, hDA, hDcard, hDC⟩ := hD G p A c L E h15 hF hout'
  obtain ⟨b, hbUD, hb1⟩ := exists_ne_one_mem_inf_of_card hp hEcard hUE (hDA.trans h.A_le_E) hU3 hDcard
  have hCU : Subgroup.centralizer (U : Set G) ≤ lieNormalizer p E :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbUD.1)).trans (hDC b hbUD.2 hb1)
  exact Sec15FA.normalizer_le_of_centralizer_le hp hE hJ hUE
    (torusNormalizer_le_lieNormalizer hp E) hCU

end CFSG.RankThree.PartOne.S15K
