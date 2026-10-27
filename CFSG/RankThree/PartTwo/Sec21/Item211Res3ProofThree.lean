module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofChoice

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item2130ThreeY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2130 G A E U c L → 27 ≤ Nat.card (A ⊓ L : Subgroup G) →
      ∃ b ∈ A ⊓ L, b ≠ 1 ∧ ∃ Y ∈ thetaComponentsAt 3 b, Y ∈ lZeroUnion A ∧
        ∃ I : Subgroup G, I ≤ L ∧ Y = I ⊔ inSubgroup (aschbacherSolvableCore 3) Y

namespace Item211Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem not_le_thetaQuotCentralizer {A Y : Subgroup G} (hY0 : Y ∈ lZeroUnion A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) : ¬ A ≤ Sec4.thetaQuotCentralizer Y := by
  intro hle
  obtain ⟨E', -, hE'A, hYE'⟩ := mem_lZeroUnion_iff.mp hY0
  obtain ⟨-, U', hU', hU'E'⟩ := mem_lZero_iff.mp hYE'
  apply hU'E'
  obtain ⟨hU'Y, -, -⟩ := mem_invariantPiSubgroups_iff.mp hU'
  have h1 : ⁅Y, E'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y :=
    (Sec6.commutator_le_theta_iff (hE'A.trans hAY)).mpr (hE'A.trans hle)
  exact (Subgroup.commutator_mono hU'Y le_rfl).trans h1

theorem mem_thetaQuotCentralizer_of_eq_sup {Y I : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hIc : I ≤ Subgroup.centralizer ({c} : Set G))
    (hY : Y = I ⊔ inSubgroup (aschbacherSolvableCore 3) Y) :
    c ∈ Sec4.thetaQuotCentralizer Y := by
  set θY := inSubgroup (aschbacherSolvableCore 3) Y with hθY
  have hIY : I ≤ Y := hY ▸ le_sup_left
  have hIN : I ≤ Subgroup.normalizer (θY : Set G) :=
    hIY.trans (Sec6.le_normalizer_theta Y)
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
  have hl' : l ∈ ((I ⊔ θY : Subgroup G) : Set G) := by rw [← hY]; exact hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right I θY hIN] at hl'
  obtain ⟨i, hi, t, ht, rfl⟩ := hl'
  have hci : c * i * c⁻¹ = i := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hIc hi)).symm, mul_inv_cancel_right]
  have hct : c * t * c⁻¹ ∈ θY :=
    (Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_theta Y hcN) t).mp ht
  have e : (i * t)⁻¹ * (c * (i * t) * c⁻¹) = t⁻¹ * (c * t * c⁻¹) := by
    have e1 : c * (i * t) * c⁻¹ = (c * i * c⁻¹) * (c * t * c⁻¹) := by group
    rw [e1, hci]
    group
  rw [e]
  exact θY.mul_mem (θY.inv_mem ht) hct

end Item211Res3Proof

open Item211Res3Proof Item211Res2Proof

theorem item2130LocalThree_of (h45 : Sec4.Item4_5) (h3Y : Item2130ThreeY) :
    Item2130LocalThree := by
  intro G _ _ A E U c L hcfg h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair := hcfg.pair
  have hG := hpair.standing.toTheoremFourHyp
  obtain ⟨⟨hcE, -⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hLs
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hcB : c ∉ A ⊓ L := fun h => hcfg.not_mem h.2
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA inf_le_left hcB hcfg.card_eq
  obtain ⟨b, hbB, hb1, Y, hYb, hY0, I, hIL, hY⟩ := h3Y G A E U c L hcfg h27
  have hbA : b ∈ A := hbB.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 Y hYb
  set D := A ⊓ Sec4.thetaQuotCentralizer Y with hD
  have hcD : c ∈ D := ⟨hcA, mem_thetaQuotCentralizer_of_eq_sup (hAY hcA) (hIL.trans hLC) hY⟩
  have hBD : A ⊓ L ≤ D := by
    intro b' hb'
    have hBe : ∀ x ∈ A ⊓ L, x ^ 3 = 1 := fun x hx => hAe.2 x hx.1
    obtain ⟨w, hwW, hwB, hwc⟩ := hcfg.full b' hb'
    obtain ⟨k, hk3, hkc⟩ := exists_pow_conj_of_isPGroup hBe hb' hwB hwc
    have hwkB := pow_conj_eq_of_conj_eq hwB k
    have hle : Subgroup.zpowers (w ^ k) ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have h1 := hwkB b hbB
      calc w ^ k * b = w ^ k * b * (w ^ k)⁻¹ * w ^ k := by group
        _ = b * w ^ k := by rw [h1]
    have hwY : w ^ k ∈ Subgroup.normalizer (Y : Set G) :=
      le_normalizer_of_isPGroup h45 hG hb3 hb1 hk3 hle Y hYb (Subgroup.mem_zpowers _)
    have hwA : w ^ k ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hwW k
    have h1 : w ^ k * c * (w ^ k)⁻¹ ∈ D :=
      ⟨(Subgroup.mem_normalizer_iff.mp hwA c).mp hcA,
        Sec6.conj_mem_thetaQuotCentralizer hcD.2 hwY⟩
    rw [hkc] at h1
    have h2 := D.mul_mem (D.inv_mem hcD) h1
    rwa [inv_mul_cancel_left] at h2
  have hAD : A ≤ D := hAB ▸ sup_le (Subgroup.zpowers_le.mpr hcD) hBD
  exact not_le_thetaQuotCentralizer hY0 hAY fun x hx => (hAD hx).2

end CFSG.RankThree.PartTwo.Sec21
