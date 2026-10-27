module

public import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_le_pPrimeCoreOf {A B : Subgroup G} (hAc : IsMulCommutative A)
    (hBA : B ≤ A) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  set N := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hN
  set C := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hC
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAc.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)
  have hCB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le hBA
  have hBN : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := ((pPrimeCoreOf_le 3 _).trans hCB).trans hBN
  have hCA : C ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  rw [Subgroup.commutator_le]
  intro g hg a ha
  have hg' : g ∈ ((N : Set G) * (C : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N C hCN]
    exact hg
  obtain ⟨n, hn, k, hk, rfl⟩ := hg'
  have hka : k * a = a * k := (Subgroup.mem_centralizer_iff.mp (hCA hk) a ha).symm
  have key : ⁅n * k, a⁆ = n * (a * n⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc n * k * a * (n * k)⁻¹ * a⁻¹ = n * (k * a) * k⁻¹ * n⁻¹ * a⁻¹ := by group
      _ = n * (a * k) * k⁻¹ * n⁻¹ * a⁻¹ := by rw [hka]
      _ = n * (a * n⁻¹ * a⁻¹) := by group
  rw [key]
  exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hBN (hAB ha)) _).mp (N.inv_mem hn))

theorem yBOne_of_lB_eq_bot {A Y B : Subgroup G} (hAc : IsMulCommutative A)
    (hB : IsHyperplane A B) (hB0 : lB A B = ⊥) : YBOne A (lB A) Y B := by
  refine sSup_le fun Q hQ => ?_
  obtain ⟨⟨hQq, hQA⟩, hQY⟩ := hQ
  set N := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hN
  have hQC : Q ≤ Subgroup.centralizer (B : Set G) := hQY.trans inf_le_right
  have hQb : Q ≤ N ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    have h1 := hQq.2 B hB
    rw [inf_eq_left.mpr hQC] at h1
    have h2 : qBound A (lB A) B = N ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
      rw [qBound, hB0, sup_bot_eq]
    rwa [h2] at h1
  have hQN : Q ≤ N := by
    rw [hQA]
    exact (Subgroup.commutator_mono hQb le_rfl).trans (commutator_sup_le_pPrimeCoreOf hAc hB.1)
  set X := Y ⊓ Subgroup.centralizer (B : Set G) with hX
  have hXN : X ≤ Subgroup.normalizer ((N ⊓ X : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCoreOf 3 _ (Subgroup.mem_inf.mp hx).2, Subgroup.le_normalizer hx⟩
  have hcop : Nat.Coprime 3 (Nat.card (N ⊓ X : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  exact (le_inf hQN hQY).trans (le_pPrimeCoreOf inf_le_right hXN hcop)

theorem exists_isLBConfig_of_not_yBOne {A Y B : Subgroup G} (hAc : IsMulCommutative A)
    (hB : IsHyperplane A B) (h : ¬ YBOne A (lB A) Y B) :
    ∃ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb := by
  by_contra hno
  push Not at hno
  exact h (yBOne_of_lB_eq_bot hAc hB (lB_eq_bot hno))

theorem step148YB_of_shape (hS : Step148YBShape) : Step148YB := by
  intro G _ _ A c L h Y hY hs B hB hnot
  obtain ⟨b, d, Lb, hconf⟩ := exists_isLBConfig_of_not_yBOne h.isElemAbelian.1 hB hnot
  obtain ⟨YB, hYB, htype, hle, hYBle⟩ := hS G A c L h Y hY hs B hB hnot b d Lb hconf
  exact ⟨YB, hYB, htype, hle, b, d, Lb, hconf, hYBle⟩

theorem rank3II_14_8_of_steps_of_lB_eq_bot
    (hN : Step148Normal) (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType)
    (hLift : Step148Lift) (hD4 : Step148D4) (hOne : Step148One) (hRank : Step148Rank)
    (hPGL : Step148PGL) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) : Item148 A (lB A) :=
  rank3II_14_8_of_cases hN h fun _ hY hs ih =>
    item148Cases_of_steps_of_yBOne hCore hPoint hKT hLift hD4 hOne hRank hPGL h hY hs ih
      fun B hB => yBOne_of_lB_eq_bot h.isElemAbelian.1 hB (hLB B hB)

end CFSG.RankThree.PartTwo.Sec14
