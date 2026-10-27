module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec12.Item128Bar

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

section

open CFSG.RankThree.PartTwo.Sec14
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]

theorem exists_isPoint148Q_of (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (hΩ : Step148PointOmega) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h143 : Item143Q A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {B : Subgroup G}
    (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)))
    (hHJ : Subgroup.zpowers b ∉ omegaA A → HJConfig143Q A b →
      ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le) :
    ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le := by
  have hD := h.toSec13Data
  have hAc : IsMulCommutative A := hD.isElemAbelian.1
  have hbA : b ∈ A := hB.1 hb
  have hQB : Q ≤ Subgroup.centralizer (B : Set G) := hQY.trans inf_le_right
  have hQb' : Q ≤ Subgroup.centralizer ({b} : Set G) :=
    hQB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hQA : Q = ⁅Q, A⁆ := hQ.2
  have hQinv : Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) := hQ.1.1
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  have hcontra : ∀ N : Subgroup G, Nat.Coprime 3 (Nat.card N) →
      Y ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (N : Set G) → Q ≤ N → False := by
    intro N hN hYN hQN
    exact hQb ((le_inf hQN (hQY.trans (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hb))))).trans (inf_le_pPrimeCoreOf148 hYN hN))
  by_cases hbΩ : Subgroup.zpowers b ∈ omegaA A
  ·
    obtain ⟨Lb, hLb⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
      hD.card_eq hbΩ
    have hLbA : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb
    have hS : Sec14Std G A b Lb := { h with zpowers_mem_omegaA := hbΩ, mem_lA := hLbA }
    set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHdef
    have hCH : Subgroup.centralizer ({b} : Set G) ≤ H := by
      rw [← centralizer_zpowers148]
      exact Subgroup.centralizer_le_normalizer _
    have hQH : Q ∈ invariantPiSubgroups H A (piCompl 3) :=
      ⟨hQb'.trans hCH, hQinv.2.1, hQinv.2.2⟩
    obtain ⟨Qs, hQs, hQQs⟩ := exists_le_mem_maxInvariantPiSubgroups hQH
    obtain ⟨hQsmem, halt⟩ := h142 G A b Lb hS Qs hQs
    have hAH : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (hAb.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
    have hYH : Y ⊓ Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (inf_le_right.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
    rcases halt with ⟨-, hQsK, hOK, hcard⟩ | ⟨hK, -⟩
    ·
      exfalso
      rw [← hHdef] at hOK hcard
      set K := k142 A (lB A) b with hKdef
      have hidx : ((pPrimeCoreOf 3 H).subgroupOf K).index = 2 := by
        have h1 := Subgroup.card_mul_index ((pPrimeCoreOf 3 H).subgroupOf K)
        have h2 : Nat.card ↥((pPrimeCoreOf 3 H).subgroupOf K) = Nat.card (pPrimeCoreOf 3 H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
        rw [h2, hcard] at h1
        have hpos : 0 < Nat.card (pPrimeCoreOf 3 H) := Nat.card_pos
        have h3 : Nat.card (pPrimeCoreOf 3 H) * ((pPrimeCoreOf 3 H).subgroupOf K).index =
            Nat.card (pPrimeCoreOf 3 H) * 2 := by rw [h1, mul_comm]
        exact Nat.eq_of_mul_eq_mul_left hpos h3
      have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q' hQ' =>
        hQ'.1.1.2.2
      have hQK : Q ≤ K := hQQs.trans (hQsK ▸ le_rfl)
      refine hcontra (pPrimeCoreOf 3 H) (coprime_card_pPrimeCoreOf 3 H) hYH ?_
      rw [hQA, Subgroup.commutator_le]
      intro x hx a ha
      have hxK : x ∈ K := hQK hx
      have hax : a * x⁻¹ * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAK ha) _).mp (K.inv_mem hxK)
      have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hxK⟩)
        (b := ⟨a * x⁻¹ * a⁻¹, hax⟩)).mpr ?_
      · rw [Subgroup.mem_subgroupOf] at hmem
        rw [commutatorElement_def]
        simpa [mul_assoc] using hmem
      · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        constructor
        · intro hx'
          exact (Subgroup.mem_normalizer_iff.mp (hAH ha) _).mp ((pPrimeCoreOf 3 H).inv_mem hx')
        · intro hax'
          have := (Subgroup.mem_normalizer_iff.mp (hAH (A.inv_mem ha)) _).mp hax'
          simpa [mul_assoc] using this
    ·
      have hQsK : Qs ≤ k142 A (lB A) b := le_delta hQsmem.1 (hQsmem.2.trans hCH)
      have hLbN : A ≤ Subgroup.normalizer (Lb : Set G) := hLbA.2.1
      have h3 : 3 ∣ Nat.card Lb := three_dvd_card_of_types148 (h.chosen136.2 b hbΩ Lb hLbA).1
      have hCLb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Lb : Set G) :=
        centralizer_le_normalizer_of_three_dvd hS h3
      have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
      have hLbH : Lb ≤ H := (le_centralizer_of_mem_thetaComponentsAt hLbA.1).trans hCH
      have hM : A ≤ Subgroup.normalizer
          ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) :=
        le_normalizer_sup (A := A) hLbN hAH
      have hCM : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ Subgroup.normalizer
          ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) := by
        have h1 : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
            Subgroup.centralizer ({b} : Set G) := (pPrimeCoreOf_le 3 _).trans hCA
        exact le_normalizer_sup (A := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
          (h1.trans hCLb) ((h1.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H))
      have hQLb : Q ≤ Lb ⊔ pPrimeCoreOf 3 H := by
        rw [hQA]
        refine (Subgroup.commutator_mono (hQQs.trans (hQsK.trans hK.le)) le_rfl).trans ?_
        exact commutator_sup_le148 hM hCM (pPrimeCoreOf_le 3 _)
      obtain ⟨K, hK', hKΔ, hKLb⟩ :=
        hΩ G A c L h Y hY hs hYB B hB Q hQ hQY b hb hbΩ Lb hLbA hQLb hQb
      exact ⟨b, K, Lb, hB, hQ, hQY, hb, hb1, hK', hKΔ, hKLb, hLbA.1, Or.inl ⟨hbΩ, hLbA⟩⟩
  ·
    obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty
      (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3)
    obtain ⟨-, halt⟩ := h143 b hbA hb1 hbΩ Qs hQs
    rcases halt with h1 | h2
    ·
      exfalso
      have hQΔ : Q ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := le_delta hQ.1 hQb'
      have hcomm := commutator_sup_le_pPrimeCoreOf hAc (Subgroup.zpowers_le.mpr hbA)
      rw [centralizer_zpowers148] at hcomm
      refine hcontra (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
        (coprime_card_pPrimeCoreOf 3 _)
        (inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 _)) ?_
      rw [hQA]
      exact (Subgroup.commutator_mono (hQΔ.trans h1.le) le_rfl).trans hcomm
    · exact hHJ hbΩ h2

theorem step148PointQ_of (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143QS14) (hΩ : Step148PointOmega) (hHJ : Step148PointHJQ) : Step148Point := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hQb
  exact exists_isPoint148Q_of h422 h45 h142 hΩ h (h143 G A c L h) hY hs hYB hB hQ hQY hb hb1 hQb
    fun hbΩ h2 => hHJ G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb h2

end

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
