module

public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec17.Item171Proof

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec17.Proof171Steps CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Delta


theorem delta_le_of_not_mem_omegaAQ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h143 : Ronan148Q.Item143Q A (lB A)) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1)
    (hbΩ : Subgroup.zpowers b ∉ omegaA A) :
    delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤
      oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  set K := oPrimeResidualOf 3 D with hK
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty D A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 b hb hb1 hbΩ Qs hQs
  rcases halt with h1 | ⟨b', d, Lb', hb'Ω, -, -, -, -, -, -, X, hDX, -, hcase⟩
  · exact h1.le.trans (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
  have hXD : X ≤ D := le_sup_right.trans hDX.ge
  have hXK : X ≤ K := by
    rcases hcase with ⟨hXθ, hXeq, -⟩ | ⟨-, ⟨𝒳, h𝒳, -, hX𝒳⟩, htypes⟩
    ·
      obtain ⟨hb'A, hb'3, -⟩ := zpowers_mem_omegaA_iff.mp hb'Ω
      have hb'1 : b' ≠ 1 := by
        rintro rfl
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb'3
        norm_num at hb'3
      have hne : Subgroup.zpowers b ≠ Subgroup.zpowers b' := fun heq => hbΩ (heq ▸ hb'Ω)
      have hB := isHyperplane_closure_pair h.isE27' hb hb'A hb1 hb'1 hne
      have hLBX : lB A (Subgroup.closure {b, b'}) ≤ X := by
        rw [hXeq]
        exact le_sup_left
      have hLBK := lB_le_oPrimeResidualOf h hB (hLBX.trans hXD)
      have hXp : Group.IsPerfect ↥X := Sec6.isPerfect_of_mem_thetaComponentsAt hXθ
      refine le_of_isPerfect_of_le_sup hXp hLBX (le_normalizer_theta X) (isSolvable_theta X)
        (theta_le X) hXeq.le hLBK ?_
      exact hXD.trans (le_normalizer_oPrimeResidualOf Subgroup.le_normalizer)
    ·
      have hXp : Group.IsPerfect ↥X := by
        rw [hX𝒳]
        exact isPerfect_sSup fun M hM => Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hM)
      have hX3 := eq_oPrimeResidualOf_of_quot hXp (oPrimeResidual_eq_top_of_types143 htypes)
      rw [hX3]
      exact oPrimeResidualOf_mono_three hXD
  exact hDX.le.trans
    (sup_le (sup_le_sup_right le_sup_right _) (le_sup_of_le_left (le_sup_of_le_left hXK)))

theorem deltaZero_le_yb171_of_itemsQ {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142R)
    (h143 : Ronan148Q.Item143Q A (lB A))
    {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    deltaZero A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ yb171 A b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hS14 := h.toSec14Std
  have hA27 : Late.IsE27 A := hS14.isE27'
  have hAmax := hS14.maximal_isElemAbelian
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set O := pPrimeCoreOf 3 C with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  set D := delta A (lB A) C with hDdef
  set K := oPrimeResidualOf 3 D with hK
  have hAb : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hb)
  have hOO' : O ⊔ O' ≤ D := by
    have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := lB A) hA27 hAmax hb
    exact le_delta hmem.1 hmem.2
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hDK : D ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oPrimeResidualOf hAD
  have hOK : O ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hOO').trans hDK
  have hO'K : O' ≤ Subgroup.normalizer (K : Set G) := (le_sup_right.trans hOO').trans hDK
  have hO'O : O' ≤ Subgroup.normalizer (O : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))).trans
      (le_normalizer_pPrimeCoreOf 3 C)
  have hO'A : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hyb : yb171 A b = ⁅O, A⁆ ⊔ K := rfl
  have hcore' : D ≤ K ⊔ O ⊔ O' →
      ∀ Q ∈ collectionIn (scriptQZero A (lB A)) C, Q ≤ yb171 A b := fun hle Q hQ =>
    hyb ▸ le_commutator_sup_of_le hQ.1.2 ((le_delta hQ.1.1 hQ.2).trans hle)
      hOK hO'K hAK hO'O hO'A
  have hcore : D ≤ K ⊔ O ⊔ O' → deltaZero A (lB A) C ≤ yb171 A b := fun hle =>
    sSup_le (hcore' hle)
  by_cases hbΩ : Subgroup.zpowers b ∈ omegaA A
  ·
    obtain ⟨Lb, hLb⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
      hD.card_eq hbΩ
    have hLbA : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb
    have hS14b : Sec14Std G A b Lb := { hS14 with zpowers_mem_omegaA := hbΩ, mem_lA := hLbA }
    have hS : Sec15R G A b Lb := ⟨hS14b, h.hypR⟩
    have hb3 : orderOf b = 3 := orderOf_eq_prime (hD.isElemAbelian.2 b hb) hb1
    set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHdef
    have hCH : C ≤ H := by
      rw [hC, hHdef, ← centralizer_zpowers148]
      exact Subgroup.centralizer_le_normalizer _
    have hΔH : delta A (lB A) H ≤ D := delta_normalizer_le hb hb3
    have hOH : pPrimeCoreOf 3 H ≤ O := pPrimeCoreOf_normalizer_le hb hb3 hAb
    have hAH : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (hAb.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
    refine sSup_le fun Q hQ => ?_
    have hQb : Q ≤ C := hQ.2
    have hQA : Q = ⁅Q, A⁆ := hQ.1.2
    have hQinv : Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) := hQ.1.1.1
    have hQH : Q ∈ invariantPiSubgroups H A (piCompl 3) :=
      ⟨hQb.trans hCH, hQinv.2.1, hQinv.2.2⟩
    obtain ⟨Qs, hQs, hQQs⟩ := exists_le_mem_maxInvariantPiSubgroups hQH
    obtain ⟨hQsmem, halt⟩ := h142 G A b Lb hS Qs hQs
    rcases halt with ⟨-, hQsK, hOKH, hcard⟩ | ⟨hKH, -⟩
    ·
      rw [← hHdef] at hOKH hcard
      set KH := k142 A (lB A) b with hKHdef
      have hidx : ((pPrimeCoreOf 3 H).subgroupOf KH).index = 2 := by
        have h1 := Subgroup.card_mul_index ((pPrimeCoreOf 3 H).subgroupOf KH)
        have h2 : Nat.card ↥((pPrimeCoreOf 3 H).subgroupOf KH) = Nat.card (pPrimeCoreOf 3 H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKH).toEquiv
        rw [h2, hcard] at h1
        have hpos : 0 < Nat.card (pPrimeCoreOf 3 H) := Nat.card_pos
        have h3 : Nat.card (pPrimeCoreOf 3 H) * ((pPrimeCoreOf 3 H).subgroupOf KH).index =
            Nat.card (pPrimeCoreOf 3 H) * 2 := by rw [h1, mul_comm]
        exact Nat.eq_of_mul_eq_mul_left hpos h3
      have hAKH : A ≤ Subgroup.normalizer (KH : Set G) := le_normalizer_sSup fun Q' hQ' =>
        hQ'.1.1.2.2
      have hQKH : Q ≤ KH := hQQs.trans (hQsK ▸ le_rfl)
      have hQOH : Q ≤ pPrimeCoreOf 3 H := by
        rw [hQA, Subgroup.commutator_le]
        intro x hx a ha
        have hxK : x ∈ KH := hQKH hx
        have hax : a * x⁻¹ * a⁻¹ ∈ KH :=
          (Subgroup.mem_normalizer_iff.mp (hAKH ha) _).mp (KH.inv_mem hxK)
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
      rw [hyb, hQA]
      exact le_sup_of_le_left (Subgroup.commutator_mono (hQA ▸ hQOH.trans hOH) le_rfl)
    ·
      refine hcore' ?_ Q hQ
      have hLbΔ : Lb ≤ D := by
        have h1 : Lb ≤ k142 A (lB A) b := by
          rw [hKH]
          exact le_sup_of_le_left le_sup_left
        exact h1.trans hΔH
      have hLbK : Lb ≤ K := by
        rw [eq_oPrimeResidualOf_of_types hLbA.1 (hS14.chosen136.2 b hbΩ Lb hLbA).1]
        exact oPrimeResidualOf_mono_three hLbΔ
      calc D ≤ delta A (lB A) H := delta_mono hCH
        _ = Lb ⊔ pPrimeCoreOf 3 H ⊔ O' := hKH
        _ ≤ K ⊔ O ⊔ O' := sup_le_sup_right (sup_le_sup hLbK hOH) _
  ·
    exact hcore (delta_le_of_not_mem_omegaAQ hS14 h143 hb hb1 hbΩ)


end Delta

theorem step171Delta0_ofQ
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142R)
    (h143 : Ronan148Q.Item143QS14) : Step171Delta0 :=
  fun G _ _ A c L _ h _ hb hb1 _ =>
    deltaZero_le_yb171_of_itemsQ h.toSec15R h422 h45 h142 (h143 G A c L h.toSec14Std) hb hb1

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
