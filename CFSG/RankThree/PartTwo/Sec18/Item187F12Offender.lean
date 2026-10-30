module

public import CFSG.RankThree.PartTwo.Sec18.Item187F10Wsub
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centerOf tripleOf)

variable {G : Type} [Group G] [Finite G]

private theorem isElemTwo_of_le_of_isElemAbelian {E D : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hDE : D ≤ E) : Sec3.IsElemTwo D :=
  ⟨fun a ha b hb => (isElemTwo_of_isElemAbelian hE).1 a (hDE ha) b (hDE hb),
    fun a ha => (isElemTwo_of_isElemAbelian hE).2 a (hDE ha)⟩

private theorem pRank_eq_of_card {S Q E : Subgroup G} (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 2 ^ CFSG.pRank 2 S) :
    CFSG.pRank 2 Q = CFSG.pRank 2 S := by
  have hp : (1 : ℕ) < 2 := by norm_num
  have hS := CFSG.SectionRank.pRank_coe_eq_openPRank 2 S
  have hQ := CFSG.SectionRank.pRank_coe_eq_openPRank 2 Q
  rw [hS] at hcard
  rw [hQ, hS]
  exact le_antisymm (CFSG.SectionRank.pRank_mono hp hQS)
    (CFSG.SectionRank.le_pRank hp hEQ hE hcard)

private theorem jG_one_le_of_le {S Q : Subgroup G} (hQS : Q ≤ S)
    (hrank : CFSG.pRank 2 Q = CFSG.pRank 2 S) : Sec3.jG Q 1 ≤ Sec3.jG S 1 := by
  unfold Sec3.jG
  refine sSup_le_sSup fun A hA => ?_
  obtain ⟨hAQ, hA2, hcard⟩ := Sec3.mem_famG.mp hA
  exact Sec3.mem_famG.mpr ⟨hAQ.trans hQS, hA2, by rw [hcard, hrank]⟩

private theorem jG_one_ge_of_forall {S Q : Subgroup G}
    (hrank : CFSG.pRank 2 Q = CFSG.pRank 2 S)
    (hall : ∀ A : Subgroup G, A ∈ Sec3.famG S 1 → A ≤ Q) : Sec3.jG S 1 ≤ Sec3.jG Q 1 := by
  unfold Sec3.jG
  refine sSup_le fun A hA => ?_
  obtain ⟨-, hA2, hcard⟩ := Sec3.mem_famG.mp hA
  exact le_sSup (Sec3.mem_famG.mpr ⟨hall A hA, hA2, by rw [hcard, hrank]⟩)

private theorem card_omegaG_le (S E W : Subgroup G) (hES : E ≤ S)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hWS : Sec3.omegaG W ≤ S)
    (hpow : 2 ^ CFSG.pRank 2 S ≤ 2 * Nat.card ↥E) :
    Nat.card ↥(Sec3.omegaG W) ≤
      2 * Nat.card (↥E ⧸ (E ⊓ Subgroup.centralizer (W : Set G)).subgroupOf E) *
        Nat.card ↥(Sec3.omegaG W ⊓ Subgroup.centralizer (E : Set G)) := by
  have hDE : E ⊓ Subgroup.centralizer (W : Set G) ≤ E := inf_le_left
  have hD2 : Sec3.IsElemTwo (E ⊓ Subgroup.centralizer (W : Set G)) :=
    isElemTwo_of_le_of_isElemAbelian hE hDE
  have hW1 : Sec3.IsElemTwo (Sec3.omegaG W) := Sec3.isElemTwo_omegaG W
  have hcomm : ∀ k ∈ E ⊓ Subgroup.centralizer (W : Set G), ∀ l ∈ Sec3.omegaG W,
      k * l = l * k := by
    intro k hk l hl
    have hkC : k ∈ Subgroup.centralizer (W : Set G) := (Subgroup.mem_inf.mp hk).2
    exact ((Subgroup.mem_centralizer_iff.mp hkC) l (Sec3.omegaG_le W hl)).symm
  have hsup2 : Sec3.IsElemTwo ((E ⊓ Subgroup.centralizer (W : Set G)) ⊔ Sec3.omegaG W) :=
    Sec3.isElemTwo_sup hD2 hW1 hcomm
  have hsupS : (E ⊓ Subgroup.centralizer (W : Set G)) ⊔ Sec3.omegaG W ≤ S :=
    sup_le (hDE.trans hES) hWS
  have hsupcard : Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊔ Sec3.omegaG W) ≤
      2 ^ CFSG.pRank 2 S :=
    Sec3.card_le_two_pow_pRank hsupS hsup2
  have hprod := Sec3.card_sup_mul_card_inf_of_commute hcomm
  have hquot : Nat.card ↥E = Nat.card ↥(E ⊓ Subgroup.centralizer (W : Set G)) *
      Nat.card (↥E ⧸ (E ⊓ Subgroup.centralizer (W : Set G)).subgroupOf E) := by
    have h := ((E ⊓ Subgroup.centralizer (W : Set G)).subgroupOf E).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv] at h
    exact h.symm
  have hint : Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊓ Sec3.omegaG W) ≤
      Nat.card ↥(Sec3.omegaG W ⊓ Subgroup.centralizer (E : Set G)) := by
    apply Subgroup.card_le_of_le
    intro x hx
    obtain ⟨hxD, hxW⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxW, ?_⟩
    have hxE : x ∈ E := (Subgroup.mem_inf.mp hxD).1
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (isElemTwo_of_isElemAbelian hE).1 e he x hxE
  have hDpos : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer (W : Set G)) := Nat.card_pos
  have key : Nat.card ↥(E ⊓ Subgroup.centralizer (W : Set G)) * Nat.card ↥(Sec3.omegaG W) ≤
      Nat.card ↥(E ⊓ Subgroup.centralizer (W : Set G)) *
        (2 * Nat.card (↥E ⧸ (E ⊓ Subgroup.centralizer (W : Set G)).subgroupOf E) *
          Nat.card ↥(Sec3.omegaG W ⊓ Subgroup.centralizer (E : Set G))) := by
    calc Nat.card ↥(E ⊓ Subgroup.centralizer (W : Set G)) * Nat.card ↥(Sec3.omegaG W)
        = Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊔ Sec3.omegaG W) *
          Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊓ Sec3.omegaG W) := hprod.symm
      _ ≤ 2 ^ CFSG.pRank 2 S *
          Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊓ Sec3.omegaG W) :=
          Nat.mul_le_mul hsupcard le_rfl
      _ ≤ (2 * Nat.card ↥E) *
          Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊓ Sec3.omegaG W) :=
          Nat.mul_le_mul hpow le_rfl
      _ = Nat.card ↥(E ⊓ Subgroup.centralizer (W : Set G)) *
          (2 * Nat.card (↥E ⧸ (E ⊓ Subgroup.centralizer (W : Set G)).subgroupOf E) *
            Nat.card ↥((E ⊓ Subgroup.centralizer (W : Set G)) ⊓ Sec3.omegaG W)) := by
          rw [hquot]
          ring
      _ ≤ _ := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hint)
  exact Nat.le_of_mul_le_mul_left key hDpos

variable {A M H : Subgroup G} {c : G} {X : Subgroup G}

private theorem exists_offender_aux (h186 : Item186H) (hX : MinCex A M H c X)
    (hbad : BadCase A M H X) :
    ∃ E : Subgroup G, E ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧ CFSG.Open.IsElemAbelian 2 E ∧
      ¬ E ≤ X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ∧
      Nat.card ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) ≤
        2 * Nat.card (↥E ⧸ (E ⊓ Subgroup.centralizer
          (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)).subgroupOf E) *
          Nat.card ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) ⊓ Subgroup.centralizer (E : Set G)) := by
  have hbad' := hbad
  unfold BadCase at hbad'
  obtain ⟨hm2, hnot1, -⟩ := hbad'
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  set Q := CFSG.Open.pCoreOf 2 X with hQdef
  have hQS : Q ≤ S := MinCex.pCoreOf_le_S h186 hX
  have hCQ : (X ⊓ Subgroup.centralizer (Wsub X S : Set G)) ⊓ S = Q :=
    MinCex.inf_centralizer_Wsub_inf_S h186 hX hbad
  have hWS : Wsub X S ≤ S := by
    intro w hw
    exact hQS (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX hw)).1
  have hW1S : Sec3.omegaG (Wsub X S) ≤ S := (Sec3.omegaG_le _).trans hWS
  obtain ⟨E, hES, hE, hcard, hEC⟩ : ∃ E : Subgroup G, E ≤ S ∧ CFSG.Open.IsElemAbelian 2 E ∧
      2 ^ (CFSG.pRank 2 S - 1) ≤ Nat.card E ∧
      ¬ E ≤ X ⊓ Subgroup.centralizer (Wsub X S : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hnot1
    obtain ⟨E0, hE0⟩ := Item181ThreeProof.exists_mem_famG_zero S
    obtain ⟨hE0S, hE02, hE0card⟩ := Sec3.mem_famG.mp hE0
    rw [Nat.sub_zero] at hE0card
    have hE0a : CFSG.Open.IsElemAbelian 2 E0 := isElemAbelian_of_isElemTwo hE02
    have hE0Q : E0 ≤ Q := by
      rw [← hCQ]
      refine le_inf (hcon E0 hE0S hE0a ?_) hE0S
      rw [hE0card]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have hrank : CFSG.pRank 2 Q = CFSG.pRank 2 S :=
      pRank_eq_of_card hQS hE0Q hE0a hE0card
    have hall : ∀ A' : Subgroup G, A' ∈ Sec3.famG S 1 → A' ≤ Q := by
      intro A' hA'
      obtain ⟨hA'S, hA'2, hA'card⟩ := Sec3.mem_famG.mp hA'
      have hA'C := hcon A' hA'S (isElemAbelian_of_isElemTwo hA'2) (le_of_eq hA'card.symm)
      rw [← hCQ]
      exact le_inf hA'C hA'S
    have hjQ : Sec3.jG Q 1 = Sec3.jG S 1 :=
      le_antisymm (jG_one_le_of_le hQS hrank) (jG_one_ge_of_forall hrank hall)
    have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
    have hXJ : X ≤ Subgroup.normalizer (Sec3.jG S 1 : Set G) := by
      rw [← hjQ]
      exact hXQ.trans (Item181ThreeProof.normalizer_le_normalizer_jG Q 1)
    have htriple : tripleOf S 1 = Sec3.omegaG (Sec3.jG S 1) :=
      (tripleOf_one_eq hm2).trans (Item181ThreeProof.fourChar_two S)
    rw [htriple]
    exact hXJ.trans (Item181ThreeProof.normalizer_le_normalizer_omegaG _)
  have hpow : 2 ^ CFSG.pRank 2 S ≤ 2 * Nat.card ↥E := by
    calc 2 ^ CFSG.pRank 2 S = 2 * 2 ^ (CFSG.pRank 2 S - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * Nat.card ↥E := Nat.mul_le_mul le_rfl hcard
  exact ⟨E, hES, hE, hEC, card_omegaG_le S E (Wsub X S) hES hE hW1S hpow⟩

section Certified


theorem MinCex.exists_offender (h1812 : Item181_2) (h184 : Item184_1) (h186 : Item186H)
    (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X)
    (hbad : BadCase A M H X) :
    ∃ E : Subgroup G, E ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧ CFSG.Open.IsElemAbelian 2 E ∧
      ¬ E ≤ X ⊓ Subgroup.centralizer (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ∧
      Nat.card ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) ≤
        2 * Nat.card (↥E ⧸ (E ⊓ Subgroup.centralizer
          (Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)).subgroupOf E) *
          Nat.card ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) ⊓ Subgroup.centralizer (E : Set G)) :=
  exists_offender_aux h186 hX hbad

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
