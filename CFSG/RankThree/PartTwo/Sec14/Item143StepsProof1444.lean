module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSignalizer
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

@[expose] noncomputable def Item143For1444 (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Prop :=
  ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
    ∃ N : Subgroup G, N ≤ delta A LB (Subgroup.centralizer ({a} : Set G)) ∧
      delta A LB (Subgroup.centralizer ({a} : Set G)) =
        N ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∧
      A ≤ Subgroup.normalizer (N : Set G) ∧
      ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer ({a} : Set G)) A (piCompl 3),
        S ≤ Subgroup.normalizer (N : Set G)

@[expose] noncomputable def Item143For1444S14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item143For1444 A (lB A)

theorem pPrimeCoreOf_centralizer_mem_invariantPiSubgroups {a : G} (ha : a ∈ A)
    (hAab : IsMulCommutative A) :
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∈
      invariantPiSubgroups (Subgroup.centralizer ({a} : Set G)) A (piCompl 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨(pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr ha)), ?_, ?_⟩
  · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
  · exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
      (le_normalizer_pPrimeCoreOf 3 _)

theorem commutator_le_delta_of_normalizer (hAab : IsMulCommutative A) {a : G} (ha : a ∈ A)
    {N : Subgroup G} (hNΔ : N ≤ delta A LB (Subgroup.centralizer {a}))
    (hΔ : delta A LB (Subgroup.centralizer {a}) =
      N ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hSN : ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer ({a} : Set G)) A (piCompl 3),
      S ≤ Subgroup.normalizer (N : Set G))
    {Q S : Subgroup G} (hQ : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ≤ delta A LB (Subgroup.centralizer {a}) := by
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hO'C : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hO'N : O' ≤ Subgroup.normalizer (N : Set G) :=
    hSN O' (pPrimeCoreOf_centralizer_mem_invariantPiSubgroups ha hAab)
  have hQΔ : Q ≤ delta A LB (Subgroup.centralizer {a}) := le_delta hQ.1.1 hQ.2
  have hQN : Q ≤ N := by
    rw [hQ.1.2]
    refine (Subgroup.commutator_mono (hQΔ.trans hΔ.le) le_rfl).trans ?_
    rw [CFSG.RankThreeEvenClassification.Helpers.normalized_sup_commutator_eq_of_fixed N O' A
      hO'N hO'C]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hSN' : S ≤ Subgroup.normalizer (N : Set G) :=
    hSN S ⟨hS.1, hS.2.1, le_sup_left.trans hS.2.2⟩
  have hQSN : ⁅Q, S⁆ ≤ N :=
    (Subgroup.commutator_mono hQN le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hSN')
  exact hQSN.trans hNΔ

theorem rank3II_14_4_4_of_for1444_at (h143 : Concl143 A LB) (hF : Item143For1444 A LB)
    (hAab : IsMulCommutative A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {Q S : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
  obtain ⟨N, hNΔ, hΔ, hAN, hSN⟩ := hF a ha ha1 hΩ
  obtain ⟨-, hQS⟩ := commutator_mem_invariantPiSubgroups ⟨hQ.1.1, hQ.2⟩ hS
  have hQSK := commutator_le_delta_of_normalizer hAab ha hNΔ hΔ hAN hSN hQ hS
  obtain ⟨Q', hQ', hle⟩ := exists_le_mem_maxInvariantPiSubgroups
    (⟨hQSK, hQS.2.1, hQS.2.2⟩ : ⁅Q, S⁆ ∈ invariantPiSubgroups
      (delta A LB (Subgroup.centralizer {a})) A (piCompl 3))
  exact ⟨mem_scriptQ_of_le (h143 a ha ha1 hΩ Q' hQ').1 hle hQS.2.2, hQS.1⟩

theorem rank3II_14_4_4_of_for1444 (h142 : Concl142 A LB) (h143 : Concl143 A LB)
    (hF : Item143For1444 A LB) (hAab : IsMulCommutative A) : Item1444 A LB := by
  intro a ha ha1 Q hQ S hS
  by_cases hΩ : Subgroup.zpowers a ∈ omegaA A
  · exact rank3II_14_4_4_of_mem_omegaA h142 hΩ hQ hS
  · exact rank3II_14_4_4_of_for1444_at h143 hF hAab ha ha1 hΩ hQ hS

theorem item1444S14_of_for1444 (h142 : Concl142S14) (h143 : Concl143S14)
    (hF : Item143For1444S14) : Item1444S14 :=
  fun G _ _ A c L h => rank3II_14_4_4_of_for1444 (h142 G A c L h) (h143 G A c L h)
    (hF G A c L h) h.isE27'.1.1

end CFSG.RankThree.PartTwo.Sec14
