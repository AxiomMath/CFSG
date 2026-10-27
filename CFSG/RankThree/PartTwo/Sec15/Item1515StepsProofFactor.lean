module

import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1515

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_le_sup {K N C A : Subgroup G} (hK : K ≤ N ⊔ C)
    (hCA : C ≤ Subgroup.centralizer (A : Set G)) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hCN : C ≤ Subgroup.normalizer (N : Set G)) : ⁅K, A⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro k hk a ha
  have hk' : k ∈ ((N ⊔ C : Subgroup G) : Set G) := hK hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N C hCN] at hk'
  obtain ⟨n, hn, x, hx, rfl⟩ := hk'
  have hxa : x * a = a * x := (Subgroup.mem_centralizer_iff.mp (hCA hx) a ha).symm
  have h1 : ⁅n * x, a⁆ = n * (a * n⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc n * x * a * (n * x)⁻¹ * a⁻¹ = n * (x * a) * x⁻¹ * n⁻¹ * a⁻¹ := by group
      _ = n * (a * x) * x⁻¹ * n⁻¹ * a⁻¹ := by rw [hxa]
      _ = n * (a * n⁻¹ * a⁻¹) := by group
  rw [h1]
  exact mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (inv_mem hn))

theorem deltaZero_le_sup_of_item142 {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h142 : Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A) (h3L : 3 ∣ Nat.card L)
    (hnot : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) (Y : Subgroup G) :
    deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set N := L ⊔ pPrimeCoreOf 3 H with hN
  obtain ⟨Q, -, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) (bot_mem_invariantPiSubgroups H A _)
  let := ker142_normal (LB := lB A) h.isElemAbelian.1 h.mem_A
  obtain ⟨-, hcases⟩ := h142 Q hQ
  have hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 H ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    rcases hcases with ⟨⟨φ⟩, -⟩ | ⟨hK, -⟩
    · exfalso
      have hS := (isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)).1
      obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv h.toSec13Data hS φ
      exact hnot.false ψ
    · exact hK
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := Sec16.normalizer_zpowers_le_normalizer_L h h3L
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_sup hHL (le_normalizer_pPrimeCoreOf 3 H)
  have hAH : A ≤ H := h.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hCH : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ H :=
    (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le (by
      rw [Set.singleton_subset_iff]
      exact h.mem_A)).trans (centralizer_singleton_le_normalizer_zpowers c))
  have hcomm : ⁅k142 A (lB A) c, A⁆ ≤ N :=
    commutator_le_of_le_sup hK.le (pPrimeCoreOf_le 3 _) (hAH.trans hHN) (hCH.trans hHN)
  refine sSup_le fun Q hQ => ?_
  obtain ⟨⟨hQq, hQeq⟩, hQY⟩ := hQ
  have hQK : Q ≤ k142 A (lB A) c := le_delta hQq (hQY.trans inf_le_right)
  rw [hQeq]
  exact (Subgroup.commutator_mono hQK le_rfl).trans hcomm

theorem eq_inf_sup_pPrimeCoreOf_of_item142 {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h142 : Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A) (h3L : 3 ∣ Nat.card L)
    (hnot : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    {Y : Subgroup G} (hY4 : Y ∈ scriptY4 A (lB A))
    (hdec : Y = pPrimeCoreOf 3 Y ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    Y = (Y ⊓ L) ⊔ pPrimeCoreOf 3 Y := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set M := deltaZero A (lB A) (Y ⊓ H) with hM
  have hMY : M ≤ Y := (deltaZero_le _).trans inf_le_left
  have hMH : M ≤ H := (deltaZero_le _).trans inf_le_right
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := Sec16.normalizer_zpowers_le_normalizer_L h h3L
  have hLH : L ≤ H := (le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1).trans
    (centralizer_singleton_le_normalizer_zpowers c)
  have hO' : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 H) := (Nat.Prime.coprime_iff_not_dvd
    Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 H)
  exact eq_inf_sup_of_le_sup hY4.2.1 (pPrimeCoreOf_le 3 Y) (le_normalizer_pPrimeCoreOf 3 Y)
    hdec.le hMY (hMH.trans hHL) (deltaZero_le_sup_of_item142 h h142 h3L hnot Y) hO'
    (hLH.trans (le_normalizer_pPrimeCoreOf 3 H)) ((pPrimeCoreOf_le 3 H).trans hHL)

omit [Finite G] in
theorem pPrimeCoreOf_eq_pCoreOf_two {Y : Subgroup G}
    (h : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y) :
    pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y := by
  rw [pPrimeCoreOf, h]
  rfl

end CFSG.RankThree.PartTwo.Sec15.Proof1515
