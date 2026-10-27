module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item1446

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_le_pPrimeCoreOf {A D : Subgroup G} {e : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (heA : e ∈ A) (hDA : D ≤ A) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), D⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) := by
  set N := pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) with hN
  set M := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hM
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨e, heA⟩))
  have hCAe : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA)
  have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans hCAe).trans (le_normalizer_pPrimeCoreOf 3 _)
  have hDN : D ≤ Subgroup.normalizer (N : Set G) :=
    (hDA.trans hAe).trans (le_normalizer_pPrimeCoreOf 3 _)
  rw [Subgroup.commutator_le]
  intro x hx δ hδ
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N M hMN] at hx
  obtain ⟨n, hn, m, hm, rfl⟩ := hx
  have hmδ : m * δ = δ * m := by
    have hmA : m ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hm
    exact (Subgroup.mem_centralizer_iff.mp hmA δ (hDA hδ)).symm
  have hδn : δ * n⁻¹ * δ⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hDN hδ) n⁻¹).mp (N.inv_mem hn)
  have heq : ⁅n * m, δ⁆ = n * (δ * n⁻¹ * δ⁻¹) := by
    rw [commutatorElement_def]
    calc n * m * δ * (n * m)⁻¹ * δ⁻¹ = n * (m * δ) * m⁻¹ * n⁻¹ * δ⁻¹ := by group
      _ = n * (δ * m) * m⁻¹ * n⁻¹ * δ⁻¹ := by rw [hmδ]
      _ = n * (δ * n⁻¹ * δ⁻¹) := by group
  rw [heq]
  exact N.mul_mem hn hδn

theorem commutator_inf_centralizer_mem {A D R : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hDA : D ≤ A) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) {b : G} (hbA : b ∈ A) :
    ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ ∈
        invariantPiSubgroups (Subgroup.centralizer ({b} : Set G)) A (piOf 2) ∧
      ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ =
        ⁅⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆, D⁆ ∧
      ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ ≤ R := by
  set X := R ⊓ Subgroup.centralizer ({b} : Set G) with hX
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_inf hAR (hAb.trans Subgroup.le_normalizer)
  have hDX : D ≤ Subgroup.normalizer (X : Set G) := hDA.trans hAX
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hDA hy⟩ ⟨x, hx⟩)
  have hTX : ⁅X, D⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hDX
  have hcop : Nat.Coprime (Nat.card D) (Nat.card X) := by
    obtain ⟨m, hm⟩ :=
      (isPGroup_three_of_isElemAbelian (Sec5.isElemAbelian_of_le hA hDA)).exists_card_eq
    obtain ⟨n, hn⟩ := (hR2.to_le (inf_le_left : X ≤ R)).exists_card_eq
    rw [hm, hn]
    exact Nat.Coprime.pow m n (by norm_num)
  refine ⟨⟨hTX.trans inf_le_right, ?_, ?_⟩, ?_, hTX.trans inf_le_left⟩
  · exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hR2.to_le (hTX.trans inf_le_left))
  · exact Sec14.le_normalizer_commutator hAX hAD
  · exact (CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime X D hcop hDX).symm

theorem exists_commutator_ne_bot_of_le {A B D R : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hBA : B ≤ A) (hB9 : 9 ≤ Nat.card B) (hDB : D ≤ B)
    (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hDR : ¬ R ≤ Subgroup.centralizer (D : Set G)) :
    ∃ b ∈ B, b ≠ 1 ∧
      ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ ∈
        invariantPiSubgroups (Subgroup.centralizer ({b} : Set G)) A (piOf 2) ∧
      ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ =
        ⁅⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆, D⁆ ∧
      ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ ≠ ⊥ ∧
      ⁅R ⊓ Subgroup.centralizer ({b} : Set G), D⁆ ≤ R := by
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hA hBA
  have hR3 : ¬ 3 ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_three_of_isPGroup_two hR2)
  obtain ⟨b, hbB, hb1, hb⟩ : ∃ b ∈ B, b ≠ 1 ∧
      ¬ R ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (D : Set G) := by
    by_contra hall
    push Not at hall
    exact hDR (le_centralizer_of_forall_ne_one hBe hB9 (hBA.trans hAR) hR3 hall)
  obtain ⟨hT, hTD, hTR⟩ := commutator_inf_centralizer_mem hA (hDB.trans hBA) hR2 hAR (hBA hbB)
  refine ⟨b, hbB, hb1, hT, hTD, fun hbot => ?_, hTR⟩
  exact hb (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

end CFSG.RankThree.PartTwo.Sec16.Proof1613Res

