module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeFrame
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
import CFSG.GroupTheory.CoprimeCentralizerRank
import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData

abbrev ofThreeCalC
    (M : Subgroup G) (K : Fin 3 → Subgroup G)
    (hK : ∀ i, K i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC M)
    (hKi : Function.Injective K)
    (hK3 : ∀ i, CFSG.Open.pRank 3 (K i) = 1)
    (S : Subgroup G)
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S (K 0 ⊔ K 1 ⊔ K 2)) :
    SylowThreeData G where
  M := M
  Lf := K
  L := K 0 ⊔ K 1 ⊔ K 2
  S := S
  hLM := fun i => (hK i).1.le
  hLnorm := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact Subgroup.le_normalizer
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.calC_le_normalizer_of_ne
        (hK i) (hK j) (fun h => hij (hKi h))
  hcomm := fun i j hij => by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.commutator_mem_pCoreOf_of_ne
      (hK i) (hK j) (fun h => hij (hKi h)) ha hb
  hperf := fun i => (hK i).2.1
  hrank := hK3
  hL := rfl
  hS := hS

theorem one_le_pRank_inf_centralizer_of_le_axis_pair (d : SylowThreeData G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ∀ k, p ∣ Nat.card (d.Lf k))
    {i j : Fin 3} (hij : i ≠ j) {B : Subgroup G}
    (hB : B ≤ d.A i ⊔ d.A j) :
    1 ≤ CFSG.Open.pRank p (d.M ⊓ Subgroup.centralizer (B : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hthird : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide
  obtain ⟨k, hki, hkj⟩ := hthird i j hij
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(d.Lf k)) p (hpK k)
  let R : Subgroup G := Subgroup.zpowers (x : G)
  have hxordG : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hxord
  have hRle : R ≤ d.Lf k := Subgroup.zpowers_le.mpr x.2
  have hRcard : Nat.card R = p ^ 1 := by
    rw [Nat.card_zpowers, hxordG, pow_one]
  have hRea : CFSG.Open.IsElemAbelian p R :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hxordG]; exact pow_orderOf_eq_one _)
  have hR : IsPGroup p ↥R := IsPGroup.of_card (n := 1) hRcard
  have hA_AA : ∀ l : Fin 3, d.A l ≤ d.AA := fun l => by
    rw [d.A_eq_AA_inf_Lf l]
    exact inf_le_left
  have hBAA : B ≤ d.AA := hB.trans (sup_le (hA_AA i) (hA_AA j))
  have hB3 : IsPGroup 3 ↥B := IsPGroup.to_le d.isElemAbelian_AA.isPGroup hBAA
  have hAA_M : d.AA ≤ d.M := by
    rw [d.AA_def]
    exact sup_le (sup_le ((d.A_le_H 0).trans ((d.H_le_Lf 0).trans (d.hLM 0)))
      ((d.A_le_H 1).trans ((d.H_le_Lf 1).trans (d.hLM 1))))
      ((d.A_le_H 2).trans ((d.H_le_Lf 2).trans (d.hLM 2)))
  have hRM : R ≤ d.M := hRle.trans (d.hLM k)
  let N : Subgroup G := CFSG.Open.pCoreOf 2 d.M
  have hMN : d.M ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 d.M
  have hNM : N ≤ d.M := CFSG.LieType.BorelTits.pCoreOf_le 2 d.M
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.M
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := hRM.trans hMN
  have hAiN : d.A i ≤ Subgroup.normalizer (N : Set G) :=
    (hA_AA i).trans (hAA_M.trans hMN)
  have hAjN : d.A j ≤ Subgroup.normalizer (N : Set G) :=
    (hA_AA j).trans (hAA_M.trans hMN)
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := hBAA.trans (hAA_M.trans hMN)
  have hi : ⁅d.A i, R⁆ ≤ N := by
    simpa only [N, Subgroup.commutator_comm] using
      (Subgroup.commutator_mono hRle ((d.A_le_H i).trans (d.H_le_Lf i))).trans
        (d.hcomm k i hki)
  have hj : ⁅d.A j, R⁆ ≤ N := by
    simpa only [N, Subgroup.commutator_comm] using
      (Subgroup.commutator_mono hRle ((d.A_le_H j).trans (d.H_le_Lf j))).trans
        (d.hcomm k j hkj)
  have hjoin := CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
    (d.A i) (d.A j) R N hi hj hAiN hAjN
  have hcomm : ⁅R, B⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hB (le_refl R)).trans hjoin
  have hpN : ¬ p ∣ Nat.card ↥N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 hp hp2
  have h3N : ¬ 3 ∣ Nat.card ↥N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
  have hle := CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
    (M := d.M) (N := N) (R := R) (B := B) hRM hNM hRN hBN hR hB3 hpN h3N hcomm
  have h1R : 1 ≤ CFSG.Open.pRank p R := by
    have h := CFSG.SectionRank.le_pRank (p := p) hp.one_lt (le_refl R) hRea (k := 1) hRcard
    simpa using h
  exact h1R.trans hle

end SylowThreeData

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_conj_mem_three_calC_of_pRank_le_three {M : Subgroup G}
    (K : Fin 3 → Subgroup G) (hK : ∀ i, K i ∈ calC M)
    (hKi : Function.Injective K)
    (hK3 : ∀ i, CFSG.Open.pRank 3 (K i) = 1)
    (hM3 : CFSG.Open.pRank 3 M ≤ 3)
    {m : G} (hm : m ∈ M) (i : Fin 3) :
    ∃ j, (K i).map (MulAut.conj m).toMonoidHom = K j := by
  classical
  let f : MulAut G := MulAut.conj m
  let L : Subgroup G := (K i).map f.toMonoidHom
  have hMmap : M.map f.toMonoidHom = M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.mp
      (Subgroup.le_normalizer hm)
  have hL : L ∈ calC M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map M f hMmap (hK i)
  have hL3 : CFSG.Open.pRank 3 L = 1 := by
    show CFSG.Open.pRank 3 ((K i).map f.toMonoidHom) = 1
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_pRank_map_aut 3 (K i) f, hK3 i]
  by_contra hcon
  push Not at hcon
  have h01 : K 0 ≠ K 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hKi h)
  have h02 : K 0 ≠ K 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hKi h)
  have h12 : K 1 ≠ K 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hKi h)
  have hcard3 : ({K 0, K 1, K 2} : Finset (Subgroup G)).card = 3 :=
    Finset.card_eq_three.2 ⟨K 0, K 1, K 2, h01, h02, h12, rfl⟩
  have hnot : L ∉ ({K 0, K 1, K 2} : Finset (Subgroup G)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    exacts [hcon 0 h, hcon 1 h, hcon 2 h]
  let S : Finset (Subgroup G) := insert L {K 0, K 1, K 2}
  have hcard : S.card = 4 := by
    rw [show S = insert L {K 0, K 1, K 2} from rfl, Finset.card_insert_of_notMem hnot, hcard3]
  have hS : ∀ A ∈ S, A ∈ calC M := by
    intro A hA
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    exacts [hL, hK 0, hK 1, hK 2]
  have hZ : ∀ A ∈ S, ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 A)) := by
    intro A hA
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        hL.2.2 (le_of_eq hL3)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        (hK 0).2.2 (le_of_eq (hK3 0))
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        (hK 1).2.2 (le_of_eq (hK3 1))
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        (hK 2).2.2 (le_of_eq (hK3 2))
  have hd : ∀ A ∈ S, 3 ∣ Nat.card A := by
    intro A hA
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one hL3
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one (hK3 0)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one (hK3 1)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one (hK3 2)
  have hle := P22fin3.card_le_pRank_of_finset (X := M) (S := S) Nat.prime_three (by norm_num)
    hS hZ hd
  rw [hcard] at hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
