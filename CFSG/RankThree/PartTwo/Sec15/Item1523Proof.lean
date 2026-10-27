module

import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Sporadic.ON
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev k1523 (A : Subgroup G) (d : G) : Subgroup G :=
  oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({d} : Set G)))

structure Data1523 (A : Subgroup G) (L Y : Subgroup G) (d : G) : Prop where
  mem_d : d ∈ A
  ne_d : d ≠ 1
  central_d : IsThreeCentralIn L d
  mem_k : k1523 A d ∈ scriptY0 A (lB A)
  type_k : Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
    CFSG.Blueprint.NativeSporadic.ON
  mem_x : oPrimeResidualOf 3 (Y ⊓ k1523 A d) ∈ scriptY4 A (lB A)
  eq_y : Y = oPrimeResidualOf 3 (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y
  type_y : (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))

theorem conclusion1523_of_meets {A : Subgroup G} {c : G} {L : Subgroup G}
    (h1514 : Item1514 A (lB A) c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hm : MeetsY4 A (lB A) L Y) :
    Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L := by
  obtain ⟨φ⟩ := hJ
  rcases h1514 Y hY hm with ⟨h1, h2, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨_, ⟨e⟩⟩, -⟩
  · exact ⟨h1, by rw [inf_comm]; exact h2⟩
  · exact (KFacts.KS14.ks17J2NotList.2.1.false (φ.symm.trans e)).elim
  · exact (KFacts.KS14.not_isLThreeEpsAt_j2 5 1 (Or.inr ⟨by norm_num, ⟨φ.symm.trans e⟩⟩)).elim

omit [Finite G] in
theorem centralizer_mem_scriptY {A : Subgroup G} (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hAab : IsMulCommutative A) {d : G} (hd : d ∈ A)
    (hd1 : d ≠ 1) : Subgroup.centralizer ({d} : Set G) ∈ scriptY A := by
  refine ⟨fun htop => hd1 ?_, ?_⟩
  · have hZ := center_eq_bot_of_isSimpleGroup hsimp hnab
    have hdZ : d ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({d} : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [hZ] at hdZ
    exact (Subgroup.mem_bot).mp hdZ
  · intro a ha
    refine Subgroup.le_normalizer ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hAab.is_comm.comm ⟨d, hd⟩ ⟨a, ha⟩)).symm

omit [Finite G] in
theorem mem_pCoreOf_iff1523 {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ CFSG.Open.pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

theorem le_pCoreOf_of_le_centralizer {Y Z : Subgroup G}
    (hY : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) (hZY : Z ≤ Y)
    (hZ : Z ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G)) :
    Z ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsCharacteristicP 2 ↥Y :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mpr hY
  intro z hz
  have hzC : (⟨z, hZY hz⟩ : ↥Y) ∈
      Subgroup.centralizer ((CFSG.pCore 2 ↥Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : (y : G) ∈ CFSG.Open.pCoreOf 2 Y := (mem_pCoreOf_iff1523 y).mpr hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZ hz) y hyQ)
  exact (mem_pCoreOf_iff1523 ⟨z, hZY hz⟩).mpr (hc hzC)

theorem false_of_centralizer_le1523 {A Y Z : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {c' d : G} (hc : c' ∈ A)
    (hc3 : Nat.card (Subgroup.zpowers c') = 3) (hd : d ∈ A) (hd1 : d ≠ 1)
    (hdc : d ∉ Subgroup.zpowers c')
    (hQd : CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G) = ⊥)
    (hZY : Z ≤ Y) (hZQ : ¬ Z ≤ CFSG.Open.pCoreOf 2 Y)
    (hZ : ∀ F : Subgroup G, F ≤ Subgroup.closure {c', d} → Nat.card F = 3 →
      F ≠ Subgroup.zpowers d → Z ≤ Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({c', d} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hc
    · exact hd
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => hA.2 x (hEA hx)
  have hEab : CFSG.Open.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (hA.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩))⟩⟩, hE3⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hcE : Subgroup.zpowers c' ≤ E :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c' _))
  have hdE : d ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem c' rfl)
  have hk2 : 2 ≤ k := by
    have hdvd : Nat.card (Subgroup.zpowers c') ∣ Nat.card E := Subgroup.card_dvd_of_le hcE
    rw [hc3, hk] at hdvd
    have hk1 : k ≠ 0 := by
      rintro rfl
      norm_num at hdvd
    by_contra hk2
    have hk1' : k = 1 := by omega
    have hcard : Nat.card E ≤ Nat.card (Subgroup.zpowers c') := by rw [hk, hc3, hk1', pow_one]
    exact hdc ((Subgroup.eq_of_le_of_card_ge hcE hcard).symm ▸ hdE)
  have hE9 : 3 ^ (1 + 1) ≤ Nat.card E := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    (hEA.trans hAY).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hcop : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Q hEab hE9 hEQ hcop
  have hQZ : Q ≤ Subgroup.centralizer (Z : Set G) := by
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    by_cases hFd : F = Subgroup.zpowers d
    · have hCd : Subgroup.centralizer (F : Set G) = Subgroup.centralizer ({d} : Set G) := by
        rw [hFd, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [hCd, hQd]
      exact bot_le
    · exact Subgroup.le_centralizer_iff.mp
        (hZ F hF.1 (by rw [hF.2, pow_one]) hFd)
  exact hZQ (le_pCoreOf_of_le_centralizer hYF hZY (Subgroup.le_centralizer_iff.mp hQZ))

theorem eleven_dvd_card_ON :
    11 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
  rw [CFSG.Sporadic.ON.card_ON]
  norm_num

omit [Finite G] in
theorem not_eleven_dvd_of_type {Y : Subgroup G}
    (htype : (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) :
    ¬ 11 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rcases htype with ⟨_, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
    rw [GaloisField.card 7 1 (by norm_num)] at hc
    norm_num at hc
    have h3 : Nat.card ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = 1876896 := by
      omega
    rw [h3]
    norm_num
  · rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven]
    norm_num

theorem sup_eq_delta_of_mem_scriptQ {A X R : Subgroup G} (hX : X = delta A (lB A) X)
    (hR : R ∈ scriptQ A (lB A)) : X ⊔ R = delta A (lB A) (X ⊔ R) :=
  le_antisymm (sup_le (hX.le.trans (delta_mono le_sup_left)) (le_delta hR le_sup_right))
    (delta_le _)

end CFSG.RankThree.PartTwo.Sec15
