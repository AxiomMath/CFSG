module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofJTwo
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (projSp)
open Equiv

namespace Item812Res8

theorem noThetaNormal_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (h3 : 3 ∣ Nat.card S) : NoThetaNormal S := by
  intro N hN _ hN3
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hN3
    rw [h, Subgroup.card_top]
    exact h3

theorem mem_normalizer_of_forall_conj_mem {X : Type*} [Group X] [Finite X] (S : Subgroup X)
    {x : X} (h : ∀ s ∈ S, x * s * x⁻¹ ∈ S) : x ∈ Subgroup.normalizer (S : Set X) := by
  have hle : S.map (MulAut.conj x).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have heq : S.map (MulAut.conj x).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

def a6T1 : Perm (Fin 6) := swap 0 1 * swap 2 3

def a6T2 : Perm (Fin 6) := swap 0 2 * swap 1 3

def a6T3 : Perm (Fin 6) := swap 0 3 * swap 1 2

def a6Y : Perm (Fin 6) := swap 0 1 * swap 1 2

def a6V : Subgroup (Perm (Fin 6)) where
  carrier := {x | x = 1 ∨ x = a6T1 ∨ x = a6T2 ∨ x = a6T3}
  mul_mem' := by
    rintro a b ha hb
    change a = 1 ∨ a = a6T1 ∨ a = a6T2 ∨ a = a6T3 at ha
    change b = 1 ∨ b = a6T1 ∨ b = a6T2 ∨ b = a6T3 at hb
    change a * b = 1 ∨ a * b = a6T1 ∨ a * b = a6T2 ∨ a * b = a6T3
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a ha
    change a = 1 ∨ a = a6T1 ∨ a = a6T2 ∨ a = a6T3 at ha
    change a⁻¹ = 1 ∨ a⁻¹ = a6T1 ∨ a⁻¹ = a6T2 ∨ a⁻¹ = a6T3
    rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem mem_a6V {x : Perm (Fin 6)} : x ∈ a6V ↔ x = 1 ∨ x = a6T1 ∨ x = a6T2 ∨ x = a6T3 :=
  Iff.rfl

theorem a6V_le_alternatingGroup : a6V ≤ alternatingGroup (Fin 6) := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  rcases mem_a6V.mp hx with rfl | rfl | rfl | rfl <;> decide

theorem a6Y_mem : a6Y ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem twoLocalThree_alternatingGroup_six : TwoLocalThree (alternatingGroup (Fin 6)) := by
  set y : alternatingGroup (Fin 6) := ⟨a6Y, a6Y_mem⟩ with hy
  set T : Subgroup (alternatingGroup (Fin 6)) := a6V.subgroupOf (alternatingGroup (Fin 6))
    with hT
  have hy3 : y ^ 3 = 1 := Subtype.ext (by decide)
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    have := orderOf_dvd_natCard y
    rwa [orderOf_eq_prime hy3 (fun h => by
      have := congrArg Subtype.val h
      revert this
      decide)] at this
  refine ⟨?_, y, T, hy3, ?_, ?_, ?_, ?_⟩
  · have e := CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating
    have hs := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    have h3' : 3 ∣ Nat.card (commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
      by rwa [Nat.card_congr e.toEquiv]
    exact Item87Proof.NoThetaNormal.of_mulEquiv e.symm (noThetaNormal_of_isSimpleGroup h3')
  · rw [Subgroup.mem_center_iff]
    intro hc
    have h1 := hc ⟨a6T1, a6V_le_alternatingGroup (Or.inr (Or.inl rfl))⟩
    have h2 := congrArg Subtype.val h1
    revert h2
    decide
  · intro h0
    have hmem : (⟨a6T1, a6V_le_alternatingGroup (Or.inr (Or.inl rfl))⟩ :
        alternatingGroup (Fin 6)) ∈ T := by
      rw [hT, Subgroup.mem_subgroupOf]
      exact Or.inr (Or.inl rfl)
    rw [h0, Subgroup.mem_bot] at hmem
    have h2 := congrArg Subtype.val hmem
    revert h2
    decide
  · intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hg : ((g : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈ a6V := g.2
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rcases mem_a6V.mp hg with h | h | h | h <;> rw [h] <;> decide
  · refine mem_normalizer_of_forall_conj_mem T fun s hs => ?_
    rw [hT, Subgroup.mem_subgroupOf] at hs ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases mem_a6V.mp hs with h | h | h | h <;> rw [h, mem_a6V] <;> decide

end Item812Res8

open Item812Res8 in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem kF89Sp4TwoLocal_holds : KF89Sp4TwoLocal := by
  intro m hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    obtain rfl : m = 1 := by omega
    have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
    set H := projSp 2 (GaloisField 2 1)
    have E : H ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
      (Sec4.projSpEquivStatedProj 2 _).trans
        (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2)
    obtain ⟨hq, -⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour E
    obtain ⟨⟨e6⟩, -⟩ := CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour E
    have heq : perfectResidual H = commutator H :=
      le_antisymm (perfectResidual_le_commutator H)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hq.1)
    exact TwoLocalThree.of_mulEquiv ((MulEquiv.subgroupCongr heq).trans e6)
      twoLocalThree_alternatingGroup_six
  ·
    set F := GaloisField 2 m
    set H := projSp 2 F
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hSP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
        (Or.inl (Or.inr h4))
    set eP : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
      MulEquiv.ofBijective (proj 2 F) ⟨KFacts.proj_injective_of_charTwo, proj_surjective⟩
    have hS : IsSimpleGroup (StatedSp 2 F) := MulEquiv.isSimpleGroup eP
    have eH : StatedSp 2 F ≃* H := KFacts.statedSpEquivProjSpOfCharTwo F
    have h3 : 3 ∣ Nat.card (StatedSp 2 F) := by
      rw [Nat.card_congr eH.toEquiv, Sec19.Step1911Proof.card_projSp_two hm]
      refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
      have h4' : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4']
      exact Item87Proof.three_dvd_four_pow_sub_one m
    have hZ : Subgroup.center (StatedSp 2 F) = ⊥ := KFacts.center_statedSp_eq_bot
    have hTL : TwoLocalThree (StatedSp 2 F) := by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := StatedSp 2 F) 3 h3
      have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
      have hy1 : y ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hy
        omega
      obtain ⟨j, hj2, hj1, hyj⟩ := Item812Res2.exists_involution_commute_of_pow_three hy3
      refine ⟨noThetaNormal_of_isSimpleGroup h3, y, Subgroup.zpowers j, hy3, ?_, ?_, ?_, ?_⟩
      · rw [hZ, Subgroup.mem_bot]
        exact hy1
      · intro h0
        apply hj1
        have : j ∈ Subgroup.zpowers j := Subgroup.mem_zpowers j
        rw [h0, Subgroup.mem_bot] at this
        exact this
      · refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, orderOf_eq_prime hj2 hj1, pow_one]
      · refine mem_normalizer_of_forall_conj_mem _ fun s hs => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
        have hc : y * j ^ k * y⁻¹ = j ^ k := by
          rw [(Commute.zpow_right (show Commute y j from hyj) k).eq, mul_inv_cancel_right]
        rw [hc]
        exact Subgroup.zpow_mem_zpowers j k
    have hnc : ∃ u v : H, u * v ≠ v * u := by
      by_contra hc
      push Not at hc
      have hct : ∀ u v : StatedSp 2 F, u * v = v * u := fun u v => by
        apply eH.injective
        rw [map_mul, map_mul]
        exact hc _ _
      have htop : Subgroup.center (StatedSp 2 F) = ⊤ :=
        eq_top_iff.mpr fun u _ => Subgroup.mem_center_iff.mpr fun v => hct v u
      rw [hZ] at htop
      have hnt : Nontrivial (StatedSp 2 F) := IsSimpleGroup.toNontrivial
      exact (bot_ne_top htop)
    have hSH : IsSimpleGroup H := MulEquiv.isSimpleGroup eH.symm
    have hperf : Group.IsPerfect H := Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hperf]
    exact TwoLocalThree.of_mulEquiv (Subgroup.topEquiv.trans eH.symm) hTL

end CFSG.RankThree.PartTwo.Sec8
