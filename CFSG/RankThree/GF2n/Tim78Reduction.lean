module

public import CFSG.RankThree.GF2n.Tim78S3Setting
public import CFSG.RankThree.GF2n.Tim78S4Setting
import CFSG.RankThree.GF2n.Tim78Bridge
import CFSG.RankThree.GF2n.Tim78Thm1Gold
import CFSG.RankThree.GF2n.Tim78Lemma218
import CFSG.RankThree.GF2n.QTwo
import CFSG.RankThree.GF2n.Assembly
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.GF2n.Tim78P214

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem exists_maximalAbelian_of_maximalElem {M B : Subgroup G}
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) :
    ∃ B' : Subgroup G, B ≤ B' ∧
      Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
        IsMulCommutative U) B' ∧ PartTwo.omegaOneSub B' = B := by
  classical
  set S : Set (Subgroup G) := {U | U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U ∧ B ≤ U} with hS
  have hBS : B ∈ S := ⟨hB.prop.1, hB.prop.2.1, hB.prop.2.2.1, le_rfl⟩
  obtain ⟨B', hB'S, hB'max⟩ := (Set.toFinite S).exists_maximal ⟨B, hBS⟩
  have hBc' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB'S.2.2.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBE : B ≤ PartTwo.omegaOneSub B' := fun x hx =>
    (mem_omegaOneSub_iff hBc').mpr ⟨hB'S.2.2.2 hx, by rw [← sq]; exact hB.prop.2.2.2 x hx⟩
  have hEN : M ≤ Subgroup.normalizer (PartTwo.omegaOneSub B' : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_self_iff, ← omegaOneSub_conj hBc' m,
      conjSubgroup_eq_self_iff.mpr (hB'S.2.1 hm)]
  have hEel : Assembly.IsElemAbelian 2 (PartTwo.omegaOneSub B') :=
    ⟨⟨⟨fun a b => Subtype.ext (hBc' _ (PartTwo.omegaOneSub_le B' a.2) _
      (PartTwo.omegaOneSub_le B' b.2))⟩⟩, fun x hx => by
        rw [sq]; exact ((mem_omegaOneSub_iff hBc').mp hx).2⟩
  refine ⟨B', hB'S.2.2.2, ⟨⟨hB'S.1, hB'S.2.1, hB'S.2.2.1⟩, fun U hU hB'U => ?_⟩, ?_⟩
  · exact hB'max ⟨hU.1, hU.2.1, hU.2.2, hB'S.2.2.2.trans hB'U⟩ hB'U
  · exact le_antisymm (hB.le_of_ge ⟨(PartTwo.omegaOneSub_le B').trans hB'S.1, hEN, hEel⟩ hBE) hBE

theorem hypH_of_maximalAbelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hchar : IsCharacteristicPType G 2) {M B B' : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) (hTI : IsTI B)
    (hB' : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
      IsMulCommutative U) B')
    (hΩ : PartTwo.omegaOneSub B' = B) : HypH M B' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : generalizedFitting M = pCore 2 M := generalizedFitting_eq_pCore hchar hM.1
  have hB'c : IsMulCommutative B' := hB'.prop.2.2
  have hBc' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB'c.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hB'Q : B' ≤ inSubgroup (pCore 2) M :=
    le_of_isMulCommutative_normal hF hB'.prop.1 hB'.prop.2.1 hB'c
  have hB'2 : IsPGroup 2 B' := (inSubgroup_pCore_two M).1.to_le hB'Q
  have hNB : Subgroup.normalizer (B : Set G) = M :=
    normalizer_eq_of_maximal hM (ne_bot_of_maximal hM.1 hB)
      (PartTwo.Sec5.isPGroup_of_isElemAbelian hB.prop.2.2) hB.prop.2.1
  refine ⟨CFSG.CGT.PushingUp.pCore_eq_bot_of_isSimpleGroup hnonab, hM, hF, hB'.prop.1,
    hB'.prop.2.1, hBc', ?_⟩
  intro g
  by_cases hbot : B' ⊓ conjSubgroup g B' = ⊥
  · exact Or.inl hbot
  right
  have hI2 : IsPGroup 2 ↥(B' ⊓ conjSubgroup g B') := hB'2.to_le inf_le_left
  obtain ⟨k, hk⟩ := hI2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hbot (Subgroup.eq_bot_of_card_eq _ hk)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B' ⊓ conjSubgroup g B')) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hc2 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hyy : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) * (c : G) = 1 := by
    have := congrArg (fun t : ↥(B' ⊓ conjSubgroup g B') => (t : G)) hc2
    simpa [sq] using this
  have hy1 : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext h
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hyB' : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) ∈ B' := c.2.1
  have hyB'g : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) ∈ conjSubgroup g B' := c.2.2
  have hyB : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) ∈ B := by
    rw [← hΩ]
    exact (mem_omegaOneSub_iff hBc').mpr ⟨hyB', hyy⟩
  have hyBg : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) ∈ conjSubgroup g B := by
    rw [← hΩ, ← omegaOneSub_conj hBc' g]
    exact (mem_omegaOneSub_iff (comm_conj hBc' g)).mpr ⟨hyB'g, hyy⟩
  have hBg : conjSubgroup g B = B := by
    refine conjSubgroup_eq_of_isTI hTI fun hb => hy1 ?_
    have : ((c : ↥(B' ⊓ conjSubgroup g B')) : G) ∈ B ⊓ conjSubgroup g B := ⟨hyB, hyBg⟩
    rwa [hb, Subgroup.mem_bot] at this
  have hgM : g ∈ M := by
    rw [← hNB]
    exact conjSubgroup_eq_self_iff.mp hBg
  rw [conjSubgroup_eq_self_iff.mpr (hB'.prop.2.1 hgM), inf_idem]

section Trichotomy


theorem tim78Trichotomy_of_sec4 (hSec4 : Tim78Sec4Statement) : Tim78TrichotomyStatement := by
  intro G _ _ _ hnonab hchar M hM B hB hTI h4
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : generalizedFitting M = pCore 2 M := generalizedFitting_eq_pCore hchar hM.1
  obtain ⟨B', hBB', hB'max, hΩ⟩ := exists_maximalAbelian_of_maximalElem hB
  have HH : HypH M B' := hypH_of_maximalAbelian hnonab hchar hM hB hTI hB'max hΩ
  have hBB : B' = B := by
    by_contra hne
    have hne' : PartTwo.omegaOneSub B' ≠ B' := fun h => hne (h.symm.trans hΩ)
    have hcard : Nat.card ↥(PartTwo.omegaOneSub B') = Nat.card B := by rw [hΩ]
    obtain ⟨k, hk⟩ := (PartTwo.Sec5.isPGroup_of_isElemAbelian hB.prop.2.2).exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases Nat.eq_or_lt_of_le hk2 with hk2' | hk3
    · subst hk2'
      have hel := tim78_theorem1_of_four_simple hnonab HH (by rw [hcard, hk]; norm_num)
      refine hne' (le_antisymm (PartTwo.omegaOneSub_le B') (fun x hx => ?_))
      exact (mem_omegaOneSub_iff HH.comm).mpr ⟨hx, by rw [← sq]; exact hel.2 x hx⟩
    · have h8 : 8 ≤ Nat.card ↥(PartTwo.omegaOneSub B') := by
        rw [hcard, hk]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hel := tim78_theorem1_of_eight_le' CFSG.CGT.T75N.benderCenterInput
        CFSG.CGT.T75N.unitaryTwoGenerationInput HH h8
      refine hne' (le_antisymm (PartTwo.omegaOneSub_le B') (fun x hx => ?_))
      exact (mem_omegaOneSub_iff HH.comm).mpr ⟨hx, by rw [← sq]; exact hel.2 x hx⟩
  rw [hBB] at hB'max HH
  have hB2 : ∀ x ∈ B, x ^ 2 = 1 := hB.prop.2.2.2
  have hBQ : B ≤ inSubgroup (pCore 2) M := HH.le_Q
  by_cases hwc : WeaklyClosedIn B (inSubgroup (pCore 2) M)
  · exact Or.inl hwc
  right
  obtain ⟨g, hgQ, hgne⟩ : ∃ g : G, conjSubgroup g B ≤ inSubgroup (pCore 2) M ∧
      conjSubgroup g B ≠ B := by
    by_contra hcon
    exact hwc ⟨hBQ, fun g hg => by_contra fun hne => hcon ⟨g, hg, hne⟩⟩
  by_cases hPQ : inSubgroup (pCore 2) M =
      ⨆ (g : G) (_ : conjSubgroup g B ≤ inSubgroup (pCore 2) M), conjSubgroup g B
  · refine ⟨hPQ, ?_⟩
    obtain ⟨-, -, -, hfr, hcent, hcomm, -⟩ := tim78_2_18 (M := M) (V := B)
      (Q := inSubgroup (pCore 2) M)
      (P := inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (B : Set G))
      (W := B ⊔ conjSubgroup g B)
      (H := (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (B : Set G)) ⊔
        conjSubgroup g (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (B : Set G))) (g := g)
      hM hF hB'max hB2 hTI rfl hgne hgQ h4 rfl rfl rfl
    refine ⟨hcomm, hfr, ?_⟩
    rw [← hcent]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
      simpa using congrArg Subtype.val this
    · rintro ⟨hxQ, hxc⟩
      refine ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hxc y y.2
      exact Subtype.ext (by simpa using this)
  · exfalso
    exact hSec4 G M B (inSubgroup (pCore 2) M)
      (⨆ (g : G) (_ : conjSubgroup g B ≤ inSubgroup (pCore 2) M), conjSubgroup g B)
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer
        ((⨆ (g : G) (_ : conjSubgroup g B ≤ inSubgroup (pCore 2) M), conjSubgroup g B :
          Subgroup G) : Set G))
      ⟨CFSG.CGT.PushingUp.pCore_eq_bot_of_isSimpleGroup hnonab, hM, hF, hB'max, hB2, hTI, h4, rfl,
        rfl, rfl, ⟨g, hgQ, hgne⟩, fun h => hPQ h.symm⟩

end Trichotomy

end CFSG.RankThree.GF2n.Tim78
