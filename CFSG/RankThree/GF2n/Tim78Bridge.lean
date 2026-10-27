module

public import CFSG.RankThree.GF2n.Tim78S3Setting
import CFSG.RankThree.GF2n.Assembly
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GH74.EvenRank
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen
import CFSG.CGT.PushingUpLit.SolKR2.Top
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.GF2n.Tim78P214

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75
open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg IsCommSubgroup)
open CFSG.CGT.PushingUpLit.SolKR2 (R2)

variable {G : Type} [Group G] [Finite G]

section Bridge


theorem tim78_theorem1_of_four_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {M B : Subgroup G} (H : HypH M B) (h4 : Nat.card ↥(PartTwo.omegaOneSub B) = 4) :
    Assembly.IsElemAbelian 2 B := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h] at h4
    have : PartTwo.omegaOneSub (⊥ : Subgroup G) = ⊥ :=
      le_bot_iff.mp (PartTwo.omegaOneSub_le _)
    rw [this, Subgroup.card_bot] at h4
    omega
  have hN : Subgroup.normalizer (B : Set G) = M := H.normalizer_eq le_rfl hB1 H.normal
  have hS : STSetting G B :=
    { simple := inferInstance
      nonab := hnonab
      tight := tightlyEmbedded_of_isTI H.two hB1 H.ti
      max := by rw [hN]; exact H.max
      fstar := by
        rw [hN, CFSG.CGT.PushingUpLit.SolKAb.pCoreOf_eq_inSubgroup_pCore]
        exact (CFSG.GH74.inf_centralizer_map_subtype_le_iff _ (CFSG.pCore 2 _)).mpr
          ((isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mpr H.fstar) }
  have hP : IsPGroup 2 ↥(⊤ : Subgroup ↥B) :=
    H.two.of_injective (Subgroup.topEquiv : (⊤ : Subgroup ↥B) ≃* ↥B).toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup ↥B) ≃* ↥B).injective
  let R : Sylow 2 ↥B := hP.toSylow (by rw [Subgroup.index_top]; norm_num)
  have hR : sylowImg R = B := by
    show (⊤ : Subgroup ↥B).map B.subtype = B
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hc : IsCommSubgroup (sylowImg R) := by
    rw [hR]; exact H.comm
  have hne' : ¬ Assembly.IsElemAbelian 2 (sylowImg R) := by rw [hR]; exact hne
  have h4' : Nat.card ↥(PartTwo.omegaOneSub (sylowImg R)) = 4 := by rw [hR]; exact h4
  obtain ⟨e⟩ := STSetting.nonempty_omegaTwoSub_equiv_of_card_omegaOne_four hS R hc hne' h4'
  rw [hR] at e
  have h2 : R2 M B := ⟨H, h4, ⟨e⟩, hne⟩
  exact CFSG.CGT.PushingUpLit.SolKR2.R2.false_of_facts hnonab
    CFSG.CGT.PushingUpLit.SolKR2.r2First_holds h2
    (CFSG.CGT.PushingUpLit.SolKR2.R2Facts.of_lemmas CFSG.CGT.PushingUpLit.SolKR2.r2Weak_holds
      CFSG.CGT.PushingUpLit.SolKR2.r2First_holds h2)

theorem maximalAbelian_of_maximalElemAbelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {M B : Subgroup G} (hM : IsMaximalTwoLocal M) (hfstar : generalizedFitting M = pCore 2 M)
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B)
    (hTI : IsTI B) (h4 : 4 ≤ Nat.card B) :
    Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
      IsMulCommutative U) B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBab : IsMulCommutative B := hB.prop.2.2.1
  refine ⟨⟨hB.prop.1, hB.prop.2.1, hBab⟩, ?_⟩
  intro U hU hBU
  obtain ⟨U', hUU', hU'⟩ := Finite.exists_le_maximal (p := fun U : Subgroup G => U ≤ M ∧
    M ≤ Subgroup.normalizer (U : Set G) ∧ IsMulCommutative U) hU
  suffices hUB : U' = B from hUU'.trans hUB.le
  have hP2B : IsPGroup 2 B := PartTwo.Sec5.isPGroup_of_isElemAbelian hB.prop.2.2
  have hB1 : B ≠ ⊥ := ne_bot_of_maximal hM.1 hB
  have hN : Subgroup.normalizer (B : Set G) = M :=
    normalizer_eq_of_maximal hM hB1 hP2B hB.prop.2.1
  have hO2 : pCore 2 G = ⊥ := by
    haveI : (pCore 2 G).Normal := pCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 G) with h | h
    · exact h
    · exfalso
      have hP : IsPGroup 2 ↥(⊤ : Subgroup G) := h ▸ pCore_isPGroup (p := 2) (G := G)
      have hP' : IsPGroup 2 G :=
        hP.of_surjective (⊤ : Subgroup G).subtype Subgroup.topEquiv.surjective
      have hnil : Group.IsNilpotent G := hP'.isNilpotent
      have hcomm : ∀ a b : G, a * b = b * a :=
        IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable G)
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hcomm a b)
  obtain ⟨hU'M, hU'N, hU'c⟩ := hU'.prop
  have hU'ab : ∀ x ∈ U', ∀ y ∈ U', x * y = y * x := fun x hx y hy => by
    have := hU'c.is_comm.comm (⟨x, hx⟩ : U') ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hBU' : B ≤ U' := hBU.trans hUU'
  have hΩab : IsMulCommutative (PartTwo.omegaOneSub U') :=
    ⟨⟨fun x y => Subtype.ext (hU'ab _ (PartTwo.omegaOneSub_le U' x.2) _
      (PartTwo.omegaOneSub_le U' y.2))⟩⟩
  have hΩ2 : ∀ x ∈ PartTwo.omegaOneSub U', x ^ 2 = 1 := fun x hx => by
    rw [sq]; exact ((mem_omegaOneSub_iff hU'ab).mp hx).2
  have hMΩ : M ≤ Subgroup.normalizer (PartTwo.omegaOneSub U' : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_self_iff, ← omegaOneSub_conj hU'ab m,
      conjSubgroup_eq_self_iff.mpr (hU'N hm)]
  have hΩM : PartTwo.omegaOneSub U' ≤ M := (PartTwo.omegaOneSub_le U').trans hU'M
  have hBΩ : B ≤ PartTwo.omegaOneSub U' := fun x hx =>
    (mem_omegaOneSub_iff hU'ab).mpr ⟨hBU' hx, by rw [← sq]; exact hB.prop.2.2.2 x hx⟩
  have hΩB : PartTwo.omegaOneSub U' ≤ B := hB.2 ⟨hΩM, hMΩ, ⟨hΩab, hΩ2⟩⟩ hBΩ
  have hΩeq : PartTwo.omegaOneSub U' = B := le_antisymm hΩB hBΩ
  have hU'Q : U' ≤ inSubgroup (pCore 2) M := le_of_isMulCommutative_normal hfstar hU'M hU'N hU'c
  have hU'2 : IsPGroup 2 U' := (inSubgroup_pCore_two M).1.to_le hU'Q
  have hTI' : IsTI U' := by
    intro g
    by_cases h : U' ⊓ conjSubgroup g U' = ⊥
    · exact Or.inl h
    · right
      have hI2 : IsPGroup 2 ↥(U' ⊓ conjSubgroup g U') := hU'2.to_le inf_le_left
      obtain ⟨k, hk⟩ := hI2.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact h (Subgroup.eq_bot_of_card_eq _ hk)
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(U' ⊓ conjSubgroup g U')) 2 (by
        rw [hk]; exact dvd_pow_self 2 hk0)
      have hc2 : ((c : G)) * (c : G) = 1 := by
        have : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
        simpa [sq] using congrArg (fun t : ↥(U' ⊓ conjSubgroup g U') => (t : G)) this
      have hc1 : (c : G) ≠ 1 := by
        intro h1
        have : c = 1 := Subtype.ext h1
        rw [this, orderOf_one] at hc
        exact absurd hc (by norm_num)
      have hcU : (c : G) ∈ U' := c.2.1
      have hcg : (c : G) ∈ conjSubgroup g U' := c.2.2
      have hcB : (c : G) ∈ B := by
        rw [← hΩeq]; exact (mem_omegaOneSub_iff hU'ab).mpr ⟨hcU, hc2⟩
      have hcgB : (c : G) ∈ conjSubgroup g B := by
        rw [mem_conjSubgroup] at hcg ⊢
        rw [← hΩeq]
        refine (mem_omegaOneSub_iff hU'ab).mpr ⟨hcg, ?_⟩
        calc g⁻¹ * (c : G) * g * (g⁻¹ * (c : G) * g) = g⁻¹ * ((c : G) * (c : G)) * g := by group
          _ = 1 := by rw [hc2]; group
      have hne : B ⊓ conjSubgroup g B ≠ ⊥ := fun hbot =>
        hc1 (Subgroup.mem_bot.mp (hbot ▸ (Subgroup.mem_inf.mpr ⟨hcB, hcgB⟩)))
      have hgM : g ∈ M := by
        rw [← hN, ← conjSubgroup_eq_self_iff]
        exact conjSubgroup_eq_of_isTI hTI hne
      rw [conjSubgroup_eq_self_iff.mpr (hU'N hgM)]
      exact inf_idem U'
  have H : HypH M U' :=
    { o2 := hO2, max := hM, fstar := hfstar, le := hU'M, normal := hU'N, comm := hU'ab,
      ti := hTI' }
  have hBelem : Assembly.IsElemAbelian 2 U' := by
    by_cases h8 : 8 ≤ Nat.card ↥(PartTwo.omegaOneSub U')
    · exact tim78_theorem1_of_eight_le' CFSG.CGT.T75N.benderCenterInput
        CFSG.CGT.T75N.unitaryTwoGenerationInput H h8
    · obtain ⟨k, hk⟩ := hP2B.exists_card_eq
      have hΩcard : Nat.card ↥(PartTwo.omegaOneSub U') = Nat.card B := by rw [hΩeq]
      have h4B : 4 ≤ 2 ^ k := hk ▸ h4
      have h8B : 2 ^ k < 8 := by rw [← hk, ← hΩcard]; omega
      have hk2 : k = 2 := by
        rcases k with _ | _ | _ | k
        · norm_num at h4B
        · norm_num at h4B
        · rfl
        · have h1 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
          have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
      exact tim78_theorem1_of_four_simple hnonab H (by rw [hΩcard, hk, hk2]; norm_num)
  refine le_antisymm (fun x hx => ?_) hBU'
  rw [← hΩeq]
  exact (mem_omegaOneSub_iff hU'ab).mpr ⟨hx, by rw [← sq]; exact hBelem.2 x hx⟩

end Bridge

end CFSG.RankThree.GF2n.Tim78
