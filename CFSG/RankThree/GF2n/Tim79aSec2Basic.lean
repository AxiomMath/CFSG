module

public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.CGT.Timmesfeld75.WeaklyClosed
public import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.RankThree.GF2n.Tim79aMinCex

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G]

theorem tim79a_1_1 [Finite G] {M V Q P : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hF : generalizedFitting M = pCore 2 M)
    (hmax : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
      IsMulCommutative U) V)
    (hel : Assembly.IsElemAbelian 2 V) (hTI : IsTI V) (h2 : 2 < Nat.card V)
    (hQ : Q = inSubgroup (pCore 2) M) (hP : P = Q ⊓ Subgroup.centralizer (V : Set G)) :
    Subgroup.centralizer (P : Set G) = V ∧ inSubgroup frattini P ≤ V := by
  obtain ⟨hVM, hMV, hVc⟩ := hmax.prop
  have hV2 : IsPGroup 2 V := CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hel
  have hVne : V ≠ ⊥ := by
    rintro rfl
    simp at h2
  have hnorm : Subgroup.normalizer (V : Set G) = M := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne hMV (Ne.symm hne)) ⟨V, hVne, hV2, rfl⟩
  have hP' : P = inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) := hQ ▸ hP
  have hα := tim78_2_9_alpha hF hVM hMV hVc hP'
  have hβ := tim78_2_9_beta_of_elementary hF hmax (fun x hx => hel.2 x hx) hP'
  have hCM : Subgroup.centralizer (P : Set G) ≤ M := by
    intro c hc
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    have hxP : x ∈ P := (hβ.2 ▸ hx : x ∈ P ⊓ Subgroup.centralizer (P : Set G)).1
    have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc x hxP).symm
    exact hnorm ▸ Tim77.mem_normalizer_of_commute_of_isTI hTI hx (fun h => hx1 (Subtype.ext h)) hcx
  refine ⟨le_antisymm (fun c hc => ?_) (by rw [hβ.2]; exact inf_le_right), hβ.1⟩
  have : c ∈ M ⊓ Subgroup.centralizer (P : Set G) := ⟨hCM hc, hc⟩
  rw [hα, ← hβ.2] at this
  exact this

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
include hc

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have h4 := hc.four
  rw [h] at h4
  simp at h4

theorem isPGroup_V : IsPGroup 2 V := CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.elemAb

theorem normalizer_eq : Subgroup.normalizer (V : Set G) = M := by
  by_contra hne
  exact hc.maxLocal.2 _ (lt_of_le_of_ne hc.maxAb.prop.2.1 (Ne.symm hne))
    ⟨V, hc.V_ne_bot, hc.isPGroup_V, rfl⟩

theorem V_le_Q : V ≤ Q := by
  rw [hc.hQ]
  exact le_of_isMulCommutative_normal hc.fitting hc.maxAb.prop.1 hc.maxAb.prop.2.1
    hc.maxAb.prop.2.2

theorem P_le_Q : P ≤ Q := hc.hP ▸ inf_le_left

theorem V_le_P : V ≤ P := by
  rw [hc.hP]
  refine le_inf hc.V_le_Q ?_
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hc.maxAb.prop.2.2

theorem isPGroup_P : IsPGroup 2 P := by
  have hQ2 := (inSubgroup_pCore_two M).1
  exact (hc.hQ ▸ hQ2 : IsPGroup 2 Q).to_le hc.P_le_Q

theorem M_le_normalizer_P : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => by
  rw [hc.hP, hc.hQ]
  exact mem_normalizer_inf ((inSubgroup_pCore_two M).2.2 hm)
    (mem_normalizer_centralizer (hc.maxAb.prop.2.1 hm))

theorem V_le_H : V ≤ H := hc.V_le_P.trans hc.PleH

theorem mem_M_of_commute {x c : G} (hxV : x ∈ V) (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ M := hc.normalizer_eq ▸ Tim77.mem_normalizer_of_commute_of_isTI hc.ti hxV hx1 hcx

theorem centralizer_P_eq_and : Subgroup.centralizer (P : Set G) = V ∧ inSubgroup frattini P ≤ V :=
  tim79a_1_1 hc.maxLocal hc.fitting hc.maxAb hc.elemAb hc.ti (by have := hc.four; omega)
    hc.hQ hc.hP

theorem centralizer_P_eq : Subgroup.centralizer (P : Set G) = V := hc.centralizer_P_eq_and.1

theorem frattini_P_le : inSubgroup frattini P ≤ V := hc.centralizer_P_eq_and.2

end MinCex

end CFSG.RankThree.GF2n.Tim79a
