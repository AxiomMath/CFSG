module

public import CFSG.RankThree.GF2n.Tim79aSec22Ti
public import CFSG.RankThree.GF2n.Tim79aSec23Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem pCore_ne_bot_of_le {K : Subgroup G} (hPK : P ≤ K) (hKH : K ≤ H) :
    inSubgroup (pCore 2) K ≠ ⊥ := by
  set S : Subgroup G := inSubgroup (pCore 2) H ⊓ K with hS
  have hSK : S ≤ K := inf_le_right
  have hSn : K ≤ Subgroup.normalizer (S : Set G) := fun k hk =>
    mem_normalizer_inf ((inSubgroup_pCore_two H).2.2 (hKH hk)) (Subgroup.le_normalizer hk)
  have hS2 : IsPGroup 2 S := (inSubgroup_pCore_two H).1.to_le inf_le_left
  have hSO : S ≤ inSubgroup (pCore 2) K := le_inSubgroup_pCore hSK hSn hS2
  intro hbot
  apply hc.eOf_inf_V_ne_bot
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxV⟩ := Subgroup.mem_inf.mp hx
  have : x ∈ S := ⟨(eOf_le_pCore H) hxE, hPK (hc.V_le_P hxV)⟩
  have := hSO this
  rw [hbot] at this
  exact this

theorem sup_eq_H_of_not_isPGroup {h : G} (hh : h ∈ H)
    (hnp : ¬ IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V))) :
    P ⊔ conjSubgroup h V = H := by
  have hVH := hc.V_le_H
  have hUH : conjSubgroup h V ≤ H := conjSubgroup_le_of_le_of_mem hVH hh
  have hKH : P ⊔ conjSubgroup h V ≤ H := sup_le hc.PleH hUH
  by_contra hKne
  have hKlt : P ⊔ conjSubgroup h V < H := lt_of_le_of_ne hKH hKne
  have hVO : V ≤ inSubgroup (pCore 2) (P ⊔ conjSubgroup h V) :=
    hc.min _ le_sup_left (hc.pCore_ne_bot_of_le le_sup_left hKH) hKlt
  apply hnp
  rw [hc.isPGroup_barOf_sup_iff hh]
  obtain ⟨hO2, hOK, hOn⟩ := inSubgroup_pCore_two (P ⊔ conjSubgroup h V)
  set U : Subgroup G := conjSubgroup h V with hU
  have hV2 : IsPGroup 2 V := CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.elemAb
  have hU2 : IsPGroup 2 U := by
    obtain ⟨n, hn⟩ := hV2.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [hU, card_conjSubgroup]; exact hn)
  have hSK : V ⊔ U ≤ P ⊔ U := sup_le (hVO.trans hOK) le_sup_right
  set T : Subgroup G := (V ⊔ U) ⊓ inSubgroup (pCore 2) (P ⊔ U) with hT
  have hTn : U ≤ Subgroup.normalizer (T : Set G) := fun s hs =>
    mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_right hs))
      (hOn (hSK (Subgroup.mem_sup_right hs)))
  have hT2 : IsPGroup 2 T := hO2.to_le inf_le_right
  have hVT : V ≤ T := le_inf le_sup_left hVO
  have hTU : IsPGroup 2 ↥(T ⊔ U) := hT2.to_sup_of_normal_left' hU2 hTn
  have hS2 : IsPGroup 2 ↥(V ⊔ U) := hTU.to_le (sup_le (hVT.trans le_sup_left) le_sup_right)
  have hW2 : IsPGroup 2 (wOf V H) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian
  exact hS2.to_sup_of_normal_right' hW2 fun k hk =>
    H_le_normalizer_wOf V H (sup_le hVH hUH hk)

theorem eq_top_of_not_isPGroup {h : G} (hh : h ∈ H)
    (hnp : ¬ IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V)))
    {S : Subgroup (Hbar V H)} (hP : barOf V H P ≤ S) (hU : barOf V H (conjSubgroup h V) ≤ S) :
    S = ⊤ := by
  have hsup := hc.sup_eq_H_of_not_isPGroup hh hnp
  have hP' : P ≤ preimOf V H S := fun p hp => by
    have hpH : p ∈ H := hc.PleH hp
    exact mem_preimOf.mpr ⟨⟨p, hpH⟩, rfl, hP (mem_barOf_iff.mpr ⟨⟨p, hpH⟩, hp, rfl⟩)⟩
  have hU' : conjSubgroup h V ≤ preimOf V H S := fun u hu => by
    have huH : u ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hh hu
    exact mem_preimOf.mpr ⟨⟨u, huH⟩, rfl, hU (mem_barOf_iff.mpr ⟨⟨u, huH⟩, hu, rfl⟩)⟩
  have hHle : H ≤ preimOf V H S :=
    calc H = P ⊔ conjSubgroup h V := hsup.symm
      _ ≤ preimOf V H S := sup_le hP' hU'
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := piBar_surjective V H y
  obtain ⟨x', hx', hxS⟩ := mem_preimOf.mp (hHle x.2)
  have : x' = x := Subtype.ext hx'
  rw [← this]
  exact hxS

end MinCex

end CFSG.RankThree.GF2n.Tim79a
