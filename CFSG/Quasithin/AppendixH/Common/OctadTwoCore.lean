module

public import CFSG.Quasithin.AppendixH.Common.OctadActionRange

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

theorem pCoreOf_octStab {O : Finset (Fin 24)} (hO : IsOctad O) :
    pCoreOf 2 (octStab O) = octFix O := by
  let H : Subgroup S24 := octStab O
  let K : Subgroup S24 := octFix O
  have hKO : K ≤ H := octFix_le_octStab O
  have hcardO : Nat.card ↥O = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hO.1]
  haveI : Nontrivial ↥O :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardO]; norm_num)
  change pCoreOf 2 H = K
  apply le_antisymm
  ·
    change (pCore 2 H).map H.subtype ≤ K
    have hNle : pCore 2 H ≤ (octAct O).ker := by
      let ψ : H →* ↥(alternatingGroup ↥O) :=
        (octAct O).codRestrict (alternatingGroup ↥O) fun g => by
          have hg : (octAct O) g ∈ (octAct O).range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
          rwa [range_octAct hO] at hg
      have hψ : Function.Surjective ψ := by
        intro a
        have ha : (a : Equiv.Perm ↥O) ∈ (octAct O).range := by
          rw [range_octAct hO]
          exact a.2
        rcases MonoidHom.mem_range.mp ha with ⟨g, hg⟩
        exact ⟨g, Subtype.ext hg⟩
      have hmap2 : IsPGroup 2 ((pCore 2 H).map ψ) :=
        (CFSG.pCore_isPGroup (G := H) (p := 2)).map ψ
      have hmapn : ((pCore 2 H).map ψ).Normal :=
        Subgroup.Normal.map (CFSG.pCore_normal (G := H) (p := 2)) ψ hψ
      have hsimple : IsSimpleGroup ↥(alternatingGroup ↥O) :=
        alternatingGroup.isSimpleGroup (α := ↥O) (by rw [hcardO]; norm_num)
      letI : ((pCore 2 H).map ψ).Normal := hmapn
      rcases hsimple.eq_bot_or_eq_top_of_normal ((pCore 2 H).map ψ) with hbot | htop
      · intro x hx
        have hx1 : ψ x = 1 := by
          have hmem : ψ x ∈ (pCore 2 H).map ψ := ⟨x, hx, rfl⟩
          rw [hbot] at hmem
          simpa using hmem
        have hx1' : (octAct O) x = 1 := by
          have h := congrArg Subtype.val hx1
          exact h
        exact MonoidHom.mem_ker.mpr hx1'
      · exfalso
        have hA2 : IsPGroup 2 ↥(alternatingGroup ↥O) := by
          rw [htop] at hmap2
          exact hmap2.of_equiv Subgroup.topEquiv
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA2
        have hcardA : Nat.card ↥(alternatingGroup ↥O) = 20160 := by
          rw [nat_card_alternatingGroup, hcardO]
          norm_num
        have h3 : 3 ∣ 2 ^ n := by rw [← hn, hcardA]; norm_num
        have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
        norm_num at h32
    have hNleK : pCore 2 H ≤ K.subgroupOf H := by
      rw [ker_octAct O] at hNle
      exact hNle
    have hmap := Subgroup.map_mono (f := H.subtype) hNleK
    rwa [Subgroup.map_subgroupOf_eq_of_le hKO] at hmap
  ·
    change K ≤ (pCore 2 H).map H.subtype
    have hKp : IsPGroup 2 (K.subgroupOf H) :=
      (isPGroup_octFix (O := O) hO).of_equiv (Subgroup.subgroupOfEquivOfLe hKO).symm
    have hle : K.subgroupOf H ≤ pCore 2 H := by
      show K.subgroupOf H ≤ sSup {N : Subgroup H | N.Normal ∧ IsPGroup 2 N}
      exact le_sSup ⟨normal_octFix O, hKp⟩
    have hmap := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hKO] at hmap

end CFSG.ASVolI.AppH
