module

public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Background.E1ElevenIso
public import CFSG.Quasithin.Vol2.Ch8Sec2L823Div
public import CFSG.Quasithin.Vol2.Ch11SecOE9F
public import CFSG.Quasithin.Vol2.Ch11SecOE9Q
public import CFSG.Quasithin.Vol2.Ch11SecE3LieMain
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.Quasithin.EmptyFaithful.E22PA6
public import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_of_nParam_eq {k j : ℕ} (hk : E1.nParam (⊤ : Subgroup Y) = (k : ℕ∞))
    (hj : E1.nParam (⊤ : Subgroup Y) = (j : ℕ∞)) : k = j :=
  ENat.coe_inj.mp (hk.symm.trans hj)

theorem nParam_eq_one_of_isSolvable (hs : Group.IsSolvable Y) (he : Even (Nat.card Y)) :
    E1.nParam (⊤ : Subgroup Y) = 1 :=
  le_antisymm (E1.solvable_nParam_le_one inferInstance)
    (Vol2.Ch11.SecE3.one_le_nParam_of_not_odd (Nat.not_odd_iff_even.mpr he))

theorem isSolvable_dihedralGroup (m : ℕ) [NeZero m] : Group.IsSolvable (DihedralGroup m) := by
  classical
  let R : Subgroup (DihedralGroup m) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = m := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup m ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact (Nat.eq_of_mul_eq_mul_right hm h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup m ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup m ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem nParam_eq_of_dihedral {m : ℕ} [NeZero m] (e : Y ≃* DihedralGroup m) :
    E1.nParam (⊤ : Subgroup Y) = 1 := by
  have := isSolvable_dihedralGroup m
  refine nParam_eq_one_of_isSolvable (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom)
    e.symm.surjective) ?_
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact even_two_mul m

theorem nParam_eq_of_isPSL {j : ℕ} (hY : IsPSL 2 2 j Y) : E1.nParam (⊤ : Subgroup Y) = j := by
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (⊤ : Subgroup Y)
  exact H13.nParam_eq_of_isPSL_82 hY hS

theorem nParam_eq_of_isSz {j : ℕ} (hY : IsSz j Y) :
    E1.nParam (⊤ : Subgroup Y) = j := by
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (⊤ : Subgroup Y)
  exact H13.nParam_eq_of_isSz_82 hY hS

theorem nParam_eq_of_isPSp4 {j : ℕ} (hY : IsPSp4 2 j Y) :
    E1.nParam (⊤ : Subgroup Y) = j := by
  have hs : IsSimpleGroup Y := E2.isSimpleGroup_of_isPSp4 hY
  have hF : CFSG.generalizedFitting Y = ⊤ := H13.generalizedFitting_eq_top_82
  have hL : IsPSp4 2 j ↥(CFSG.generalizedFitting Y) := by
    rw [hF]
    exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hY
  have hFs : IsSimpleGroup ↥(CFSG.generalizedFitting Y) := by
    rw [hF]
    exact Subgroup.topEquiv.isSimpleGroup
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (⊤ : Subgroup Y)
  have hT : quasithinIsSylowTwo S := by
    refine ⟨hS.2.1, ?_⟩
    have h2 := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h2
  have hFT : CFSG.generalizedFitting Y ⊔ S = ⊤ := by
    rw [hF]
    exact top_sup_eq _
  refine le_antisymm ?_ (Vol2.Ch11.SecE3.Lie3.le_nParam_of_isPSp4 hL hFs hT hFT)
  by_cases htw : E2.IsDiagramNontrivial S (CFSG.generalizedFitting Y)
      (S ⊓ CFSG.generalizedFitting Y)
  · exact Vol2.Ch11.SecE3.Lie3.nParam_le_of_isPSp4_of_twisted hL hFs hT hFT htw
  · exact Vol2.Ch11.SecE3.Lie3.nParam_le_of_isPSp4_of_untwisted hL hT hFT htw

theorem generalizedFitting_perm_six :
    CFSG.generalizedFitting (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hnc : ∃ x y : alternatingGroup (Fin 6), x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative (alternatingGroup (Fin 6)) := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := Group.is_simple_iff_prime_card.1
      (inferInstance : IsSimpleGroup (alternatingGroup (Fin 6)))
    rw [hcard] at hp
    norm_num at hp
  exact CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot _ hnc
    (CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (by simp))

theorem nParam_perm_six :
    E1.nParam (⊤ : Subgroup (Equiv.Perm (Fin 6))) = 1 := by
  refine le_antisymm (E2.E22N.nParam_le_one_of_alt6
    ⟨MulEquiv.subgroupCongr generalizedFitting_perm_six⟩)
    (Vol2.Ch11.SecE3.one_le_nParam_of_not_odd ?_)
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem nParam_eq_of_perm_six (e : Y ≃* Equiv.Perm (Fin 6)) :
    E1.nParam (⊤ : Subgroup Y) = 1 := by
  rw [E1.Eleven.nParam_top_mulEquiv e]
  exact nParam_perm_six

theorem nParam_eq_of_isSp4Full
    {j : ℕ} (hY : IsSp4Full j Y) : E1.nParam (⊤ : Subgroup Y) = j := by
  rcases hY with hY | ⟨rfl, ⟨e⟩⟩
  · exact nParam_eq_of_isPSp4 hY
  · exact_mod_cast nParam_eq_of_perm_six e

end CFSG.Quasithin.SimsE2
