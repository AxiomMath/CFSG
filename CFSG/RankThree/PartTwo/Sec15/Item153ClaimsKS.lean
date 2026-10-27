module

public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsL
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.Asc83Table.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M11
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
public import CFSG.RankThree.PartTwo.Toolkit.M12LocalGroups

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

theorem exists_e9_of_e9Basis {X : Type*} [Group X] (B : CFSG.RankThree.Asc83Table.E9Basis X) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨hc, hp⟩ := CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.mp B.isElementaryAbelian
  exact ⟨B.sub, ⟨⟨⟨fun a b => Subtype.ext (hc _ a.2 _ b.2)⟩⟩, hp⟩, B.card⟩

theorem exists_e9_of_isLThreePi {X : Type} [Group X] (h : IsLThreePi X) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨p, e, hp, he, hiso⟩ := h
  rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · obtain ⟨D, hD, h9⟩ := exists_elemAbelian_nine_projImage_slPi
      (piField_galoisField p e he) (π := true) hq
    exact exists_e9_of_mulEquiv (φ.trans (MulEquiv.subgroupCongr (projSL_eq p e))) ⟨D, hD, h9⟩
  · obtain ⟨D, hD, h9⟩ := exists_elemAbelian_nine_projImage_slPi
      (piField_galoisField_two p e he) (π := false) hq
    exact exists_e9_of_mulEquiv (φ.trans (MulEquiv.subgroupCongr (projSU_eq p e))) ⟨D, hD, h9⟩

theorem exists_e9_alternatingGroup_seven :
    ∃ E : Subgroup (alternatingGroup (Fin 7)), CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  obtain ⟨E, hcomm, hpow, hcard, -⟩ :=
    CFSG.QuasithinUnique.Unc25G2.exists_elemAbelian_nine_of_commuting
      (a := (⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 7)))
      (b := (⟨List.formPerm [3, 4, 5], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 7)))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  exact ⟨E, ⟨⟨⟨fun x y => Subtype.ext (hcomm _ x.2 _ y.2)⟩⟩, hpow⟩, hcard⟩

theorem exists_e9_alternatingGroup_ten :
    ∃ E : Subgroup (alternatingGroup (Fin 10)), CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  obtain ⟨E, hcomm, hpow, hcard, -⟩ :=
    CFSG.QuasithinUnique.Unc25G2.exists_elemAbelian_nine_of_commuting
      (a := (⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 10)))
      (b := (⟨List.formPerm [3, 4, 5], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 10)))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  exact ⟨E, ⟨⟨⟨fun x y => Subtype.ext (hcomm _ x.2 _ y.2)⟩⟩, hpow⟩, hcard⟩

theorem ks153ThreeRank : KS153ThreeRank := by
  intro X _ _ htypes
  rcases htypes with ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · obtain ⟨E, hE, h9⟩ := CFSG.QuasithinUnique.Id2519.exists_elemAbelian_nine_J2
    exact exists_e9_of_mulEquiv φ ⟨E, hE, by rw [h9]; norm_num⟩
  · exact exists_e9_of_isLThreePi hL3
  · exact exists_e9_of_mulEquiv φ exists_e9_alternatingGroup_seven
  · exact exists_e9_of_mulEquiv φ (exists_e9_of_e9Basis CFSG.RankThree.Asc83Table.M22.E)
  · exact exists_e9_of_mulEquiv φ
      (exists_e9_of_e9Basis CFSG.RankThree.PartTwo.Toolkit.M12.basisE)

theorem center_eq_bot_of_quasisimple_types {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X)
    (htypes : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    Subgroup.center X = ⊥ := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := sporadicModels131
  rcases htypes with ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv φ hJ2z
  · obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hq3).2
    · by_cases hq2 : 2 < p ^ e
      · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hq3 hq2).2
      · exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        have := isSolvable_projSU_two
        have hsol : Group.IsSolvable X :=
          Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
        have := CFSG.LocalCores.isQuasisimple_nontrivial hq
        have := hq.1
        exact Group.IsPerfect.not_isSolvable _ hsol
  · exact center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2
  · exact center_eq_bot_of_mulEquiv φ hM22z
  · exact center_eq_bot_of_mulEquiv φ hM12z

theorem hasFaithfulE9_of_le_lA {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y : Subgroup G} (hLY : L ≤ Y) :
    HasFaithfulE9 Y :=
  hasFaithfulE9_of_le_of_ks153 ks153ThreeRank h hLY

end CFSG.RankThree.PartTwo.Sec15
