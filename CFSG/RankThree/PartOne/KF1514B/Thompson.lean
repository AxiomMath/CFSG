module

public import CFSG.RankThree.PartOne.KF1514B.Family
public import CFSG.Quasithin.Background.BlueprintB2Thompson

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail QuadraticMap Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem isElementaryAbelian_iff_elemAb {A : Subgroup ↥(U0 b c)} :
    IsElementaryAbelian 2 A ↔ ElemAb A := by
  rw [CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff]
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨hc, fun x hx => by simpa [pow_two] using hp x hx⟩
  · rintro ⟨hc, hp⟩
    exact ⟨hc, fun x hx => by rw [pow_two]; exact hp x hx⟩

theorem exists_ne_zero_fin2 : ∃ w : Fin 2 → K, w ≠ 0 :=
  ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0⟩

theorem db_eq_zero_of_mem_family {A : Subgroup ↥(U0 b c)}
    (hA : A ∈ elemThompsonFamily ↥(U0 b c) 2) : ∀ g ∈ A, db g = 0 := by
  intro g hg
  by_contra hb0
  obtain ⟨w, hw⟩ := exists_ne_zero_fin2 (K := K)
  obtain ⟨hAel, hmax⟩ := CFSG.Quasithin.BlueprintB2.mem_elemThompsonFamily_iff.1 hA
  have h1 : Nat.card K ^ 6 ≤ Nat.card ↥A :=
    (card_Aw_ge (b := b) (c := c) hw).trans
      (hmax _ (isElementaryAbelian_iff_elemAb.2 (elemAb_Aw w)))
  have h2 := card_le_pow5_of_db_ne (isElementaryAbelian_iff_elemAb.1 hAel) hg hb0
  have h3 : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right Finite.one_lt_card (by norm_num)
  omega

theorem z0_mem_E (w : Fin 2 → K) :
    z0 (b := b) (c := c) w ∈ elemThompsonCenterTorsion ↥(U0 b c) 2 := by
  rw [CFSG.Quasithin.BlueprintB2.mem_elemThompsonCenterTorsion_iff_centralizer]
  refine ⟨?_, ?_⟩
  · have hJ : elemThompson ↥(U0 b c) 2 ≤ Subgroup.centralizer ({z0 (b := b) (c := c) w} : Set ↥(U0 b c)) := by
      refine sSup_le fun A hA a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (commute_z0 (db_eq_zero_of_mem_family hA a ha) w).symm
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.1 (hJ hj) _ (Set.mem_singleton _)).symm
  · rw [pow_two]
    exact (elemAb_Aw w).sq _ (z0_mem_Aw w)

theorem db_eq_zero_of_mem_centralizer_E {g : ↥(U0 b c)}
    (hg : g ∈ Subgroup.centralizer (elemThompsonCenterTorsion ↥(U0 b c) 2 : Set ↥(U0 b c))) :
    db g = 0 := by
  obtain ⟨w, hw⟩ := exists_ne_zero_fin2 (K := K)
  exact db_eq_zero_of_commute_z0 w
    (by have := Subgroup.mem_centralizer_iff.1 hg _ (z0_mem_E (b := b) (c := c) w)
        exact this.symm)

end CFSG.RankThree.PartOne.KF1514B
