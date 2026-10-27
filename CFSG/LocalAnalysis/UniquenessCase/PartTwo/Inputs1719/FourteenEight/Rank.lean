module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_sup_of_conj {X K K' : Subgroup G} (hK : K ∈ calC X) (hK' : K' ∈ calC X)
    (hne : K' ≠ K) {g : G} (hg : K' = K.map (MulAut.conj g).toMonoidHom) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hZ : Subgroup.center (Bar2 K) = ⊥)
    (hrK : r ∣ Nat.card (Bar2 K)) :
    2 ≤ CFSG.Open.pRank r (K ⊔ K') := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := uc22p20d_bar2_conj g K
  have hZ' : Subgroup.center (Bar2 (uc22p20bCj g K)) = ⊥ := by
    rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
  have hcentK : r ∣ (Subgroup.center (Bar2 K)).index := by
    rwa [hZ, Subgroup.index_bot]
  have hcentK' : r ∣ (Subgroup.center (Bar2 K')).index := by
    rw [hg]
    change r ∣ (Subgroup.center (Bar2 (uc22p20bCj g K))).index
    rw [hZ', Subgroup.index_bot]
    rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv hK'
  obtain ⟨SA⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X K)))
  obtain ⟨SB⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X K')))
  obtain ⟨hpg, hnc⟩ := uc22p22u_noncyclic_of_commuting
    (uc22p22l_barImage_commute hK hK' hne.symm)
    SA SB (uc22p22u_sylow_not_le_center SA (by rwa [← uc22p22u_index_center_eq eA]))
    (uc22p22u_sylow_not_le_center SB (by rwa [← uc22p22u_index_center_eq eB]))
  exact uc22p22u_two_le_pRank_of_bar (sup_le hK.1.le hK'.1.le) hr hr2 hpg hnc
    (sup_le ((Subgroup.map_subtype_le _).trans (uc22p22u_barImage_mono le_sup_left))
      ((Subgroup.map_subtype_le _).trans (uc22p22u_barImage_mono le_sup_right)))

theorem exists_noncyclic_le_of_two_le_pRank {Y : Subgroup G} {r : ℕ} (hr : r.Prime)
    (h : 2 ≤ CFSG.Open.pRank r Y) : ∃ E : Subgroup G, E ≤ Y ∧ IsPGroup r E ∧ ¬ IsCyclic E := by
  obtain ⟨E, hEY, hE, hcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained r hr Y
  refine ⟨E, hEY, CFSG.Open.IsElemAbelian.isPGroup hE, ?_⟩
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c7_not_isCyclic_of_elemAbelian hr hE ?_
  rw [hcard]
  exact Nat.pow_le_pow_right hr.pos h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
