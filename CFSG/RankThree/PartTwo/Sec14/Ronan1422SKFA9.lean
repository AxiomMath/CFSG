module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofIrred
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG.Assembly.RankThreeEven (projSp)

theorem aut_eq_conj_symm_of_congr {S Y : Type*} [Group S] [Group Y] (e : S ≃* Y) (α : MulAut S)
    (y : Y) (h : MulAut.congr e α = MulAut.conj y) : α = MulAut.conj (e.symm y) := by
  apply (MulAut.congr e).injective
  rw [h]
  ext z
  simp [MulAut.congr_apply, map_mul, map_inv]

theorem alt9_aut_inner_of_cube (α : MulAut (alternatingGroup (Fin 9))) (hα : α ^ 3 = 1) :
    ∃ s : alternatingGroup (Fin 9), α = MulAut.conj s := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 α
  have h3 : σ ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hσ, hα, map_one]
  have hsign : Equiv.Perm.sign σ = 1 := by
    have h3s : Equiv.Perm.sign σ ^ 3 = 1 := by
      rw [← map_pow, h3, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · rw [h] at h3s
      have h3v := congrArg Units.val h3s
      norm_num at h3v
  have hmem : σ ∈ alternatingGroup (Fin 9) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  refine ⟨⟨σ, hmem⟩, ?_⟩
  rw [← hσ]
  refine MulEquiv.ext fun x => Subtype.ext ?_
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem sp62_aut_inner_of_iso {S : Type*} [Group S] (e : S ≃* projSp 3 (GaloisField 2 1))
    (α : MulAut S) : ∃ s : S, α = MulAut.conj s := by
  obtain ⟨h, hh⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.mem_range_conj_H6
    (MulAut.congr (e.trans CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.sp62Equiv) α)
  exact ⟨(e.trans CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.sp62Equiv).symm h,
    aut_eq_conj_symm_of_congr _ α h hh.symm⟩

theorem aut_inner_of_cube_of_iso {S : Type*} [Group S]
    (hS : Nonempty (S ≃* alternatingGroup (Fin 9)) ∨ Nonempty (S ≃* projSp 3 (GaloisField 2 1)))
    (α : MulAut S) (hα : α ^ 3 = 1) : ∃ s : S, α = MulAut.conj s := by
  rcases hS with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hc : (MulAut.congr e α) ^ 3 = 1 := by
      rw [← map_pow, hα, map_one]
    obtain ⟨s, hs⟩ := alt9_aut_inner_of_cube (MulAut.congr e α) hc
    exact ⟨e.symm s, aut_eq_conj_symm_of_congr e α s hs⟩
  · exact sp62_aut_inner_of_iso e α

theorem kf1422A9Sp6_holds : KF1422A9Sp6 := by
  intro S _ _ hS
  refine ⟨fun α hα => aut_inner_of_cube_of_iso hS α hα, fun E hE hE27 D hDE hD9 => ?_⟩
  by_contra hcon
  push Not at hcon
  have hN : Subgroup.normalizer (E : Set S) ≤ Subgroup.normalizer (D : Set S) := by
    intro n hn
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcon n hn)
  rcases CFSG.RankThree.PartTwo.Sec8.kF812E27NormIrred_holds S hS E D hE hE27 hDE hN with h | h
  · rw [h, Subgroup.card_bot] at hD9
    omega
  · rw [h, hE27] at hD9
    omega

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
