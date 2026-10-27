module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOneField
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldTransfer
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSp4Engine
import CFSG.RankThree.PartOne.KF.ClsSpUpper

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)


section Certs


theorem k419OneFieldPSp4Even_holds : K419OneFieldPSp4Even := by
  intro G _ _ L hL h46 F _ _ _ x a hx3 hxa hxk haL ha3 haC hdiag K hK hKc ht
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F)) := by
    rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
  have hin : ¬ InducesOuterTheta a L := by
    rcases hdiag with h | ⟨e', hx', hd⟩
    · exact h
    · exfalso
      obtain ⟨A, hA⟩ := hd.1
      exact hd.2 (hA ▸ conjAut_mem_inner_of_charTwo A)
  let e₂ : L ⧸ aschbacherSolvableCore 3 L ≃* StatedSp 2 F :=
    e.trans (CFSG.RankThree.PartOne.KFU.spEquivProj (K := F) (by norm_num : 1 ≤ 2)).symm
  have hinner : IsInnerAut (inducedAutHom L e₂ ⟨a, haL⟩) := by
    by_contra h
    exact hin ((not_isInnerAut_inducedAutHom_iff L e₂ haL).mp h)
  obtain ⟨g, hg⟩ := hinner
  have hτ3 := inducedAutHom_pow_eq_one L e₂ haL ha3'
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg]; exact hτ3
    have h2 : g ^ 3 ∈ Subgroup.center (StatedSp 2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun γ : MulAut (StatedSp 2 F) => γ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 3 = g ^ 3 * y * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
        _ = g ^ 3 * y := by group
    rwa [CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num : 1 ≤ 2),
      Subgroup.mem_bot] at h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply haC
    refine Item419Res3.mem_centralizer_of_inducedAutHom_eq_one hL e₂ haL ?_
    rw [← hg, map_one]
  obtain ⟨hs, hZ, ι, hι, hfix⟩ := HeringOF.exists_injective_fixSub haL hK hKc ht e₂
  have hcomm : ∀ k, ι k * g = g * ι k := by
    intro k
    have h := hfix k
    rw [← hg, HeringOF.fixSub_conj_eq_centralizer'] at h
    exact (Subgroup.mem_centralizer_singleton_iff.mp h)
  exact HeringOF.not_isType419_of_commute_sp4 ht hs hZ ι hι g hg3 hg1 hcomm

end Certs

end CFSG.RankThree.PartTwo.Sec4
