module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LUSa
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid
public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S CFSG.RankThree.PartTwo.Sec14.Ronan148S

section Row


theorem rowH2_of_noA6 {S : Type} [Group S] [Finite S]
    (h : ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* S) → ∀ τ : MulAut T, τ ^ 3 = 1 →
      NoA6At τ) : RowH2 S := by
  intro Γ _ _ C _ hCθ _ A L K d hA hLA hdA _ _ hLq hCL _ hKM hKsn hKq _ hA6 ⟨e⟩ hZL
  exfalso
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hAC : A ≤ C := hLA ▸ le_sup_right
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer {d} := hKM.trans inf_le_right
  have hZ3 := isPGroup_center_of_normal hCθ hLC hCL hLq
  obtain ⟨z, hzK, hKz, hz3, hZ⟩ := exists_pCore_center_eq_zpowers hKq hA6.1
  have hLz : ¬ L ≤ Subgroup.centralizer {z} := by
    intro hLz
    apply hZL
    rw [hZ, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)
  obtain ⟨-, hinf, -, -, -⟩ := exists_cq_bar hZ3 hKL hKq hzK hKz hz3 hZ hLz
  have hdN : d ∈ Subgroup.normalizer (L : Set Γ) := hCL (hAC hdA)
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hτ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set Γ)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  let eB := equivBar hKL hinf
  exact h _ ⟨e⟩ _ hτ3 _ (map_le_autFix hdN hKd) (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hKq)
    (isSubnormal_bar hdN hKM hKsn) (Sec13.isTripleCover_of_mulEquiv (thetaQuotCongr eB) hA6)

end Row

section Lie

theorem rowOfH2_of_lie {X : Type} [Group X] (idx : TauCeti.ValidLieTypeIndex)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)) : RowOfH2 X := by
  intro S _ _ hs hna ⟨eS⟩
  obtain ⟨eX⟩ := hX
  refine rowH2_of_noA6 fun T _ _ ⟨eT⟩ τ hτ => ?_
  obtain ⟨hsT, hnaT⟩ := simple_nonab_of_mulEquiv eT hs hna
  exact noA6At_of_lie hsT hnaT idx ⟨(eT.trans eS).trans eX⟩ τ hτ

end Lie

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
