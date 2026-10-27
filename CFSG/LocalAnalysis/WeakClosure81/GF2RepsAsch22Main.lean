module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Central
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Cover
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Noncentral
import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem pRank_le_three_or_onan_of_perfect_cover
    (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    (hNC : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentreRank)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide)
    (hON : Nonempty (CFSG.Blueprint.NativeSporadic.ON ≃* TauCeti.SporadicName.ONan.Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKGroup G) (H : Subgroup G) (N : Subgroup H) [N.Normal]
    [simpleQ : IsSimpleGroup (H ⧸ N)]
    (hnab : ∃ a b : H ⧸ N, a * b ≠ b * a)
    {Y : Type} [gY : Group Y] [finY : Finite Y] [perfY : Group.IsPerfect Y]
    (P : Subgroup Y) [normP : P.Normal] (hP : IsPGroup p P)
    (e : Y ⧸ P ≃* H ⧸ N)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (hrkY : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup G))
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) ≤ 3 ∨
      p = 3 ∧ Nonempty ((H ⧸ N) ≃* CFSG.Blueprint.NativeSporadic.ON) := by
  have hS' : IsSimpleGroup (Y ⧸ P) := e.isSimpleGroup
  have hnabY : ∃ a b : Y ⧸ P, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hcatHN : CFSG.Open.IsCatalogGroup (H ⧸ N) :=
    hK.isCatalogGroup_of_surjective H hnab (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  by_cases hc : P ≤ Subgroup.center Y
  · have hbot : Subgroup.center (Y ⧸ P) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ P)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnabY
        have hb : b ∈ Subgroup.center (Y ⧸ P) := h ▸ Subgroup.mem_top b
        exact hab (Subgroup.mem_center_iff.mp hb a)
    have hle : Subgroup.center Y ≤ P := by
      intro z hz
      have hz' : QuotientGroup.mk' P z ∈ Subgroup.center (Y ⧸ P) :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective P) ⟨z, hz, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hz'
      exact (QuotientGroup.eq_one_iff (N := P) (x := z)).mp (by
        simpa [QuotientGroup.mk'_apply] using hz')
    have hPeq : P = Subgroup.center Y := le_antisymm hc hle
    subst P
    have hqY : CFSG.Open.IsQuasisimple Y := ⟨Group.isPerfect_def.mp perfY, hS'⟩
    have hcatY : CFSG.Open.IsCatalogGroup (Y ⧸ Subgroup.center Y) :=
      CFSG.Open.isCatalogGroup_isoInvariant e hcatHN
    have hres := Asch22.pRank_quotient_le_three_of_central hC5 hNC hW hON hp hp2 hqY
      hcatY hP (hrkY.trans hrk)
    rcases hres with h | ⟨hp3, ⟨b⟩⟩
    · refine Or.inl ?_
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact h
    · exact Or.inr ⟨hp3, ⟨e.symm.trans b⟩⟩
  · refine Or.inl ?_
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact Asch22.pRank_quotient_le_three_of_not_le_center hp hp2 P hP hS' hmin hc
      (hrkY.trans hrk)

theorem asch2_2Simple_of_kfacts (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    (hNC : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentreRank)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide)
    (hON : Nonempty (CFSG.Blueprint.NativeSporadic.ON ≃* TauCeti.SporadicName.ONan.Group)) :
    Asch2_2Simple := by
  intro G _ _ hK p hp hp2 hrk H N _ hS hnab
  obtain ⟨Y, hGY, hFinY, P, hPN, hperf, hP, ⟨e⟩, hmin, hrkY⟩ :=
    @Asch22.exists_perfect_pCover G _ _ p hp H N _
      (CFSG.RankThree.OddKernel.isPerfect_of_isSimpleGroup' hnab)
  exact pRank_le_three_or_onan_of_perfect_cover hC5 hNC hW hON hp hp2 hK H N
    (simpleQ := hS) hnab (gY := hGY) (finY := hFinY) (perfY := hperf) P
    (normP := hPN) hP e hmin hrkY hrk

end CFSG.LocalAnalysis.WeakClosure81
