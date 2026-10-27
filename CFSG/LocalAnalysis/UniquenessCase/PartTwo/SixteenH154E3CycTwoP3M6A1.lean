module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M6A1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP3M6_m2
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hm2 : ¬ MBarGT D.M V₀ V 2) :
    ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  subst hp3
  have h3mem : 3 ∈ D.sig := by
    obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    rcases hres q hq with rfl | ⟨h7, -⟩
    · exact hq
    · omega
  have h3 : D.sig = {3} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨h3mem, fun q hq => by
      rcases hres q hq with rfl | ⟨h7, -⟩
      · rfl
      · omega⟩
  obtain ⟨R, hRle, hRp, hRc⟩ :=
    s16h_e3_CycTwoP3M6_noncyclic D S hr3 hσ h hc hLp hm hs2 h3
  intro w hw hw1
  by_cases hw0 : w ∈ V₀
  · exact s16c34_uniqueMax_cent_of_mem_v0 D S.h61 h.hyp16 h3mem (S.hSig.three_le 3 h3mem) hw0 hw1
  · have hwV : w ∈ V := preTil_le V₀ V hV _ hw
    exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 h3mem hRp hRc hwV hw0
      (hRle.trans (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hw))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
