module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)


theorem OrthWeakFrame.exists_coxRefl_perf_eq_pair (hL1 : GGSecFiveL1PhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6)
    (Φ : OrthWeakFrame p Bs L) :
    ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧ GGIsReflection p r₀ ∧
      ggRankOnePerf Bs r₀ =
        ((Φ.Δ.rankOne ⟨0, by have := Φ.hr; omega⟩ ⟨1, by have := Φ.hr; omega⟩).subgroupOf
          (orthDerived Φ.Q)).map Φ.ψ := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r₀, hr₀A, hr₀, hrank⟩ :=
    Φ.exists_swap_refl (i := ⟨0, by have := Φ.hr; omega⟩) (j := ⟨1, by have := Φ.hr; omega⟩)
      (by simp [Fin.ext_iff])
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) hr₀
  exact ⟨r₀, hr₀A, hr₀C, hr₀,
    (hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl) r₀ hr₀A hr₀C).trans hrank⟩

end OrthTorus

end CFSG.StandardType
