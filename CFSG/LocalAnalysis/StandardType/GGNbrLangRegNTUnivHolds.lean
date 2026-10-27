module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivDefs
public import CFSG.LocalAnalysis.StandardType.KGCenterCoprime
public import CFSG.LocalAnalysis.StandardType.KGConclPushDown
public import CFSG.LocalAnalysis.StandardType.KGCoverLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

theorem largeEvenLabelAll_hasLabel (lab : LargeEvenLabel) :
    LargeEvenLabelAll lab fun R _ _ _ => GGHasLabel lab R := by
  intro Q h
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [GGHasLabel, LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hq, K, i1, i2, hK, b, c, hbc, ⟨MulEquiv.refl _⟩⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hq, K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩)

theorem kgLangTorusNTCont_of_univ {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hU : KGLangTorusNTUnivCont p R I F)
    (hZ : ∀ (K : Type) [Group K] [Finite K] (_ : K ⧸ Subgroup.center K ≃* R),
      commutator K = ⊤ → Nat.Coprime (Nat.card (Subgroup.center K)) p) :
    KGLangTorusNTCont p R I F := by
  intro K _ _ θ hK A hA hAI hA0 α₀ hα₀ hα₀I
  obtain ⟨hfin, hperf, θC, κ, lift, hκ, hκc, -, hlift, hind⟩ := KGUniv.exists_universal_cover_lift hK θ
  haveI := hfin
  have hliftInj : Function.Injective lift := by
    refine (injective_iff_map_eq_one lift).2 fun α hα => ?_
    refine MulEquiv.ext fun k => ?_
    obtain ⟨x, rfl⟩ := hκ k
    have h1 := hlift α x
    rw [hα] at h1
    simpa using h1.symm
  have hconcl : KGLangTorusConcl p θC I (A.map lift) (lift α₀) := by
    refine hU θC hperf (A.map lift) ⟨?_, ?_⟩ ?_ ?_ (lift α₀) (Subgroup.mem_map_of_mem _ hα₀) ?_
    · refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨_, a', ha', rfl⟩ := a
      obtain ⟨_, b', hb', rfl⟩ := b
      have := hA.1.is_comm.comm (⟨a', ha'⟩ : A) ⟨b', hb'⟩
      exact Subtype.ext (by simpa [← map_mul] using congrArg (fun z : A => lift z.1) this)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA.2 a ha, map_one]
    · rintro _ ⟨a, ha, rfl⟩
      rw [hind]
      exact hAI a ha
    · obtain ⟨a, ha, ha1, haI⟩ := hA0
      refine ⟨lift a, Subgroup.mem_map_of_mem _ ha, fun h => ha1 (hliftInj (h.trans (map_one lift).symm)), ?_⟩
      rw [hind]
      exact haI
    · rw [hind]
      exact hα₀I
  exact KGUniv.kgLangTorusConcl_of_cover hp θ θC I A α₀ κ hκ hκc (hZ _ θC hperf) lift hlift hind hconcl

theorem kgLangTorusNTOn_of_univ (hZ : KGCenterCoprimeInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGNbrLangRegLabel p lab) (hU : KGLangTorusNTUnivOn S) :
    KGLangTorusNTOn S := by
  intro p lab hp hp2 hlab hSp Q hQ
  have h2 := largeEvenLabelAll_hasLabel lab _ (hU p lab hp hp2 hlab hSp Q hQ)
  refine largeEvenRawDatum_mono ?_ h2
  rintro R _ I F ⟨⟨hq, hu⟩, hl⟩
  refine ⟨hq, kgLangTorusNTCont_of_univ hp hu fun K _ _ θ hK => ?_⟩
  refine hZ p hp hp2 lab hlab (hS p lab hSp) K hK ?_
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨e'⟩ => ⟨θ.trans e'⟩) hl

end CFSG.StandardType
