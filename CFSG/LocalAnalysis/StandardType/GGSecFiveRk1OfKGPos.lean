module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGRankOneRootMatch
public import CFSG.LocalAnalysis.StandardType.GGRankOneTags
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

private theorem exists_sl2_range_rankOne {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
      φ.range = CFSG.LieType.CurtisTits.rankOne D.rootGroup i := by
  unfold GGRankOneModel at hM
  obtain ⟨x, C, O, hE, -⟩ := hM
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · rintro y ⟨M, rfl⟩
    have hM' : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hM'
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩

theorem ggSecFiveRk1Input_of_kgPos
    (hKG : GGSecFiveKGPosInput) (hL1 : GGSecFiveL1CoxInput) (hSplit : GGSecFiveSplitNbrInput) :
    GGSecFiveRk1Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX r hrA hrC
  have hXs : GGSplitLie p X := by
    rcases hX with hXL | hK
    · rw [hXL]
      exact hsplit
    · exact hSplit G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hK
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  obtain ⟨t, n, f, ψ, hadm, h3, hker, hrange, htag, hpf, hpos⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs
  unfold GGTableBPos at hpos
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hrk : 2 ≤ (ggU t n f).D.rank :=
    two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm h3
  let i₁ : Fin (ggU t n f).D.rank := ⟨0, by omega⟩
  let r₀ : MulAut ↥Bs :=
    ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁) :
      ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
  have hr₀A : r₀ ∈ ggAutomizer X Bs :=
    (ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁)).2
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin hX hr₀A) (hεrefl i₁)
  have hperf₀ : ggRankOnePerf Bs r₀ = ggRankOneIn X Bs r₀ :=
    hL1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX r₀ hr₀A hr₀C
  have hperf : ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
    hL1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX r hrA hrC
  have hlevi₁ : ggRankOneIn X Bs r₀ =
      (ggRootLevi (ggU t n f).D (Pi.single i₁ 1)).map ψ := by
    have h := hεlevi 1 i₁
    simp only [one_mul, inv_one, mul_one, map_one, Module.End.one_apply] at h
    exact h
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hrC
  obtain ⟨g, -, -, hg⟩ :=
    mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 haA)
  have hconj : (ggRankOnePerf Bs r₀).map (MulAut.conj g).toMonoidHom = ggRankOnePerf Bs r := by
    rw [ggRankOnePerf_map_conj hg r₀, ← hra]
  have hMod : GGRankOneModel (ggU t n f).D (GaloisField 2 f) :=
    ggRankOneModel_of_tag htag hadm h3
  obtain ⟨φ, hφinj, hφrange⟩ := exists_sl2_range_rankOne hMod i₁
  let θ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G :=
    (MulAut.conj g).toMonoidHom.comp (ψ.comp φ)
  haveI hchar : CharP (GaloisField 2 f) 2 := inferInstance
  have hψφinj : Function.Injective (ψ.comp φ) :=
    PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
  have hθinj : Function.Injective θ := (MulAut.conj g).injective.comp hψφinj
  have hθrange : θ.range = ggRankOneIn X Bs r := by
    change ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)).range = ggRankOneIn X Bs r
    rw [← MonoidHom.map_range (MulAut.conj g).toMonoidHom (ψ.comp φ)]
    rw [← MonoidHom.map_range ψ φ]
    rw [hφrange]
    have hlevi' : (CFSG.LieType.CurtisTits.rankOne (ggU t n f).D.rootGroup i₁).map ψ =
        (ggRootLevi (ggU t n f).D (Pi.single i₁ 1)).map ψ := rfl
    rw [hlevi']
    rw [← hlevi₁]
    rw [← hperf₀]
    rw [hconj, hperf]
  have hr2 : r * r = 1 := by
    have h := (ggCoxRefl_isReflection hpres.2 hrC).1
    simpa [pow_two] using h
  obtain ⟨n', hn'in, hn'N, hn'act⟩ := ggExists_weylElt_of_mem_ggAutomizer hrA hr2
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, θ, ?_, hθinj, hθrange,
    ⟨n', hn'in, hn'N, hn'act⟩, ?_, ?_⟩
  · infer_instance
  · intro _
    rw [GaloisField.card 2 f (by have hf : 1 ≤ f := hadm.2.1; omega)]
    exact hpf
  · intro hns
    exact absurd hXs hns

end CFSG.StandardType

end
