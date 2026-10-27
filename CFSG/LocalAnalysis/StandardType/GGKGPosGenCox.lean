module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section GenCox

private theorem exists_weylAction_of_mem_roots {U : Type*} [Group U] (D : UniversalRootDatum U)
    (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      γ = weylAction D.isFiniteType w (Pi.single i 1) := by
  change γ ∈ roots D.isFiniteType D.divisible at hγ
  rw [roots, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hγ
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact ⟨w, i, rfl⟩
  · rw [hdiv] at hi
    simp at hi

private theorem ggU_divisible_eq_empty {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    (ggU t n f).D.divisible = ∅ := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · cases n with
    | zero => simp only [ggU, lieUniversal]; rfl
    | succ m => simp only [ggU, lieUniversal]; rfl
  · by_cases hn : 3 ≤ n
    · have e : ggU .POmegaPlus n f =
          ⟨↥(spinGroup (Spin.quadPlus n (GaloisField 2 f))),
            Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [e]
      rfl
    · have e : ggU .POmegaPlus n f = trivialUniversal := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [e]
      rfl
  · simp only [ggU, lieUniversal]
    rfl
  · simp only [ggU, lieUniversal]
    rfl
  · simp only [ggU, lieUniversal]
    rfl

theorem ggSecFiveGenCoxInput_of_kgPos (hKG : GGSecFiveKGPosInput) : GGSecFiveGenCoxInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 X hX hXs
  obtain ⟨t, n, f, ψ, hadm, h3t, hker, hrange, ht, hdvd, hpos⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 X hX hXs
  unfold GGTableBPos at hpos
  obtain ⟨ε, hεrefl, hεlevi, _⟩ := hpos
  have hdiv : (ggU t n f).D.divisible = ∅ := ggU_divisible_eq_empty ht
  have hgen : ggSub (ggU t n f).D (ggU t n f).D.roots = ⊤ :=
    (ggTagFacts_of_admissible hadm h3t).2.2.1
  refine le_antisymm ?_ ?_
  ·
    conv_lhs => rw [← hrange]
    rw [MonoidHom.range_eq_map, ← hgen, ggSub]
    simp only [Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨w, i, rfl⟩ := exists_weylAction_of_mem_roots (ggU t n f).D hdiv hγ
    have hlevi := hεlevi w i
    simp only [ggRootLevi] at hlevi
    refine le_trans (Subgroup.map_mono (le_sup_left : (ggU t n f).D.rootGroup
      (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ≤
      (ggU t n f).D.rootGroup (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ⊔
      (ggU t n f).D.rootGroup (-(weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))))) ?_
    rw [← hlevi]
    refine le_iSup₂ (f := fun r (_ : r ∈ {r : MulAut ↥Bs |
        r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e}) => ggRankOneIn X Bs r) _ ⟨?_, ?_⟩
    · exact (ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)).2
    · refine ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (ggAutomizer_le_ggAutomizerJoin hX
          (ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)).2) ?_
      have hconj : ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
            ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
          ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
            ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) :
              ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
            ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)⁻¹ := by
        simp [map_mul, map_inv]
      rw [hconj]
      exact (hεrefl i).conj ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
  ·
    refine iSup₂_le fun r _ => (ggOTwoPrime_le _).trans inf_le_left

end GenCox

end CFSG.StandardType
