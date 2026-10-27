module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2POmegaPosDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSUPos
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.OmegaSmallPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.OmegaSmallMinus

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.LieKnownR2.POmega

private theorem pomega_ns_of_component {X : Type} [Group X] {J G₀ D : Subgroup X}
    (h : CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    ¬ Group.IsSolvable ↥J := by
  haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr h.2.2.1
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := h.2.2.2
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  exact Group.IsPerfect.not_isSolvable ↥J

private theorem pomega_itemTwo_orth
    {t'' : StatedLieTag} (ht'' : t'' = .POmegaPlus ∨ t'' = .POmegaMinus) {f mK : ℕ}
    (hf : 1 ≤ f) (hmK : 3 ≤ mK) (hf2 : mK = 3 → 2 ≤ f) {X : Type} [Group X] [Finite X]
    (φK : (ggU t'' mK f).K →* X) (hker : φK.ker ≤ Subgroup.center (ggU t'' mK f).K)
    {βK : Fin (ggU t'' mK f).D.rank → ℤ} (hβK : βK ∈ (ggU t'' mK f).D.roots)
    (hlong : GGLongRoot (ggU t'' mK f).D βK) (uK : (ggU t'' mK f).K) :
    GGRootInnerAt φK.range (ggRootSub (ggU t'' mK f).D φK βK uK) ∧
      GGRootNoCentralAt φK.range (ggRootSub (ggU t'' mK f).D φK βK uK) := by
  rcases ht'' with rfl | rfl
  · rcases Nat.lt_or_ge mK 4 with h4 | h4
    · obtain rfl : mK = 3 := by omega
      exact ggRootItemTwo_pomegaPlus_three (hf2 rfl) φK hker hβK hlong uK
    · exact ⟨ggRootInnerAt_ggU_pomegaPlus h4 φK hker hβK uK,
        ggRootNoCentralAt_ggU_pomegaPlus h4 φK hker hβK uK⟩
  · rcases Nat.lt_or_ge mK 4 with h4 | h4
    · obtain rfl : mK = 3 := by omega
      exact ggRootItemTwo_pomegaMinus_three hf φK hker hβK hlong uK
    · exact ⟨ggRootInnerAt_ggU_pomegaMinus h4 φK hker hβK hlong uK,
        ggRootNoCentralAt_ggU_pomegaMinus h4 φK hker hβK hlong uK⟩

private theorem pomega_itemThree
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n f p : ℕ} (hn : 4 ≤ n)
    {X : Type} [Group X] [Finite X] (ψ : (ggU t n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) {R Rm : Subgroup X}
    (hpos0 : GGRootPosG0 t n f p ψ R Rm) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  obtain ⟨β, hβ, hlong, u, hRβ, -⟩ := hpos0
  rcases ht with rfl | rfl
  · exact itemThree_ggU_pomegaPlus hn ψ hker hβ u hRβ
  · have hl : GGLongRoot (ggU .POmegaMinus n f).D β := by
      rcases hlong with hl | ⟨hbad, -⟩
      · exact hl
      · exfalso
        rcases hbad with h | h | ⟨h | h, -⟩ <;> exact absurd h (by decide)
    exact itemThree_ggU_pomegaMinus hn ψ hker hβ hl u hRβ

theorem ggSixLieKnownPos_POmega_of_explicit
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hpos : GGSixPOmegaPosExplicit t) : GGSixLieKnownPos t := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hadm : StatedLieAdmissible t n 2 f := h3.admissible
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ n := by
    rcases ht with rfl | rfl
    · exact hadm.2.2
    · exact hadm.2.2
  have hH : CFSG.StandardType.ClassicalPosition.GGSixPosHyp t n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hcases⟩ := hpos X n f ψ p G₀ B₁ D J L x hH
  have hB₁p : IsPGroup p B₁ := by
    intro b
    refine ⟨1, Subtype.ext ?_⟩
    simpa using h9.2 b b.2
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases with hcase1 | hcase2 | hcase3
    · obtain ⟨t', mJ, βJ, ht', hmJ3, hβJ, hlongJ, hviaJ, hnbr⟩ := hcase1
      obtain ⟨t'', mK, βK, ht'', hlt, hβK, hlongK, hviaK⟩ :=
        hnbr e he hene K hKG hKcomp hJK hKne hKodd
      obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
      have hmain := pomega_itemTwo_orth ht'' hf (by omega) (fun h => by omega) φK hφKker hβK
        hlongK uK
      rw [hφKrange, ← hRKdef] at hmain
      exact hmain
    · obtain ⟨kJ, βJ, hβJ, hviaJ, hnbr⟩ := hcase2
      obtain ⟨φJ, hφJrange, hφJker, uJ, hRJdef⟩ := hviaJ
      have hJns : ¬ Group.IsSolvable ↥φJ.range := by
        rw [hφJrange]
        exact pomega_ns_of_component h15
      have hdimJ := PSL.jDim_psl hf φJ hφJker hJns h5 h6 hB₁p
        (hφJrange ▸ h13) (hφJrange ▸ h14) h10 h12
      rcases hnbr e he hene K hKG hKcomp hJK hKne hKodd with
        ⟨kK, βK, hlt, hβK, hviaK⟩ | ⟨t'', mK, βK, ht'', hmK3, hle, hβK, hlongK, hviaK⟩
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hmain := PSL.itemTwo_of_models hf hlt φJ hφJker hJns h5 h6 hB₁p
          (hφJrange ▸ h13) (hφJrange ▸ h14) h10 h12 φK hφKker hβK uK hRKdef
        rw [hφKrange] at hmain
        exact hmain
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hf2 : mK = 3 → 2 ≤ f := by
          intro h3K
          rcases hdimJ with ⟨hf1, h3⟩ | ⟨hf2, -⟩ | ⟨hf3, -⟩ <;> omega
        have hmain := pomega_itemTwo_orth ht'' hf hmK3 hf2 φK hφKker hβK hlongK uK
        rw [hφKrange, ← hRKdef] at hmain
        exact hmain
    · obtain ⟨m'J, βJ, hβJ, hviaJ, hnbr⟩ := hcase3
      obtain ⟨φJ, hφJrange, hφJker, uJ, hRJdef⟩ := hviaJ
      have hJns : ¬ Group.IsSolvable ↥φJ.range := by
        rw [hφJrange]
        exact pomega_ns_of_component h15
      have hJdim := PSU.jDim_selfDual_psu φJ hJns
      rcases hnbr e he hene K hKG hKcomp hJK hKne hKodd with
        ⟨m'K, βK, hlt, hβK, hlong, hviaK⟩ | ⟨t'', mK, βK, ht'', hmK3, hle, hβK, hlongK, hviaK⟩
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hm'K3 : 3 ≤ m'K := by omega
        have hne : ¬ (m'K = 3 ∧ f = 1) := by
          rintro ⟨hm'K3', hf1⟩
          have hm'J2 : m'J = 2 := by omega
          have hf2 : 2 ≤ f := hJdim.2 (by omega)
          omega
        have hmain := PSU.ggRootInnerAt_ggU_psu hm'K3 hne φK hφKker hβK (Or.inl hlong) uK
        have hmain2 := PSU.ggRootNoCentralAt_ggU_psu hm'K3 hne φK hφKker hβK (Or.inl hlong) uK
        rw [hφKrange, ← hRKdef] at hmain hmain2
        exact ⟨hmain, hmain2⟩
      · obtain ⟨φK, hφKrange, hφKker, uK, hRKdef⟩ := hviaK
        have hf2 : mK = 3 → 2 ≤ f := by
          intro h3K
          exact hJdim.2 (by omega)
        have hmain := pomega_itemTwo_orth ht'' hf hmK3 hf2 φK hφKker hβK hlongK uK
        rw [hφKrange, ← hRKdef] at hmain
        exact hmain
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    exact pomega_itemThree ht hn4 ψ h2 hpos0 Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnown_POmegaPlus_of_explicit
    (hpos : GGSixPOmegaPosExplicit .POmegaPlus) : GGSixLieKnown .POmegaPlus :=
  ggSixLieKnown_of_pos_POmegaPlus (ggSixLieKnownPos_POmega_of_explicit (Or.inl rfl) hpos)

theorem ggSixLieKnown_POmegaMinus_of_explicit
    (hpos : GGSixPOmegaPosExplicit .POmegaMinus) : GGSixLieKnown .POmegaMinus :=
  ggSixLieKnown_of_pos_POmegaMinus (ggSixLieKnownPos_POmega_of_explicit (Or.inr rfl) hpos)

end CFSG.StandardType.LieKnownR2.POmega

end
