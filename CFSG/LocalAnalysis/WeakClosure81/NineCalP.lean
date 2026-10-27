module

public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.WeakClosure81.SixTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

theorem calP_mono {X Y : Subgroup G} (hX : X ∈ calP V) (hYX : Y ≤ X) : Y ∈ calP V := by
  rcases hX with ⟨p, hp, hp2, hXp, hXM, hXG, hXtriv⟩
  refine ⟨p, hp, hp2, hXp.to_le hYX, hYX.trans hXM, ?_, ?_⟩
  · have hmono := CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := p) (k := 1) hYX
    exact hmono.trans hXG
  · intro g hg hVg
    have hle : Y ⊓ conjSubgroup (normalizer (V : Set G)) g ≤
        X ⊓ conjSubgroup (normalizer (V : Set G)) g := inf_le_inf_right _ hYX
    rw [hXtriv g hg hVg, le_bot_iff] at hle
    exact hle

theorem calP_conj {X : Subgroup G} (hX : X ∈ calP V) {m : G} (hm : m ∈ normalizer (V : Set G)) :
    conjSubgroup X m ∈ calP V := by
  rcases hX with ⟨p, hp, hp2, hXp, hXM, hXG, hXtriv⟩
  have hMm : conjSubgroup (normalizer (V : Set G)) m = normalizer (V : Set G) :=
    (conjSubgroup_eq_iff_mem_normalizer).2 (Subgroup.le_normalizer hm)
  refine ⟨p, hp, hp2, isPGroup_conjSubgroup hXp m, ?_, ?_, ?_⟩
  · exact (conjSubgroup_mono_left m hXM).trans_eq hMm
  · rw [rankThreeGamma_conjSubgroup]
    exact (conjSubgroup_mono_left m hXG).trans_eq hMm
  · intro g hg hVg
    have hgm : g * m⁻¹ ∉ normalizer (V : Set G) := by
      intro hmem
      apply hg
      have hg_eq : g = (g * m⁻¹) * m := by group
      rw [hg_eq]
      exact mul_mem hmem hm
    have hVgm : conjSubgroup V (g * m⁻¹) ≤ normalizer (V : Set G) := by
      rw [← conjSubgroup_conjSubgroup]
      have h1 : conjSubgroup (conjSubgroup V g) m⁻¹ ≤
          conjSubgroup (normalizer (V : Set G)) m⁻¹ := conjSubgroup_mono_left m⁻¹ hVg
      have hMm' : conjSubgroup (normalizer (V : Set G)) m⁻¹ = normalizer (V : Set G) :=
        (conjSubgroup_eq_iff_mem_normalizer).2
          (Subgroup.le_normalizer (inv_mem hm))
      exact h1.trans_eq hMm'
    have htriv := hXtriv (g * m⁻¹) hgm hVgm
    have hkey : conjSubgroup X m ⊓ conjSubgroup (normalizer (V : Set G)) g =
        conjSubgroup (X ⊓ conjSubgroup (normalizer (V : Set G)) (g * m⁻¹)) m := by
      rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, show g * m⁻¹ * m = g by group]
    rw [hkey, htriv, conjSubgroup_bot]

end CFSG.LocalAnalysis.WeakClosure81
