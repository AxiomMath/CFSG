module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Bridge

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
open scoped commutatorElement

theorem eq_highRoot_G2_of_height_eq
    {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    (h : height γ = height (highRoot .G2)) : γ = highRoot .G2 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hcheck : (List.range (Tag.rootCertificate .G2).roots.length).all (fun k =>
      decide (height ((Tag.rootCertificate .G2).root k) ≠ height (highRoot .G2)) ||
        decide (List.ofFn ((Tag.rootCertificate .G2).root k) == List.ofFn (highRoot .G2))) =
      true := by decide +kernel
  have hk' := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hk'
  rcases hk' with hne | heq
  · exact absurd h hne
  · exact RootCertificate.eq_of_ofFn_beq heq

theorem triD4_longRoot_conj
    {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    {β : Fin (Tag.rank .G2) → ℤ} (hl : GGLongRoot (twistedDatum σ) β) :
    ∃ m : twistedGroup σ, (twistedDatum σ).rootGroup β =
      ((twistedDatum σ).rootGroup (highRoot .G2)).map (MulAut.conj m).toMonoidHom := by
  unfold GGLongRoot at hl
  obtain ⟨w, γ₀, hγ₀root, hmax, hβeq⟩ := hl
  have hγ₀isRoot : IsRoot .G2 γ₀ := by
    rw [twistedDatum_roots] at hγ₀root
    exact hγ₀root
  have hhigh : highRoot .G2 ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_highRoot .G2
  have hle1 : height (τ := .G2) (highRoot .G2) ≤ height (τ := .G2) γ₀ :=
    hmax (highRoot .G2) hhigh
  have hle2 : height (τ := .G2) γ₀ ≤ height (τ := .G2) (highRoot .G2) :=
    height_le_height_highRoot (τ := .G2) hγ₀isRoot
  have hγ₀ : γ₀ = highRoot .G2 :=
    eq_highRoot_G2_of_height_eq hγ₀isRoot (le_antisymm hle2 hle1)
  refine ⟨nrep (twistedDatum_isCTGroupDatum σ hσ) w, ?_⟩
  rw [hβeq, hγ₀]
  exact (actsAs_nrep (twistedDatum_isCTGroupDatum σ hσ) w (highRoot .G2) hhigh).symm

theorem ggLongRoot_twistedDatum_single_zero
    {K : Type} [Field K] (σ : K →+* K) :
    GGLongRoot (twistedDatum σ) (Pi.single (ng 0) 1) := by
  have hv : (CFSG.LieType.Chevalley.simple .G2 (ng 1) *
      CFSG.LieType.Chevalley.simple .G2 (ng 0)) • highRoot .G2 = Pi.single (ng 0) 1 := by
    simp only [mul_smul, CFSG.LieType.Chevalley.simple_smul]
    decide +kernel
  refine ⟨CFSG.LieType.Chevalley.simple .G2 (ng 1) * CFSG.LieType.Chevalley.simple .G2 (ng 0),
    highRoot .G2, ?_, fun δ hδ => ?_, hv.symm⟩
  · rw [twistedDatum_roots]
    exact isRoot_highRoot .G2
  · rw [twistedDatum_roots] at hδ
    exact height_le_height_highRoot (τ := .G2) hδ

end CFSG.StandardType.LieKnownR2.TriD4.Bridge
