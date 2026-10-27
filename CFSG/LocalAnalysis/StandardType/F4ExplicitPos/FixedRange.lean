module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB2Part2
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Inner
import CFSG.LocalAnalysis.StandardType.GGFamF4Tame
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2

public section

namespace CFSG.StandardType.F4ExplicitPos.FixedRange

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem rankThree_fixedRange (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K Ω]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f) (hk : Nat.card K = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ) (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i)
    (hshape : CFSG.StandardType.TableCRes.FamF4B3Shape (componentRoots χ i) ∨
      CFSG.StandardType.TableCRes.FamF4C3Shape (componentRoots χ i)) :
    ∃ Φ : ↥(StatedSp 3 K) →* ModGL Tag.F4 Ω, Function.Injective Φ ∧
      Φ.range = rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
  classical
  have h3 : compRank (componentRoots χ i) = 3 := by
    rcases hshape with h | h
    · exact (CFSG.StandardType.TableCRes.famF4_b3Shape_rankCard h).1
    · exact (CFSG.StandardType.TableCRes.famF4_c3Shape_rankCard h).1
  have h18 : (componentRoots χ i).ncard = 18 := by
    rcases hshape with h | h
    · exact (CFSG.StandardType.TableCRes.famF4_b3Shape_rankCard h).2
    · exact (CFSG.StandardType.TableCRes.famF4_c3Shape_rankCard h).2
  have hinner : twistInner (componentRoots χ i) ρ :=
    CFSG.StandardType.F4ExplicitPos.RankThreeModels.twistInner_of_compRank_three_ncard_eighteen_generic
      (Ω := Ω) (χ := χ) hρ i h3 h18 hstable
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      (χ := χ) D f hf hq ρ hρ i hker hinner
  have hKq : Nat.card K = D.q := hk.trans hq.symm
  have hFr : ∀ c, σ.toRingHom c = c ^ Nat.card K := by
    intro c
    change σ c = c ^ Nat.card K
    rw [hσc, ← hKq]
  have hz_adj : z ∈ adjointGroup Tag.F4 Ω :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub_le_adjointGroup χ hzZ
  have hfrob_bcgl : frobGL (τ := Tag.F4) σ = bcGL (τ := Tag.F4) σ.toRingHom :=
    CFSG.StandardType.F4ExplicitPos.RankThreeModels.frobGL_eq_bcGL (Ω := Ω) σ
  rcases hshape with ⟨v, hv⟩ | ⟨v, hv⟩
  ·
    have hshapeB : componentRoots χ i = (fun α => v • α) '' b3LeviRoots := by
      rw [hv,
        CFSG.StandardType.F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviB3_eq_b3LeviRoots]
    set n : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω v with hn_def
    have hn_adj : n ∈ adjointGroup Tag.F4 Ω :=
      canonicalRep_mem_adjointGroup (τ := Tag.F4) (coxeterSystem Tag.F4) Ω v
    have hn : bcGL (τ := Tag.F4) σ.toRingHom n = n := by
      rw [hn_def]
      exact bcGL_canonicalRep (τ := Tag.F4) σ.toRingHom (coxeterSystem Tag.F4) v
    have hrange_n : MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalB3.conjBM Ω n) =
        rootSpan Tag.F4 Ω (componentRoots χ i) := by
      rw [hn_def, CFSG.StandardType.F4ExplicitPos.RationalB3.range_conjBM_canonicalRep,
        ← hshapeB]
    have hzH : ∀ g, g ∈ MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalB3.conjBM Ω n) ↔
        z * g * z⁻¹ ∈ MonoidHom.range
          (CFSG.StandardType.F4ExplicitPos.RationalB3.conjBM Ω n) := by
      intro g
      rw [hrange_n]
      exact CFSG.StandardType.F4ExplicitPos.NativePinFinal.normalizesAll_apply hnorm i g
    have hzF : ∀ g ∈ MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalB3.conjBM Ω n),
        D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹ := by
      intro g hg
      rw [hrange_n] at hg
      rw [← hfrob_bcgl]
      exact hgoal g hg
    refine ⟨CFSG.StandardType.F4ExplicitPos.RationalB3.PhiB (K := K) Ω n z, ?_, ?_⟩
    · exact CFSG.StandardType.F4ExplicitPos.RationalB3.PhiB_injective (Ω := Ω) n z
    · rw [CFSG.StandardType.F4ExplicitPos.RationalB3.range_PhiB_eq_inf_model
        (Ω := Ω) (K := K) D σ.toRingHom hFr n z hn_adj hz_adj hn hzH hzF, hrange_n]
  ·
    have hshapeC : componentRoots χ i =
        (fun α => v • α) '' CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet := by
      rw [hv,
        CFSG.StandardType.F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviC3_eq_c3RootSet]
    set n : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω v with hn_def
    have hn_adj : n ∈ adjointGroup Tag.F4 Ω :=
      canonicalRep_mem_adjointGroup (τ := Tag.F4) (coxeterSystem Tag.F4) Ω v
    have hn : bcGL (τ := Tag.F4) σ.toRingHom n = n := by
      rw [hn_def]
      exact bcGL_canonicalRep (τ := Tag.F4) σ.toRingHom (coxeterSystem Tag.F4) v
    have hrange_n : MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM Ω n) =
        rootSpan Tag.F4 Ω (componentRoots χ i) := by
      rw [hn_def, CFSG.StandardType.F4ExplicitPos.RationalC3.range_conjIM_canonicalRep,
        ← hshapeC]
    have hzH : ∀ g, g ∈ MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM Ω n) ↔
        z * g * z⁻¹ ∈ MonoidHom.range
          (CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM Ω n) := by
      intro g
      rw [hrange_n]
      exact CFSG.StandardType.F4ExplicitPos.NativePinFinal.normalizesAll_apply hnorm i g
    have hzF : ∀ g ∈ MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM Ω n),
        D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹ := by
      intro g hg
      rw [hrange_n] at hg
      rw [← hfrob_bcgl]
      exact hgoal g hg
    refine ⟨((MulAut.conj z).toMonoidHom.comp
      (CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM Ω n)).comp
      (statedSpMap (algebraMap K Ω) 3), ?_, ?_⟩
    · exact CFSG.StandardType.F4ExplicitPos.RationalC3.Phi_injective (Ω := Ω) n z
    · rw [CFSG.StandardType.F4ExplicitPos.RationalC3.range_Phi_eq_inf_model
        (Ω := Ω) (K := K) D σ.toRingHom hFr n z hn_adj hz_adj hn hzH hzF, hrange_n]

theorem b2_fixedRange (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K Ω]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f) (hk : Nat.card K = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ) (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i)
    (hshape : CFSG.StandardType.TableCRes.FamF4B2Shape (componentRoots χ i)) :
    ∃ κ : ↥(StatedSp 2 K) →* ModGL Tag.F4 Ω, Function.Injective κ ∧
      κ.range = rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
  classical
  obtain ⟨v, hv⟩ := hshape
  have hS : ∀ γ ∈ b2LeviRoots, IsRoot Tag.F4 γ := fun γ hγ => (mem_b2LeviRoots.1 hγ).1
  let n : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω v
  have hnRange : MonoidHom.range
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n) =
      rootSpan Tag.F4 Ω (componentRoots χ i) := by
    rw [CFSG.StandardType.F4ExplicitPos.RationalB2.range_conjIMB2 Ω n,
      CFSG.RankThree.PartOne.KE.map_conj_rootSpan (L := Ω) v hS, ← hv]
  have hinner : twistInner (componentRoots χ i) ρ :=
    CFSG.StandardType.F4ExplicitPos.B2Inner.b2_component_rho_twistInner
      (D := D) (ρ := ρ) hρ i hv hstable
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      (χ := χ) D f hf hq ρ hρ i hker hinner
  have hKq : Nat.card K = D.q := hk.trans hq.symm
  have hσ : ∀ c, σ c = c ^ Nat.card K := fun c => by rw [hσc c, ← hKq]
  have hn : bcGL (τ := Tag.F4) σ.toRingHom n = n := by
    rw [show n = canonicalRep (coxeterSystem Tag.F4) Ω v from rfl]
    exact bcGL_canonicalRep (τ := Tag.F4) σ.toRingHom (coxeterSystem Tag.F4) v
  have hn_adj : n ∈ adjointGroup Tag.F4 Ω :=
    canonicalRep_mem_adjointGroup (τ := Tag.F4) (coxeterSystem Tag.F4) Ω v
  have hz_adj : z ∈ adjointGroup Tag.F4 Ω :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub_le_adjointGroup χ hzZ
  have hbc : bcGL (τ := Tag.F4) σ.toRingHom = frobGL σ := by
    unfold CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL
    rw [CFSG.StandardType.F4ExplicitPos.BaseChange.bcEndHom_eq_entrywiseHom]
  have hzH : ∀ g, g ∈ MonoidHom.range
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range
        (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n) := by
    intro g
    rw [hnRange]
    exact CFSG.StandardType.F4ExplicitPos.NativePinFinal.normalizesAll_apply hnorm i g
  have hzF : ∀ g ∈ MonoidHom.range
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹ := by
    intro g hg
    rw [hnRange] at hg
    rw [hbc]
    exact hgoal g hg
  let κ : ↥(StatedSp 2 K) →* ModGL Tag.F4 Ω :=
    ((MulAut.conj z).toMonoidHom.comp
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n)).comp
      (statedSpMap (algebraMap K Ω) 2)
  have hκrange : κ.range = rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
    change MonoidHom.range (((MulAut.conj z).toMonoidHom.comp
        (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n)).comp
        (statedSpMap (algebraMap K Ω) 2)) = _
    rw [CFSG.StandardType.F4ExplicitPos.RationalB2.range_PhiB2_eq_inf_model Ω D σ.toRingHom hσ
      n z hn_adj hz_adj hn hzH hzF, hnRange]
  have hκinj : Function.Injective κ := by
    change Function.Injective (((MulAut.conj z).toMonoidHom.comp
      (CFSG.StandardType.F4ExplicitPos.RationalB2.conjIMB2 Ω n)).comp
      (statedSpMap (algebraMap K Ω) 2))
    exact CFSG.StandardType.F4ExplicitPos.RationalB2.PhiB2_injective Ω n z
  exact ⟨κ, hκinj, hκrange⟩

end CFSG.StandardType.F4ExplicitPos.FixedRange

end
