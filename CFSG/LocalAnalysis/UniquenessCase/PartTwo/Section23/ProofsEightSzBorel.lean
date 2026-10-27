module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSz
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open CFSG.SectionRank
open scoped Pointwise

private theorem card_torusSub (m : ℕ) (hm : 0 < m) :
    Nat.card (torusSub m) = 2 ^ (2 * m + 1) - 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  have hbij : Function.Bijective
      (fun x : Kˣ => (⟨torus m x, torus_mem m x⟩ : torusSub m)) := by
    refine ⟨fun x y hxy => szTorus_injective m (Subtype.ext_iff.mp hxy), fun g => ?_⟩
    obtain ⟨x, hx⟩ := (mem_torusSub m hm).mp g.2
    exact ⟨x, Subtype.ext hx.symm⟩
  calc Nat.card (torusSub m) = Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card K - 1 := Nat.card_units K
    _ = 2 ^ (2 * m + 1) - 1 := by rw [natCard_binaryGaloisField]

private theorem exists_torus_normalizing (m : ℕ) (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m)) :
    ∃ D : Subgroup (SuzukiMatrixGroup m), Nat.card D = 2 ^ (2 * m + 1) - 1 ∧
      D ≤ Subgroup.normalizer ((S : Subgroup (SuzukiMatrixGroup m)) : Set _) := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_rootSub m hm
  haveI : MulAction.IsPretransitive (SuzukiMatrixGroup m)
      (Sylow 2 (SuzukiMatrixGroup m)) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := SuzukiMatrixGroup m) R S
  have hS : (S : Subgroup (SuzukiMatrixGroup m)) =
      (rootSub m).map (MulAut.conj g).toMonoidHom := by
    rw [← congrArg (fun P : Sylow 2 (SuzukiMatrixGroup m) =>
      (P : Subgroup (SuzukiMatrixGroup m))) hg, Sylow.coe_subgroup_smul, hR,
      CFSG.GroupActions.mulAut_smul_subgroup_eq_map]
  refine ⟨(torusSub m).map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_torusSub m hm
  · have hTH : (torusSub m).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer
          (((rootSub m).map (MulAut.conj g).toMonoidHom :
            Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono (torusSub_le_normalizer m)
    rwa [← hS] at hTH

theorem kSzBorel_holds : KSzBorel := by
  intro X _ _ a hSz S
  obtain ⟨m, hm, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  let e' : X ≃* SuzukiMatrixGroup m :=
    e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv m)
  let S' : Sylow 2 (SuzukiMatrixGroup m) :=
    Sylow.mapSurjective (f := e'.toMonoidHom) e'.surjective S
  have hS' : (S' : Subgroup (SuzukiMatrixGroup m)) =
      (S : Subgroup X).map e'.toMonoidHom := rfl
  obtain ⟨D, hDcard, hDnorm⟩ := exists_torus_normalizing m hm S'
  refine ⟨D.comap e'.toMonoidHom, ?_, ?_⟩
  · have hcard : Nat.card (D.comap e'.toMonoidHom) = Nat.card D := by
      rw [Subgroup.comap_equiv_eq_map_symm',
        Subgroup.card_map_of_injective e'.symm.injective]
    rw [hcard, hDcard]
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    have hx' : e' x ∈ Subgroup.normalizer
        ((S' : Subgroup (SuzukiMatrixGroup m)) : Set _) := hDnorm hx
    have hle : x ∈ Subgroup.normalizer
        (((S' : Subgroup (SuzukiMatrixGroup m))).comap e'.toMonoidHom : Set X) :=
      Subgroup.le_normalizer_comap e'.toMonoidHom hx'
    have hScomap : ((S' : Subgroup (SuzukiMatrixGroup m)).comap e'.toMonoidHom :
        Subgroup X) = (S : Subgroup X) := by
      rw [hS', Subgroup.comap_map_eq_self_of_injective e'.injective]
    rwa [hScomap] at hle

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
