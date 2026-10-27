module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs
import CFSG.LieType.Steinberg.Adjoint.Presentation

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section WeylSq

private theorem weylElement_mul_self_eq_one {τ : CFSG.Blueprint.Chevalley.Tag} {K : Type}
    [Field K] [CharP K 2] (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i * CFSG.LieType.Chevalley.weylElement τ K i = 1 := by
  have hneg : (-1 : Kˣ) = 1 := by
    apply Units.ext
    rw [Units.val_neg, Units.val_one, neg_one_eq_one_iff.mpr (ringChar.eq K 2)]
  have hsq : CFSG.LieType.Chevalley.weylElement τ K i ^ 2 =
      CFSG.LieType.Chevalley.torusElement τ K i (-1) := by
    apply Subtype.ext
    exact CFSG.LieType.Chevalley.weylElt_one_sq τ K i
  rw [sq] at hsq
  rw [hsq, hneg, CFSG.LieType.Steinberg.Adjoint.torusElement_one_eq]

end WeylSq

section Tag

variable {G : Type} [Group G] [Finite G]

theorem ggTagFacts_F4 {n f : ℕ} (hadm : StatedLieAdmissible .F4 n 2 f)
    (hrank : 3 ≤ bnRank .F4 n) : GGTagFacts .F4 n f := by
  have hD : (ggU .F4 n f).D = CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f) := rfl
  have hrank4 : (CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f)).rank = 4 := rfl
  unfold GGTagFacts
  rw [hD]
  refine ⟨?_, ?_⟩
  · rw [hrank4]
    norm_num
  · exact ggUniversalFacts_of_steinberg
      (D := CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f))
      (n := CFSG.LieType.Chevalley.weylElement .F4 (GaloisField 2 f))
      (H := CFSG.LieType.Steinberg.Adjoint.torus (τ := .F4) (GaloisField 2 f))
      (by rw [hrank4]; norm_num)
      (CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum (GaloisField 2 f))
      (CFSG.LieType.Steinberg.Adjoint.f4_steinbergExtras (GaloisField 2 f))
      (fun i => weylElement_mul_self_eq_one (τ := .F4) (K := GaloisField 2 f) i)

theorem ggTagFacts_E8 {n f : ℕ} (hadm : StatedLieAdmissible .E8 n 2 f)
    (hrank : 3 ≤ bnRank .E8 n) : GGTagFacts .E8 n f := by
  have hD : (ggU .E8 n f).D = CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f) := rfl
  have hrank8 : (CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f)).rank = 8 := rfl
  unfold GGTagFacts
  rw [hD]
  refine ⟨?_, ?_⟩
  · rw [hrank8]
    norm_num
  · exact ggUniversalFacts_of_steinberg
      (D := CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f))
      (n := CFSG.LieType.Chevalley.weylElement .E8 (GaloisField 2 f))
      (H := CFSG.LieType.Steinberg.Adjoint.torus (τ := .E8) (GaloisField 2 f))
      (by rw [hrank8]; norm_num)
      (CFSG.LieType.Steinberg.Adjoint.e8_isCTGroupDatum (GaloisField 2 f))
      (CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras (GaloisField 2 f))
      (fun i => weylElement_mul_self_eq_one (τ := .E8) (K := GaloisField 2 f) i)

theorem ggSecFivePres_of_psi_E8 {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .E8 n 2 f) (hrank : 3 ≤ bnRank .E8 n)
    (ψ : (ggU .E8 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E8 n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .E8 n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_E8 hadm hrank) ψ hker hrange

end Tag

end CFSG.StandardType

end
