module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PerfectC3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2SmallJ
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LiteralSetup

@[expose] public section

public noncomputable section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

open CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Assembly

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.FixedImage

open CFSG.StandardType.F4ExplicitPos.ActualSetup

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.LiteralSetup

namespace CFSG.StandardType.F4ExplicitPos.ActualPerfect

variable {X : Type} [Group X] [Finite X]

theorem isPerfect_adjointGroup_F4_galoisField
    (f : ℕ) :
    Group.IsPerfect ↥(adjointGroup .F4 (GaloisField 2 f)) :=
  _root_.CFSG.StandardType.F4ExplicitPos.PerfectC3.finiteF4perfection (K := GaloisField 2 f)

theorem f4_actual_model_perfect
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {G0 B1 : Subgroup X}
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (_hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (_hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : F4Omega f →+* F4Omega f) (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup .F4) {g0 : ModGL .F4 (F4Omega f)}
    (hg0C : g0 ∈ adjointGroup .F4 (F4Omega f))
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr ⟨g0, hg0C⟩ :
      adjointGroup .F4 (F4Omega f)) : ModGL .F4 (F4Omega f)) =
      g0 * canonicalRep (coxeterSystem .F4) (F4Omega f) w) :
    Group.IsPerfect
      ↥(langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).model := by
  have hcenter : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_F4_galoisField f
  have hF4 : Group.IsPerfect ↥(adjointGroup .F4 (GaloisField 2 f)) :=
    isPerfect_adjointGroup_F4_galoisField f
  have hG0perf : Group.IsPerfect ↥G0 := by
    have : Group.IsPerfect ↥(adjointGroup .F4 (GaloisField 2 f)) := hF4
    exact Group.IsPerfect.ofSurjective
      (f := (eF4 ψ G0 hG0 hker hcenter).toMonoidHom)
      (eF4 ψ G0 hG0 hker hcenter).surjective
  have : Group.IsPerfect ↥G0 := hG0perf
  have hRangePerf : Group.IsPerfect
      ↥(etaF4 (L := F4Omega f) ψ G0 hG0 hker hcenter g0).range :=
    Group.IsPerfect.range (f := etaF4 (L := F4Omega f) ψ G0 hG0 hker hcenter g0)
  rwa [etaF4_range_model (K := GaloisField 2 f) (L := F4Omega f) ψ G0 hG0 hker hcenter
    Fr hFr w hg0C hg0] at hRangePerf

theorem f4_langDatum_gamma_eq_model
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {G0 B1 : Subgroup X}
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : F4Omega f →+* F4Omega f) (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup .F4) {g0 : ModGL .F4 (F4Omega f)}
    (hg0C : g0 ∈ adjointGroup .F4 (F4Omega f))
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr ⟨g0, hg0C⟩ :
      adjointGroup .F4 (F4Omega f)) : ModGL .F4 (F4Omega f)) =
      g0 * canonicalRep (coxeterSystem .F4) (F4Omega f) w) :
    (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).Γ =
      (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).model := by
  have : Group.IsPerfect
      ↥(langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).model :=
    f4_actual_model_perfect hG0 hker hBN hinner Fr hFr w hg0C hg0
  simpa only [LangDatum.Γ] using
    (Subgroup.commutator_eq_self
      (H := (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) Fr hFr w hg0C hg0).model))

theorem fixed_range_le_component_ambient {G : Type*} [Group G]
    {Γ M H Ccent N : Subgroup G} (hΓ : Γ = M) (hH : H ≤ Ccent) (hN : N = H ⊓ M) :
    N ≤ Γ ⊓ Ccent := by
  rw [hN, hΓ]
  exact le_inf inf_le_right (inf_le_left.trans hH)

theorem f4_actual_etaJ_injective_range
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {G0 : Subgroup X}
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (g0 : ModGL .F4 (F4Omega f)) {J : Subgroup X} (hJG : J ≤ G0) :
    Function.Injective ((etaF4 (L := F4Omega f) ψ G0 hG0 hker
        (center_adjointGroup_F4_galoisField f) g0).comp (Subgroup.inclusion hJG)) ∧
      ((etaF4 (L := F4Omega f) ψ G0 hG0 hker
        (center_adjointGroup_F4_galoisField f) g0).comp (Subgroup.inclusion hJG)).range =
        (J.subgroupOf G0).map (etaF4 (L := F4Omega f) ψ G0 hG0 hker
          (center_adjointGroup_F4_galoisField f) g0) := by
  constructor
  · exact (etaF4_injective (L := F4Omega f) ψ G0 hG0 hker
      (center_adjointGroup_F4_galoisField f) g0).comp (Subgroup.inclusion_injective hJG)
  · rw [← MonoidHom.map_range (etaF4 (L := F4Omega f) ψ G0 hG0 hker
      (center_adjointGroup_F4_galoisField f) g0) (Subgroup.inclusion hJG),
      Subgroup.inclusion_range]

end CFSG.StandardType.F4ExplicitPos.ActualPerfect

end

end
