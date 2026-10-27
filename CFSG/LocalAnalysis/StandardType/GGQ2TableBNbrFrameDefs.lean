module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBNbr

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

structure CodeWeylDatum (R : RawFrameData) (k : R.Code) where
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  coxeter : CoxeterMatrix ι
  cartan : Matrix ι ι ℤ
  coroot : ι → R.V
  root : ι → Dual (ZMod 3) R.V
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod 3)
  refl : ι → (R.V ≃ₗ[ZMod 3] R.V)
  refl_apply : ∀ i v, refl i v = v - root i v • coroot i
  closure_refl : Subgroup.closure (Set.range refl) = R.normalizerGroup k
  ker_iff : ∀ v, (∀ i, root i v = 0) ↔ v ∈ R.cent k

attribute [instance] CodeWeylDatum.instFintype CodeWeylDatum.instDecEq

@[expose] def NbrWeylData (R : RawFrameData) : Prop :=
  ∀ (v : R.V) (k : R.Code), v ≠ 0 → R.admissible k → R.occurs ((ZMod 3) ∙ v) k →
    3 + finrank (ZMod 3) (R.cent k) ≤ finrank (ZMod 3) R.V → Nonempty (CodeWeylDatum R k)

@[expose] def TableBNbrAtFrame (R : RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      ActualFrame (ggG0 p B x L D J) Bs R →
      ∀ [Fact p.Prime] {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
        ∃ M : GGQ2NbrDatum p Bs K, 3 ≤ Fintype.card M.Λ

theorem ggQ2TableBNbr_of_placement {catalogue : FrameKind → RawFrameData}
    (hp : PlacementInput catalogue) (h : ∀ kind, TableBNbrAtFrame (catalogue kind)) :
    GGQ2TableBNbr := by
  intro G _ _ p B Bs x L D J hS hp3 hI1 _ y K hnb
  obtain ⟨kind, hF⟩ := hp hS hp3
  exact h kind hS hp3 hI1 hF hnb

end CFSG.StandardType.GGQ2Frame

end
