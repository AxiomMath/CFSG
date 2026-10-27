module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_2_2 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h15 : Lemma1515Concl T Mc M) (htwo : IsGreatestOrd T M) {X : Subgroup G} (hTX : T ≤ X)
    (hXM : X ≤ M)
    (hX : (m0Of T Mc M : Set G) ⊆ (X : Set G) *
          ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) ∨
        (m0Of T Mc M : Set G) ⊆ (X : Set G) *
          ((M ⊓ Subgroup.normalizer
            ((quasithinOmegaOneCenter T ⊓ V154 T Mc M : Subgroup G) : Set G) : Subgroup G) :
              Set G)) :
    IsUniqueM X M := by
  have hMT : InM T M := hM.1.1
  refine ⟨⟨hMT.1, hXM⟩, fun M₁ hM₁ => ?_⟩
  have hM₁T : InM T M₁ := ⟨hM₁.1, hTX.trans hM₁.2⟩
  have hord : OrdLE T M₁ M := htwo.2 M₁ hM₁T
  have hVE : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ h hMT)
  have hVp : IsPGroup 2 (V154 T Mc M) := fun x => ⟨1, Subtype.ext (by simpa using hVE.2 x x.2)⟩
  have hgen : V154 T Mc M =
      conjClosure (V154 T Mc M ⊓ quasithinOmegaOneCenter T) (M₁ ⊓ M) := by
    apply le_antisymm
    · refine h15.gen.le.trans (conjClosure_le fun m hm z hz => ?_)
      have hzV := hz.2
      have hzZ := hz.1
      have hz' : z ∈ V154 T Mc M ⊓ quasithinOmegaOneCenter T := ⟨hzV, hzZ⟩
      rcases hX with hX | hX
      · obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp (hX hm)
        have hcz : (c : G) * z * c⁻¹ = z := by
          have := Subgroup.mem_centralizer_iff.mp hc.2 z hzV
          rw [← this]; group
        have : x * c * z * (x * c)⁻¹ = x * z * x⁻¹ := by
          rw [show x * c * z * (x * c)⁻¹ = x * (c * z * c⁻¹) * x⁻¹ by group, hcz]
        rw [this]
        exact mem_conjClosure (show x ∈ M₁ ⊓ M from ⟨hM₁.2 hx, hXM hx⟩) hz'
      · obtain ⟨x, hx, n, hn, rfl⟩ := Set.mem_mul.mp (hX hm)
        have hnz : n * z * n⁻¹ ∈ quasithinOmegaOneCenter T ⊓ V154 T Mc M :=
          (Subgroup.mem_normalizer_iff.mp hn.2 z).mp hz
        have hnz' : n * z * n⁻¹ ∈ V154 T Mc M ⊓ quasithinOmegaOneCenter T := ⟨hnz.2, hnz.1⟩
        have : x * n * z * (x * n)⁻¹ = x * (n * z * n⁻¹) * x⁻¹ := by group
        rw [this]
        exact mem_conjClosure (show x ∈ M₁ ⊓ M from ⟨hM₁.2 hx, hXM hx⟩) hnz'
    · refine conjClosure_le fun m hm z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_V154 T Mc M hm.2) z).mp hz.1
  have hle : M₁ ≤ M :=
    le_of_ordLE_of_normal hMT.1 hord (V154_ne_bot h) hVp (le_normalizer_V154 T Mc M) hgen
  exact (hM₁.1.2 M hMT.1.1 hle).symm

end CFSG.Quasithin
