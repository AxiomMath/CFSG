module

public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

private theorem ggLAutImage_eq_inducedSub {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hE : E ≤ Subgroup.normalizer (L' : Set M)) :
    ggLAutImage L' θ E = TypeA.inducedSub (ggQuotHom θ) (ggGamma L' hE).range := by
  ext a
  constructor
  · intro ha
    change a ∈ (E.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ) at ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    let b₀ : E := ⟨g.1, Subgroup.mem_subgroupOf.mp hg⟩
    refine ⟨ggGamma L' hE b₀, ⟨b₀, rfl⟩, ?_⟩
    intro l
    have h1 : ggLAut L' θ g = ggBeta L' θ hE b₀ := by
      rw [ggBeta_eq]
    rw [h1]
    exact ggBeta_ggQuotHom L' hE θ b₀ l
  · intro ha
    obtain ⟨γ, ⟨b, rfl⟩, hact⟩ := ha
    change a ∈ (E.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ)
    refine Subgroup.mem_map.mpr ⟨⟨b.1, hE b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, ?_⟩
    symm
    refine TypeA.induced_unique (ggQuotHom θ) (ggQuotHom_surjective θ) hact ?_
    intro l
    have h1 : ggLAut L' θ ⟨b.1, hE b.2⟩ = ggBeta L' θ hE b := by
      rw [ggBeta_eq]
    rw [h1]
    exact ggBeta_ggQuotHom L' hE θ b l

theorem pow_pred_le_card_ggLAutImage {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p r : ℕ}
    (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime) (hr : p ^ r ≤ Nat.card E) :
    p ^ (r - 1) ≤ Nat.card (ggLAutImage L' θ E) := by
  have hγ := TableBBridge.pow_pred_le_card_range hP hp hr
  have hcard : Nat.card (TypeA.inducedSub (ggQuotHom θ) (ggGamma L' hE).range) =
      Nat.card (ggGamma L' hE).range :=
    TypeA.card_inducedSub (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hP.1
      (A := (ggGamma L' hE).range)
      (fun a ha => by
        obtain ⟨φ, -, hφ⟩ := TableBBridge.induces_range_gamma hP a ha
        exact ⟨φ, hφ⟩)
  calc p ^ (r - 1) ≤ Nat.card (ggGamma L' hE).range := hγ
    _ = Nat.card (TypeA.inducedSub (ggQuotHom θ) (ggGamma L' hE).range) := hcard.symm
    _ = Nat.card (ggLAutImage L' θ E) :=
        (congrArg (fun H : Subgroup (MulAut R) => Nat.card H)
          (ggLAutImage_eq_inducedSub (E := E) (θ := θ) hE)).symm

end CFSG.StandardType
