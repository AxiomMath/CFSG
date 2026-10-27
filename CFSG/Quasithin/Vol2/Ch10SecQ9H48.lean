module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H47
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherIntrinsicPoints

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K]

@[expose] def PresPts (α : MulAut (StatedProj (StatedSp 2 K))) : Prop :=
  ∀ L : SpPoint 2 K, ∃ L' : SpPoint 2 K,
    (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K L'.line

theorem map_mul_aut {G : Type*} [Group G] (α β : MulAut G) (H : Subgroup G) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem presPts_one : PresPts (1 : MulAut (StatedProj (StatedSp 2 K))) := fun L =>
  ⟨L, by
    have : (1 : MulAut (StatedProj (StatedSp 2 K))).toMonoidHom = MonoidHom.id _ := rfl
    rw [this, Subgroup.map_id]⟩

theorem presPts_mul {α β : MulAut (StatedProj (StatedSp 2 K))} (hα : PresPts α)
    (hβ : PresPts β) : PresPts (α * β) := fun L => by
  obtain ⟨L₁, h₁⟩ := hβ L
  obtain ⟨L₂, h₂⟩ := hα L₁
  exact ⟨L₂, by rw [map_mul_aut, h₁, h₂]⟩

theorem exists_point_of_finrank {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h : finrank K W = 1) :
    ∃ L : SpPoint 2 K, L.line = W := ⟨⟨W, h⟩, rfl⟩

theorem not_presPts [Finite K] {α : MulAut (StatedProj (StatedSp 2 K))} (hα : ¬ PresPts α)
    (L : SpPoint 2 K) : ∃ W : Submodule K (Fin 2 ⊕ Fin 2 → K), W ≠ ⊥ ∧
      IsTotallyIsotropic (pairedSympForm K 2) W ∧ finrank K W = 2 ∧
        (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K W := by
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : SpPoint 2 K, ∀ L' : SpPoint 2 K,
      (projStabilizer 2 K L₁.line).map α.toMonoidHom ≠ projStabilizer 2 K L'.line := by
    by_contra hc
    exact hα fun L => by
      by_contra h
      exact hc ⟨L, fun L' h' => h ⟨L', h'⟩⟩
  obtain ⟨W, h0, hW, heq⟩ := exists_map_projStabilizer α L₁.line_ne_bot (isTotallyIsotropic_line L₁)
  have hd := one_le_finrank_le_two h0 hW
  have h2 : finrank K W = 2 := by
    by_contra hne
    obtain ⟨L', hL'⟩ := exists_point_of_finrank (W := W) (by omega)
    exact hL₁ L' (by rw [heq, hL'])
  obtain ⟨W₂, h0₂, hW₂, hd₂, heq₂⟩ := exists_map_projStabilizer_of_finrank α
    (isTotallyIsotropic_line L₁) (isTotallyIsotropic_line L)
    (by rw [L₁.finrank_line, L.finrank_line]) hW h0 heq
  exact ⟨W₂, h0₂, hW₂, hd₂.trans h2, heq₂⟩

theorem presPts_inv_mul [Finite K] {α β : MulAut (StatedProj (StatedSp 2 K))} (hα : ¬ PresPts α)
    (hβ : ¬ PresPts β) : PresPts (α⁻¹ * β) := fun L => by
  obtain ⟨W, h0, hW, hd, heq⟩ := not_presPts hβ L
  obtain ⟨W₀, h0₀, hW₀, hd₀, heq₀⟩ := not_presPts hα L
  have hinv : (projStabilizer 2 K W₀).map (α⁻¹).toMonoidHom = projStabilizer 2 K L.line := by
    rw [← heq₀, ← map_mul_aut, inv_mul_cancel]
    exact Subgroup.map_id _
  obtain ⟨W', h0', hW', hd', heq'⟩ := exists_map_projStabilizer_of_finrank α⁻¹ hW₀ hW
    (hd₀.trans hd.symm) (isTotallyIsotropic_line L) L.line_ne_bot hinv
  obtain ⟨L', hL'⟩ := exists_point_of_finrank (W := W') (hd'.trans L.finrank_line)
  exact ⟨L', by rw [map_mul_aut, heq, heq', hL']⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
