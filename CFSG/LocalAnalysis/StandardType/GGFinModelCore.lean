module

public import CFSG.LocalAnalysis.StandardType.GGFinModelTorus
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFCore

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Core

theorem ggPsiU_range_eq_conj
    (t : StatedLieTag) (n f : ℕ) :
    (ggPsiU t n f).range = (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)).range := by
  unfold ggPsiU
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (Subgroup.center (ggU t n f).K)),
    Subgroup.map_top]

namespace GGTorusData

theorem ggBfull_index_inner_psi
    {t : StatedLieTag} {n f : ℕ} {τ : Tag} {R p : ℕ} [NeZero p] {hR : R = τ.rank}
    {π : Equiv.Perm (Fin R)} {D : LangDatum τ GGL} {ι₀ : GGKb t n f →* ModGL τ GGL} {ζ : GGLˣ}
    (hT : GGTorusData hR p π D ι₀ ζ) (hp3 : 3 ≤ p) :
    Nat.card hT.ggBfull ≤ p * Nat.card ↥(hT.ggBfull ⊓ (ggPsiU t n f).range) := by
  have h := hT.ggBfull_index_inner hp3
  rwa [← ggPsiU_range_eq_conj t n f] at h

theorem ggBfull_diag_of_coprime
    {t : StatedLieTag} {n f : ℕ} {τ : Tag} {R p : ℕ} [NeZero p] {hR : R = τ.rank}
    {π : Equiv.Perm (Fin R)} {D : LangDatum τ GGL} {ι₀ : GGKb t n f →* ModGL τ GGL} {ζ : GGLˣ}
    (hT : GGTorusData hR p π D ι₀ ζ) (hco : Nat.Coprime p (ι₀.range.relIndex D.fix)) :
    ∀ b ∈ hT.ggBfull, GGInnDiagU t n f b := by
  intro b hb
  refine GGSFCore.ggInnDiagU_of_mem_range ?_
  rw [ggPsiU_range_eq_conj t n f]
  exact hT.ggBfull_le_inn hco hb

theorem ggBfull_coord_surj_of_coprime
    {t : StatedLieTag} {n f : ℕ} {τ : Tag} {R p : ℕ} [NeZero p] {hR : R = τ.rank}
    {π : Equiv.Perm (Fin R)} {D : LangDatum τ GGL} {ι₀ : GGKb t n f →* ModGL τ GGL} {ζ : GGLˣ}
    (hT : GGTorusData hR p π D ι₀ ζ) (hco : Nat.Coprime p (ι₀.range.relIndex D.fix))
    (g : Fin R → ZMod p) (hg : ∀ i, g (π i) = g i) :
    ∃ b : hT.ggBfull, (b : GGAutU t n f) ∈ (ggPsiU t n f).range ∧
      Multiplicative.toAdd (hT.ggCoord b) = g := by
  let z : Multiplicative (ggFixAdd p π) := Multiplicative.ofAdd ⟨g, mem_ggFixAdd.2 hg⟩
  refine ⟨⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩, ?_, ?_⟩
  · rw [ggPsiU_range_eq_conj t n f]
    exact hT.ggBfull_le_inn hco ⟨z, rfl⟩
  · rw [ggCoord_apply]
    rfl

end GGTorusData

end Core

end CFSG.StandardType.GGFinModel
