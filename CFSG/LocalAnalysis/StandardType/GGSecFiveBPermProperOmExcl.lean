module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorusConj
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorusEichler
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.LocalAnalysis.StandardType.GGSpinInnerAction
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKToral
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial

theorem GGConfig.false_of_normOmega_bBlockOn_of_inner {G : Type} [Group G] [Finite G]
    {p n m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] (E : QuadExt F K (unitaryInvolution K 2 f))
    (hK : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (hm : 2 ≤ m) {B Bs : Subgroup G}
    {x : G} {L D J X : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    (e : ↥X ≃* normOmega E m) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {I : Finset (Fin n)} (hI : I.card = m)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I) : False := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  obtain ⟨χ₀, hχ₀⟩ := exists_injective_unitChar (p := p) hK hpq
  have hZX : Subgroup.center ↥X = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, center_normOmega_eq_bot E hm, Subgroup.map_bot]
  have hF : Nat.card F = 2 ^ f := card_base_eq_two_pow E hK
  have hrange : (X.subtype.comp e.symm.toMonoidHom).range = X := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact (e.symm s).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
  have hcard := ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le_of_bBlockOn hp2 hA
  rw [hI] at hcard
  obtain ⟨-, κ, hκ, -, htor⟩ := ggSecFiveBPermSpK_exists_toral_of_inner hcfg.2.1
    (φ := X.subtype.comp e.symm.toMonoidHom) (X.subtype_injective.comp e.symm.injective)
    hrange hZX hinner hcard (D := normPlaneTorus E hm hpq χ₀) fun A hA hcardA => by
      obtain ⟨g, hg, hmap⟩ :=
        exists_normOmegaConj_map_eq_normPlaneTorus_range E hp2 hF hm hpq hχ₀ A hA hcardA
      exact ⟨normOmegaConj E hg, hmap⟩
  obtain ⟨U, hU1, hU2, hUN⟩ := exists_twoSubgroup_normalized_normPlaneTorus E hm hpq χ₀
  refine hcfg.not_normalizes_two_of_B_lt_Bs hlt (hU2.map κ)
    ((Subgroup.map_eq_bot_iff_of_injective U hκ).not.mpr hU1) ?_
  rw [Subgroup.le_normalizer_iff]
  intro b hb y hy
  obtain ⟨t, ht⟩ := htor b hb
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  rw [ht u]
  exact Subgroup.mem_map_of_mem κ ((Subgroup.mem_normalizer_iff.mp (hUN t) u).mp hu)

section Marked

theorem GGConfig.false_of_normOmega_bBlockOn (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p n m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K]
    [Algebra (GaloisField 2 f) K] [Finite K] [CharP K 2]
    (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)) (hK : UnitaryFieldData 2 f K)
    (hpq : p ∣ 2 ^ f + 1) (hm : 3 ≤ m) {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* normOmega E m) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {I : Finset (Fin n)} (hI : I.card = m)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I) : False := by
  have hrange : ∀ {S : Type} [Group S] (ψ : S ≃* X), (X.subtype.comp ψ.toMonoidHom).range = X := by
    intro S _ ψ
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact (ψ s).2
    · intro hy
      exact ⟨ψ.symm ⟨y, hy⟩, by simp⟩
  refine hcfg.false_of_normOmega_bBlockOn_of_inner hp2 E hK hpq (by omega) hlt ?_ e eta hI hA
  rcases Nat.even_or_odd m with hev | hodd
  · obtain ⟨ψ⟩ := nonempty_spinPlus_mulEquiv_normOmega E hev (by omega)
    exact ggSpinPlusInnerAction_of_mp hMp (by omega) hK.one_le hmark
      (X.subtype.comp (ψ.trans e.symm).toMonoidHom)
      (X.subtype_injective.comp (ψ.trans e.symm).injective) (hrange (ψ.trans e.symm))
  · obtain ⟨ψ⟩ := nonempty_spinMinus_mulEquiv_normOmega E hodd hm
      (CFSG.LieType.Universal.minusCoeffs_irr 2 f)
    exact ggSpinMinusInnerAction_of_mp hMp (by omega) hK.one_le hmark
      (X.subtype.comp (ψ.trans e.symm).toMonoidHom)
      (X.subtype_injective.comp (ψ.trans e.symm).injective) (hrange (ψ.trans e.symm))

end Marked

end CFSG.StandardType

end
