module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylHolds
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusNormalizer
public import CFSG.LocalAnalysis.StandardType.GGHalfLeviGlueTorus
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylRank
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private lemma hasLabel_of_equiv_sl {G : Type} [Group G] {J : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (e : SpecialLinearGroup (Fin (m + 1)) F2 ≃* ↥J) :
    GGHasLabel ⟨.A, m, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F2 ≃*
      (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hmodel : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL (m + 1) 2 1 := by
    refine ⟨⟨Nat.prime_two, le_refl 1, by omega, ?_, ?_⟩, F2, inferInstance, inferInstance,
      GaloisField.card 2 1 (by omega), ⟨?_⟩⟩
    · intro h
      have h1 : m + 1 = 2 := (Prod.mk.inj h).1
      omega
    · intro h
      have h1 : m + 1 = 2 := (Prod.mk.inj h).1
      omega
    · exact e'.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F2)
  exact ggHasLabel_typeA (n := m) (f := 1) hmodel

theorem GGHalfJoin.leviData (hsub : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m : ℕ} {y : G} {K : Subgroup G}
    (hctx : GGHalfWeylCtx 3 B Bs x L D J m y K) (hNoTr : GGNoTransvection 3 Bs) :
    ∃ TJ : Subgroup G, TJ ≤ Bs ∧ TJ ≤ J ∧ Nat.card TJ = 3 ^ ((m + 1) / 2) ∧
      Nat.card Bs = 3 ^ ((m + 3) / 2 + 1) ∧ Subgroup.center ↥J = ⊥ ∧
      GGHasLabel ⟨.A, m, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨φ₁, φ₂, hco⟩ :=
    ggTypeAHalfCoordInput_of_subcomponent hsub G 3 B Bs x L D J m y K hctx.cfg hctx.inn hctx.nbr
  let lam : SpecialLinearGroup (Fin (m + 1)) F2 →* G := φ₁.comp (slLower2Hom m)
  have hlinj : Function.Injective lam :=
    hco.inj₁.comp (GGHalf.slLower2Hom_injective m)
  have hH : GGHalfCtx 3 B Bs x L D J m y K φ₁ φ₂ :=
    ⟨hctx.cfg, hctx.inn, hNoTr, hctx.nbr, hco⟩
  have hm : 2 ≤ m := by have := hctx.five_le; omega
  let e : SpecialLinearGroup (Fin (m + 1)) F2 ≃* ↥J :=
    (MonoidHom.ofInjective hlinj).trans (MulEquiv.subgroupCongr hco.rangeJ)
  have hcenterJ : Subgroup.center ↥J = ⊥ := by
    rw [← Subgroup.map_center_eq e, GGHalf.center_eq_bot, Subgroup.map_bot]
  obtain ⟨ψL, ψK, hL, hK⟩ := hctx.exists_frames (@ggHalf_torusFrame)
  have hcardBs : Nat.card Bs = 3 ^ ((m + 1 + 1 + 1) / 2 + 1) := hctx.card_bs hL
  refine ⟨(halfTorus m).map lam, ?_, ?_, ?_, ?_, hcenterJ, ?_⟩
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
    show φ₁ (slLower2Hom m s) ∈ Bs
    exact hH.torusL_le (Subgroup.mem_map_of_mem φ₁ (GGHalf.slLower2Hom_mem_halfTorus hs))
  · rw [← hco.rangeJ]
    exact Subgroup.map_le_range lam (halfTorus m)
  · rw [Subgroup.card_map_of_injective hlinj, GGHalf.card_halfTorus m]
  · have h : m + 1 + 1 + 1 = m + 3 := by omega
    rw [hcardBs, h]
  · exact hasLabel_of_equiv_sl hm e

end CFSG.StandardType

end
