module

public import CFSG.Quasithin.EmptyFaithful.S151XC
public import CFSG.Quasithin.EmptyFaithful.T1515eA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Input15124SevenElt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Seven T Mc M →
    ∃ x : G, x ∈ Subgroup.normalizer (Z₁ : Set G) ∧ (∃ k : ℕ, orderOf x = 3 ^ k) ∧
      x ∉ Subgroup.centralizer (Z₁ : Set G)

theorem input15124SevenBlock_of (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hX : Input15124SevenElt) : Input15124SevenBlock := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h7
  by_contra hn3
  obtain ⟨x, hxN, ⟨k, hxk⟩, hxC⟩ := hX G T Mc M Z₁ Z₂ V₁ V₂ L hc h7
  have hS := hc.ctx.setting
  set H : Subgroup G := Subgroup.normalizer (Z₁ : Set G) with hHdef
  have hCH : g1_1516 Z₁ ≤ H := Subgroup.centralizer_le_normalizer _
  have hsub : IsSubnormal (g1_1516 Z₁) H :=
    A3.subnormal_of_normal hCH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr
        (normalizer_le_normalizer_centralizer Z₁))
  have hLcH : L ∈ cComp H := cComp_mem_of_subnormal hsub hc.hL.comp
  have hZ1ab : IsElemAbelian 2 Z₁ :=
    isElemAbelian_mono151 (hS.z1_le.trans inf_le_left) (hS.V_isElemAbelian hc.ctx.qtfe hc.ctx.mf)
  have hpc : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : Z₁ ≤ H) le_rfl (isPGroup_of_isElemAbelian hZ1ab)
    rw [h0] at this
    exact hS.z1_ne (le_bot_iff.mp this)
  have hH : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hc.ctx.qtfe.qtke hc.ctx.qtfe.simple hc.ctx.qtfe.nonabelian hpc
  obtain ⟨S, _, _, ⟨e⟩, hSx⟩ :=
    exists_exclusion_model_of_case15122 hK hc.h19.one hc.hL hn3 hc.h22
  have hLeq : L = oPrimeResidualOf 3 H :=
    eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hH hLcH hc.hL.quasi e hSx
  have hxL : x ∈ L := by
    rw [hLeq]
    exact Subgroup.subset_closure ⟨hxN, k, hxk⟩
  exact hxC (le_of_mem_cComp hc.hL.comp hxL)

end CFSG.Quasithin
