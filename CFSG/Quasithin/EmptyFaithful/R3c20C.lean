module

public import CFSG.Quasithin.EmptyFaithful.S151S4F

public section

namespace CFSG.Quasithin

namespace R3c20

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.S151S4 (pCoreOf_le_of_isSubnormal center_eq_bot_of_isPSL2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def BaumNormalizesL2Statement : Prop :=
  ∀ H T L : Subgroup G, CharTwo H → CharTwo L → IsSylowTwoOf T H → IsSQTKTC H → L ∈ cComp H →
    H = L ⊔ T → ¬ T ≤ Subgroup.normalizer (L : Set G) →
    (∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ⁅L, thompsonJ T⁆ = L →
    ¬ L ≤ Subgroup.centralizer (VZ T H : Set G) → baum T ≤ Subgroup.normalizer (L : Set G)

@[expose] def TheoremC116L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BaumNormalizesL2Statement (G := G)

theorem baum_le_normalizer_of_l2 (h116 : BaumNormalizesL2Statement (G := G))
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hchar : CharTwo L) {n : ℕ} (hn : 1 < n) (hLn : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L))
    (hX : CharTwo (L ⊔ s1516 T Z₁)) (hSN : ¬ s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G))
    (hJ : ⁅L, thompsonJ (s1516 T Z₁)⁆ = L) :
    baum (s1516 T Z₁) ≤ Subgroup.normalizer (L : Set G) := by
  set S := s1516 T Z₁ with hSdef
  set X := L ⊔ S with hXdef
  have hq := hc.ctx.qtfe
  have hSet := hc.ctx.setting
  have hMf := hc.ctx.mf
  have hlocal := quasithinIsLocal_iff_lFamily.mp hc.hL.mem.2
  have hSyl : IsSylowTwoOf S X := hlocal.2.1
  have hpcX : pCoreOf 2 X ≠ ⊥ := hlocal.2.2
  have hSQ : IsSQTKTC X :=
    ⟨kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpcX,
      stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpcX⟩
  have hLX : L ∈ cComp X := cComp_of_isLocal hc.hL.mem.2
  have hLG : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  set V := VZ S X with hVdef
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hLnV : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hLV
    apply hc.hL.not_le
    intro x hx
    refine ⟨hLG hx, hq.centralizer_le_mc ?_⟩
    have hTV : quasithinOmegaOneCenter T ≤ V := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      have hzS : z ∈ S := ⟨hz.1.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hz.1.2 y (hZ₁T hy)⟩
      have hzZS : z ∈ quasithinOmegaOneCenter S :=
        Subgroup.subset_closure ⟨⟨hzS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_iff.mp hz.1.2 y (s1516_le T Z₁ hy)⟩, hz.2⟩
      exact le_conjClosure _ _ hzZS
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTV) (hLV hx)
  exact h116 X S L hX hchar hSyl hSQ hLX rfl hSN ⟨n, hn, hLn⟩ hc.hL.quasi hJ hLnV

end R3c20

end CFSG.Quasithin
