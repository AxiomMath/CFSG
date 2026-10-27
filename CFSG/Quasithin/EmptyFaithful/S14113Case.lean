module

public import CFSG.Quasithin.Background.C2Bridge
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S14117Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem hypC23_of_cgs {T Mc M H : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hHM : H ≤ M) (hR : pCoreOf 2 H ≠ ⊥) (hC : cgsIn M (pCoreOf 2 H) ≤ H) :
    HypC23 M (pCoreOf 2 H) H := by
  have hMne : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
  have hNH : M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
    le_antisymm ((inf_normalizer_le_cgsIn hR).trans hC)
      (le_inf hHM (le_normalizer_pCoreOf 2 H))
  have hcc : conjClosure (pCoreOf 2 H) H = pCoreOf 2 H := by
    refine le_antisymm (conjClosure_le fun g hg z hz => ?_) (le_conjClosure _ _)
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) z).mp hz
  refine ⟨⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hMne,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hMne⟩,
    ⟨(pCoreOf_le 2 H).trans hHM, hR, by rw [hNH]⟩, hHM, hC, ?_⟩
  refine ⟨le_conjClosure _ _, pCoreOf_isPGroup 2 H, ?_⟩
  rw [hcc, Subgroup.subgroupOf_self, Subgroup.index_top]
  decide

omit [Finite G] in
theorem isBlock2_of_oTwoFIn {M X : Subgroup G} (hX : IsBlock2 (oTwoFIn M) X) : IsBlock2 M X := by
  have hXF : X ≤ oTwoFIn M := hX.2.1
  have hFM : IsSubnormal (oTwoFIn M) M :=
    A4.subnormal_of_normal C2Six.oTwoFIn_le C2Six.normal_oTwoFIn_subgroupOf
  have hsub : IsSubnormal X M := A4.subnormal_trans (IsBlock2.isSubnormal hX) hFM
  exact ⟨hX.1, hXF.trans C2Six.oTwoFIn_le,
    (isSubnormal_iff_subgroupOf (hXF.trans C2Six.oTwoFIn_le)).mp hsub⟩

omit [Finite G] in
theorem fitting_le_imageOTwoQuot {M H : Subgroup G} (hF : oTwoFIn M ≤ H) :
    CFSG.fittingSubgroup (OTwoQuot M) ≤ imageOTwoQuot M H := by
  intro q hq
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  have hz : (z : G) ∈ oTwoFIn M := by
    rw [oTwoFIn_eq_map_O2F]
    exact ⟨z, hq, rfl⟩
  exact mem_imageOTwoQuot_iff.mpr ⟨z, z.2, hF hz, rfl⟩

@[expose] def Stage14113CaseTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M H : Subgroup G, InM T M → T ≤ H → H ≤ M → pCoreOf 2 H ≠ ⊥ →
      cgsIn M (pCoreOf 2 H) ≤ H → oTwoEIn M ≤ H → M = Mc →
      2 < Nat.card (quasithinOmegaOneCenter T) →
      ∀ (r : ℕ) (Lb : Fin r → Subgroup G),
        (∀ i, IsBlock2 (oTwoFIn M) (Lb i) ∧ IsAltType (Lb i) 3 ∧ ¬ Lb i ≤ H ∧
          ⁅Lb i, thompsonJ (pCoreOf 2 H)⁆ = Lb i) →
        (∀ x ∈ oTwoFIn M, ∃ m ∈ H ⊓ oTwoFIn M, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
          x = m * (List.ofFn y).prod) →
        ¬ oTwoFIn M ≤ H →
        Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ H

end CFSG.Quasithin
