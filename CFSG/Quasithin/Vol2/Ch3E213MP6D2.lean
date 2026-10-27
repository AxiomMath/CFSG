module

public import CFSG.Quasithin.Vol2.Ch3E213MP6D1
public import CFSG.Quasithin.Vol2.Ch3E213MP6A
public import CFSG.Quasithin.Vol2.Ch3E213MSL2PairE

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent uElt)
open CFSG.GorensteinWalter (sl2UpperUnipotent sl2UpperUnipotentSubgroup sl2Borel
  mem_sl2UpperUnipotentSubgroup_iff)
open scoped MatrixGroups

namespace P6D

theorem pair_of_sp4Diag
    {G : Type} [Group G] [Finite G]
    {H T M V K : Subgroup G} (hS : Setting H T M V K) {k : Type} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (D : Sp4Data H T M V K k) {μ : k} (hμ : μ ≠ 0)
    (hVμ : coordIn D.θ V ≤ zLine 1 μ) :
    ∃ T' : Sylow 2 ↥H, (T' : Subgroup H) = T.subgroupOf H ∧
      SL2Pair.Pair T' (M.subgroupOf H) (V.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  set μ' : kˣ := Units.mk0 μ hμ
  set θ := D.θ
  set φ : SL(2, k) →* (↥H ⧸ kerIn (M.subgroupOf H) ⊤) :=
    (kZero H M).subtype.comp (θ.symm.toMonoidHom.comp (P6D.diagSLμ μ')) with hφdef
  have hmem : ∀ (X : Subgroup G) (y : antiSp k),
      ((θ.symm y : kZero H M) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈ barIn M H X ↔
        y ∈ coordIn θ X := fun X y => by
    rw [coordIn, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  refine ⟨T', hT', SL2Pair.qrc_pair_of_sl2 hS.not_solvable hcharH T' hTn hTM' hMH' hmax' hVT'
    hTV' hVM' hVQ' hk φ ?_ ?_ ?_ ?_ ?_⟩
  · exact (kZero H M).subtype_injective.comp (θ.symm.injective.comp (P6D.diagSLμ_injective μ'))
  · exact fun g => (θ.symm (P6D.diagSLμ μ' g)).2
  ·
    intro g
    rw [hT']
    change ((θ.symm (P6D.diagSLμ μ' g) : kZero H M) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈
      barIn M H T ↔ _
    rw [hmem, D.sylow, P6D.diagSLμ_mem_antiUnipotent_iff]
  ·
    intro g hg
    change ((θ.symm (P6D.diagSLμ μ' g) : kZero H M) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈
      barIn M H M
    apply D.borel_le
    have hN : (Subgroup.normalizer
        (((barIn M H T ⊓ kZero H M).subgroupOf (kZero H M) : Subgroup (kZero H M)) :
          Set (kZero H M))).map θ.toMonoidHom =
        Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
      rw [Subgroup.map_equiv_normalizer_eq, Subgroup.inf_subgroupOf_right,
        show ((barIn M H T).subgroupOf (kZero H M)).map θ.toMonoidHom = coordIn θ T from rfl,
        D.sylow]
    have h1 : θ.symm (P6D.diagSLμ μ' g) ∈ Subgroup.normalizer
        (((barIn M H T ⊓ kZero H M).subgroupOf (kZero H M) : Subgroup (kZero H M)) :
          Set (kZero H M)) := by
      rw [← H13.QRC.map_symm_eq_of_map_eq θ hN]
      exact ⟨_, P6D.diagSLμ_mem_normalizer μ' hg, rfl⟩
    rw [← H13.QRC.inf_normalizer_subgroupOf inf_le_right] at h1
    exact h1
  ·
    intro e he
    have heK : e ∈ kZero H M := D.V_le he
    obtain ⟨t, ht⟩ := hVμ ((hmem V (θ ⟨e, heK⟩)).1 (by rw [θ.symm_apply_apply]; exact he))
    refine ⟨sl2UpperUnipotent t, (mem_sl2UpperUnipotentSubgroup_iff _).2 ⟨t, rfl⟩, ?_⟩
    have h1 : P6D.diagSLμ μ' (sl2UpperUnipotent t) = θ ⟨e, heK⟩ := by
      rw [P6D.diagSLμ_upperUnipotent, ht]
      rfl
    change ((θ.symm (P6D.diagSLμ μ' (sl2UpperUnipotent t)) : kZero H M) :
      ↥H ⧸ kerIn (M.subgroupOf H) ⊤) = e
    rw [h1, θ.symm_apply_apply]

end P6D

theorem pkgSp4Diag :
    PkgSp4Diag := by
  intro G _ _ H T M V K hS _ _ _ k _ _ _ n _ hk D μ hμ hVμ
  obtain ⟨T', hT', hP⟩ := P6D.pair_of_sp4Diag hS hk D hμ hVμ
  exact SL2Pair.e213Concl_of_pair hS hT' hP

end CFSG.Quasithin.Ch3E213M
