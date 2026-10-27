module

public import CFSG.Quasithin.EmptyFaithful.S151WK
public import CFSG.Quasithin.EmptyFaithful.S151WL
public import CFSG.Quasithin.EmptyFaithful.S151ZT

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Bridge.Over

theorem input15122Rank2Lat_G2
    (G : Type) [Group G] [Finite G]
    (L B : Subgroup G) (h : IsG2Block L) (hB : IsSylowTwoOf B L) :
    L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P := by
  obtain ⟨-, hpsu, -⟩ := h
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (K := ↥L ⧸ CFSG.pCore 2 ↥L) (Or.inl ⟨by decide, hpsu⟩)
  let e' : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥U33Lat.MU :=
    e.trans (MulEquiv.subgroupCongr CertU33.closure_mGens.symm)
  let α : ↥L →* ↥U33Lat.MU := e'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hα : Function.Surjective α := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : α.ker = CFSG.pCore 2 ↥L := by
    ext x
    simp only [α, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact rank2Lat_of_sylow_data hB α hα hker U33Lat.sylow_DU U33Lat.rank2Data_U33

theorem input15122Rank2Lat_holds :
    Input15122Rank2Lat := by
  intro G _ _ L B htype hB
  rcases htype with h3 | h6 | hg
  · exact input15122Rank2Lat_L3 G L B h3 hB
  · exact input15122Rank2Lat_A6 G L B h6 hB
  · exact input15122Rank2Lat_G2 G L B hg hB

end CFSG.Quasithin
