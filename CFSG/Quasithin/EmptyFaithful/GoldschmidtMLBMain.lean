module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBSub
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBNorm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBOrd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.EmptyFaithful.FLcL45
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBCover
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLie
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.GoldMLB

theorem input15120MLB_holds
    (h38 : A38ForSQTK) : Input15120MLB := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hB
  have h18 := hc.h18
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516 h18
  have hLX : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  have hsqtk : IsSQTKIn (g1_1516 Z₁) := h18.five.2.2.sqtk
  have hSylL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow h18.four hc.hL
  have hperf : commutator ↥L = ⊤ := hcomp.2.2.1
  have hY := quotModel_of_typeB hperf hB
  have hXL : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    normalizes_of_not_a38 h38 hsqtk hLcomp (not_a38Types_image hLX hY)
  set S₀ : Subgroup G := s1516 T Z₁ ⊓ L with hS₀
  have hS₀L : S₀ ≤ L := inf_le_right
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hS₀' : IsSylowTwoOf (S₀.subgroupOf L) (⊤ : Subgroup ↥L) := by
    rw [A312.isSylowTwoOf_top_iff_map, Subgroup.map_subgroupOf_eq_of_le hS₀L]
    exact hSylL
  have hU : IsSylowTwoOf ((S₀.subgroupOf L).map π) ⊤ :=
    A312.isSylowTwoOf_top_map π hπs hS₀'
  have : Finite (↥L ⧸ CFSG.pCore 2 ↥L) := inferInstance
  obtain ⟨P, hpk, hext⟩ : ∃ P : Fin 2 → Subgroup (↥L ⧸ CFSG.pCore 2 ↥L),
      Rk2.Rank2Pkg (↥L ⧸ CFSG.pCore 2 ↥L) ((S₀.subgroupOf L).map π) P ∧
      Rk2.Rank2Pkg.Ext (↥L ⧸ CFSG.pCore 2 ↥L) ((S₀.subgroupOf L).map π) P := by
    rcases hY with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · exact Rk2.rank2PkgExt_exists hn (Or.inl h) hU
    · exact Rk2.rank2PkgExt_exists hn (Or.inr h) hU
  have hdata : YData (↥L ⧸ CFSG.pCore 2 ↥L) ((S₀.subgroupOf L).map π) P :=
    ⟨hpk.res, hpk.norm, hext.charTwo_par, hext.le_perfectCore, hext.inner,
      hext.solvable_le_normalizer⟩
  have hl1 := hdata.lieLevel hU
  have hl2 := LieLevel.comap hπs hk hS₀' rfl hl1
  have hl3 := LieLevel.of_subtype hS₀L hl2
  exact main_of_lie hl3 (mZ1516_le_g1 Mc Z₁) hLX hXL hSylL (inf_le_left.trans hSM)
    hc.hL.not_le hc.h19.two

end CFSG.Quasithin
