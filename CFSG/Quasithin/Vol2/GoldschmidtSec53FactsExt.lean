module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsAm
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
import CFSG.Quasithin.Vol2.Ch5Sec1Basic
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.F1AmalgamRestrict
public import CFSG.Quasithin.Vol2.GoldschmidtF431Lie

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1 CFSG.Quasithin.H13.F431

structure ExtFacts {D : Type} [Group D] {G : Type} [Group G] {M₁ M₂ : Subgroup G}
    (E : LieExt D M₁ M₂) : Prop where
  solv : Group.IsSolvable ↥(E.N1 ⊓ E.N2)
  core : pCoreOf 2 (E.N1 ⊓ E.N2) ≤ perfectCore E.N1

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}
  {Y : Type} [Group Y] [Finite Y]

theorem facts_i_of_ext (h531 : Stmt5_3_1) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T t m f)
    (hpar : IsSec53Param t m f) (E : LieExt Y (sec53M1 L) (sec53M2 H)) (hX : ExtFacts E) :
    perfectCore (sec53M1 L) = L ∧ perfectCore (sec53M2 H) = oTwoUpper H ∧
      pCoreOf 2 (sec53M12 L H) = sec53S T L := by
  obtain ⟨-, -, ⟨hN1, -, -⟩, ⟨hLM, hKM⟩⟩ := h531 G T M L V H B D L₂ n t m f hyp hty hpar
  have := hX.solv
  have hsolv : Group.IsSolvable ↥(sec53M12 L H) :=
    Group.isSolvable_of_isSolvable_injective (f := E.phi12.toMonoidHom) E.phi12.injective
  have hLG : L ≤ sec53M1 L := Subgroup.le_normalizer
  have hKG : oTwoUpper H ≤ sec53M2 H := Subgroup.le_normalizer
  have hL1 : perfectCore (sec53M1 L) = L := by
    have hAn : (L.subgroupOf (sec53M1 L)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr le_rfl
    exact le_antisymm (perfectCore_le_of_sup_solvable hLG hAn hLM.symm hsolv)
      (le_perfectCore_of_perfect hLG hyp.toHyp5_1_8.toHyp5_0_1.commutator_eq)
  have hK2 : perfectCore (sec53M2 H) = oTwoUpper H := by
    have hAn : ((oTwoUpper H).subgroupOf (sec53M2 H)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr le_rfl
    exact le_antisymm (perfectCore_le_of_sup_solvable hKG hAn hKM.symm hsolv)
      (le_perfectCore_of_perfect hKG hty.2.1.2.1.2.1)
  refine ⟨hL1, hK2, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxM : x ∈ sec53M12 L H := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have hT1 : T ≤ sec53M1 L := hyp.T_le.trans hyp.normal
    have hT2 : T ≤ sec53M2 H := hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
    have hTM : T ≤ sec53M12 L H := le_inf hT1 hT2
    have hSyl : IsSylowTwoOf T (sec53M12 L H) := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM
    have hxT : x ∈ T :=
      hSyl.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hx
    have h12 := (mem_pCoreOf_iff_of_equiv E.phi12 ⟨x, hxM⟩).mp hx
    have h1 : ((E.phi12 ⟨x, hxM⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut Y) ∈ perfectCore E.N1 := hX.core h12
    have hxL : x ∈ L := by
      have e1 := E.phi1_phi12 ⟨x, hxM⟩
      have := (mem_perfectCore_iff_of_equiv E.phi1 ⟨x, hxM.1⟩).mpr (by rw [e1]; exact h1)
      rwa [hL1] at this
    exact ⟨hxT, hxL⟩
  · have hSM : sec53S T L ≤ sec53M12 L H := hN1 ▸ Subgroup.le_normalizer
    have hn : (sec53S T L).subgroupOf (sec53M12 L H) |>.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mpr hN1.symm.le
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hSM hn
      (hyp.toHyp5_1_8.toHyp5_0_1.sylow.1.to_le inf_le_left)

end CFSG.Quasithin.H13.Sec53F
