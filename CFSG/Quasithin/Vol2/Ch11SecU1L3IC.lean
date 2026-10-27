module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IB
public import CFSG.Quasithin.Vol2.Ch11SecU1Set
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin

theorem nParam_le_one_of_psl3_inner {G : Type} [Group G] [Finite G] {T : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : IsPSL 3 p 1 ↥(CFSG.generalizedFitting G))
    (hTF : T ≤ CFSG.generalizedFitting G) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have htop : CFSG.generalizedFitting G = ⊤ := by rw [← hFT, sup_eq_left.mpr hTF]
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 hF
  rw [E1.Eleven.nParam_top_mulEquiv
    ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e)]
  exact nParam_psl3_le_one hp2

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open

@[expose] def E114ResRestL3EpsOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
    (∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 (ASInputs.FStar G) ∧ (s = true → ¬ T ≤ CFSG.generalizedFitting G)) →
    E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114ResRestL3Eps_of_out (h : E114ResRestL3EpsOut) : E114ResRestL3Eps := by
  intro G _ _ T hSQ hFs hT hFT ⟨s, p, hp, hp2, h4, h4', hP⟩
  by_cases hin : s = true ∧ T ≤ CFSG.generalizedFitting G
  · obtain ⟨rfl, hTF⟩ := hin
    exact Vol2.Ch11.SecU1.L3I.nParam_le_one_of_psl3_inner hp hp2 hP hTF hFT
  · exact h G T hSQ hFs hT hFT ⟨s, p, hp, hp2, h4, h4', hP, fun hs hTF => hin ⟨hs, hTF⟩⟩

theorem e114OneResRest_of_L3EpsOut
    (h : E114ResRestL3EpsOut) : E114OneResRest :=
  e114OneResRest_of_L3Eps (e114ResRestL3Eps_of_out h)

end CFSG.Quasithin.E2.E22N
