module

public import CFSG.Quasithin.EmptyFaithful.S1421STDefs
public import CFSG.Quasithin.EmptyFaithful.S1421Easy
public import CFSG.Quasithin.EmptyFaithful.S1421QL12Comm
public import CFSG.Quasithin.EmptyFaithful.S1421QL12Lift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem pCoreOf_le_sOf_of_mem_cComp (st : Setting1427 T M H K1)
    (hK : K1 ∈ cComp H) : pCoreOf 2 M ≤ sOf T K1 := by
  intro x hx
  have N := st.notation_
  have hTM : IsSylowTwoOf T M := isSylowTwoOf_of_isSylowTwo st.hyp.sylow st.hyp.m_max.1.2
  have hxT : x ∈ T := pCoreOf_two_le_of_isSylowTwoOf hTM hx
  refine Subgroup.mem_inf.mpr ⟨hxT, ?_⟩
  by_contra hxN
  obtain ⟨b, hb, hbodd, hbnot⟩ := exists_odd_borel_not_mem_solvRad N.sylow N.bender
  exact hbnot (mem_solvRad_of_odd_of_conj hK (st.hStar.1.1 hxT) hxN (pCoreOf_isPGroup 2 M) hx
    (Subgroup.mem_inf.mp hb).1 (le_normalizer_pCoreOf 2 M (N.borel_le hb)) hbodd)

end S1421

@[expose] def Lemma14212Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    Shape1428 T H K1 → oTwoUpper H ∈ cComp H → K1 < oTwoUpper H →
      ShapeL3Sp4 T K1 (oTwoUpper H) →
        pCoreOf 2 M ≤ S1421.sOf T K1 ∨ S1421.L34Cfg T M H K1

theorem lemma14212_of_three (h : Lemma14212Three) (G : Type)
    [Group G] [Finite G] (T M H K1 : Subgroup G) (st : Setting1427 T M H K1)
    (sh : Shape1428 T H K1) : pCoreOf 2 M ≤ S1421.sOf T K1 ∨ S1421.L34Cfg T M H K1 := by
  rcases sh.cases with ⟨hK1, -⟩ | ⟨hK1c, -⟩ | ⟨hKc, hlt, hL⟩
  · left
    rcases st.notation_.index with ⟨-, hT⟩ | ⟨hlt, -⟩
    · exact S1421.pCoreOf_le_sOf_of_eq st (inf_eq_left.mpr hT)
    · exact absurd hK1 (ne_of_lt hlt)
  · exact Or.inl (S1421.pCoreOf_le_sOf_of_mem_cComp st hK1c)
  · exact h G T M H K1 st sh hKc hlt hL

end CFSG.Quasithin
