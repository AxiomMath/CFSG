module

public import CFSG.Quasithin.Background.C1PackS15212B
public import CFSG.Quasithin.Background.C1PackS15212Six
public import CFSG.Quasithin.EmptyFaithful.S141Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack12

variable {G : Type} [Group G] [Finite G]

structure Core15212 (T Mc M H : Subgroup G) : Prop where
  cases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
    Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212He T Mc (conjClosure (oTwoUpper H) Mc)
  eq_oThreePrime : conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc

@[expose] def Input15212Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Core15212 T Mc M H

theorem le_centralizer_of_cases {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (h1416 : StageLemma1416) (c19 : Lemma1519Concl T Mc M) (hH : IsHStar T M H)
    (hcases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
      Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212He T Mc (conjClosure (oTwoUpper H) Mc)) :
    conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hMc : perfectCore Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    ((h1416 G T Mc hs.qtfe).2.2.2 Mc
      ⟨hs.qtfe.t_le_mc, pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1⟩).1
  have hcomp : ∀ L ∈ cComp Mc, L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun L hL => (le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)).trans hMc
  rcases hcases with h | h | h | h
  · rw [h]
    exact (oTwoUpper_le H).trans (c19.three H hH).1
  · exact hcomp _ h.2.1
  · obtain ⟨L, t, -, hL, htT, -, hKc, -, -⟩ := h
    rw [hKc]
    refine sup_le (hcomp L hL) fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have htMc : t ∈ Mc := hs.qtfe.t_le_mc htT
    have hy' : y ∈ perfectCore Mc :=
      le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL) hy
    have h4 : (MulAut.conj t).toMonoidHom y ∈ perfectCore Mc :=
      (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_perfectCore Mc (Subgroup.le_normalizer htMc)) y).mp hy'
    exact hMc h4
  · exact hcomp _ h.2.1

theorem stageLemma15212_of_core (h1416 : StageLemma1416) (h1515 : StageLemma1515)
    (h15201 : StageLemma15201) (h5 : StageLemma15205)
    (h1519 : StageLemma1519) (h15208 : StageLemma15208) (h15209 : StageNotation15209)
    (h15211 : StageLemma15211) (core : Input15212Core) : StageLemma15212 := by
  intro G _ _ T Mc M hs H hH B hB
  have s := St12.of_stages h5 h1519 h15208 h15209 h15211 hs hH hB
  have c := core G T Mc M hs H hH
  have hle := le_centralizer_of_cases hs h1416 s.c19 hH c.cases
  have hd : S152Y.Data T Mc M :=
    ⟨hs.qtfe, hs.mf, h1515 G T Mc M hs.qtfe hs.mf, h15201 G T Mc M hs⟩
  have hsix : ¬ Case1512Six T Mc M := not_case1512Six_of_oThreePrime hd c.eq_oThreePrime hle
  exact ⟨s.xi, c.cases, s.unique, s.H_le_normalizer, s.normalizer_le, c.eq_oThreePrime, hle,
    hsix, V154_eq_VZ hsix⟩

end C1Pack12

end CFSG.Quasithin
