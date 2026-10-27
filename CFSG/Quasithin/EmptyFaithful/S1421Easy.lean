module

public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem pCoreOf_le_sOf_of_eq (st : Setting1427 T M H K1) (hS : sOf T K1 = T) :
    pCoreOf 2 M ≤ sOf T K1 := by
  rw [hS]
  exact pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo st.hyp.sylow st.hyp.m_max.1.2)

theorem lemma_14_2_13_of_pCore_le (hO : pCoreOf 2 M ≤ sOf T K1) :
    pCoreOf 2 (yOfL22 T M) ≤ sOf T K1 :=
  (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (yOfL22_le T M))
    (F7.le_normalizer_pCoreOf_of_le_normalizer (le_normalizer_yOfL22 T M))
    (pCoreOf_isPGroup 2 _)).trans hO

theorem hyp111f_of_pCore_le (st : Setting1427 T M H K1) (hO : pCoreOf 2 M ≤ sOf T K1) :
    CharTwo (l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1)) := by
  have hyp := st.hyp
  have N := st.notation_
  have hTM : T ≤ M := hyp.m_max.1.2
  have hM2 : CharTwo M := charTwo_of_inH' hyp.qtke hyp.sylow (inH_of_inM hyp.m_max.1)
  have hYM := yOfL22_le T M
  have hL2 : l2Of T H (yOfL22 T M) ≤ M :=
    sup_le hYM (sup_le ((pCoreOf_le 2 _).trans hYM) (inf_le_left.trans hTM))
  have hSM : sOf T K1 ≤ M := sOf_le_T.trans hTM
  have hBM : borelOf K1 (sOf T K1) ≤ M := by
    have hB : borelOf K1 (sOf T K1) =
        K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) := by
      unfold borelOf
      rw [sOf_inf_K1]
    rw [hB]
    exact N.borel_le
  have hXM : l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1) ≤ M :=
    sup_le (sup_le hL2 hSM) hBM
  have hSX : sOf T K1 ≤ l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1) :=
    le_sup_right.trans le_sup_left
  have hOX : pCoreOf 2 M ≤
      pCoreOf 2 (l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1)) :=
    le_pCoreOf_of_le_normalizer 2 (hO.trans hSX) (hXM.trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  rintro x ⟨hxX, hxC⟩
  exact hOX (hM2 ⟨hXM hxX, Subgroup.centralizer_le hOX hxC⟩)

theorem lemma_14_2_15_of_sOf_eq (st : Setting1427 T M H K1) (hS : sOf T K1 = T) :
    pCoreOf 2 (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1) = ⊥ := by
  by_contra hne
  obtain ⟨M₁, hM₁⟩ := exists_inM_of_pCoreOf_ne_bot hne
  have hYL : yOfL22 T M ≤ l2Of T H (yOfL22 T M) := le_sup_left
  have hYG : yOfL22 T M ≤ K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1 :=
    hYL.trans (le_sup_right.trans le_sup_left)
  have hTS : T ≤ sOf T K1 := le_of_eq hS.symm
  have hTG : T ≤ K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1 := hTS.trans le_sup_right
  have hInM : InM (yOfL22 T M ⊔ T) M₁ := ⟨hM₁.1, (sup_le hYG hTG).trans hM₁.2⟩
  have heq : M₁ = M := st.facts.unique.2 M₁ hInM
  have hK1G : K1 ≤ K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1 := le_sup_left.trans le_sup_left
  exact st.notation_.not_le (hK1G.trans (le_of_le_of_eq hM₁.2 heq))

end S1421

end CFSG.Quasithin
