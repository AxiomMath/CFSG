module

public import CFSG.Quasithin.EmptyFaithful.S1421L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

section Hyp111

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem sOf_le_T : sOf T K1 ≤ T := inf_le_left

omit [Finite G] in
theorem sOf_inf_K1 : sOf T K1 ⊓ K1 = T ⊓ K1 := by
  ext x
  simp only [sOf, Subgroup.mem_inf]
  exact ⟨fun ⟨⟨hT, _⟩, hK⟩ => ⟨hT, hK⟩, fun ⟨hT, hK⟩ => ⟨⟨hT, Subgroup.le_normalizer hK⟩, hK⟩⟩

omit [Finite G] in
theorem s2_le_sOf (N : Notation1428 T M H K1) (h13 : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1) :
    s2Of T H (yOfL22 T M) ≤ sOf T K1 :=
  sup_le h13 (le_inf inf_le_left N.inf_le)

theorem charTwo_k1_sup_s (st : Setting1427 T M H K1) : CharTwo (K1 ⊔ sOf T K1) := by
  have hyp := st.hyp
  have hStar := st.hStar
  have N := st.notation_
  have hH : CharTwo H := charTwo_of_inH' hyp.qtke hyp.sylow hStar.1
  have hTH : T ≤ H := hStar.1.1
  have hXH : K1 ⊔ sOf T K1 ≤ H :=
    sup_le (N.le_K.trans (oTwoUpper_le H)) (inf_le_left.trans hTH)
  have hOS : pCoreOf 2 H ≤ sOf T K1 :=
    le_inf (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hyp.sylow hTH)) N.pCore_le
  have hOX : pCoreOf 2 H ≤ pCoreOf 2 (K1 ⊔ sOf T K1) :=
    le_pCoreOf_of_le_normalizer 2 (hOS.trans le_sup_right)
      (hXH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  rintro x ⟨hxX, hxC⟩
  have hx : x ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    ⟨hXH hxX, Subgroup.centralizer_le hOX hxC⟩
  exact hOX (hH hx)


theorem borelOf_l2_eq (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1) :
    borelOf (l2Of T H (yOfL22 T M)) (sOf T K1) = s2Of T H (yOfL22 T M) := by
  have hc : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M := lemma_14_2_14 h311 st
  have hS2S : s2Of T H (yOfL22 T M) ≤ sOf T K1 := s2_le_sOf st.notation_ h13
  have hInfL : sOf T K1 ⊓ l2Of T H (yOfL22 T M) = s2Of T H (yOfL22 T M) :=
    inf_l2_eq st.hyp st.facts hS2S sOf_le_T
  unfold borelOf
  rw [hInfL]
  exact l2_inf_normalizer_s2 st.hyp st.facts hc

theorem hyp111_of_inputs (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1)
    (hf : CharTwo (l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1)))
    (h15 : pCoreOf 2 (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1) = ⊥)
    (hbridge : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 3)) → IsL2Quot 1 X) :
    Hyp111 K1 (l2Of T H (yOfL22 T M)) (sOf T K1) := by
  have hyp := st.hyp
  have F := st.facts
  have N := st.notation_
  have hStar := st.hStar
  have hTH : T ≤ H := hStar.1.1
  have hc : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M := lemma_14_2_14 h311 st
  have hS2S : s2Of T H (yOfL22 T M) ≤ sOf T K1 := s2_le_sOf N h13
  have hInfL : sOf T K1 ⊓ l2Of T H (yOfL22 T M) = s2Of T H (yOfL22 T M) :=
    inf_l2_eq hyp F hS2S sOf_le_T
  have hBorel2 : borelOf (l2Of T H (yOfL22 T M)) (sOf T K1) = s2Of T H (yOfL22 T M) :=
    borelOf_l2_eq h311 st h13
  have hTL : T ≤ Subgroup.normalizer (l2Of T H (yOfL22 T M) : Set G) :=
    F1.le_normalizer_sup (T_le_normalizer_y hyp) (T_le_normalizer_s2 hyp hTH)
  refine ⟨⟨inferInstance, hyp.sylow.1.to_le sOf_le_T, inf_le_right, ?_, ?_, ?_, ?_⟩,
    ⟨inferInstance, hyp.sylow.1.to_le sOf_le_T, sOf_le_T.trans hTL, ?_, ?_, ?_, hf⟩, h15⟩
  · rw [sOf_inf_K1]
    exact N.sylow
  · obtain ⟨n, hn, hb⟩ := N.bender
    exact IsBenderQuot.isRankOneListed (by omega) hb
  · rw [hBorel2]
    exact hS2S.trans inf_le_right
  · rw [hBorel2, sup_eq_left.mpr (hS2S.trans le_sup_right)]
    exact charTwo_k1_sup_s st
  · rw [hInfL]
    exact isSylowTwoOf_s2_l2 hyp F
  · obtain ⟨e⟩ := oTwoQuot_l2_equiv_perm3 hyp F hc
    exact Or.inl ⟨1, le_rfl, hbridge _ ⟨e⟩⟩
  · have hX : borelOf K1 (sOf T K1) = K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) := by
      unfold borelOf
      rw [sOf_inf_K1]
    rw [hX]
    have hXM : K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ≤ M := N.borel_le
    have hXK : K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ≤ oTwoUpper H := inf_le_left.trans N.le_K
    have hXY : K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ≤
        Subgroup.normalizer (yOfL22 T M : Set G) := hXM.trans (le_normalizer_yOfL22 T M)
    have hXO : K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 (yOfL22 T M) : Set G) :=
      F7.le_normalizer_pCoreOf_of_le_normalizer hXY
    have hXTK : K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
      (le_inf hXM hXK).trans N.borel_inf
    exact F1.le_normalizer_sup hXY (F1.le_normalizer_sup hXO hXTK)

end Hyp111

end S1421

end CFSG.Quasithin
