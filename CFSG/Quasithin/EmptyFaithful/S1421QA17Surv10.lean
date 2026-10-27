module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17Setup
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.Quasithin.EmptyFaithful.S1421Lem14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA17

theorem nonempty_mulEquiv_alt5_of_isL2Quot_two {X : Type} [Group X] (h : IsL2Quot 2 X) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card X = 60 := by rw [h.card (by norm_num)]; norm_num
  obtain ⟨e⟩ := h
  have hF4 : 4 ≤ Nat.card (GaloisField 2 2) := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
  have : IsSimpleGroup X := e.isSimpleGroup
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard

theorem omegaOneCenterOf_le' {K : Type*} [Group K] (X : Subgroup K) : omegaOneCenterOf X ≤ X := by
  unfold omegaOneCenterOf omegaOneOf
  rw [Subgroup.closure_le]
  intro x hx
  exact hx.1.1

section Setting

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem vz_le_pCoreOf (st : Setting1427 T M H K1) : VZ T M ≤ pCoreOf 2 H := by
  have hyp := st.hyp
  have F := st.facts
  have hH := st.hStar
  set Z := quasithinOmegaOneCenter T with hZ
  have h1 := (lemma_14_2_6_two hyp F hH.1 hH.2.1).1
  have hHM : H ≤ mcOf T := le_mcOf_of_isHStar hyp hH
  have hZT : Z ≤ T := (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hZH : Z ≤ pCoreOf 2 H := by
    refine le_pCoreOf_of_le_normalizer 2 (hZT.trans hH.1.1) ?_ ?_
    · rw [← normalizer_omegaOneCenter_eq_mcOf hyp] at hHM
      exact hHM.trans le_rfl
    · exact IsPGroup.of_card (n := 1) (by rw [hyp.card_omegaOneCenter]; norm_num)
  obtain ⟨hVred, -⟩ := S1421.isTwoReducedIn_VZ_of_hyp hyp
  intro v hv
  have hvU : v ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hv
  have hvN : v ∈ Subgroup.normalizer (Z : Set G) := by
    rw [normalizer_omegaOneCenter_eq_mcOf hyp]
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hwV : w ∈ VZ T M := le_conjClosure _ _ hw
    have := hVred.2.2.1.1.is_comm.comm ⟨w, hwV⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  have h2 := secMk_mem_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z)
    (X := conjClosure (VZ T M) H) (x := ⟨v, hvN⟩) hvU
  have h3 := h1 h2
  have h4 := omegaOneCenterOf_le' _ h3
  exact (secMk_mem_secImg_iff (A := Subgroup.normalizer (Z : Set G)) (B := Z) hZH).mp h4

end Setting

end S1421QA17

end CFSG.Quasithin
