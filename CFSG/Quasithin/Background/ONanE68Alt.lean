module

public import CFSG.Quasithin.Background.ONanE68Small
public import CFSG.Quasithin.Background.E6TwentyA

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique

section Alt

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem case4_of_alt (hAlt : E68AltRank) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {z : G}
    (hCD : Lemma115CaseC L z ∨ Lemma115CaseD L z)
    (hmodel : Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨
      (Nat.card (Subgroup.center ↥L) = 3 ∧
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6))) ∨
      (Nat.card (Subgroup.center ↥L) = 3 ∧
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)))) :
    E68Case4 M V U L := by
  classical
  have hLM := not_le_of_component h hU.1 hL
  obtain ⟨hle4, hgen⟩ := hAlt G L V _ z hCD (baseHyp h hU hL)
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hpow := E3.relIndex_eq_two_pow h.isPGroup_V C
  have hne0 : E3.mQuot V C ≠ 0 := mQuot_ne_zero_of_not_le h hLM
  have hm2 : E3.mQuot V C ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have h8 : 2 ^ 3 ≤ 2 ^ E3.mQuot V C := Nat.pow_le_pow_right (by norm_num) hlt
    rw [← hpow] at h8
    omega
  have hUC : U ≤ C := le_inf_centralizer_component hU.1 hL
  have hLC : L ≤ Subgroup.centralizer (C : Set G) := le_centralizer_inf_centralizer V L
  have hex : ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ E3.mQuot V A = 1 ∧
      ¬ L ⊓ Subgroup.centralizer (A : Set G) ≤ M := by
    rcases (show E3.mQuot V C = 1 ∨ E3.mQuot V C = 2 by omega) with h1 | h2
    · exact ⟨C, hUC, inf_le_left, h1, by rw [inf_eq_left.2 hLC]; exact hLM⟩
    · have hrel : C.relIndex V = 4 := by rw [hpow, h2]; norm_num
      have hgen' := hgen hrel
      by_contra hno
      push Not at hno
      apply hLM
      refine hgen'.trans (iSup₂_le fun a ha => ?_)
      obtain ⟨haV, haC⟩ := ha
      have haC' : a ∉ C := fun hac => haC hac.2
      have hmA : E3.mQuot V (C ⊔ Subgroup.zpowers a) + 1 = E3.mQuot V C :=
        mQuot_sup_zpowers_add h.isElemAbelian (inf_le_left : C ≤ V) haV haC'
      have hle : L ⊓ Subgroup.centralizer ({a} : Set G) ≤
          L ⊓ Subgroup.centralizer ((C ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
        rw [centralizer_sup_eq, centralizer_zpowers_eq]
        exact le_inf inf_le_left (le_inf (inf_le_left.trans hLC) inf_le_right)
      exact hle.trans (hno (C ⊔ Subgroup.zpowers a) (hUC.trans le_sup_left)
        (sup_le inf_le_left (Subgroup.zpowers_le.2 haV)) (by omega))
  obtain ⟨A, hUA, hAV, hA1, hAM⟩ := hex
  exact ⟨hmodel, ⟨A, hUA, hAV, hA1, hAM⟩,
    rParam_eq_one_of h hAV hA1 fun hC => hAM (inf_le_right.trans hC), hm2⟩

end Alt

end E68Proof

end E6

end CFSG.Quasithin
