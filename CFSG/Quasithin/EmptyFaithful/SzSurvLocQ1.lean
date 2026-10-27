module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocCases
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocConv
public import CFSG.Quasithin.EmptyFaithful.S1421QA16Red
public import CFSG.Quasithin.EmptyFaithful.S1421QA16J2
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Irred
public import CFSG.Quasithin.EmptyFaithful.S1421QA27O2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SzSurvLoc

open S1421QA27

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem qo2_survivor11Loc
    (st : Setting1427 T M H K1)
    (hsurv : Survivor11Loc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) :
    pCoreOf 2 (K1 ⊔ S1421.sOf T K1) ≤ pCoreOf 2 K1 := by
  have hsurvF : F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) :=
    Or.inr (Or.inr hsurv)
  obtain ⟨⟨e⟩, hQ8, Y, _, hY, TY, M₁, φ, -, -⟩ := hsurv
  have hcK : Nat.card (OTwoQuot K1) = 60 := by
    rcases survivorLoc_cases_legacyBare st.notation_.cComp_mem sOf_le_normalizer hsurvF with
      ⟨-, -, hSp⟩ | ⟨hc, -, -⟩
    · exact absurd (hQ8.1.symm.trans hSp.2.1) (by norm_num)
    · exact hc
  have hψ : Function.Injective (M₁.subtype.comp φ.toMonoidHom) :=
    Subtype.val_injective.comp φ.injective
  have hdvd := card_sup_dvd (M₁.subtype.comp φ.toMonoidHom) hψ
  obtain ⟨j, hj⟩ := exists_card_sup_eq (isPGroup_sOf st) sOf_le_normalizer
  rw [card_of_equiv_mulAut_quasithinJ2 hY, hj, card_K1_of_two hcK hQ8] at hdvd
  have h630 : 2 ^ j ∣ 630 := by
    have h : 1920 * 2 ^ j ∣ 1920 * 630 := by
      rw [show (1920 : ℕ) * 630 = 1209600 by norm_num]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hj1 : j ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := h4.trans h630
    norm_num at this
  have h120 : Nat.card (OTwoQuot (K1 ⊔ S1421.sOf T K1)) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hX := card_eq_card_oTwoQuot_mul (K1 ⊔ S1421.sOf T K1)
  rw [hj, card_K1_of_two hcK hQ8, h120] at hX
  have hQX := Subgroup.card_le_of_le (pCoreOf_le_pCoreOf_sup (T := T) (K1 := K1))
  rw [hQ8.1] at hQX
  interval_cases j
  · norm_num at hX
    omega
  · have hle : Nat.card ↥(pCoreOf 2 (K1 ⊔ S1421.sOf T K1)) ≤ Nat.card ↥(pCoreOf 2 K1) := by
      rw [hQ8.1]
      norm_num at hX
      omega
    exact (Subgroup.eq_of_le_of_card_ge pCoreOf_le_pCoreOf_sup hle).symm.le

theorem qo2_of_survivorLoc
    (st : Setting1427 T M H K1)
    (hsurv : F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) :
    pCoreOf 2 (K1 ⊔ S1421.sOf T K1) ≤ pCoreOf 2 K1 := by
  rcases hsurv with h4 | h10 | h11
  · exact qo2_survivor4 st h4
  · rw [sup_eq_left.mpr h10.2.2]
  · exact qo2_survivor11Loc st h11

theorem q16IrredLoc_of_irred4 (hI : Lemma14216QIrred4LegacyBare) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1)
    (hsurv : F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) :
    Q16Irred G T K1 := by
  rcases survivorLoc_cases_legacyBare st.notation_.cComp_mem sOf_le_normalizer hsurv with
    ⟨-, -, hSp⟩ | ⟨hc, hs, hQ8⟩
  · rcases hsurv with h4 | h10 | h11
    · exact hI G T M H K1 st h13 h4
    · exact absurd (h10.2.1.1.symm.trans hSp.2.1) (by norm_num)
    · exact absurd (h11.2.1.1.symm.trans hSp.2.1) (by norm_num)
  · exact Q16.q16Irred_of_dvd_five st (by rw [hc]; norm_num) hs hQ8

theorem pCoreOf_mcOf_eq_of_q16IrredLoc (st : Setting1427 T M H K1)
    (hsurv : F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1))
    (hi : pCoreOf 2 (K1 ⊔ S1421.sOf T K1) ≤ pCoreOf 2 K1) (hirr : Q16Irred G T K1) :
    pCoreOf 2 (mcOf T) = pCoreOf 2 K1 := by
  have hRQ : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 K1 := (Q16.pCoreOf_mcOf_le_pCoreOf_sup st).trans hi
  have hinv : ∀ k ∈ K1, ∀ w ∈ pCoreOf 2 (mcOf T), k * w * k⁻¹ ∈ pCoreOf 2 (mcOf T) :=
    fun k hk w hw => (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (mcOf T) (Q9.k1_le_mcOf st hk)) w).mp hw
  rcases hirr _ (Q16.omegaOneCenter_le_pCoreOf_mcOf st) hRQ hinv with hRZ | hRQ'
  · exfalso
    have hcen : mcOf T ≤ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
      rw [hRZ]
    have hMcR : mcOf T ≤ pCoreOf 2 (mcOf T) := fun x hx => Q16.charTwo_mcOf st ⟨hx, hcen hx⟩
    have hK1Z : K1 ≤ quasithinOmegaOneCenter T :=
      (Q9.k1_le_mcOf st).trans (hMcR.trans hRZ.le)
    have h1 : Nat.card (OTwoQuot K1) ∣ Nat.card K1 := Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card K1 ≤ 2 :=
      (Subgroup.card_le_of_le hK1Z).trans st.hyp.card_omegaOneCenter.le
    have h3 : Nat.card (OTwoQuot K1) ≤ 2 := (Nat.le_of_dvd Nat.card_pos h1).trans h2
    rcases survivorLoc_cases_legacyBare st.notation_.cComp_mem sOf_le_normalizer hsurv with
      ⟨hc, -, -⟩ | ⟨hc, -, -⟩ <;> omega
  · exact hRQ'

end SzSurvLoc

theorem lemma14216QLoc_holds :
    Lemma14216QLoc := by
  intro G _ _ T M H K1 st h13 hsurv
  exact SzSurvLoc.pCoreOf_mcOf_eq_of_q16IrredLoc st hsurv
    (SzSurvLoc.qo2_of_survivorLoc st hsurv)
    (SzSurvLoc.q16IrredLoc_of_irred4 S1421QA27.lemma14216QIrred4_holds_legacyBare st h13 hsurv)

end CFSG.Quasithin
