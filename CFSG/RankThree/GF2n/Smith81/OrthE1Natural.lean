module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.RankThree.GF2n.Smith81.OrthE2PlusTwo

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {t : G}

theorem e1Natural_minus_two (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hc : Ctx M Q Z B) (hs : Sec5Hyp hc 4 t) (hE : CaseE1Minus M Q Z B t) :
    OmegaMinusNat hc t 2 := by
  classical
  obtain ⟨-, hNt, ⟨hNn, KE, hFE, hFinE, hKE, bE, cE, hirrE, ⟨e⟩⟩⟩ := hE
  haveI := hNn
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have hq4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨hsimple, -, hodd⟩ := endg_omegaMinus_facts hq4 (le_refl 2) hirrE
  haveI := hsimple
  have hqe : Even (Nat.card KE) := orth_even_card KE
  have hY2 : ¬ IsPGroup 2 ↥(StatedOmega (StatedQuadMinus 2 KE bE cE)) :=
    orth_not_pgroup_of_dvd hqe (by omega) hodd
  have hcore := orth_e2_core h34 h310 hc hs hNt hY2 e
  have hqZ : Even (Nat.card Z : ℤ) := by
    rw [← hKE]; exact orth_even_card_int KE
  have hq0 : (Nat.card Z : ℤ) ≠ 0 := by have := hc.hyp.q4; omega
  obtain ⟨XE, hXE, hYE⟩ := orth_card_omegaMinus_form (K := KE) (le_refl 2) hirrE
  rw [hKE] at hYE
  rcases hcore with ⟨K, fK, finK, k, hKq, hk, hdim, hcard⟩ |
    ⟨K, fK, finK, k, hKq, hk, hcard⟩ |
    ⟨K, fK, finK, k, hKq, hk, hnat, hcard⟩ | ⟨K, fK, finK, k, b, c, hKq, hk, hirr, hnat, hcard⟩
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    refine orth_sl_exp_false_of_two_le (q := Nat.card Z) ?_ (by have := hc.hyp.q4; omega)
      (le_refl 2) hdim (Y := Nat.card ↥(StatedOmega (StatedQuadMinus 2 KE bE cE))) hXE ?_ ?_
    · rw [← hKE]; exact orth_even_card KE
    · exact_mod_cast hYE
    · rw [← hcard, ← hKq]
      exact orth_dvd_card_statedSL (by omega)
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_sp_form (K := K) k
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedSp k K) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus 2 KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    exact orth_sp_exp_ne hqZ hq0 (le_refl 2) hX' hXE h1
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    have hq4K : 4 ≤ Nat.card K := by rw [hKq]; exact hc.hyp.q4
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaPlus_form hq4K hk
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadPlus k K)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus 2 KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = 2 := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact orth_card_plus_ne_minus_of_two_le (K := K) (K' := KE) (hKE.trans hKq.symm) hq4K
      (le_refl 2) hirrE hcard
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaMinus_form (K := K) hk hirr
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus 2 KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = 2 := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact ⟨K, fK, finK, hKq, b, c, hirr, hnat⟩

theorem e1Natural_plus_of_nt (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hH : E1Hyp M Q Z B t) (hE : CaseE1Plus M Q Z B t) :
    OmegaPlusNat hH.ctx t 2 := by
  classical
  obtain ⟨-, -, hY⟩ := hE
  obtain ⟨hNn, KE, hFE, hFinE, hKE, ⟨e⟩⟩ := hY
  haveI := hNn
  have hc : Ctx M Q Z B := hH.ctx
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have hs : Sec5Hyp hc 4 t := hH.sec
  have hNtCN : hc.CN t = Nt M (LB M Q B) t :=
    (hNt G M Q Z B hc 4 hH.case.width (by norm_num) hH.noA2 hH.gen t hH.mem
      hH.notQ).symm
  have hRN : Nat.card ↥(Rt M (LB M Q B) t) =
      Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) * Nat.card ↥(Nt M (LB M Q B) t) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t))
    have h2 : Nat.card ↥((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) =
        Nat.card ↥(Nt M (LB M Q B) t) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orth_Nt_le_Rt M (LB M Q B) t)).toEquiv
    rw [h2, Nat.card_congr e.toEquiv] at h1
    exact h1
  exact orth_e2Natural_plus_two h34 h310 hc hs hNtCN hKE hRN

theorem e1Natural_of_nt (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) : E1NaturalStatement := by
  intro G _ _ M Q Z B t hH
  exact ⟨fun hE => e1Natural_plus_of_nt h34 h310 hNt hH hE,
    fun hE => e1Natural_minus_two h34 h310 hH.ctx hH.sec hE⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1
