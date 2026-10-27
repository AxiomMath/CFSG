module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinIrred
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial


private theorem q2cLin_linConjAut_scalar_eq_one {N : ℕ} {K : Type} [Field K] (z : Kˣ) :
    TableB.linConjAut (Fin N) K (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [TableB.linConjAut_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hcomm : (h : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) z =
        Matrix.GeneralLinearGroup.scalar (Fin N) z * (h : GL (Fin N) K) :=
      Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin N) z) h
    rw [← hcomm]
    group

theorem q2c_rLevel_linear :
    Q2CensusRLevel (fun lab => lab.tag = .A ∧ 2 ≤ lab.n) (fun kind => kind = .linear) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn2⟩ := hS
  dsimp only at htag hn2
  subst htag
  simp only [LargeEvenInLambda2] at hΛ
  obtain ⟨-, hl, -⟩ := hΛ
  have hpq : p ∣ 2 ^ n - 1 := by
    rcases hsplit with ⟨-, hpq⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨hn1, -⟩
    · exact hpq
    · exact absurd trivial h
    · have ht : (⟨.A, l, n⟩ : LargeEvenLabel).tag = .A := rfl
      rw [ht] at h
      rcases h with h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exfalso
      simp only at hn1
      omega
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
  obtain ⟨F, _, _, hFcard, hQ'⟩ := hQ
  refine ⟨F, inferInstance, inferInstance, hFcard, hQ', ?_⟩
  intro A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hKcard he
  haveI : CharP F 2 := charP_two_of_card hFcard
  have hN2 : 2 ≤ l + 1 := by omega
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hpF : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpq
  obtain ⟨g, hgu⟩ := TableB.exists_eq_linConjAut (hAI u hu)
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    have := hp.two_le
    omega
  have hker : TableB.linConjAut (Fin (l + 1)) F (g ^ p) = 1 := by
    rw [map_pow, ← hgu, ← huo, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := q1CentLin_scalar_of_linConjAut_eq_one (N := l + 1) hN2 hker
  by_cases hpt : ∃ z : Fˣ, z ^ p = c
  ·
    obtain ⟨z, hz⟩ := hpt
    set g' : GL (Fin (l + 1)) F :=
      Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) z⁻¹ * g with hg'def
    have hgp : g' ^ p = 1 := by
      rw [hg'def, Commute.mul_pow (Matrix.GeneralLinearGroup.scalar_commute z⁻¹ g)]
      have h1 : (Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) z⁻¹) ^ p =
          Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) ((z⁻¹) ^ p) :=
        (map_pow (Matrix.GeneralLinearGroup.scalar (Fin (l + 1))) z⁻¹ p).symm
      have h2 : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) (z ^ p) := by
        rw [← hc, ← hz]
      rw [h1, h2, ← map_mul, inv_pow, inv_mul_cancel, map_one]
    have hgu' : TableB.linConjAut (Fin (l + 1)) F g' = u := by
      rw [hg'def, map_mul, q2cLin_linConjAut_scalar_eq_one, one_mul, hgu]
    have hgune : TableB.linConjAut (Fin (l + 1)) F g' ≠ 1 := by
      rw [hgu']
      exact hu1
    have hJ' : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup
        (TableB.linConjAut (Fin (l + 1)) F g')) := by
      rw [hgu']
      exact hJ
    have huniq' : ∀ J' : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) F)),
        CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup
          (TableB.linConjAut (Fin (l + 1)) F g')) → J' = J := by
      intro J' hJ'
      rw [hgu'] at hJ'
      exact huniq J' hJ'
    obtain ⟨a, tt, ha2, ht1, htp, hNsum, hiso⟩ :=
      q2c_lin_split (N := l + 1) hp hp2 hpF hF4 hN2 hgp hgune hJ' huniq'
    obtain ⟨eJ⟩ := he
    obtain ⟨eA⟩ := hiso
    have hψ : LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin a) F) :=
      (TypeA.recipeEquiv d K).symm.trans (eJ.symm.trans eA)
    obtain ⟨haeq, hFeq⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := a) (m := m) (F₀ := K) (E := F)
        hd hm hKcard hψ
    have hNsum' : l + 1 = d + tt := by
      rw [hNsum, haeq]
    have hnotdvd : ¬ p ∣ l + 1 := by
      rw [hNsum']
      intro h
      have hptt : p ∣ tt :=
        (Nat.dvd_add_iff_right hpd).mpr h
      have hple : p ≤ tt := Nat.le_of_dvd (by omega) hptt
      omega
    have hcop : Nat.Coprime p (l + 1) := hp.coprime_iff_not_dvd.mpr hnotdvd
    have hN4 : 4 ≤ l + 1 := by omega
    have hsec : TypeA.SLHasSections (l + 1) F :=
      slHasSections_of_four_le (d := l + 1) (K := F) hp hpF hN4
    have hlift : GGTorusLift p ((l + 1) - 1)
        (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) F)) :=
      TableBF4.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) F)
        (TypeA.ggTorusLift_coprime (d := l + 1) (K := F) hp hpF hN2 hcop hsec)
    have hbig' := hbig ((l + 1) - 1) hlift
    have hle : (l + 1) - 1 ≤ d :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp (hbig'.trans hup)
    have htt1 : tt = 1 := by omega
    have hld : l = d := by omega
    have h2m : 2 ^ m = 2 ^ n := by
      rw [← hKcard, ← hFeq, hFcard]
    refine ⟨.linear, rfl, hp, hp2, hpd, hpm, rfl, hld, h2m⟩
  ·
    exfalso
    have hcne : ∀ z : Fˣ, z ^ p ≠ c := fun z hz => hpt ⟨z, hz⟩
    have hgscalar : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) c := hc.symm
    have hJg : CFSG.Open.IsComponentOf J
        (ggAutFixedSubgroup (TableB.linConjAut (Fin (l + 1)) F g)) := by
      rw [← hgu]
      exact hJ
    obtain ⟨a, E, hEfld, hEfin, ha2, hNsum, hEcard, hiso⟩ :=
      q2c_lin_irred (N := l + 1) hp hp2 hpF hF4 hN2 hcne hgscalar hJg
    letI : Field E := hEfld
    letI : Finite E := hEfin
    obtain ⟨eJ⟩ := he
    obtain ⟨eA⟩ := hiso
    have hψ : LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin a) E) :=
      (TypeA.recipeEquiv d K).symm.trans (eJ.symm.trans eA)
    obtain ⟨haeq, -⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := a) (m := m) (F₀ := K) (E := E)
        hd hm hKcard hψ
    have hNsum' : l + 1 = p * d := by
      rw [hNsum, haeq]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hN4 : 4 ≤ l + 1 := by
      rw [hNsum']
      calc 4 ≤ 3 * 3 := by norm_num
        _ ≤ p * d := Nat.mul_le_mul hp3 hd
    have hsec : TypeA.SLHasSections (l + 1) F :=
      slHasSections_of_four_le (d := l + 1) (K := F) hp hpF hN4
    have hlift : GGTorusLift p ((l + 1) - 2)
        (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) F)) :=
      TableBF4.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) F)
        (TypeA.ggTorusLift_sub_two (d := l + 1) (K := F) hp hpF hN2 hsec)
    have hbig' := hbig ((l + 1) - 2) hlift
    have hle : (l + 1) - 2 ≤ d :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp (hbig'.trans hup)
    have hNle : l + 1 ≤ d + 2 := by omega
    rw [hNsum'] at hNle
    have hmul : 3 * d ≤ p * d := Nat.mul_le_mul_right d hp3
    have hcon : 3 * d ≤ d + 2 := le_trans hmul hNle
    omega

end CFSG.StandardType
