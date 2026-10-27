module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Bar
public import CFSG.Quasithin.H13.KGFactT3J4Core
public import CFSG.Quasithin.Background.SmithC27RHat6Lin

public section

namespace CFSG.Quasithin.H13.J4Cover

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam
open CFSG.Quasithin.J4M2
open CFSG.Quasithin.H13.S125KG CFSG.Quasithin.H13.S125KG.J4 CFSG.Quasithin.H13.S125KG.M24
open CFSG.Quasithin.A312M24 (G24)
open CFSG.QuasithinUnique
open scoped commutatorElement

private theorem card_eq_of_isHat_alt6 {B : Subgroup J}
    (hB : CFSG.Quasithin.IsHat (↥B ⧸ CFSG.pCore 2 ↥B) (alternatingGroup (Fin 6))) :
    ∃ c : ℕ, Nat.card B = 2 ^ c * 135 := by
  have hQ : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1080 :=
    CFSG.Quasithin.SmithC27.card_of_isHat_alt6 hB
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  rw [hQ, hc] at h
  refine ⟨c + 3, ?_⟩
  have h1080 : 1080 = 2 ^ 3 * 135 := by norm_num
  rw [h, h1080, pow_add]
  ring

private theorem card_sup_P0
    {B : Subgroup J} (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) {c : ℕ}
    (hc : Nat.card B = 2 ^ c * 135) : Nat.card ↥(B ⊔ P0) = 2 ^ 21 * 135 := by
  have hF : J4Facts := j4Facts
  have hJ : ¬ 2 ^ 22 ∣ Nat.card J := by
    rw [card_J hF]
    norm_num
  exact CFSG.Quasithin.H13.KGT3J4.card_sup_two hPB (card_P0 hF.mat hF) hc (by decide) hJ

private theorem eq_of_card_of_unique
    {S A B : Subgroup G24} (hS : IsSylowTwoOf S ⊤) (hA : S ≤ A) (hB : S ≤ B)
    (hAB : Nat.card A = Nat.card B)
    (huniq : ∀ i ≤ 13, ∀ j ≤ 13,
      [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD i 0 * 1024 = Nat.card A →
      [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 * 1024 = Nat.card A →
      i = j) : A = B := by
  obtain ⟨ψ, hψ⟩ := M24.exists_equiv ⟨MulEquiv.refl G24⟩ hS
  obtain ⟨i, hi, hAi, hci⟩ := M24.exists_member_map ψ hψ hA
  obtain ⟨j, hj, hBj, hcj⟩ := M24.exists_member_map ψ hψ hB
  have hij : i = j := huniq i hi j hj hci.symm (hcj.symm.trans hAB.symm)
  apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  rw [hAi, hBj, hij]

private theorem eq_M2_inf_Hj
    {Y : Subgroup J} (hP : P0 ≤ Y) (hYH : Y ≤ Hj)
    (hcard : Nat.card Y = 2 ^ 21 * 135) : Y = J4M2.M2 ⊓ Hj := by
  have hF : J4Facts := j4Facts
  have hE : Eg uJ 11 ≤ Y := Eg_le_P0.trans hP
  have hEM : Eg uJ 11 ≤ J4M2.M2 ⊓ Hj :=
    le_inf (Eg_le_P0.trans (P0_le_M2 hF)) (Eg_le_P0.trans P0_le_Hj)
  have hM2H : J4M2.M2 ⊓ Hj ≤ Hj := inf_le_right
  have hP0M : P0 ≤ J4M2.M2 ⊓ Hj := le_inf (P0_le_M2 hF) P0_le_Hj
  have hbarY : Nat.card (bar Y) = 135 * 1024 := by
    have h := card_bar hE hYH
    rw [hcard] at h
    have h2 : (2 : ℕ) ^ 11 * (135 * 1024) = 2 ^ 11 * Nat.card (bar Y) := by
      rw [← h]
      norm_num
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h2).symm
  have hbarM : Nat.card (bar (J4M2.M2 ⊓ Hj)) = 135 * 1024 := by
    have h := card_bar hEM hM2H
    rw [card_M2_inf_Hj] at h
    have h2 : (2 : ℕ) ^ 11 * (135 * 1024) =
        2 ^ 11 * Nat.card (bar (J4M2.M2 ⊓ Hj)) := by
      rw [← h]
      norm_num
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h2).symm
  have hbarEq : bar Y = bar (J4M2.M2 ⊓ Hj) := by
    refine eq_of_card_of_unique isSylowTwoOf_bar_P0 (bar_mono hP) (bar_mono hP0M) ?_ ?_
    · rw [hbarY, hbarM]
    · intro i hi j hj hij hjj
      rw [hbarY] at hij hjj
      have hi3 : i = 3 := by
        interval_cases i <;>
          simp only [List.getD_cons_succ, List.getD_cons_zero] at hij <;> omega
      have hj3 : j = 3 := by
        interval_cases j <;>
          simp only [List.getD_cons_succ, List.getD_cons_zero] at hjj <;> omega
      rw [hi3, hj3]
  refine le_antisymm ?_ ?_
  · exact (bar_le_iff hEM hYH).mp hbarEq.le
  · exact (bar_le_iff hE hM2H).mp hbarEq.ge

theorem le_centralizer_of_hat6
    {B : Subgroup J} (hperf : ⁅B, B⁆ = B)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J))
    (hB : CFSG.Quasithin.IsHat (↥B ⧸ CFSG.pCore 2 ↥B) (alternatingGroup (Fin 6))) :
    B ≤ Subgroup.centralizer ({z0} : Set J) := by
  have hF : J4Facts := j4Facts
  obtain ⟨c, hc⟩ := card_eq_of_isHat_alt6 hB
  have hcard : Nat.card ↥(B ⊔ P0) = 2 ^ 21 * 135 := card_sup_P0 hPB hc
  have hP : P0 ≤ B ⊔ P0 := le_sup_right
  have hBle : B ≤ B ⊔ P0 := le_sup_left
  rcases over_P0 hP with htop | hHj | hM3 | hM2
  · exfalso
    rw [htop, Subgroup.card_top, card_J hF] at hcard
    norm_num at hcard
  · have hY : B ⊔ P0 = J4M2.M2 ⊓ Hj := eq_M2_inf_Hj hP hHj hcard
    refine hBle.trans ?_
    rw [hY]
    exact inf_le_left
  · exfalso
    have hdvd : Nat.card ↥(B ⊔ P0) ∣ Nat.card ↥M3 := Subgroup.card_dvd_of_le hM3
    rw [hcard, card_M3 hF] at hdvd
    norm_num at hdvd
  · rw [hM2] at hBle
    exact hBle

end CFSG.Quasithin.H13.J4Cover
