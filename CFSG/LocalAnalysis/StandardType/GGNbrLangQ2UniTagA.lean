module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniCover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift
public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import CFSG.LocalAnalysis.StandardType.GGLinCentBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinHeld
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers.Held

private theorem cuq2a_psu_not_psl
    {P : Type} [Group P] {a f d m : ℕ} {E1 : Type} [Field E1] [Finite E1]
    (ha : 2 ≤ a) (hE1card : Nat.card E1 = 2 ^ f)
    (φ : P ≃* StatedProj (StatedSL a E1))
    {E2 : Type} [Field E2] (hE2 : UnitaryFieldData 2 m E2) (hd : 3 ≤ d)
    (θ : P ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E2 (2 ^ m))) : False := by
  have hm : 1 ≤ m := hE2.one_le
  haveI : Finite E2 := hE2.finite
  have hE2card : Nat.card E2 = (2 ^ m) ^ 2 := by rw [hE2.card, ← pow_mul, mul_comm]
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hE1card
      have := Finite.one_lt_card (α := E1)
      omega
    · exact h
  have hcardPSL : Nat.card (StatedProj (StatedSL a E1)) = ordA (a - 1) (2 ^ f) := by
    rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega : 1 ≤ a), hE1card,
      Open.ordA, Nat.sub_add_cancel (by omega : 1 ≤ a), mul_comm (a - 1) a]
  have hcardPSU : Nat.card (StatedProj (StatedSU d (2 ^ m) E2)) = ordTwistedA (d - 1) (2 ^ m) := by
    rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hm hE2card
        (by omega : 2 ≤ d),
      Open.ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ d), mul_comm (d - 1) d]
  have hisoSU : LargeEvenProj (LargeEvenSUGroup (Fin d) E2 (2 ^ m)) ≃*
      StatedProj (StatedSU d (2 ^ m) E2) :=
    (nonempty_proj_congr (CFSG.Assembly.largeEvenSUGroup_eq_statedSU (K := E2) d (2 ^ m))).some
  have hcomp : StatedProj (StatedSL a E1) ≃* StatedProj (StatedSU d (2 ^ m) E2) :=
    φ.symm.trans (θ.trans hisoSU)
  have hcardeq : Nat.card (StatedProj (StatedSL a E1)) =
      Nat.card (StatedProj (StatedSU d (2 ^ m) E2)) :=
    Nat.card_congr hcomp.toEquiv
  have heq : ordA (a - 1) (2 ^ f) = ordTwistedA (d - 1) (2 ^ m) := by
    rw [← hcardPSL, ← hcardPSU]
    exact hcardeq
  exact absurd heq (Timmesfeld.Orders.ordA_ne_ordTwistedA (n := a - 1) (f := f) (u := d - 1)
    (g := m) (by omega) hf (by omega) hm)

private theorem cuq2a_q2URLevel_tagA : Q2URLevel (fun _ lab => lab.tag = .A) := by
  intro p d m lab hΛ htag hsplit hshape hpm hdm
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .A := htag
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro A hAab hAI hTor u hu hou J hJ hAJ E iE hE hne M hM
  letI : Field E := iE
  have hpodd : Odd p := by
    rcases hshape with ⟨hp3, -⟩ | ⟨hp5, -⟩
    · rw [hp3]; norm_num
    · rw [hp5]; norm_num
  have hd3 : 3 ≤ d := by
    rcases hshape with ⟨-, hd⟩ | ⟨-, hd⟩
    · rcases hd with rfl | rfl <;> norm_num
    · omega
  have hN : 2 ≤ l + 1 := by
    have h := hΛ
    simp only [LargeEvenInLambda2] at h
    omega
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨g, hgu⟩ := TableB.exists_eq_linConjAut (hAI u hu)
  have hJc : CFSG.Open.IsComponentOf J
      (ggAutFixedSubgroup (TableB.linConjAut (Fin (l + 1)) K g)) := by
    rw [← hgu]; exact hJ
  have hgodd : Odd (orderOf g) :=
    q1CentLin_odd_orderOf g (by rw [← hgu, hou]; exact hpodd)
  obtain ⟨C, hC, hCSL, hJeq⟩ := q1TorLin_component_lift hN g J hJc
  obtain ⟨a, E1, hE1f, hE1alg, hE1fin, ha, ⟨φ⟩⟩ :=
    linCentComp_block g hgodd C hC hCSL J hJeq
  letI : Field E1 := hE1f
  letI : Finite E1 := hE1fin
  letI : Algebra K E1 := hE1alg
  have h2E1 : (2 : E1) = 0 := by
    have h : (algebraMap K E1) (2 : K) = 0 := by
      rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2, map_zero]
    exact (map_ofNat (algebraMap K E1) 2).symm.trans h
  haveI : CharP E1 2 := by
    have hdvd : ringChar E1 ∣ 2 := (ringChar.spec E1 2).mp h2E1
    rcases Nat.prime_two.eq_one_or_self_of_dvd (ringChar E1) hdvd with h1 | h2
    · exfalso
      haveI : CharP E1 1 := ringChar.of_eq h1
      have h1z : ((1 : ℕ) : E1) = 0 := (CharP.cast_eq_zero_iff E1 1 1).mpr (one_dvd 1)
      exact one_ne_zero (by simpa only [Nat.cast_one] using h1z)
    · exact ringChar.of_eq h2
  obtain ⟨n', -, hfcard⟩ := @FiniteField.card E1 _ (Fintype.ofFinite E1) 2 _
  let f : ℕ := n'
  have hE1card : Nat.card E1 = 2 ^ f := by
    rw [@Nat.card_eq_fintype_card E1 (Fintype.ofFinite E1), hfcard]
  exact (cuq2a_psu_not_psl ha hE1card φ hE hd3 hne.some).elim

theorem ggBstarAbelianPreimageJUniS1On_tagA :
    GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag = .A) :=
  ggBstarAbelianPreimageJUniS1On_of_rLevel cuq2a_q2URLevel_tagA

end CFSG.StandardType
