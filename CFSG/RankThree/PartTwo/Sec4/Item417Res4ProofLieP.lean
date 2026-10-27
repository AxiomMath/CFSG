module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofLieP
import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU)
open Matrix

theorem pRank_le_of_pRank_quot_center {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] {r : ℕ}
    (hr : 1 ≤ r) (h : CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ r) : CFSG.pRank 3 X ≤ r := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hZ | hZ
  · have e : X ≃* X ⧸ Subgroup.center X :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    exact (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num) e.toMonoidHom
      e.injective).trans h
  · refine le_trans ?_ hr
    refine csSup_le' ?_
    rintro k ⟨B, hB, hk⟩
    by_contra hk1
    have h9 : 9 ≤ Nat.card B := by
      rw [hk]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨⟨x, hxB⟩, hx1⟩ : ∃ x : B, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Subsingleton B := ⟨fun a b => by rw [hcon a, hcon b]⟩
      rw [Nat.card_unique] at h9
      omega
    have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hx3 : x ^ 3 = 1 := by
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hxB⟩
      simpa using congrArg Subtype.val h
    have hN : (Subgroup.zpowers x).Normal := ⟨fun n _ g => by
      have hc : g ∈ Subgroup.center X := hZ ▸ Subgroup.mem_top g
      rwa [(Subgroup.mem_center_iff.mp hc n).symm, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
    · exact hx1' (Subgroup.zpowers_eq_bot.mp h1)
    · have hX3 : Nat.card X ≤ 3 := by
        rw [← Subgroup.card_top, ← h1, Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
      have := Subgroup.card_le_card_group B
      omega

theorem pRank_projSL_four_le_two {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq3 : p ^ f % 3 = 2) :
    CFSG.pRank 3 (projSL 4 (GaloisField p f)) ≤ 2 := by
  set F := GaloisField p f
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p f (by omega)]
  have hs : IsSimpleGroup (projSL 4 F) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := F) 4 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (Sec4.projSLEquivPSLn 4 F).isSimpleGroup
  have : Finite (projSL 4 F) := inferInstance
  refine pRank_le_of_pRank_quot_center (by norm_num)
    (Sec21.Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
      Sec4.card_le_of_projImage (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker hs (m := 4)
        (by norm_num) (fun c hc => ?_) (by norm_num) (fun P hPH hcomm hexp => ?_) B hB)
  · apply Sec4.pow_four_of_det_scalar
    have := congrArg Units.val (MonoidHom.mem_ker.mp hc)
    rwa [GeneralLinearGroup.val_det_apply] at this
  · have : Finite P := Finite.of_injective _ Subtype.val_injective
    have h := Sec21.Item223CensusResProof.card_sq_le_of_card_mod_two hF hq3 P hcomm hexp
    rw [Fintype.card_fin] at h
    nlinarith

theorem pRank_projSU_four_le_two {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq3 : p ^ f % 3 = 1) : CFSG.pRank 3 (projSU 4 p f) ≤ 2 := by
  set F := GaloisField p (2 * f)
  have hF : Nat.card F = p ^ (2 * f) := GaloisField.card p (2 * f) (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out hp3 hF
  have hs : IsSimpleGroup (projSU 4 p f) := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f
      (by rw [hF, ← pow_mul, mul_comm]) 4 (by norm_num) (by
        intro h
        exact absurd (Prod.mk.inj h).1 (by norm_num))
    exact (Sec4.projSUEquivStatedProj 4 p f).isSimpleGroup
  have : Finite (projSU 4 p f) := inferInstance
  refine pRank_le_of_pRank_quot_center (by norm_num)
    (Sec21.Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
      Sec4.card_le_of_projImage (Subgroup.closure {A : GL (Fin 4) F |
        GeneralLinearGroup.det A = 1 ∧
        ((A : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)))ᵀ * (A : Matrix (Fin 4) (Fin 4) F) = 1})
        hs (m := 4) (by norm_num)
        (fun c hc => Sec4.pow_four_of_det_scalar (Sec4.det_of_mem_closure_su _ hc))
        (by norm_num) (fun P hPH hcomm hexp => ?_) B hB)
  have : Finite F := inferInstance
  have : Finite P := Finite.of_injective _ Subtype.val_injective
  have h := Sec21.Item223CensusResProof.card_sq_le_of_unitary_of_mod_one h3 hq3 P hcomm hexp
    fun x hx => Sec21.Item223CensusResProof.unitary_of_mem_closure_su (hPH hx)
  rw [Fintype.card_fin] at h
  nlinarith

theorem pRank_g2_le_two
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (X : Type) [Group X] [Finite X]
    (hX : ChevalleyExceptionalModel X .G2 p 1) : CFSG.pRank 3 X ≤ 2 := by
  have h := Sec21.g2OddThreeRankTwo_holds p hp3 X hX
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  have hZ := Sec21.Item223RankResProof.center_eq_bot_of_mulEquiv e
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have e' : X ≃* X ⧸ Subgroup.center X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num) e'.toMonoidHom
    e'.injective).trans h

theorem k417RankTwoLieP_holds :
    Res417Three.K417RankTwoLieP := by
  intro p _ hp3
  refine ⟨fun X _ _ hX => pRank_g2_le_two hp3 X hX, fun hp => ?_, fun hp => ?_⟩
  · exact pRank_projSU_four_le_two (by omega) le_rfl (by rw [pow_one]; exact hp)
  · exact pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp)

end CFSG.RankThree.PartTwo.Sec4.Res417Four
