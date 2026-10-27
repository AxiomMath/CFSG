module

public import CFSG.RankThree.GF2n.Smith81.S81VTheta
public import CFSG.RankThree.GF2n.Smith81.S81VPointData
public import CFSG.RankThree.GF2n.Smith81.S81VV1Bound
public import CFSG.RankThree.GF2n.Smith81.S81VUniformCore

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.S81J CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Module

theorem smith24E3UUniform_of_inputs (h34 : Stroth34Statement)
    (hGen : StrothGenByBStatement) : Smith24E3UUniformStatement := by
  intro G _ _ M Q Z B IH hR h3U K _ _ γ M₀ hg
  have hc : SmithECfg M Q Z B := by
    obtain ⟨t, hD, h⟩ := h3U
    exact ⟨hR.toCfg, t, hD, Or.inl ⟨h.1, h.2.1, Or.inl h.2.2⟩⟩
  have hctx : Ctx M Q Z B := hc.ctx
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hq4 : 4 ≤ Nat.card Z := hctx.hyp.q4
  obtain ⟨f, k, hf, -⟩ := hctx.hyp.cp
  have hf1 : 1 ≤ f := by
    by_contra h0
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hf
    omega
  haveI : CharP K 2 := charP_two_of_card_eq hf1 (hKcard.trans hf)
  obtain ⟨t, -, hQ21, -, hN, F, _, _, hFcard, ⟨θ⟩⟩ := id h3U
  haveI := hN
  have hF2 : Nat.card F = (2 ^ f) ^ 2 := by rw [hFcard, hf]
  haveI : CharP F 2 := charP_two_of_card_eq (n := 2 * f) (by omega) (by rw [hF2, ← pow_mul, mul_comm])
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) := isUnitaryInvolution_unitaryInvolution hF2
  have hFσ : Nat.card (Fσ (unitaryInvolution F 2 f)) = 2 ^ f := card_Fσ_eq hF2
  have hFK : Nat.card (Fσ (unitaryInvolution F 2 f)) = Nat.card K := by rw [hFσ, hKcard, hf]
  have hFK2 : Nat.card F = Nat.card K ^ 2 := by rw [hF2, hKcard, hf]
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite (Fσ (unitaryInvolution F 2 f))
  have hKK' : Fintype.card K = Fintype.card (Fσ (unitaryInvolution F 2 f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hFK.symm
  let e₀ : K ≃+* Fσ (unitaryInvolution F 2 f) := FiniteField.ringEquivOfCardEq hKK'
  obtain ⟨Θ, hΘ, hk3, hkc⟩ : ∃ Θ : ↥(SUid (unitaryInvolution F 2 f) 6) →*
      (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))), Function.Surjective Θ ∧
      (∀ n ∈ Θ.ker, n ^ 3 = 1) ∧ (∀ n ∈ Θ.ker, ∀ x : ↥(SUid (unitaryInvolution F 2 f) 6), n * x = x * n) := by
    have key : ∀ q : ℕ, q = 2 ^ f →
        ∀ θ' : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃*
          StatedProj (StatedSU 6 q F),
        ∃ Θ : ↥(SUid (unitaryInvolution F 2 f) 6) →*
          (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))), Function.Surjective Θ ∧
          (∀ n ∈ Θ.ker, n ^ 3 = 1) ∧
          (∀ n ∈ Θ.ker, ∀ x : ↥(SUid (unitaryInvolution F 2 f) 6), n * x = x * n) := by
      intro q hq θ'
      subst hq
      exact exists_ThetaU hF2 θ'
    exact key _ hf θ
  obtain ⟨T, hTe, hTker, hTiso⟩ := exists_T_Lgen_isom hctx hg
  let Tbar : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) →* (M₀.E ≃ₗ[K] M₀.E) :=
    QuotientGroup.lift (Q.subgroupOf (Lgen M (LB M Q B))) T
      (fun s hs => (hTker s).2 (Subgroup.mem_subgroupOf.1 hs))
  let A : ↥(SUid (unitaryInvolution F 2 f) 6) →* (M₀.E ≃ₗ[K] M₀.E) := Tbar.comp Θ
  have hA1 : ∀ (h : ↥(SUid (unitaryInvolution F 2 f) 6)) (s : Lgen M (LB M Q B)),
      Θ h = QuotientGroup.mk s → ∀ v, A h v = T s v := by
    intro h s hs v
    show Tbar (Θ h) v = T s v
    rw [hs]
    rfl
  have hAT1 : ∀ s : Lgen M (LB M Q B), ∃ h : ↥(SUid (unitaryInvolution F 2 f) 6),
      ∀ v, T s v = A h v := by
    intro s
    obtain ⟨h, hh⟩ := hΘ (QuotientGroup.mk s)
    exact ⟨h, fun v => (hA1 h s hh v).symm⟩
  have hAT2 : ∀ h : ↥(SUid (unitaryInvolution F 2 f) 6), ∃ s : Lgen M (LB M Q B),
      ∀ v, T s v = A h v := by
    intro h
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Θ h)
    exact ⟨s, fun v => (hA1 h s hs.symm v).symm⟩
  obtain ⟨e', ψ, φ, hE⟩ := uniform_of_core_U hσ e₀ (by rw [hKcard]; exact hq4) hFK2
    (finrank_E_eq_twenty hg hZQ hQ21) T hTe hTker (Lgen_le_normalizer_Q hctx) hTiso A hAT1 hAT2
    (fun A' hA'Z hA'Q hA'ne => exists_point_dataU h34 hGen IH hc h3U hg hσ hFK Θ hΘ hk3 hkc T hTe
      hTker A hA1 hA'Z hA'Q hA'ne)
    ⟨hctx.conj, hctx.le, hctx.ne⟩ (fun v => points_span hctx.hyp M₀ v)
    (fun W hFix hU' => finrank_V1At_le h34 hGen IH hc h3U hg T hTe A W hFix hU')
  exact ⟨F, inferInstance, inferInstance, inferInstance, f, hF2, e', ψ, φ, hE⟩

end CFSG.RankThree.GF2n.Smith81.S81V
