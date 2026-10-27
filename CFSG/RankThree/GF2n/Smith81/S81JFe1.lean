module

public import CFSG.RankThree.GF2n.Smith81.S81JUniform
public import CFSG.RankThree.GF2n.Smith81.S81JGSide
public import CFSG.RankThree.GF2n.Smith81.S81BCount

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.S81J Module

section Points

private theorem exists_mul_of_mem_sup {G : Type} [Group G] {Q H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hx : x ∈ Q ⊔ H) :
    ∃ q ∈ Q, ∃ h ∈ H, q * h = x := by
  have hconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.1 (hH hh) q).1 hq
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, H.one_mem, by simp⟩
    · exact ⟨1, Q.one_mem, x, hx, by simp⟩
  · exact ⟨1, Q.one_mem, 1, H.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    exact ⟨y₁ * (z₁ * y₂ * z₁⁻¹), Q.mul_mem hy₁ (hconj z₁ hz₁ y₂ hy₂), z₁ * z₂,
      H.mul_mem hz₁ hz₂, by simp [mul_assoc]⟩
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨z⁻¹ * y⁻¹ * z⁻¹⁻¹, ?_, z⁻¹, H.inv_mem hz, by simp [mul_assoc]⟩
    exact hconj z⁻¹ (H.inv_mem hz) y⁻¹ (Q.inv_mem hy)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_point_data [CharP K 2] (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h3L : InCaseE3L M Q Z B)
    (hg : GlobalModelData M Q Z γ M₀) [(Q.subgroupOf (Lgen M (LB M Q B))).Normal]
    (Θ : ↥(StatedSL 6 K) →* (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))))
    (hΘ : Function.Surjective Θ) (hk3 : ∀ n ∈ Θ.ker, n ^ 3 = 1)
    (hkc : ∀ n ∈ Θ.ker, ∀ x : ↥(StatedSL 6 K), n * x = x * n)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hTker : ∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q) (A : SLAct K M₀.E)
    (hA1 : ∀ (h : ↥(StatedSL 6 K)) (s : Lgen M (LB M Q B)), Θ h = QuotientGroup.mk s →
      ∀ v, A.act h v = T s v)
    {A' : Subgroup G} (hA'Z : IsZConjugate Z A') (hA'Q : A' ≤ Q) (hA'ne : A' ≠ Z) :
    ∃ W : Submodule K (Fin 6 → K), finrank K W = 3 ∧ finrank K (A.Fix W) = 1 ∧
      (∀ v, v ∈ A.Fix W ↔ ∃ x ∈ A', M₀.π x = v) ∧
      ∀ u ∈ UnipGL K W, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A' ∧ ∀ v, T t v = A.act u v := by
  classical
  have hctx : Ctx M Q Z B := hc.ctx
  have hctxA : Ctx M Q Z A' := ⟨hctx.hyp, hA'Z, hA'Q, hA'ne⟩
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hM : M ≤ Subgroup.normalizer (Q : Set G) := hctx.hyp.Q_normal.2
  have hQ21 : Nat.card Q = Nat.card Z ^ 21 := by
    obtain ⟨t, -, h⟩ := h3L
    exact h.1
  have hw : Width Q Z 10 := by simpa [Width] using hQ21
  obtain ⟨hno, hgen⟩ := eTacitE3L_of_genByB hGen G M Q Z B IH hc h3L A' hctxA
  obtain ⟨-, hCQt, hLBcard, -⟩ := stroth_3_5 h34 hctxA hw (by norm_num) hno hgen
  have hLBle : LB M Q A' ≤ Lgen M (LB M Q B) :=
    LB_le_Lgen_of_point_E3L h34 hGen IH hc h3L hctxA
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  have hLBcard9 : Nat.card ↥(LB M Q A') = Nat.card Q * Nat.card Z ^ 9 := by
    simpa using hLBcard
  obtain ⟨hcomm, hsq, hbcard⟩ := bar_props hctxA hQLg hLBle hLBcard9
  have hbcardK : Nat.card ↥(bar (Lgen M (LB M Q B)) Q (LB M Q A')) = Nat.card K ^ 9 := by
    rw [hbcard, hg.card]
  obtain ⟨W, E, hW3, hEmap, hEU⟩ := exists_W_of_bar Θ hΘ hk3 hkc _ hcomm hsq hbcardK
  have hU : ∀ u ∈ UnipGL K W, ∃ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A' ∧
      ∀ v, A.act u v = T s v := by
    intro u hu
    obtain ⟨h, hhE, rfl⟩ := (hEU u).1 hu
    have hmem : Θ h ∈ bar (Lgen M (LB M Q B)) Q (LB M Q A') := by
      rw [← hEmap]
      exact Subgroup.mem_map_of_mem _ hhE
    obtain ⟨s, hs, hsΘ⟩ := Subgroup.mem_map.1 hmem
    exact ⟨s, Subgroup.mem_subgroupOf.1 hs, fun v => hA1 h s hsΘ.symm v⟩
  have hU' : ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A' →
      ∃ u ∈ UnipGL K W, ∀ v, A.act u v = T s v := by
    intro s hs
    have hmem : (QuotientGroup.mk s : ↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ∈
        bar (Lgen M (LB M Q B)) Q (LB M Q A') :=
      Subgroup.mem_map.2 ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [← hEmap] at hmem
    obtain ⟨h, hhE, hhΘ⟩ := Subgroup.mem_map.1 hmem
    exact ⟨(h : GL (Fin 6) K), (hEU _).2 ⟨h, hhE, rfl⟩, fun v => hA1 h s hhΘ v⟩
  have hFix : ∀ v, v ∈ A.Fix W ↔ ∃ x ∈ A', M₀.π x = v := by
    intro v
    rw [← fixed_iff_mem_img (Lg := Lgen M (LB M Q B)) hctxA hctxA.LB_le_M hM hZQ rfl hCQt hA'Q T
      hTe hLBle v, SLAct.mem_Fix]
    constructor
    · intro hv s hs
      obtain ⟨u, hu, hAu⟩ := hU' s hs
      rw [← hAu v]
      exact hv u hu
    · intro hv u hu
      obtain ⟨s, hs, hAu⟩ := hU u hu
      rw [hAu v]
      exact hv s hs
  have hline : finrank K (A.Fix W) = 1 := by
    obtain ⟨g, hg'⟩ := hA'Z
    subst hg'
    obtain ⟨e, he0, he⟩ := hg.line g hA'ne hA'Q
    have hspanE : A.Fix W = Submodule.span K {e} := by
      ext v
      rw [hFix v, Submodule.mem_span_singleton]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨s, hs⟩ := (he (M₀.π x)).1 ⟨x, hx, hA'Q hx, rfl⟩
        exact ⟨s, hs.symm⟩
      · rintro ⟨s, rfl⟩
        obtain ⟨x, hx, -, hxs⟩ := (he (s • e)).2 ⟨s, rfl⟩
        exact ⟨x, hx, hxs⟩
    rw [hspanE]
    exact finrank_span_singleton he0
  refine ⟨W, hW3, hline, hFix, ?_⟩
  intro u hu
  obtain ⟨s, hs, hAu⟩ := hU u hu
  obtain ⟨q, hq, t', ht', hqt⟩ := exists_mul_of_mem_sup (Q := Q) (H := QB A' ⊓ M)
    (fun x hx => hM hx.2) hs
  have hqLg : q ∈ Lgen M (LB M Q B) := hQLg hq
  have ht'Lg : t' ∈ Lgen M (LB M Q B) := by
    have e : t' = q⁻¹ * (s : G) := by
      rw [← hqt]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hqLg) s.2
  refine ⟨⟨t', ht'Lg⟩, (Subgroup.mem_inf.1 ht').1, fun v => ?_⟩
  have hs_eq : s = ⟨q, hqLg⟩ * ⟨t', ht'Lg⟩ := Subtype.ext hqt.symm
  have hTq : T ⟨q, hqLg⟩ = 1 := (hTker _).2 hq
  rw [hAu v, hs_eq, map_mul, hTq, one_mul]

theorem smith24E3LUniform_of_inputs (h34 : Stroth34Statement) (hGen : StrothGenByBStatement) :
    Smith24E3LUniformStatement := by
  intro G _ _ M Q Z B IH hR h3L K _ _ γ M₀ hg
  have hc : SmithECfg M Q Z B := by
    obtain ⟨t, hD, h⟩ := h3L
    exact ⟨hR.toCfg, t, hD, Or.inl ⟨h.1, h.2.1, Or.inr h.2.2⟩⟩
  have hctx : Ctx M Q Z B := hc.ctx
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hq4 : 4 ≤ Nat.card Z := hctx.hyp.q4
  have hcp : CharP K 2 := by
    obtain ⟨n, k, hn, -⟩ := hctx.hyp.cp
    have hn1 : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      rw [hn0, pow_zero] at hn
      omega
    exact charP_two_of_card_eq hn1 (hKcard.trans hn)
  haveI := hcp
  obtain ⟨t, -, hQ21, -, hN, K', _, _, hK'card, ⟨θ⟩⟩ := id h3L
  haveI := hN
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite K'
  have hKK' : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard, hK'card]
  obtain ⟨Θ, hΘ, hk3, hkc⟩ := S81J.exists_Theta (FiniteField.ringEquivOfCardEq hKK') θ
  obtain ⟨T, hTe, hTker⟩ := exists_T_Lgen hctx hg
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_SLAct T (fun s hs => (hTker s).2 hs) Θ hΘ
  exact uniform_of_core (by rw [hKcard]; exact hq4) (finrank_E_eq_twenty hg hZQ hQ21) T hTe hTker
    (Lgen_le_normalizer_Q hctx) A hA2 hA3
    (fun A' hA'Z hA'Q hA'ne => exists_point_data h34 hGen IH hc h3L hg Θ hΘ hk3 hkc T hTe hTker A
      hA1 hA'Z hA'Q hA'ne)
    ⟨hctx.conj, hctx.le, hctx.ne⟩ (fun v => points_span hctx.hyp M₀ v)

end Points

end CFSG.RankThree.GF2n.Smith81
