module

public import CFSG.RankThree.GF2n.Smith81.S81VGroupSide
public import CFSG.RankThree.GF2n.Smith81.S81VCoreFix
public import CFSG.RankThree.GF2n.Smith81.S81JGSide

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Module

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

theorem exists_point_dataU [CharP K 2] (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h3U : InCaseE3U M Q Z B)
    (hg : GlobalModelData M Q Z γ M₀) [(Q.subgroupOf (Lgen M (LB M Q B))).Normal]
    {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ)
    (hFK : Nat.card (Fσ σ) = Nat.card K)
    (Θ : ↥(SUid σ 6) →* (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))))
    (hΘ : Function.Surjective Θ) (hk3 : ∀ n ∈ Θ.ker, n ^ 3 = 1)
    (hkc : ∀ n ∈ Θ.ker, ∀ x : ↥(SUid σ 6), n * x = x * n)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hTker : ∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q)
    (A : ↥(SUid σ 6) →* (M₀.E ≃ₗ[K] M₀.E))
    (hA1 : ∀ (h : ↥(SUid σ 6)) (s : Lgen M (LB M Q B)), Θ h = QuotientGroup.mk s →
      ∀ v, A h v = T s v)
    {A' : Subgroup G} (hA'Z : IsZConjugate Z A') (hA'Q : A' ≤ Q) (hA'ne : A' ≠ Z) :
    ∃ W : Submodule F (Fin 6 → F), IsTotIso σ W ∧ finrank F W = 3 ∧ finrank K (fixAt σ A W) = 1 ∧
      (∀ v, v ∈ fixAt σ A W ↔ ∃ x ∈ A', M₀.π x = v) ∧
      (∀ u ∈ PtStab σ W, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A' ∧ ∀ v, T t v = A u v) ∧
      ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A' → ∃ u ∈ PtStab σ W, ∀ v, A u v = T s v := by
  classical
  have hctx : Ctx M Q Z B := hc.ctx
  have hctxA : Ctx M Q Z A' := ⟨hctx.hyp, hA'Z, hA'Q, hA'ne⟩
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hM : M ≤ Subgroup.normalizer (Q : Set G) := hctx.hyp.Q_normal.2
  have hQ21 : Nat.card Q = Nat.card Z ^ 21 := by
    obtain ⟨t, -, h⟩ := h3U
    exact h.1
  have hw : Width Q Z 10 := by simpa [Width] using hQ21
  obtain ⟨hno, hgen⟩ := eTacitE3U_of_genByB hGen G M Q Z B IH hc h3U A' hctxA
  obtain ⟨-, hCQt, hLBcard, -⟩ := stroth_3_5 h34 hctxA hw (by norm_num) hno hgen
  have hLBle : LB M Q A' ≤ Lgen M (LB M Q B) :=
    LB_le_Lgen_of_point_E3U h34 hGen IH hc h3U hctxA
  have hQLg : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen _)
  have hLBcard9 : Nat.card ↥(LB M Q A') = Nat.card Q * Nat.card Z ^ 9 := by
    simpa using hLBcard
  obtain ⟨hcomm, hsq, hbcard⟩ := bar_props hctxA hQLg hLBle hLBcard9
  have hbcardF : Nat.card ↥(bar (Lgen M (LB M Q B)) Q (LB M Q A')) = Nat.card (Fσ σ) ^ 9 := by
    rw [hbcard, hFK, hg.card]
  obtain ⟨W, E, hWtot, hW3, hEmap, hEW⟩ :=
    exists_W_of_barU hσ Θ hΘ hk3 hkc _ hcomm hsq hbcardF
  subst hEW
  have hU : ∀ u ∈ PtStab σ W, ∃ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A' ∧
      ∀ v, A u v = T s v := by
    intro u hu
    have hmem : Θ u ∈ bar (Lgen M (LB M Q B)) Q (LB M Q A') := by
      rw [← hEmap]
      exact Subgroup.mem_map_of_mem _ hu
    obtain ⟨s, hs, hsΘ⟩ := Subgroup.mem_map.1 hmem
    exact ⟨s, Subgroup.mem_subgroupOf.1 hs, fun v => hA1 u s hsΘ.symm v⟩
  have hU' : ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q A' →
      ∃ u ∈ PtStab σ W, ∀ v, A u v = T s v := by
    intro s hs
    have hmem : (QuotientGroup.mk s : ↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ∈
        bar (Lgen M (LB M Q B)) Q (LB M Q A') :=
      Subgroup.mem_map.2 ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [← hEmap] at hmem
    obtain ⟨h, hhE, hhΘ⟩ := Subgroup.mem_map.1 hmem
    exact ⟨h, hhE, fun v => hA1 h s hhΘ v⟩
  have hFix : ∀ v, v ∈ fixAt σ A W ↔ ∃ x ∈ A', M₀.π x = v := by
    intro v
    rw [← fixed_iff_mem_img (Lg := Lgen M (LB M Q B)) hctxA hctxA.LB_le_M hM hZQ rfl hCQt hA'Q T
      hTe hLBle v, mem_fixAt]
    constructor
    · intro hv s hs
      obtain ⟨u, hu, hAu⟩ := hU' s hs
      rw [← hAu v]
      exact hv u hu
    · intro hv u hu
      obtain ⟨s, hs, hAu⟩ := hU u hu
      rw [hAu v]
      exact hv s hs
  have hline : finrank K (fixAt σ A W) = 1 := by
    obtain ⟨g, hg'⟩ := hA'Z
    subst hg'
    obtain ⟨e, he0, he⟩ := hg.line g hA'ne hA'Q
    have hspanE : fixAt σ A W = Submodule.span K {e} := by
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
  refine ⟨W, hWtot, hW3, hline, hFix, ?_, hU'⟩
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

end CFSG.RankThree.GF2n.Smith81.S81V
