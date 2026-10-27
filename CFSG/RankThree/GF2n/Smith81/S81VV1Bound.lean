module

public import CFSG.RankThree.GF2n.Smith81.S81VCoreFix
public import CFSG.RankThree.GF2n.Smith81.S81JGSide

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem finrank_V1At_le (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h3U : InCaseE3U M Q Z B)
    (hg : GlobalModelData M Q Z γ M₀)
    {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (A : ↥(SUid σ 6) →* (M₀.E ≃ₗ[K] M₀.E)) (W : Submodule F (Fin 6 → F))
    (hFix : ∀ v, v ∈ fixAt σ A W ↔ ∃ x ∈ B, M₀.π x = v)
    (hU' : ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q B → ∃ u ∈ PtStab σ W, ∀ v, A u v = T s v) :
    finrank K (V1At σ A M₀.B W) ≤ 10 := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hctx : Ctx M Q Z B := hc.ctx
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hQ21 : Nat.card Q = Nat.card Z ^ 21 := by
    obtain ⟨t, -, h⟩ := h3U
    exact h.1
  have hw : Width Q Z 10 := by simpa [Width] using hQ21
  obtain ⟨hno, hgen⟩ := eTacitE3U_of_genByB hGen G M Q Z B IH hc h3U B hctx
  have h34' : Conc34 M Q Z B := h34 G M Q Z B hctx 10 hw (by norm_num) hno hgen
  obtain ⟨-, -, -, hcard⟩ := stroth_3_5 h34 hctx hw (by norm_num) hno hgen
  have h1 : 1 < Nat.card Z := by
    rw [← hg.card]
    exact Finite.one_lt_card
  have hZpos : 0 < Nat.card Z := by omega
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, ∀ y, y ∈ X ↔ y ∈ Q ∧ M₀.π y ∈ V1At σ A M₀.B W := by
    refine ⟨{ carrier := {y | y ∈ Q ∧ M₀.π y ∈ V1At σ A M₀.B W}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun y => Iff.rfl⟩
    · rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
      refine ⟨Q.mul_mem hy hz, ?_⟩
      rw [M₀.π_mul y hy z hz]
      exact Submodule.add_mem _ hy' hz'
    · refine ⟨Q.one_mem, ?_⟩
      rw [M₀.pi_one]
      exact Submodule.zero_mem _
    · rintro y ⟨hy, hy'⟩
      refine ⟨Q.inv_mem hy, ?_⟩
      rw [M₀.pi_inv hy]
      exact Submodule.neg_mem _ hy'
  have hXle : X ≤ Q ⊓ Subgroup.centralizer (B : Set G) := by
    intro y hy
    obtain ⟨hyQ, hyV⟩ := (hX y).1 hy
    refine Subgroup.mem_inf.2 ⟨hyQ, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
    have hbB : b ∈ B := hb
    have hfix : M₀.π b ∈ fixAt σ A W := (hFix _).2 ⟨b, hbB, rfl⟩
    have hz : M₀.B (M₀.π b) (M₀.π y) = 0 := (mem_V1At.1 hyV).1 _ hfix
    exact (M₀.comm_iff_B hg.reg (hctx.le hbB) hyQ).2 hz
  have key : ∀ s : Lgen M (LB M Q B), (s : G) ∈ LB M Q B → ∀ y ∈ X,
      ⁅(s : G), y⁆ ∈ (B ⊔ Z : Subgroup G) := by
    intro s hs y hy
    obtain ⟨hyQ, hyV⟩ := (hX y).1 hy
    obtain ⟨u, hu, hAu⟩ := hU' s hs
    have hTe' : M₀.π ((s : G) * y * (s : G)⁻¹) = T s (M₀.π y) := hTe s y hyQ
    obtain ⟨b, hb, hbp⟩ := (hFix _).1 ((mem_V1At.1 hyV).2 u hu)
    have hbp' : M₀.π b = T s (M₀.π y) - M₀.π y := by rw [hbp, hAu]
    have hsN : (s : G) ∈ Subgroup.normalizer (Q : Set G) := Lgen_le_normalizer_Q hctx s.2
    have hty : (s : G) * y * (s : G)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hsN y).1 hyQ
    have hcQ : ⁅(s : G), y⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hty (Q.inv_mem hyQ)
    have hπc : M₀.π ⁅(s : G), y⁆ = T s (M₀.π y) + -M₀.π y := by
      rw [commutatorElement_def, M₀.π_mul _ hty _ (Q.inv_mem hyQ), M₀.pi_inv hyQ, hTe']
    have hbQ : b ∈ Q := hctx.le hb
    have hπeq : M₀.π b = M₀.π ⁅(s : G), y⁆ := by
      rw [hπc, hbp', sub_eq_add_neg]
    have hbc : b⁻¹ * ⁅(s : G), y⁆ ∈ Z := (M₀.pi_eq_iff hbQ hcQ).1 hπeq
    have hmem := Subgroup.mul_mem_sup hb hbc
    rwa [mul_inv_cancel_left] at hmem
  have hcond : ∀ x ∈ X, ∀ t ∈ LB M Q B, ⁅t, x⁆ ∈ (B ⊔ Z : Subgroup G) := by
    intro y hy t ht
    have hLg : t ∈ Lgen M (LB M Q B) := le_Lgen (LB M Q B) ht
    exact key ⟨t, hLg⟩ ht y hy
  have hXQB : X ≤ Q ⊓ QB B := h34' X hXle hcond
  have hsub : ∀ w ∈ V1At σ A M₀.B W, w ∈ M₀.img (Q ⊓ QB B) := by
    intro w hw
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj w
    exact M₀.pi_mem_img (hXQB ((hX x).2 ⟨hxQ, hw⟩)) hxQ
  have hinj : Function.Injective
      (fun w : ↥(V1At σ A M₀.B W) => (⟨(w : M₀.E), hsub (w : M₀.E) w.2⟩ :
        ↥(M₀.img (Q ⊓ QB B)))) := by
    intro a b hab
    have h2 := congrArg Subtype.val hab
    exact Subtype.ext h2
  have hle_card : Nat.card ↥(V1At σ A M₀.B W) ≤ Nat.card ↥(M₀.img (Q ⊓ QB B)) :=
    Nat.card_le_card_of_injective _ hinj
  have hS : Q ⊓ QB B ≤ Q := inf_le_left
  have hVS : Z ≤ Q ⊓ QB B := le_inf hZQ hctx.Z_le_QB.1
  have hcS := M₀.card_eq hS hVS
  rw [hcard, pow_succ'] at hcS
  have himg : Nat.card ↥(M₀.img (Q ⊓ QB B)) = Nat.card Z ^ 10 :=
    (Nat.eq_of_mul_eq_mul_left hZpos hcS).symm
  have hcardV : Nat.card ↥(V1At σ A M₀.B W) = Nat.card K ^ finrank K (V1At σ A M₀.B W) :=
    Module.natCard_eq_pow_finrank
  rw [hcardV, himg, hg.card] at hle_card
  exact (Nat.pow_le_pow_iff_right h1).mp hle_card

end CFSG.RankThree.GF2n.Smith81.S81V
