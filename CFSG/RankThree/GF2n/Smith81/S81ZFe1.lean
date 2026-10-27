module

public import CFSG.RankThree.GF2n.Smith81.S81ZUniform
public import CFSG.RankThree.GF2n.Smith81.S81ZG1
public import CFSG.RankThree.GF2n.Smith81.S81E5Point
public import CFSG.RankThree.GF2n.Smith81.S81E5Stab

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.E7X
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section M2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_map_conj_of_map_conj_eq {H : Type*} [Group H] {A U : Subgroup H} {g : H}
    (h : A.map (MulAut.conj g).toMonoidHom = U) : A = U.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [← h, Subgroup.map_map]
  conv_lhs => rw [← Subgroup.map_id A]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem lvlU_top_eq_UA : lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6) = UA K a7 := by
  have h1 := map_lvlU_top_eq_rootRad7 (K := K)
  rw [rootRad7_eq] at h1
  exact Subgroup.map_injective (f := ιV K) ιV_injective h1

theorem e7M2_holds : E7M2 K := fun A hel hcard => by
  obtain ⟨g, hg⟩ := exists_map_conj_eq_lvlU_top A hel hcard
  exact ⟨g⁻¹, eq_map_conj_of_map_conj_eq (hg.trans lvlU_top_eq_UA)⟩

end M2

theorem smith24E5Uniform_of_inputs (hG1 : E5G1Statement)
    (h34 : Stroth34Statement) (hGen : StrothGenByBStatement) : Smith24E5UniformStatement := by
  intro G _ _ M Q Z B IH hR h5 K _ _ γ M₀ hg
  have hc : SmithECfg M Q Z B := by
    obtain ⟨t, hD, h⟩ := h5
    exact ⟨hR.toCfg, t, hD, Or.inr (Or.inr h)⟩
  have hctx : Ctx M Q Z B := hc.ctx
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hw : Width Q Z 28 := by
    obtain ⟨t, -, h⟩ := h5
    exact h.1
  obtain ⟨f, k, hf, -⟩ := hctx.hyp.cp
  have hf1 : 1 ≤ f := by
    by_contra h0
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hf
    have := hctx.hyp.q4
    omega
  haveI : CharP K 2 := Smith81.charP_two_of_card_eq hf1 (hKcard.trans hf)
  obtain ⟨K', _, _, _, hK'card, θ₁, hθ₁s, hθ₁k⟩ := hG1 G M Q Z B IH hc h5
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite K'
  have hKK' : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'card, hKcard]
  let τ : K' ≃+* K := FiniteField.ringEquivOfCardEq hKK'
  let θ : Lgen M (LB M Q B) →* Gp K :=
    (eAutEquiv K).symm.toMonoidHom.comp ((twistEAut τ).toMonoidHom.comp θ₁)
  have hθs : Function.Surjective θ :=
    (eAutEquiv K).symm.surjective.comp ((twistEAut τ).surjective.comp hθ₁s)
  have hθk : ∀ s : Lgen M (LB M Q B), θ s = 1 ↔ (s : G) ∈ Q := by
    intro s
    have h1 : θ s = 1 ↔ θ₁ s = 1 := by
      show (eAutEquiv K).symm (twistEAut τ (θ₁ s)) = 1 ↔ _
      rw [map_eq_one_iff _ (eAutEquiv K).symm.injective, map_eq_one_iff _ (twistEAut τ).injective]
    rw [h1, hθ₁k]
  have hTac := eTacitE5_of_genByB hGen G M Q Z B IH hc h5
  have hLBle : ∀ A : Subgroup G, Ctx M Q Z A → LB M Q A ≤ Lgen M (LB M Q B) :=
    fun A hA => LB_le_Lgen_of_tacit h34 hc hTac hA
  obtain ⟨ψ, φ, hrange, hker, hequiv⟩ := uniform_of_core_E5 e7M2_holds (e5StabChar_holds K) h34 hctx hw
    hg hTac hLBle θ hθs hθk
  refine ⟨ψ, φ, ⟨hrange, hker, Lgen_le_normalizer_Q hctx, hequiv, ?_⟩⟩
  intro A hAZ hAQ hAne
  exact point_E5 h34 hGen IH hc h5 hg ψ φ hrange hker hequiv hAZ hAQ hAne

end CFSG.RankThree.GF2n.Smith81.S81Z
