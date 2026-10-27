module

public import CFSG.Quasithin.MS93.S5Q2X52Sp
public import CFSG.Quasithin.MS93.S5Q2X52Coc

public noncomputable section

namespace CFSG.Quasithin.MS93.S5Q2.X52

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

open MSP

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem shape_of_eq (hF : Fintype.card F = 2) {φ : Sp4 F → V4 F}
    (hφ : ∀ g g', φ (g * g') = φ g + mat g *ᵥ φ g') {B : F} (hB : B ≠ 0) {m₀ : V4 F}
    (hform : ∀ g, φ g = S5.cform B m₀ g) {E : Subgroup (Sp4 F)} (hE2 : IsPGroup 2 E)
    (hq : commSp E ≤ fixSp E) (hE1 : E ≠ ⊥)
    (hcard : Nat.card (V4 F) = Nat.card E * Nat.card (fixSp E)) {v : V4 F}
    (hv : ∀ g ∈ E, φ g = mat g *ᵥ v - v) :
    (∃ w : V4 F, w ≠ 0 ∧ E = xPoint (F ∙ w)) ∨
      ∃ w₁ w₂ : V4 F, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ (F ∙ w₁) ≠ (F ∙ w₂) ∧ form F w₁ w₂ = 0 ∧
        E = xPoint (F ∙ w₁) ⊔ xPoint (F ∙ w₂) ∧ Nat.card E = 4 := by
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hV : Nat.card (V4 F) = 16 := by rw [card_V4, hNF]; norm_num
  have hfix : Nat.card (fixSp E) = 2 ^ Module.finrank F (fixSp E) := by rw [card_fixSp, hNF]
  have hd4 : Module.finrank F (fixSp E) ≤ 4 := (Submodule.finrank_le _).trans (by simp)
  by_cases hd : Module.finrank F (fixSp E) ≤ 2
  · right
    obtain ⟨hl, hEl, -⟩ := S33.line_of_quadratic hE2 hq hd
    have hf4 : Nat.card (fixSp E) = 4 := card_eq_four_of_isLine hNF hl
    have hE4 : Nat.card E = 4 := by rw [hV, hf4] at hcard; omega
    obtain ⟨g₀, J, m', hJQ, hJE, hJ0⟩ := exists_conj_Q₁ hφ hform hl hEl hv
    have hcJ : Nat.card J = 4 := by rw [← hE4, ← hJE, card_map_conj]
    obtain ⟨x, y, hx, hy, hxl, hyl, hxy, hJeq⟩ := S5.eq_xPoint_sup_of_cform hF hB hJQ hJ0 hcJ.ge
    refine ⟨mat g₀ *ᵥ x, mat g₀ *ᵥ y, fun h0 => hx (mulVec_mat_injective g₀ (by
      show mat g₀ *ᵥ x = mat g₀ *ᵥ 0
      rw [h0, Matrix.mulVec_zero])), fun h0 => hy (mulVec_mat_injective g₀ (by
      show mat g₀ *ᵥ y = mat g₀ *ᵥ 0
      rw [h0, Matrix.mulVec_zero])), fun h0 => hxy ?_, ?_, ?_, hE4⟩
    · have e1 := congrArg (Submodule.map (Matrix.mulVecLin (mat g₀⁻¹))) h0
      simp only [Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply,
        mat_inv_mulVec] at e1
      exact e1
    · rw [form_mat]
      have hxl' : x ∈ ln₀ F := hxl
      have hyl' : y ∈ ln₀ F := hyl
      exact isLine_ln₀.le_perp hyl' |> fun h' => (mem_perp.1 h') x hxl'
    · rw [← hJE, hJeq, Subgroup.map_sup, xPoint_map_conj, xPoint_map_conj,
        Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
      rfl
  · left
    push Not at hd
    have hd3 : Module.finrank F (fixSp E) = 3 := by
      by_contra h3
      have h4 : Module.finrank F (fixSp E) = 4 := by omega
      have htop : fixSp E = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h4)
      exact hE1 (fixSp_eq_top_iff.1 htop)
    have hp : IsPoint (perp (fixSp E)) := by
      have := finrank_perp (fixSp E)
      unfold IsPoint
      omega
    have hEx : E ≤ xPoint (perp (fixSp E)) := by
      show E ≤ fixer (perp (perp (fixSp E)))
      rw [perp_perp]
      exact le_fixer_iff.2 le_rfl
    obtain ⟨w, hw, hpw⟩ := exists_eq_span_of_isPoint hp
    refine ⟨w, hw, ?_⟩
    rw [← hpw]
    refine Subgroup.eq_of_le_of_card_ge hEx ?_
    rw [card_xPoint hp, hNF]
    rw [hV, hfix, hd3] at hcard
    omega

omit [Fintype F] [CharP F 2] in
theorem exists_swap_of_xPoint (c : ZMod 2 ≃+* F) {w : V4 F} (hw : w ≠ 0) :
    ∃ a b : Fin 6, a ≠ b ∧ B5FinSp.theta c (Equiv.swap a b) = transv w 1 ∧
      ∀ g ∈ xPoint (F ∙ w), g = 1 ∨ g = transv w 1 := by
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_congr c.toEquiv.symm, Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨a, b, hab, hs⟩ := isSwap_theta_symm_transv c hw
  refine ⟨a, b, hab, ?_, fun g hg => S33.eq_one_or_eq_transv hNF hw hg⟩
  rw [← hs, MulEquiv.apply_symm_apply]

theorem swap_disjoint : ∀ a b c d : Fin 6, a ≠ b → c ≠ d →
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b →
    Equiv.swap a b ≠ Equiv.swap c d → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  decide

end Sp

section Count

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}
  (h : PUHyp M T L) (nv : S5.NatVec M T L a) {K : Subgroup G} (hKM : K ≤ M)

omit [Fintype F] in
theorem card_range_le_relIndex_xFix :
    Nat.card (Set.range (phiK h nv hKM)) ≤
      (Subgroup.centralizer (K : Set G)).relIndex (xFix h) := by
  set H := (Subgroup.centralizer (K : Set G)).subgroupOf (xFix h) with hH
  set N := (phiK h nv hKM).ker with hN
  have hHN : H ≤ N := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext κ
    rw [phiK_apply]
    have hc : ⁅(κ : G), (y : G)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hy) κ κ.2
    rw [hc, S5.uCoord_one]
    rfl
  have h2 : H.relIndex N * N.index = H.index := Subgroup.relIndex_mul_index hHN
  have h3 : N.index = Nat.card (Set.range (phiK h nv hKM)) := Subgroup.index_ker _
  have h4 : 0 < H.relIndex N := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) = H.index := rfl
  rw [h1, ← h2, h3]
  exact Nat.le_mul_of_pos_left _ h4

omit [Fintype F] in
theorem mem_centralizer_of_relIndex_eq
    (heq : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) =
      Nat.card (Set.range (phiK h nv hKM)))
    {w : G} (hw : w ∈ xFix h) (hw0 : ∀ κ : ↥K, S5.uCoord nv ⁅(κ : G), w⁆ = 0) :
    w ∈ Subgroup.centralizer (K : Set G) := by
  set H := (Subgroup.centralizer (K : Set G)).subgroupOf (xFix h) with hH
  set N := (phiK h nv hKM).ker with hN
  have hHN : H ≤ N := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext κ
    rw [phiK_apply]
    have hc : ⁅(κ : G), (y : G)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hy) κ κ.2
    rw [hc, S5.uCoord_one]
    rfl
  have h2 : H.relIndex N * N.index = H.index := Subgroup.relIndex_mul_index hHN
  have h3 : N.index = Nat.card (Set.range (phiK h nv hKM)) := Subgroup.index_ker _
  have h0 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : H.relIndex N = 1 := by
    have : H.index = N.index := by rw [h3]; exact heq
    rw [this] at h2
    exact (Nat.mul_eq_right h0.ne').1 h2
  have hNH : N ≤ H := Subgroup.relIndex_eq_one.1 h1
  have hwN : (⟨w, hw⟩ : ↥(xFix h)) ∈ N := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext κ
    rw [phiK_apply]
    exact hw0 κ
  exact Subgroup.mem_subgroupOf.1 (hNH hwN)

theorem card_le_card_range (hd : S5.IsSp4Data M T L 1 F a) {x : G} (hx : x ∈ xFix h)
    {B : F} (hB : B ≠ 0) {m₀ : MSP.V4 F} [CharP F 2]
    (hform : ∀ g, S5.cocSp hd nv x g = S5.cform B m₀ g)
    (hE2 : IsPGroup 2 (S5.imSp a K))
    (hq : MSP.commSp (S5.imSp a K) ≤ MSP.fixSp (S5.imSp a K)) (hE1 : S5.imSp a K ≠ ⊥) :
    Nat.card (S5.imSp a K) ≤ Nat.card (Set.range (phiK h nv hKM)) ∧
      (Nat.card (Set.range (phiK h nv hKM)) ≤ Nat.card (S5.imSp a K) →
        (∃ w : MSP.V4 F, w ≠ 0 ∧ S5.imSp a K = MSP.xPoint (F ∙ w)) ∨
        (∃ w₁ w₂ : MSP.V4 F, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ (F ∙ w₁) ≠ (F ∙ w₂) ∧ MSP.form F w₁ w₂ = 0 ∧
          S5.imSp a K = MSP.xPoint (F ∙ w₁) ⊔ MSP.xPoint (F ∙ w₂) ∧
          Nat.card (S5.imSp a K) = 4) ∨
        ∃ l, MSP.IsLine l ∧ S5.imSp a K = MSP.qLine l) := by
  have hF : Fintype.card F = 2 := by simpa using hd.card_eq
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hV : Nat.card (MSP.V4 F) = 16 := by rw [MSP.card_V4, hNF]; norm_num
  have hφ := S5.cocSp_mul hd h nv hx.1 hx.2
  set E := S5.imSp a K with hE
  set r := Nat.card (Set.range (phiK h nv hKM)) with hr
  set f := Nat.card (MSP.fixSp E) with hf
  have hr1 : 16 ≤ f * r := hV ▸ card_le_card_fixSp_mul_card_range h nv hKM
  have hf0 : 0 < f := Nat.card_pos
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have htwo : (∀ v : MSP.V4 F, ∃ g ∈ E, S5.cocSp hd nv x g ≠ MSP.mat g *ᵥ v - v) →
      32 ≤ f * r := by
    intro hnc
    have key := two_mul_card_le_card_fixSp_mul_card_range h nv hKM hx fun v => by
      obtain ⟨g, hg, hgv⟩ := hnc v
      obtain ⟨⟨m, hmM⟩, hmK, rfl⟩ := hg
      rw [S5.cocSp_a hd h nv hx.1 hx.2 hmM] at hgv
      exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hmK⟩, hgv⟩
    rw [hV] at key
    exact key
  rcases quad_shape hNF hE2 hq hE1 with ⟨hl, hT1⟩ | ⟨hl, hT2⟩ | ⟨-, hT3⟩ | ⟨-, hT4⟩
  · have hcard : Nat.card E = 4 := by rw [hT1]; exact MSP.card_qLine_inf_commutator hNF hl
    have hf4 : f = 4 := card_eq_four_of_isLine hNF hl
    have h32 := htwo (not_cob_of_shape hF hφ hB hform hl (Or.inl hT1))
    rw [hf4] at h32
    exact ⟨by omega, fun hle => by omega⟩
  · have hcard : Nat.card E = 8 := by rw [hT2, MSP.card_qLine hl, hNF]; norm_num
    have hf4 : f = 4 := card_eq_four_of_isLine hNF hl
    have h32 := htwo (not_cob_of_shape hF hφ hB hform hl (Or.inr hT2))
    rw [hf4] at h32
    exact ⟨by omega, fun _ => Or.inr (Or.inr ⟨_, hl, hT2⟩)⟩
  · have h1 : 2 * Nat.card E ≤ r := by
      have : f * (2 * Nat.card E) ≤ f * r := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hf0
    exact ⟨by omega, fun hle => by omega⟩
  · have h1 : Nat.card E ≤ r := by
      have : f * Nat.card E ≤ f * r := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hf0
    refine ⟨h1, fun hle => ?_⟩
    have hrE : r = Nat.card E := le_antisymm hle h1
    have hcard : Nat.card (MSP.V4 F) = Nat.card E * f := by
      rw [hV]
      nlinarith
    have hcob : ∃ v : MSP.V4 F, ∀ g ∈ E, S5.cocSp hd nv x g = MSP.mat g *ᵥ v - v := by
      by_contra hcon
      push Not at hcon
      have := htwo hcon
      nlinarith
    obtain ⟨v, hv⟩ := hcob
    rcases shape_of_eq hF hφ hB hform hE2 hq hE1 hcard hv with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)

end Count

end CFSG.Quasithin.MS93.S5Q2.X52
