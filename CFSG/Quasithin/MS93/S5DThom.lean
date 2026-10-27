module

public import CFSG.Quasithin.MS93.S5Q2X52Eq
public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.MS93.Q2GOff
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S51Thom

public section

namespace CFSG.Quasithin.MS93.S5D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

variable {F : Type} [Field F]

theorem mulVec_eq_of_commute_transv (hF : Nat.card F = 2) {g : MSP.Sp4 F} {x : MSP.V4 F}
    (hx : x ≠ 0) (hc : g * MSP.transv x 1 = MSP.transv x 1 * g) : MSP.mat g *ᵥ x = x := by
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF
  have hconj : MSP.transv (MSP.mat g *ᵥ x) 1 = MSP.transv x 1 := by
    rw [← MSP.transv_conj, hc, mul_inv_cancel_right]
  obtain ⟨v, hv⟩ := MSP.exists_form_eq_one hx
  have h1 := congrArg (fun t : MSP.Sp4 F => MSP.mat t *ᵥ v) hconj
  simp only [MSP.transv_mulVec, one_mul, hv, one_smul, add_right_inj] at h1
  rcases MSP.eq_zero_or_eq_one_of_ringEquiv c (MSP.form F (MSP.mat g *ᵥ x) v) with h0 | h0
  · rw [h0, zero_smul] at h1
    exact absurd h1.symm hx
  · rwa [h0, one_smul] at h1

theorem mem_qLine_of_commute_transv (hF : Nat.card F = 2) {g : MSP.Sp4 F} {x y : MSP.V4 F}
    (hx : x ≠ 0) (hy : y ≠ 0) {l : Submodule F (MSP.V4 F)} (hl : l = (F ∙ x) ⊔ (F ∙ y))
    (hcx : g * MSP.transv x 1 = MSP.transv x 1 * g)
    (hcy : g * MSP.transv y 1 = MSP.transv y 1 * g) : g ∈ MSP.qLine l := by
  have hgx := mulVec_eq_of_commute_transv hF hx hcx
  have hgy := mulVec_eq_of_commute_transv hF hy hcy
  intro v hv
  rw [hl] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hu
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hgx, hgy]

theorem xPoint_le_qLine_of_le_stab {p l : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hl : MSP.IsLine l) (h : MSP.xPoint p ≤ MSP.stab l) : MSP.xPoint p ≤ MSP.qLine l :=
  MSP.xPoint_le_qLine hl (MSP.le_of_xPoint_le_stab hp hl h)

theorem qLine_le_qLine_of_le_stab {l l' : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hl' : MSP.IsLine l') (h : MSP.qLine l' ≤ MSP.stab l) : MSP.qLine l' ≤ MSP.qLine l := by
  have hle : l' ≤ l := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact l.zero_mem
    have hp := MSP.isPoint_span hw0
    have hx : MSP.xPoint (F ∙ w) ≤ MSP.qLine l' :=
      MSP.xPoint_le_qLine hl' ((Submodule.span_singleton_le_iff_mem w l').2 hw)
    exact (Submodule.span_singleton_le_iff_mem w l).1
      (MSP.le_of_xPoint_le_stab hp hl (hx.trans h))
  have heq : l' = l := Submodule.eq_of_le_of_finrank_eq hle (by rw [hl.1, hl'.1])
  rw [heq]

theorem le_qLine_of_shape {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    {E : Subgroup (MSP.Sp4 F)} (hEl : E ≤ MSP.stab l)
    (hs : (∃ w : MSP.V4 F, w ≠ 0 ∧ E = MSP.xPoint (F ∙ w)) ∨
      (∃ w₁ w₂ : MSP.V4 F, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ (F ∙ w₁) ≠ (F ∙ w₂) ∧ MSP.form F w₁ w₂ = 0 ∧
        E = MSP.xPoint (F ∙ w₁) ⊔ MSP.xPoint (F ∙ w₂) ∧ Nat.card E = 4) ∨
      ∃ l', MSP.IsLine l' ∧ E = MSP.qLine l') : E ≤ MSP.qLine l := by
  rcases hs with ⟨w, hw, rfl⟩ | ⟨w₁, w₂, hw₁, hw₂, -, -, rfl, -⟩ | ⟨l', hl', rfl⟩
  · exact xPoint_le_qLine_of_le_stab (MSP.isPoint_span hw) hl hEl
  · exact sup_le (xPoint_le_qLine_of_le_stab (MSP.isPoint_span hw₁) hl (le_sup_left.trans hEl))
      (xPoint_le_qLine_of_le_stab (MSP.isPoint_span hw₂) hl (le_sup_right.trans hEl))
  · exact qLine_le_qLine_of_le_stab hl hl' hEl

theorem map_span_mat (g : MSP.Sp4 F) (x : MSP.V4 F) :
    (F ∙ x).map (Matrix.mulVecLin (MSP.mat g)) = F ∙ (MSP.mat g *ᵥ x) := by
  rw [Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply]

theorem mat_mulVec_ne_zero (g : MSP.Sp4 F) {x : MSP.V4 F} (hx : x ≠ 0) :
    MSP.mat g *ᵥ x ≠ 0 := by
  intro h0
  apply hx
  rw [← MSP.mat_inv_mulVec g x, h0, Matrix.mulVec_zero]

theorem eq_sup_of_le {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {x y : MSP.V4 F}
    (hx : x ≠ 0) (hy0 : y ≠ 0) (hxy : (F ∙ x) ≠ (F ∙ y)) (hxl : (F ∙ x) ≤ l)
    (hyl : (F ∙ y) ≤ l) : l = (F ∙ x) ⊔ (F ∙ y) := by
  have hy : y ∉ F ∙ x := by
    intro hyx
    apply hxy
    exact (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem y _).2 hyx)
      (by rw [MSP.isPoint_span hy0, MSP.isPoint_span hx])).symm
  have h2 : Module.finrank F ↥(Submodule.span F {x, y}) = 2 := MSP.finrank_span_pair hx hy
  have hsup : (F ∙ x) ⊔ (F ∙ y) = Submodule.span F {x, y} := by
    rw [Submodule.span_insert]
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hxl hyl) (by rw [hsup, h2, hl.1])).symm

theorem le_qLine_of_cob [Fintype F] [CharP F 2] (hF : Fintype.card F = 2)
    {φ : MSP.Sp4 F → MSP.V4 F} (hφ : ∀ g g', φ (g * g') = φ g + MSP.mat g *ᵥ φ g') {B : F}
    (hB : B ≠ 0) {m₀ : MSP.V4 F} (hform : ∀ g, φ g = S5.cform B m₀ g)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {E : Subgroup (MSP.Sp4 F)}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {v : MSP.V4 F}
    (hv : ∀ g ∈ E, φ g = MSP.mat g *ᵥ v - v) (h4 : 4 ≤ Nat.card ↥(E ⊓ MSP.qLine l)) :
    E ≤ MSP.qLine l := by
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨g₀, J, m', hJQ, hJE, hJ0⟩ := S5Q2.X52.exists_conj_Q₁ hφ hform hl
    (inf_le_right : E ⊓ MSP.qLine l ≤ MSP.qLine l) (fun g hg => hv g hg.1)
  have hcJ : Nat.card J = Nat.card ↥(E ⊓ MSP.qLine l) := by rw [← hJE, MSP.card_map_conj]
  obtain ⟨x, y, hx, hy, -, -, hxy, hJeq⟩ := S5.eq_xPoint_sup_of_cform hF hB hJQ hJ0 (hcJ ▸ h4)
  set x' := MSP.mat g₀ *ᵥ x with hx'
  set y' := MSP.mat g₀ *ᵥ y with hy'
  have hx0 : x' ≠ 0 := mat_mulVec_ne_zero g₀ hx
  have hy0 : y' ≠ 0 := mat_mulVec_ne_zero g₀ hy
  have hE0 : E ⊓ MSP.qLine l = MSP.xPoint (F ∙ x') ⊔ MSP.xPoint (F ∙ y') := by
    rw [← hJE, hJeq, Subgroup.map_sup, MSP.xPoint_map_conj, MSP.xPoint_map_conj, map_span_mat,
      map_span_mat]
  have hxE : MSP.xPoint (F ∙ x') ≤ E ⊓ MSP.qLine l := hE0 ▸ le_sup_left
  have hyE : MSP.xPoint (F ∙ y') ≤ E ⊓ MSP.qLine l := hE0 ▸ le_sup_right
  have hxl : (F ∙ x') ≤ l :=
    (MSP.xPoint_le_qLine_iff (MSP.isPoint_span hx0) hl).1 (hxE.trans inf_le_right)
  have hyl : (F ∙ y') ≤ l :=
    (MSP.xPoint_le_qLine_iff (MSP.isPoint_span hy0) hl).1 (hyE.trans inf_le_right)
  have hxy' : (F ∙ x') ≠ (F ∙ y') := by
    intro heq
    apply hxy
    have := congrArg (fun W => W.map (Matrix.mulVecLin (MSP.mat g₀⁻¹))) heq
    simp only [hx', hy', map_span_mat, MSP.mat_inv_mulVec] at this
    exact this
  have hleq := eq_sup_of_le hl hx0 hy0 hxy' hxl hyl
  have htx : MSP.transv x' 1 ∈ E := (hxE (MSP.transv_mem_xPoint x' 1)).1
  have hty : MSP.transv y' 1 ∈ E := (hyE (MSP.transv_mem_xPoint y' 1)).1
  intro g hg
  exact mem_qLine_of_commute_transv hNF hx0 hy0 hleq (hEc g hg _ htx) (hEc g hg _ hty)

theorem exists_pair_of_isLine {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) :
    ∃ x y : MSP.V4 F, x ≠ 0 ∧ y ≠ 0 ∧ (F ∙ x) ≠ (F ∙ y) ∧ (F ∙ x) ≤ l ∧ (F ∙ y) ≤ l := by
  have hne : l ≠ ⊥ := by
    intro h0
    have := hl.1
    rw [h0, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨x, hxl, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : (F ∙ x) < l := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem x l).2 hxl) fun heq => ?_
    have h1 := MSP.isPoint_span hx
    have h2 := hl.1
    rw [← heq] at h2
    unfold MSP.IsPoint at h1
    omega
  obtain ⟨y, hyl, hyx⟩ := IsConcreteLE.exists_of_lt hlt
  have hy : y ≠ 0 := fun h0 => hyx (h0 ▸ (F ∙ x).zero_mem)
  refine ⟨x, y, hx, hy, fun heq => hyx ?_, (Submodule.span_singleton_le_iff_mem x l).2 hxl,
    (Submodule.span_singleton_le_iff_mem y l).2 hyl⟩
  rw [heq]
  exact Submodule.mem_span_singleton_self y

end Sp

section Thom

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem relIndex_centralizer_Xq_le (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    (Subgroup.centralizer (A : Set G)).relIndex (Xq M) ≤ Nat.card (S5.imSp a A) := by
  have hAT : A ≤ T := hA.1
  have hXT : Xq M ≤ T := (Xq_le_pCoreOf M).trans h.pCore_le
  have h1 := card_le_relIndex_mul_card h.isElemAbelian_Xq hXT hA
  have hQC : A ⊓ pCoreOf 2 M ≤ A ⊓ Subgroup.centralizer (Xq M : Set G) :=
    inf_le_inf_left A (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf M)
  have h2 : (A ⊓ Subgroup.centralizer (Xq M : Set G)).relIndex A ≤
      (pCoreOf 2 M).relIndex A := by
    rw [← Subgroup.inf_relIndex_right (pCoreOf 2 M), inf_comm (pCoreOf 2 M)]
    refine Subgroup.relIndex_le_of_le_left hQC ?_
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) (Xq M)
  have hpos : 0 < Nat.card ↥(Xq M ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  rw [hd.card_imSp h hAT]
  rw [inf_comm] at h3
  have : (Subgroup.centralizer (A : Set G)).relIndex (Xq M) *
      Nat.card ↥(Xq M ⊓ Subgroup.centralizer (A : Set G)) ≤
      (pCoreOf 2 M).relIndex A * Nat.card ↥(Xq M ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [h3]
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  exact Nat.le_of_mul_le_mul_right this hpos

theorem imSp_le_qLine (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L) {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l) (hTl : S5.imSp a T ≤ MSP.stab l) (hlT : MSP.qLine l ≤ S5.imSp a T)
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) : S5.imSp a A ≤ MSP.qLine l := by
  classical
  have hF : Fintype.card F = 2 := by simpa using hd.card_eq
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hAT : A ≤ T := hA.1
  have hAM : A ≤ M := hAT.trans h.le
  set E := S5.imSp a A with hEdef
  have hET : E ≤ S5.imSp a T := S5.imSp_mono a hAT
  have hEl : E ≤ MSP.stab l := hET.trans hTl
  have hT2 : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hE2 : IsPGroup 2 E := hT2.to_le hET
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := hA.2.1.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩
    have hc' : (x : G) * y = y * x := congrArg Subtype.val hc
    exact Subtype.ext (by simpa using hc')
  by_cases hE1 : E = ⊥
  · rw [hE1]
    exact bot_le
  obtain ⟨x, hx, hxN⟩ := S5Q2.X52.exists_mem_xFix_not_mem h hXL hne
  obtain ⟨B, m₀, hB, hform⟩ := S5Q2.X52.exists_cform_of_mem_xFix hd h nv hx hxN
  have hrng : Nat.card (Set.range (S5Q2.X52.phiK h nv hAM)) ≤ Nat.card E := by
    have h1 := S5Q2.X52.relIndex_mul_card_range_le h nv hAM
    have h2 : 0 < (Subgroup.centralizer (A : Set G)).relIndex (Zq M L) := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    calc Nat.card (Set.range (S5Q2.X52.phiK h nv hAM))
        ≤ (Subgroup.centralizer (A : Set G)).relIndex (Zq M L) *
          Nat.card (Set.range (S5Q2.X52.phiK h nv hAM)) := Nat.le_mul_of_pos_left _ h2
      _ ≤ (Subgroup.centralizer (A : Set G)).relIndex (Xq M) := h1
      _ ≤ Nat.card E := relIndex_centralizer_Xq_le hd h hA
  by_cases h2 : 2 ≤ Module.finrank F (MSP.fixSp E)
  ·
    obtain ⟨l', hl', hl'E, hEl'⟩ := MSP.exists_line_of_two_le_finrank_fixSp hE2 hE1 h2
    have hq : MSP.commSp E ≤ MSP.fixSp E :=
      (MSP.commSp_mono hEl').trans (by rw [MSP.commSp_qLine hl']; exact hl'E)
    obtain ⟨-, hshape⟩ := S5Q2.X52.card_le_card_range h nv hAM hd hx hB hform hE2 hq hE1
    exact le_qLine_of_shape hl hEl (hshape hrng)
  ·
    push Not at h2
    have hfix : Nat.card (MSP.fixSp E) ≤ 2 := by
      rw [MSP.card_fixSp, hNF]
      calc 2 ^ Module.finrank F (MSP.fixSp E) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have hoff := S51.card_V4_le_of_isMaxElemAbelian hd h hA
    rw [MSP.card_V4, hNF] at hoff
    have hE8 : 8 ≤ Nat.card E := by nlinarith
    have hT16 : Nat.card (S5.imSp a T) ≤ 16 := Q2G.card_le_sixteen hNF hT2
    have hq8 : Nat.card (MSP.qLine l) = 8 := by rw [MSP.card_qLine hl, hNF]; norm_num
    have hidxT : (MSP.qLine l).relIndex (S5.imSp a T) ≤ 2 := by
      have h1 := Subgroup.relIndex_mul_card (MSP.qLine l) (S5.imSp a T)
      rw [inf_eq_left.2 hlT, hq8] at h1
      have h2 : (MSP.qLine l).relIndex (S5.imSp a T) * 8 ≤ 16 := by rw [h1]; exact hT16
      omega
    have hidx : (MSP.qLine l).relIndex E ≤ 2 :=
      (Subgroup.relIndex_le_of_le_right hET Subgroup.index_ne_zero_of_finite).trans hidxT
    have hE0 : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ MSP.qLine l) := by
      have h1 := Subgroup.relIndex_mul_card (MSP.qLine l) E
      rw [inf_comm] at h1
      rw [← h1]
      exact Nat.mul_le_mul_right _ hidx
    have h4 : 4 ≤ Nat.card ↥(E ⊓ MSP.qLine l) := by
      have hE8' : 8 ≤ Nat.card E := hE8
      omega
    by_cases hcob : ∃ v : MSP.V4 F, ∀ g ∈ E, S5.cocSp hd nv x g = MSP.mat g *ᵥ v - v
    · obtain ⟨v, hv⟩ := hcob
      exact le_qLine_of_cob hF (S5.cocSp_mul hd h nv hx.1 hx.2) hB hform hl hEc hv h4
    · push Not at hcob
      have h32 := S5Q2.X52.two_mul_card_le_card_fixSp_mul_card_range h nv hAM hx fun v => by
        obtain ⟨g, hg, hgv⟩ := hcob v
        obtain ⟨m, hm, hmM, rfl⟩ := S5.mem_imSp.1 hg
        rw [S5.cocSp_a hd h nv hx.1 hx.2 hmM] at hgv
        exact ⟨⟨m, hm⟩, hgv⟩
      rw [MSP.card_V4, hNF] at h32
      have hE16 : 16 ≤ Nat.card E := by nlinarith
      have hQE : MSP.qLine l ≤ E := by
        have hc : Nat.card (MSP.qLine l) ≤ Nat.card ↥(E ⊓ MSP.qLine l) := by omega
        have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right : E ⊓ MSP.qLine l ≤ _) hc
        rw [← heq]
        exact inf_le_left
      obtain ⟨y₁, y₂, hy₁, hy₂, hne₁₂, hy₁l, hy₂l⟩ := exists_pair_of_isLine hl
      have hleq := eq_sup_of_le hl hy₁ hy₂ hne₁₂ hy₁l hy₂l
      have ht₁ : MSP.transv y₁ 1 ∈ E :=
        hQE (MSP.xPoint_le_qLine hl hy₁l (MSP.transv_mem_xPoint y₁ 1))
      have ht₂ : MSP.transv y₂ 1 ∈ E :=
        hQE (MSP.xPoint_le_qLine hl hy₂l (MSP.transv_mem_xPoint y₂ 1))
      intro g hg
      exact mem_qLine_of_commute_transv hNF hy₁ hy₂ hleq (hEc g hg _ ht₁) (hEc g hg _ ht₂)

theorem thompsonJ_le_liftT_qLine (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L) {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l) (hTl : S5.imSp a T ≤ MSP.stab l) (hlT : MSP.qLine l ≤ S5.imSp a T) :
    thompsonJ T ≤ S5.liftT T a (MSP.qLine l) := by
  refine iSup₂_le fun A hA => ?_
  have hAT : A ≤ T := hA.1
  have hle := imSp_le_qLine h hd hXL hne hl hTl hlT hA
  intro t ht
  exact S5.mem_liftT.2 ⟨hAT ht, hAT.trans h.le ht,
    hle (S5.mem_imSp.2 ⟨t, ht, hAT.trans h.le ht, rfl⟩)⟩

theorem baum_le_liftT_qLine (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L) {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l) (hTl : S5.imSp a T ≤ MSP.stab l) (hlT : MSP.qLine l ≤ S5.imSp a T) :
    baum T ≤ S5.liftT T a (MSP.qLine l) := by
  classical
  have := hd.charP
  have hl' := (S5.sp4Lift G M T L h 1 F _ _ a hd).2.2
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hthom := thompsonJ_le_liftT_qLine h hd hXL hne hl hTl hlT
  have hJM : thompsonJ T ≤ M := (C1GN.thompsonJ_le T).trans h.le
  have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans (h.Z0q_le_pCoreOf.trans h.pCore_le)
  have hCU : Uq M T L ⊓ Subgroup.centralizer (thompsonJ T : Set G) ≤
      omegaOneCenterOf (thompsonJ T) := by
    rw [(omegaOne_centralizer_thompsonJ T).2]
    intro u hu
    simp only [Subgroup.mem_iInf]
    intro A hA
    rw [eq_omegaOneOf_centralizer hA]
    refine Subgroup.subset_closure ⟨⟨hUT hu.1, ?_⟩, h.isElemAbelian_Uq.2 u hu.1⟩
    exact Subgroup.centralizer_le (B6.le_thompsonJ hA) hu.2
  refine (inf_le_inf_left T (Subgroup.centralizer_le hCU)).trans ?_
  intro t ⟨htT, htC⟩
  have htM : t ∈ M := h.le htT
  refine S5.mem_liftT.2 ⟨htT, htM, ?_⟩
  have hlfix : l ≤ MSP.fixSp (S5.imSp a (thompsonJ T)) := by
    rw [← MSP.fixSp_qLine hl]
    refine MSP.fixSp_antitone ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (S5.mem_liftT.1 (hthom (Subgroup.mem_subgroupOf.1 hj))).2.2
  intro w hw
  obtain ⟨u, rfl⟩ := nv.surj (Multiplicative.ofAdd w)
  have huJ : (u : G) ∈ Subgroup.centralizer (thompsonJ T : Set G) := by
    rw [nv.mem_centralizer_iff_vec_mem_fixSp hd.nat.1 hl' hJM u]
    exact hlfix hw
  have hcomm : ((⟨t, htM⟩ : ↥M) : G) * (u : G) = (u : G) * ((⟨t, htM⟩ : ↥M) : G) := by
    have := Subgroup.mem_centralizer_iff.1 htC (u : G) ⟨u.2, huJ⟩
    exact this.symm
  exact nv.mat_mulVec_vec_of_commute ⟨t, htM⟩ u hcomm

end Thom

end CFSG.Quasithin.MS93.S5D
