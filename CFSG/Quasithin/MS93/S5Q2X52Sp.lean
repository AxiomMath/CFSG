module

public import CFSG.Quasithin.MS93.S5A53
public import CFSG.Quasithin.MS93.S5Q2Par
public import CFSG.Quasithin.MS93.S33LamQ

public section

namespace CFSG.Quasithin.MS93.S5Q2.X52

open CFSG.Assembly.LowTwoRank MSP
open scoped Matrix

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] [CharP F 2] in
theorem card_eq_four_of_isLine [Finite F] (hF : Nat.card F = 2) {l : Submodule F (V4 F)}
    (hl : IsLine l) : Nat.card l = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := F), hl.1, hF]
  norm_num

theorem quad_shape (hF : Nat.card F = 2) {E : Subgroup (Sp4 F)} (hE2 : IsPGroup 2 E)
    (hq : commSp E ≤ fixSp E) (hE1 : E ≠ ⊥) :
    (IsLine (fixSp E) ∧ E = qLine (fixSp E) ⊓ commutator (Sp4 F)) ∨
      (IsLine (fixSp E) ∧ E = qLine (fixSp E)) ∨
      (E ≤ commutator (Sp4 F) ∧ 2 * (Nat.card E * Nat.card (fixSp E)) ≤ Nat.card (V4 F)) ∨
      (¬ E ≤ commutator (Sp4 F) ∧ Nat.card E * Nat.card (fixSp E) ≤ Nat.card (V4 F)) := by
  have hV : Nat.card (V4 F) = 16 := by rw [card_V4, hF]; norm_num
  have hfix : Nat.card (fixSp E) = 2 ^ Module.finrank F (fixSp E) := by rw [card_fixSp, hF]
  have hd4 : Module.finrank F (fixSp E) ≤ 4 := (Submodule.finrank_le _).trans (by simp)
  have hE1' : Nat.card E ≠ 1 := fun h1 => hE1 (Subgroup.eq_bot_of_card_eq E h1)
  by_cases hd : Module.finrank F (fixSp E) ≤ 2
  · obtain ⟨hl, hEl, -⟩ := S33.line_of_quadratic hE2 hq hd
    have hf2 : Module.finrank F (fixSp E) = 2 := hl.1
    have hfix4 : Nat.card (fixSp E) = 4 := by rw [hfix, hf2]; norm_num
    have hdvd : Nat.card E ∣ 8 := by
      have := Subgroup.card_dvd_of_le hEl
      rwa [card_qLine hl, hF] at this
    have h8 : Nat.card E ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at h8
    simp only [Finset.mem_insert, Finset.mem_singleton] at h8
    rcases h8 with h1 | h2 | h4 | h8
    · exact absurd h1 hE1'
    · by_cases hEc : E ≤ commutator (Sp4 F)
      · exact Or.inr (Or.inr (Or.inl ⟨hEc, by rw [h2, hfix4, hV]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hEc, by rw [h2, hfix4, hV]; norm_num⟩))
    · by_cases hEc : E ≤ commutator (Sp4 F)
      · exact Or.inl ⟨hl, eq_qLine_inf_commutator hF hl hEl hEc h4.ge⟩
      · exact Or.inr (Or.inr (Or.inr ⟨hEc, by rw [h4, hfix4, hV]⟩))
    · refine Or.inr (Or.inl ⟨hl, Subgroup.eq_of_le_of_card_ge hEl ?_⟩)
      rw [card_qLine hl, hF, h8]
      norm_num
  · push Not at hd
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
    have hcard : Nat.card E ≤ 2 := by
      have := Subgroup.card_le_of_le hEx
      rwa [card_xPoint hp, hF] at this
    refine Or.inr (Or.inr (Or.inr ⟨fun hEc => ?_, by rw [hfix, hd3, hV]; nlinarith⟩))
    obtain ⟨v, hv, hpv⟩ := exists_eq_span_of_isPoint hp
    obtain ⟨⟨e, heE⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
    have hex := hEx heE
    rw [hpv] at hex
    rcases S33.eq_one_or_eq_transv hF hv hex with h1 | ht
    · exact he1 (Subtype.ext h1)
    · exact transv_not_mem_commutator_of_card_two hF hv 1 one_ne_zero (ht ▸ hEc heE)

omit [Fintype F] [CharP F 2] in
theorem qLine_not_le_qPoint [Finite F] {l p : Submodule F (V4 F)} (hl : IsLine l)
    (hp : IsPoint p) : ¬ qLine l ≤ qPoint p := by
  intro hle
  have heq : qLine l = qPoint p :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_qLine hl, card_qPoint hp])
  have hq : commSp (qPoint p) ≤ fixSp (qPoint p) := by
    rw [← heq, fixSp_qLine hl]
    exact commSp_qLine_le hl
  obtain ⟨g, rfl⟩ := exists_map_pt₀_eq hp
  rw [qPoint_map_eq, commSp_map_conj, fixSp_map_conj] at hq
  exact not_commSp_Q₂_le_fixSp
    ((Submodule.map_le_map_iff_of_injective (mulVec_mat_injective g) _ _).1 hq)

omit [Fintype F] [CharP F 2] in
theorem qLine_inf_commutator_not_le_qPoint [Finite F] (hF : Nat.card F = 2)
    {l p : Submodule F (V4 F)} (hl : IsLine l) (hp : IsPoint p) :
    ¬ qLine l ⊓ commutator (Sp4 F) ≤ qPoint p := by
  intro hle
  set E := qLine l ⊓ commutator (Sp4 F) with hE
  have hcard : Nat.card E = 4 := card_qLine_inf_commutator hF hl
  have hlE : l ≤ fixSp E := le_fixer_iff.1 inf_le_left
  have hd : Module.finrank F (fixSp E) ≤ 2 := by
    by_contra hd
    push Not at hd
    have hd3 : Module.finrank F (fixSp E) = 3 := by
      by_contra h3
      have h4 : Module.finrank F (fixSp E) = 4 := by
        have := (Submodule.finrank_le (fixSp E)).trans (by simp : Module.finrank F (V4 F) ≤ 4)
        omega
      have htop : fixSp E = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h4)
      have hbot := fixSp_eq_top_iff.1 htop
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    have hpE : IsPoint (perp (fixSp E)) := by
      have := finrank_perp (fixSp E)
      unfold IsPoint
      omega
    have hEx : E ≤ xPoint (perp (fixSp E)) := by
      show E ≤ fixer (perp (perp (fixSp E)))
      rw [perp_perp]
      exact le_fixer_iff.2 le_rfl
    have := Subgroup.card_le_of_le hEx
    rw [card_xPoint hpE, hF, hcard] at this
    omega
  have hfix : fixSp E = l :=
    (Submodule.eq_of_le_of_finrank_le hlE (by rw [hl.1]; exact hd)).symm
  have hpl : p ≤ l := by
    rw [← hfix]
    exact le_fixer_iff.1 (hle.trans (qPoint_le_fixer p))
  have hX : xPoint p ≤ E := by
    by_contra hX
    have hne : Nat.card ↥(E ⊔ xPoint p) ≠ Nat.card E := fun he =>
      hX ((Subgroup.eq_of_le_of_card_ge le_sup_left he.le) ▸ le_sup_right)
    have hdvd := Subgroup.card_dvd_of_le (le_sup_left : E ≤ E ⊔ xPoint p)
    have hpos : 0 < Nat.card ↥(E ⊔ xPoint p) := Nat.card_pos
    have h8 : 8 ≤ Nat.card ↥(E ⊔ xPoint p) := by
      rw [hcard] at hdvd hne
      obtain ⟨c, hc⟩ := hdvd
      rcases c with _ | _ | c
      · omega
      · omega
      · omega
    have hsub : E ⊔ xPoint p ≤ qLine l ⊓ qPoint p :=
      sup_le (le_inf inf_le_left hle) (le_inf (xPoint_le_qLine hl hpl) (xPoint_le_qPoint hp))
    have hc8 : Nat.card (qLine l) ≤ Nat.card ↥(qLine l ⊓ qPoint p) := by
      rw [card_qLine hl, hF]
      exact h8.trans (Subgroup.card_le_of_le hsub)
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : qLine l ⊓ qPoint p ≤ qLine l) hc8
    exact qLine_not_le_qPoint hl hp (heq ▸ inf_le_right)
  exact xPoint_not_le_commutator hF hp (hX.trans inf_le_right)

omit [Fintype F] [CharP F 2] in
theorem cocycle_sub_cob {φ : Sp4 F → V4 F} (hφ : ∀ g g', φ (g * g') = φ g + mat g *ᵥ φ g')
    (v : V4 F) (g g' : Sp4 F) :
    φ (g * g') - (mat (g * g') *ᵥ v - v) =
      (φ g - (mat g *ᵥ v - v)) + mat g *ᵥ (φ g' - (mat g' *ᵥ v - v)) := by
  rw [hφ, mat_mul_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub]
  abel

theorem cform_sub_cob (B : F) (m₀ v : V4 F) (g : Sp4 F) :
    S5.cform B m₀ g - (mat g *ᵥ v - v) = S5.cform B (m₀ - v) g := by
  unfold S5.cform
  rw [Matrix.mulVec_sub]
  abel

theorem exists_conj_Q₁ {φ : Sp4 F → V4 F} (hφ : ∀ g g', φ (g * g') = φ g + mat g *ᵥ φ g')
    {B : F} {m₀ : V4 F} (hform : ∀ g, φ g = S5.cform B m₀ g) {l : Submodule F (V4 F)}
    (hl : IsLine l) {E : Subgroup (Sp4 F)} (hEl : E ≤ qLine l) {v : V4 F}
    (hv : ∀ g ∈ E, φ g = mat g *ᵥ v - v) :
    ∃ (g₀ : Sp4 F) (J : Subgroup (Sp4 F)) (m' : V4 F), J ≤ Q₁ F ∧
      J.map (MulAut.conj g₀).toMonoidHom = E ∧ ∀ j ∈ J, S5.cform B m' j = 0 := by
  obtain ⟨g₀, rfl⟩ := exists_map_ln₀_eq hl
  rw [qLine_map_eq] at hEl
  set J := E.map (MulAut.conj g₀⁻¹).toMonoidHom with hJ
  have hJE : J.map (MulAut.conj g₀).toMonoidHom = E := by
    ext x
    rw [hJ, map_conj_map_conj, mul_inv_cancel, mem_map_conj]
    simp
  have hJQ : J ≤ Q₁ F := by
    rintro _ ⟨z, hz, rfl⟩
    have := hEl hz
    rw [mem_map_conj] at this
    simpa using this
  set ψ : Sp4 F → V4 F := fun g => φ g - (mat g *ᵥ v - v) with hψ
  have hψc : ∀ g g', ψ (g * g') = ψ g + mat g *ᵥ ψ g' := cocycle_sub_cob hφ v
  have hψf : ∀ g, ψ g = S5.cform B (m₀ - v) g := fun g => by
    rw [hψ]
    dsimp only
    rw [hform, cform_sub_cob]
  have hψ0 : ∀ j ∈ J.map (MulAut.conj g₀).toMonoidHom, ψ j = 0 := by
    rw [hJE]
    intro j hj
    rw [hψ]
    dsimp only
    rw [hv j hj, sub_self]
  exact ⟨g₀, J, _, hJQ, hJE, S5.cform_vanish_of_conj hψc hψf hψ0⟩

theorem not_cob_of_shape (hF : Fintype.card F = 2) {φ : Sp4 F → V4 F}
    (hφ : ∀ g g', φ (g * g') = φ g + mat g *ᵥ φ g') {B : F} (hB : B ≠ 0) {m₀ : V4 F}
    (hform : ∀ g, φ g = S5.cform B m₀ g) {l : Submodule F (V4 F)} (hl : IsLine l)
    {E : Subgroup (Sp4 F)} (hE : E = qLine l ⊓ commutator (Sp4 F) ∨ E = qLine l) (v : V4 F) :
    ∃ g ∈ E, φ g ≠ mat g *ᵥ v - v := by
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  by_contra hcon
  push Not at hcon
  have hEl : E ≤ qLine l := by rcases hE with rfl | rfl; exacts [inf_le_left, le_rfl]
  obtain ⟨g₀, J, m', hJQ, hJE, hJ0⟩ := exists_conj_Q₁ hφ hform hl hEl hcon
  have hcJ : Nat.card J = Nat.card E := by rw [← hJE, card_map_conj]
  rcases hE with rfl | rfl
  · have h4 : 4 ≤ Nat.card J := by rw [hcJ, card_qLine_inf_commutator hNF hl]
    obtain ⟨x, y, hx, -, -, -, -, hJeq⟩ := S5.eq_xPoint_sup_of_cform hF hB hJQ hJ0 h4
    have htJ : transv x 1 ∈ J := by
      rw [hJeq]
      exact Subgroup.mem_sup_left (transv_mem_xPoint x 1)
    have hc : g₀ * transv x 1 * g₀⁻¹ ∈ commutator (Sp4 F) := by
      have : (MulAut.conj g₀).toMonoidHom (transv x 1) ∈ qLine l ⊓ commutator (Sp4 F) := by
        rw [← hJE]
        exact Subgroup.mem_map_of_mem _ htJ
      exact this.2
    have hc' : transv x 1 ∈ commutator (Sp4 F) := by
      have := (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hc g₀⁻¹
      simpa [mul_assoc] using this
    exact transv_not_mem_commutator_of_card_two hNF hx 1 one_ne_zero hc'
  · have hle := S5.card_le_of_cform_Q₁ hB (S := (J : Set (Sp4 F))) hJQ hJ0
    have hc : Nat.card (J : Set (Sp4 F)) = Nat.card J := rfl
    rw [hc, hcJ, card_qLine hl, hNF] at hle
    norm_num at hle

end CFSG.Quasithin.MS93.S5Q2.X52
