module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BF
public import CFSG.Quasithin.Vol2.Ch3E213MP6CG
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt antiUnipotentCenter
  minorAut)
open CFSG.Quasithin.SteinbergBS (rootLong)
open CFSG.QuasithinUnique.Setup.X7b (uElt_zero_eq_one)

variable {k : Type} [Field k] [CharP k 2] [Finite k]

section Hyp

variable {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k) (hl : W ⊓ rootLong k = ⊥)
  {h : antiSp k} (hh : IsUpper h) {r : ℕ}
  (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W)
include hWZ hl hh hσ

theorem nonAlt_of_mem : ∀ w ∈ W, w ≠ 1 → w * w = 1 ∧ ∃ x, spBil x (natAct w x) ≠ 0 := by
  intro w hw hw1
  obtain ⟨b, c, rfl⟩ := hWZ hw
  refine ⟨uElt_center_mul_self b c, exists_spBil_uElt_center_ne_zero ?_⟩
  rintro rfl
  have hb := eq_zero_of_short_mem hl hh hσ hw
  subst hb
  exact hw1 uElt_zero_eq_one

theorem nonAlt_of_mem_conj (g : antiSp k) :
    ∀ w ∈ W.map (MulAut.conj g).toMonoidHom, w ≠ 1 → w * w = 1 ∧ ∃ x, spBil x (natAct w x) ≠ 0 := by
  rintro _ ⟨w, hw, rfl⟩ hw1
  have hw1' : w ≠ 1 := fun h1 => hw1 (by rw [h1, map_one])
  obtain ⟨h1, x, hx⟩ := nonAlt_of_mem hWZ hl hh hσ w hw hw1'
  refine ⟨?_, natAct g x, ?_⟩
  · change g * w * g⁻¹ * (g * w * g⁻¹) = 1
    calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · change spBil (natAct g x) (natAct (g * w * g⁻¹) (natAct g x)) ≠ 0
    rwa [spBil_natAct_conj, natAct_inv_natAct]

theorem exists_c2_mem (hsp : SpansCenter W) : ∃ β γ : k, β ≠ 0 ∧ γ ≠ 0 ∧ uElt 0 β γ 0 ∈ W := by
  obtain ⟨b, c, -, -, hz, -, hb, -⟩ := exists_indep hWZ hsp
  refine ⟨b, c, hb, fun hc => hb ?_, hz⟩
  subst hc
  exact eq_zero_of_short_mem hl hh hσ hz

end Hyp

theorem exists_member_or_suzuki (hG41 : FactSp4TransvW) (hCTwo : FactSp4CTwo) {n : ℕ}
    (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {W : Subgroup (antiSp k)}
    (hWZ : W ≤ antiUnipotentCenter k) (hl : W ⊓ rootLong k = ⊥) (hsp : SpansCenter W)
    {h : antiSp k} (hh : IsUpper h) {r : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W) :
    (∃ (F₀ : Subfield k) (c g : antiSp k), IsUpper c ∧
        g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ∧
        W ⊔ W.map (MulAut.conj g).toMonoidHom = (subfieldSp F₀).map (MulAut.conj c).toMonoidHom) ∨
      ∃ (F₀ : Subfield k) (a : ℕ), 1 ≤ a ∧ Nat.card F₀ = 2 ^ (2 * a + 1) ∧
        ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom := by
  obtain ⟨β, γ, hβ, hγ, hz⟩ := exists_c2_mem hWZ hl hh hσ hsp
  have hWZ' := map_minorAut_le_center hWZ
  have hl' := map_minorAut_inf_rootLong hWZ hl hh hσ
  have hsp' := spansCenter_map_minorAut hWZ hsp hh hσ
  have hh' := isUpper_minorAut hh
  have hσ' := minorAut_inv_map hσ
  suffices key : ∀ N : ℕ, ∀ (F₀ : Subfield k) (c : antiSp k), IsUpper c →
      W ≤ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom →
      Nat.card ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) ≤ N →
      (∃ (F₀ : Subfield k) (c g : antiSp k), IsUpper c ∧
          g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ∧
          W ⊔ W.map (MulAut.conj g).toMonoidHom =
            (subfieldSp F₀).map (MulAut.conj c).toMonoidHom) ∨
        ∃ (F₀ : Subfield k) (a : ℕ), 1 ≤ a ∧ Nat.card F₀ = 2 ^ (2 * a + 1) ∧
          ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom by
    refine key _ ⊤ 1 isUpper_one ?_ le_rfl
    rw [map_conj_one, subfieldSp_top]
    exact le_top
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro F₀ c hc hW hcard
    set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hY
    set g := c * wLong * c⁻¹ with hg
    have hgY : g ∈ Y := ⟨wLong, wLong_mem_subfieldSp F₀, rfl⟩
    set I := W ⊔ W.map (MulAut.conj g).toMonoidHom with hI
    have hIY : I ≤ Y := by
      refine sup_le hW ?_
      rintro _ ⟨w, hw, rfl⟩
      exact Y.mul_mem (Y.mul_mem hgY (hW hw)) (Y.inv_mem hgY)
    have hopp : IsOppStd g := isOppStd_conj_of_isUpper hc
    have hirr : IsIrreducibleSp4 I := irrStatement_holds k W g hWZ hsp hopp
    have step : ∀ (F₀' : Subfield k) (c' : antiSp k),
        I = (subfieldSp F₀').map (MulAut.conj c').toMonoidHom →
        (∃ (F₀ : Subfield k) (c g : antiSp k), IsUpper c ∧
            g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ∧
            W ⊔ W.map (MulAut.conj g).toMonoidHom =
              (subfieldSp F₀).map (MulAut.conj c).toMonoidHom) ∨
          ∃ (F₀ : Subfield k) (a : ℕ), 1 ≤ a ∧ Nat.card F₀ = 2 ^ (2 * a + 1) ∧
            ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom := by
      intro F₀' c' hIeq
      have hzI : uElt 0 β γ 0 ∈ (subfieldSp F₀').map (MulAut.conj c').toMonoidHom :=
        hIeq ▸ (le_sup_left : W ≤ I) hz
      obtain ⟨c'', hc'', hc''eq⟩ := exists_isUpper_conj_c2 hβ hγ hzI
      by_cases hEq : I = Y
      · exact Or.inl ⟨F₀, c, g, hc, hgY, hEq⟩
      · have hlt : Nat.card I < Nat.card Y := Subgroup.card_lt_of_lt (lt_of_le_of_ne hIY hEq)
        refine ih (Nat.card I) (lt_of_lt_of_le hlt hcard) F₀' c'' hc'' ?_ ?_
        · rw [hc''eq, ← hIeq]
          exact le_sup_left
        · rw [hc''eq, ← hIeq]
    by_cases htr : ∃ x ∈ I, IsTransvection x
    · obtain ⟨x, hx, hxt⟩ := htr
      rcases hG41 k n hk I hirr ⟨x, hx, hxt⟩ with h1 | h2 | h3
      · obtain ⟨F₀', c', hIeq⟩ := h1
        exact step F₀' c' hIeq
      · exact absurd h2 (not_g41Orth_of_inv hWZ hl hsp hh hσ le_sup_left)
      · exact absurd h3 (not_g41Dec_of_nonAlt hirr (nonAlt_of_mem hWZ hl hh hσ)
          (nonAlt_of_mem_conj hWZ hl hh hσ g))
    by_cases htr' : ∃ x ∈ I, IsTransvection (minorAut k x)
    ·
      obtain ⟨x, hx, hxt⟩ := htr'
      have hopp' : IsOppStd (minorAut k g) := by
        rw [hg, map_mul, map_mul, map_inv, minorAut_wLong]
        exact isOppStd_conj_of_isUpper (isUpper_minorAut hc)
      have hρI := map_minorAut_sup_conj W g
      rw [← hI] at hρI
      have hirr' : IsIrreducibleSp4 (I.map (minorAut k).toMonoidHom) := by
        rw [hρI]
        exact irrStatement_holds k _ _ hWZ' hsp' hopp'
      rcases hG41 k n hk _ hirr' ⟨minorAut k x, ⟨x, hx, rfl⟩, hxt⟩ with h1 | h2 | h3
      · obtain ⟨F₀', c₁, hρeq⟩ := h1
        refine step F₀' ((minorAut k).symm c₁) ?_
        rw [← map_symm_minorAut_conj_subfieldSp, ← hρeq, Subgroup.map_map]
        convert (Subgroup.map_id I).symm
        ext y
        simp
      · rw [hρI] at h2
        exact absurd h2 (not_g41Orth_of_inv hWZ' hl' hsp' hh' hσ' le_sup_left)
      · rw [hρI] at h3 hirr'
        exact absurd h3 (not_g41Dec_of_nonAlt hirr' (nonAlt_of_mem hWZ' hl' hh' hσ')
          (nonAlt_of_mem_conj hWZ' hl' hh' hσ' _))
    · push Not at htr htr'
      exact Or.inr (hCTwo k n hn hk W hWZ hl hsp
        ⟨h, mem_normalizer_of_isUpper hh, 2 * r + 1, odd_two_mul_add_one r, hσ⟩ g hopp htr htr')

end CFSG.Quasithin.Ch3E213M.P6B
