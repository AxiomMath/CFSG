module

public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.OrthogonalInvolutions QuadraticMap Matrix

section Stab

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

def SingPerp (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) : Type :=
  {e : Fin d → K // polar Q w e = 0 ∧ Q e = 0}

def Perp (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) : Type :=
  {x : Fin d → K // polar Q w x = 0}

theorem polar_self_zero (x : Fin d → K) : polar Q x x = 0 := polar_self_eq_zero Q x

omit [CharP K 2] in
theorem map_add_smul (e w : Fin d → K) (t : K) :
    Q (e + t • w) = Q e + t * t * Q w + t * polar Q e w := by
  rw [map_add_eq, QuadraticMap.map_smul, polar_smul_right]
  simp only [smul_eq_mul]

noncomputable def decompEquiv [Finite K] (w : Fin d → K) (hw : Q w = 1) :
    SingPerp Q w × K ≃ Perp Q w :=
  Equiv.ofBijective
    (fun p => ⟨p.1.1 + p.2 • w, by
      rw [polar_add_right, p.1.2.1, polar_smul_right, polar_self_zero]
      simp⟩)
    ⟨by
      rintro ⟨⟨e, he1, he2⟩, t⟩ ⟨⟨e', he1', he2'⟩, t'⟩ h
      have h' : e + t • w = e' + t' • w := congrArg Subtype.val h
      have hh : e' = e + (t + t') • w := by
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        have : e' = e + t • w - t' • w := by rw [h']; abel
        rw [this, add_smul, sub_eq_add_neg, add_assoc, ← neg_smul, CharTwo.neg_eq]
      have hq := map_add_smul (Q := Q) e w (t + t')
      rw [← hh, he2', he2, hw, polar_comm, he1] at hq
      have : (t + t') * (t + t') = 0 := by linear_combination -hq
      have ht : t + t' = 0 := mul_self_eq_zero.1 this
      have htt : t = t' := by
        have : t = -t' := eq_neg_of_add_eq_zero_left ht
        rw [this, CharTwo.neg_eq]
      subst htt
      have hee : e = e' := by
        rw [hh, ht, zero_smul, add_zero]
      subst hee
      rfl, by
      rintro ⟨x, hx⟩
      obtain ⟨s, hs⟩ : ∃ s : K, s * s = Q x :=
        let _ : Fintype K := Fintype.ofFinite K
        let ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q x)
        ⟨s, hs.symm⟩
      refine ⟨⟨⟨x + s • w, ?_, ?_⟩, s⟩, ?_⟩
      · rw [polar_add_right, hx, polar_smul_right, polar_self_zero]
        simp
      · have h := map_add_smul (Q := Q) x w s
        rw [hw, polar_comm, hx, mul_zero, add_zero, mul_one, hs] at h
        rw [h]
        exact CharTwo.add_self_eq_zero _
      · apply Subtype.ext
        change x + s • w + s • w = x
        rw [add_assoc, ← two_smul K, CharTwo.two_eq_zero, zero_smul, add_zero]⟩

section Count

variable [Finite K]

omit [CharP K 2] [Finite K] in
theorem card_perp (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw : w ≠ 0) :
    Nat.card (Perp Q w) = Nat.card K ^ (d - 1) := by
  let φ : (Fin d → K) →ₗ[K] K := Q.polarBilin w
  obtain ⟨y, hy⟩ : ∃ y, polar Q w y ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hw (hnd.1 w fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hall y
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨(c / polar Q w y) • y, ?_⟩
    change polar Q w ((c / polar Q w y) • y) = c
    rw [polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hy]
  have hrange : Module.finrank K φ.range = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self]
  have hker : Module.finrank K φ.ker = d - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, Module.finrank_fin_fun] at h
    omega
  have hcard : Nat.card φ.ker = Nat.card K ^ (d - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := φ.ker), hker]
  rw [← hcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [LinearMap.mem_ker]
    change polar Q w x = 0 ↔ Q.polarBilin w x = 0
    rw [QuadraticMap.polarBilin_apply_apply])

theorem card_singPerp (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw : Q w = 1)
    (hd : 2 ≤ d) : Nat.card (SingPerp Q w) = Nat.card K ^ (d - 2) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hw
    exact zero_ne_one hw
  have h1 := Nat.card_congr (decompEquiv w hw)
  rw [Nat.card_prod, card_perp hnd hw0] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h2 : Nat.card K ^ (d - 1) = Nat.card K ^ (d - 2) * Nat.card K := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem two_dvd_card : 2 ∣ Nat.card K := by
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.ne_zero

end Count

section Fixed

variable [Finite K]

theorem exists_fixed_singular (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw : Q w = 1)
    (hd : 3 ≤ d) (R : Subgroup (GL (Fin d) K)) (hR2 : IsPGroup 2 R)
    (hRO : R ≤ matrixIsometries Q) (hRw : ∀ r ∈ R, r.val *ᵥ w = w) :
    ∃ e : Fin d → K, e ≠ 0 ∧ polar Q w e = 0 ∧ Q e = 0 ∧ ∀ r ∈ R, r.val *ᵥ e = e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction R (SingPerp Q w) :=
    { smul := fun r e => ⟨((r : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ e.1, by
        have h1 := polar_mulVec_of_mem (hRO r.2) w e.1
        rw [hRw r r.2] at h1
        refine ⟨?_, ?_⟩
        · rw [h1]
          exact e.2.1
        · rw [map_mulVec_of_mem (hRO r.2)]
          exact e.2.2⟩
      one_smul := fun e => Subtype.ext (by
        change (((1 : R) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ e.1 = e.1
        simp)
      mul_smul := fun g h e => Subtype.ext (by
        change (((g * h : R) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ e.1 =
          ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
            (((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ e.1)
        simp [Matrix.mulVec_mulVec]) }
  have hfin : Finite (SingPerp Q w) := inferInstanceAs (Finite {e : Fin d → K // _})
  have hmod := hR2.card_modEq_card_fixedPoints (SingPerp Q w)
  have heven : 2 ∣ Nat.card (SingPerp Q w) := by
    rw [card_singPerp hnd hw (by omega)]
    exact dvd_pow two_dvd_card (by omega)
  by_contra hcon
  push Not at hcon
  have hone : Nat.card (MulAction.fixedPoints R (SingPerp Q w)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨0, by simp [polar_zero_right], QuadraticMap.map_zero Q⟩, ?_⟩⟩⟩
    · have key : ∀ z : MulAction.fixedPoints R (SingPerp Q w), z.1.1 = 0 := by
        intro z
        by_contra hz
        obtain ⟨⟨e, he1, he2⟩, hzf⟩ := z
        obtain ⟨r, hr, hne⟩ := hcon e hz he1 he2
        exact hne (congrArg Subtype.val (hzf ⟨r, hr⟩))
      exact Subtype.ext (Subtype.ext ((key a).trans (key b).symm))
    · intro r
      apply Subtype.ext
      change ((r : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (0 : Fin d → K) = 0
      simp
  rw [hone] at hmod
  obtain ⟨k, hk⟩ := heven
  unfold Nat.ModEq at hmod
  omega

end Fixed

section Transitive

variable [Finite K]

theorem exists_stab_map (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {w e e' : Fin d → K} (hw : Q w = 1) (he1 : polar Q w e = 0) (he2 : Q e = 0)
    (he'1 : polar Q w e' = 0) (he'2 : Q e' = 0) (he0 : e ≠ 0) (he'0 : e' ≠ 0) :
    ∃ γ ∈ matrixDerived Q, γ.val *ᵥ w = w ∧ γ.val *ᵥ e = e' := by
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hli : ∀ {x : Fin d → K}, polar Q w x = 0 → Q x = 0 → x ≠ 0 →
      LinearIndependent K ![x, w] := by
    intro x hx1 hx2 hx0
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : Q (s • x + t • w) = 0 := by rw [hst, QuadraticMap.map_zero]
    rw [map_add_smul, QuadraticMap.map_smul, hx2, polar_smul_left, polar_comm, hx1, hw] at h0
    have ht : t * t = 0 := by
      simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at h0
      linear_combination h0
    have ht0 : t = 0 := mul_self_eq_zero.1 ht
    subst ht0
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hx0, rfl⟩
  have hew : polar Q e w = 0 := by rw [polar_comm]; exact he1
  have hew' : polar Q e' w = 0 := by rw [polar_comm]; exact he'1
  obtain ⟨g, hgO, hg⟩ := exists_mem_orthogonalGroup_apply_eq hnd (k := 2) ![e, w] ![e', w]
    (hli he1 he2 he0) (hli he'1 he'2 he'0)
    (Fin.forall_fin_two.2 ⟨by
      change Q e' = Q e
      rw [he2, he'2], rfl⟩)
    (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨by
      change polar Q e' e' = polar Q e e
      rw [polar_self_zero, polar_self_zero], by
      change polar Q e' w = polar Q e w
      rw [hew', hew]⟩, Fin.forall_fin_two.2 ⟨by
      change polar Q w e' = polar Q w e
      rw [he'1, he1], rfl⟩⟩)
  let γ₀ : GL (Fin d) K := matrixLinearIso.symm g
  have hγ₀g : matrixLinearIso γ₀ = g := MulEquiv.apply_symm_apply _ _
  have hγ₀O : γ₀ ∈ matrixIsometries Q := by
    change matrixLinearIso γ₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [hγ₀g]
    exact hgO
  have hγe : γ₀.val *ᵥ e = e' := by
    rw [← matrixLinearIso_apply, hγ₀g]
    simpa using hg 0
  have hγw : γ₀.val *ᵥ w = w := by
    rw [← matrixLinearIso_apply, hγ₀g]
    simpa using hg 1
  have hrw : (reflMat Q w hw0).val *ᵥ w = w := by
    rw [reflMat_mulVec_one w hw hw0, polar_self_zero, zero_smul, add_zero]
  have hre : (reflMat Q w hw0).val *ᵥ e = e := by
    rw [reflMat_mulVec_one w hw hw0, he1, zero_smul, add_zero]
  rcases mem_or_mul_reflMat_mem hnd hT hγ₀O w hw0 with h | h
  · exact ⟨γ₀, h, hγw, hγe⟩
  · refine ⟨γ₀ * reflMat Q w hw0, h, ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hrw, hγw]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hre, hγe]

end Transitive

section PerpFixed

theorem eq_one_or_eq_refl_of_fix_perp (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K}
    (hw : Q w = 1) {r : GL (Fin d) K} (hr : r ∈ matrixIsometries Q) (hrw : r.val *ᵥ w = w)
    (hfix : ∀ x, polar Q w x = 0 → r.val *ᵥ x = x) :
    r = 1 ∨ r = reflMat Q w (by rw [hw]; exact one_ne_zero) := by
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hw' : w ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hw
    exact zero_ne_one hw
  obtain ⟨y₀, hy₀⟩ : ∃ y, polar Q w y ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hw' (hnd.1 w fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hall y
  set x₀ : Fin d → K := (polar Q w y₀)⁻¹ • y₀ with hx₀
  have hx₀1 : polar Q w x₀ = 1 := by
    rw [hx₀, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy₀]
  have hperp : ∀ x : Fin d → K, polar Q w (x - polar Q w x • x₀) = 0 := by
    intro x
    rw [polar_sub_right, polar_smul_right, hx₀1, smul_eq_mul, mul_one, sub_self]
  set δ : Fin d → K := r.val *ᵥ x₀ - x₀ with hδ
  have hδperp : ∀ u, polar Q w u = 0 → polar Q δ u = 0 := by
    intro u hu
    have h1 := polar_mulVec_of_mem hr x₀ u
    rw [hfix u hu] at h1
    rw [hδ, polar_sub_left, h1, sub_self]
  have hδy : ∀ y, polar Q δ y = polar Q δ x₀ * polar Q w y := by
    intro y
    have h1 := hδperp _ (hperp y)
    rw [polar_sub_right, polar_smul_right, smul_eq_mul, sub_eq_zero] at h1
    rw [h1, mul_comm]
  have hδw : δ = polar Q δ x₀ • w := by
    have : δ - polar Q δ x₀ • w = 0 := by
      refine hnd.1 _ fun y => ?_
      rw [QuadraticMap.polarBilin_apply_apply, polar_sub_left, polar_smul_left, hδy y,
        smul_eq_mul, polar_comm Q w y, sub_self]
    exact sub_eq_zero.1 this
  set μ : K := polar Q δ x₀ with hμ
  have hrx : ∀ x, r.val *ᵥ x = x + (polar Q w x * μ) • w := by
    intro x
    have h1 := hfix _ (hperp x)
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at h1
    have h2 : r.val *ᵥ x₀ = x₀ + μ • w := by
      rw [← hδw, hδ]
      abel
    rw [h2] at h1
    have h3 : r.val *ᵥ x = x - polar Q w x • x₀ + polar Q w x • (x₀ + μ • w) := by
      rw [← h1]
      abel
    rw [h3]
    module
  have hμ2 : μ * μ + μ = 0 := by
    have h1 := map_mulVec_of_mem hr x₀
    have h2 := hrx x₀
    rw [hx₀1, one_mul] at h2
    rw [h2, map_add_smul, hw, polar_comm, hx₀1] at h1
    linear_combination h1
  have hμ' : μ = 0 ∨ μ = 1 := by
    have : μ * (μ + 1) = 0 := by linear_combination hμ2
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · right
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h - h2
  rcases hμ' with h | h
  · left
    refine Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)
    rw [hrx, h, mul_zero, zero_smul, add_zero, Units.val_one, Matrix.one_mulVec]
  · right
    refine Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)
    rw [hrx, h, mul_one, reflMat_mulVec_one w hw hw0]

end PerpFixed

section Final

variable [Finite K]

theorem eq_bot_of_normal_two_subgroup (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {w : Fin d → K} (hw : Q w = 1) (hd : 3 ≤ d) (R : Subgroup (GL (Fin d) K))
    (hR2 : IsPGroup 2 R) (hRΓ : R ≤ matrixDerived Q) (hRw : ∀ r ∈ R, r.val *ᵥ w = w)
    (hnorm : ∀ s ∈ matrixDerived Q, s.val *ᵥ w = w → ∀ r ∈ R, s * r * s⁻¹ ∈ R) : R = ⊥ := by
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hRO : R ≤ matrixIsometries Q := hRΓ.trans (matrixDerived_le_isometries Q)
  obtain ⟨e₀, he0, he01, he02, hfix₀⟩ := exists_fixed_singular hnd hw hd R hR2 hRO hRw
  have hfixZ : ∀ e : Fin d → K, polar Q w e = 0 → Q e = 0 → ∀ r ∈ R, r.val *ᵥ e = e := by
    intro e he1 he2 r hr
    by_cases he0' : e = 0
    · subst he0'
      simp
    · obtain ⟨γ, hγΓ, hγw, hγe⟩ := exists_stab_map hnd hT hw he01 he02 he1 he2 he0 he0'
      have hγinvw : (γ⁻¹).val *ᵥ w = w := by
        have := congrArg (fun v => (γ⁻¹).val *ᵥ v) hγw
        simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec] at this
        exact this.symm
      have hrr : γ⁻¹ * r * γ⁻¹⁻¹ ∈ R := hnorm γ⁻¹ (inv_mem hγΓ) hγinvw r hr
      have hid : r * γ = γ * (γ⁻¹ * r * γ⁻¹⁻¹) := by group
      calc r.val *ᵥ e = r.val *ᵥ (γ.val *ᵥ e₀) := by rw [hγe]
        _ = (r * γ).val *ᵥ e₀ := by rw [Units.val_mul, Matrix.mulVec_mulVec]
        _ = γ.val *ᵥ ((γ⁻¹ * r * γ⁻¹⁻¹).val *ᵥ e₀) := by
          rw [hid, Units.val_mul, Matrix.mulVec_mulVec]
        _ = γ.val *ᵥ e₀ := by rw [hfix₀ _ hrr]
        _ = e := hγe
  have hfixU : ∀ r ∈ R, ∀ x : Fin d → K, polar Q w x = 0 → r.val *ᵥ x = x := by
    intro r hr x hx
    obtain ⟨⟨⟨e, he1, he2⟩, t⟩, hxe⟩ := (decompEquiv w hw).surjective ⟨x, hx⟩
    have hx' : x = e + t • w := by
      have := congrArg Subtype.val hxe
      exact this.symm
    rw [hx', Matrix.mulVec_add, Matrix.mulVec_smul, hfixZ e he1 he2 r hr, hRw r hr]
  refine (Subgroup.eq_bot_iff_forall R).2 fun r hr => ?_
  rcases eq_one_or_eq_refl_of_fix_perp hnd hw (hRO hr) (hRw r hr) (hfixU r hr) with h | h
  · exact h
  · exact absurd (h ▸ hRΓ hr) (reflMat_not_mem_derived hnd hT w hw0)

end Final

end Stab

end CFSG.RankThree.PartOne.AUTSL
