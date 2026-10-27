module

public import CFSG.Quasithin.Vol2.F134LieOddModel
public import CFSG.Quasithin.Vol2.F134LieOddBasic
public import CFSG.Quasithin.Vol2.F134LieOddMatrix

public section

namespace CFSG.Quasithin.F134.LieOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem injective_of_ne {α : Type*} {δ : Fin 3 → α} (h01 : δ 0 ≠ δ 1) (h02 : δ 0 ≠ δ 2)
    (h12 : δ 1 ≠ δ 2) : Function.Injective δ := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem exists_diagHom_of_isDiag3 {g : GL (Fin 3) K}
    (hd : IsDiag3 (g : Matrix (Fin 3) (Fin 3) K)) : ∃ e : Fin 3 → Kˣ, g = diagHom 3 e := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have hdiag := hd.eq_diagonal
  rw [hdiag, det_diagonal, Fin.prod_univ_three] at hdet
  have hne : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    have h2 := right_ne_zero_of_mul hdet
    have h01 := left_ne_zero_of_mul hdet
    intro i
    fin_cases i
    exacts [left_ne_zero_of_mul h01, right_ne_zero_of_mul h01, h2]
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_diagHom]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    exact hd i j hij

theorem sq_add_add_one_eq_zero {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (ω : K) ^ 2 + ω + 1 = 0 := by
  have h3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have h1 : (ω : K) - 1 ≠ 0 := fun h => hω1 (Units.ext (sub_eq_zero.1 h))
  have : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 this).resolve_left h1

variable {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

namespace OddModel

variable (h : OddModel H M)
include h

section Heis

variable [Finite K] {P : Subgroup (StatedProj H)}
  (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
  (hstd : ∀ x : H, proj H x ∈ P → (x : GL (Fin 3) K) ∈ torus3 M ⊔ Subgroup.zpowers cycGL)
  {x₀ : H} (hx₀ : proj H x₀ ∈ P) (hx₀T : (x₀ : GL (Fin 3) K) ∉ torus3 M)
include hPab hstd hx₀ hx₀T

omit h hPab in
theorem exists_x₀_eq : ∃ t₀ ∈ torus3 M, ∃ j : ℕ, (j = 1 ∨ j = 2) ∧
    (x₀ : GL (Fin 3) K) = t₀ * cycGL ^ j := by
  obtain ⟨t₀, ht₀, j, hj, hx₀eq⟩ := exists_mem_torus3_mul_cyc M (hstd x₀ hx₀)
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hx₀T
    rw [hx₀eq, pow_zero, mul_one]
    exact ht₀
  exact ⟨t₀, ht₀, j, by omega, hx₀eq⟩

omit h in
theorem diag_cases {s : H} (hs : proj H s ∈ P) (hsT : (s : GL (Fin 3) K) ∈ torus3 M) :
    s ∈ scal H ∨ ∃ δ : Fin 3 → K, Function.Injective δ ∧
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal δ := by
  obtain ⟨t₀, ht₀, j, hj, hx₀eq⟩ := exists_x₀_eq hstd hx₀ hx₀T
  obtain ⟨c, hc⟩ := mem_scal_iff.1 (commutator_mem_scal (hPab _ hx₀ _ hs))
  have hwT : cycGL ^ j * (s : GL (Fin 3) K) * (cycGL ^ j)⁻¹ ∈ torus3 M := by
    have hn : (cycGL : GL (Fin 3) K) ^ j ∈
        Subgroup.normalizer (torus3 (K := K) M : Set (GL (Fin 3) K)) :=
      Subgroup.pow_mem _ (cycGL_mem_normalizer_torus3 M) j
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 hsT
  have hconj : cycGL ^ j * (s : GL (Fin 3) K) * (cycGL ^ j)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * (s : GL (Fin 3) K) := by
    have h1 := torus3_comm M ht₀ hwT
    have e : ((x₀ * s * x₀⁻¹ * s⁻¹ : H) : GL (Fin 3) K) =
        cycGL ^ j * (s : GL (Fin 3) K) * (cycGL ^ j)⁻¹ * (s : GL (Fin 3) K)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx₀eq]
      calc t₀ * cycGL ^ j * (s : GL (Fin 3) K) * (t₀ * cycGL ^ j)⁻¹ * (s : GL (Fin 3) K)⁻¹
          = t₀ * (cycGL ^ j * (s : GL (Fin 3) K) * (cycGL ^ j)⁻¹) * t₀⁻¹ *
              (s : GL (Fin 3) K)⁻¹ := by group
        _ = cycGL ^ j * (s : GL (Fin 3) K) * (cycGL ^ j)⁻¹ * (s : GL (Fin 3) K)⁻¹ := by
          rw [h1]; group
    rw [e] at hc
    rw [← hc]
    group
  obtain ⟨d, hd, hsd⟩ := exists_diag_of_mem_torus3 hsT
  rw [hsd, scalar_eq_diagHom, ← map_mul] at hconj
  obtain ⟨μ, hμ3, h1, h2⟩ : ∃ μ : Kˣ, μ ^ 3 = 1 ∧ d 1 = μ * d 0 ∧ d 2 = μ * μ * d 0 := by
    rcases hj with rfl | rfl
    · rw [pow_one, cycGL_conj_diagHom] at hconj
      have e := diagHom_injective 3 hconj
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      have e2 := congrFun e 2
      simp only [Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] at e0 e1 e2
      have hc3 : c ^ 3 = 1 := by
        have : d 0 = c ^ 3 * d 0 := by
          calc d 0 = c * d 1 := e1
            _ = c * (c * d 2) := by rw [e2]
            _ = c * (c * (c * d 0)) := by rw [e0]
            _ = c ^ 3 * d 0 := by rw [pow_three]; simp only [mul_assoc]
        exact (mul_eq_right.1 this.symm)
      refine ⟨c * c, by rw [mul_pow, hc3, one_mul], ?_, ?_⟩
      · rw [e2, e0, ← mul_assoc]
      · calc d 2 = c * d 0 := e0
          _ = c ^ 3 * (c * d 0) := by rw [hc3, one_mul]
          _ = c * c * (c * c) * d 0 := by rw [pow_three']; simp only [mul_assoc]
    · rw [cycGL_sq_conj_diagHom] at hconj
      have e := diagHom_injective 3 hconj
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      have e2 := congrFun e 2
      simp only [Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] at e0 e1 e2
      have hc3 : c ^ 3 = 1 := by
        have : d 0 = c ^ 3 * d 0 := by
          calc d 0 = c * d 2 := e2
            _ = c * (c * d 1) := by rw [e1]
            _ = c * (c * (c * d 0)) := by rw [e0]
            _ = c ^ 3 * d 0 := by rw [pow_three]; simp only [mul_assoc]
        exact (mul_eq_right.1 this.symm)
      refine ⟨c, hc3, e0, ?_⟩
      rw [e1, e0, ← mul_assoc]
  by_cases hμ : μ = 1
  · left
    refine mem_scal_iff.2 ⟨d 0, ?_⟩
    rw [hsd, scalar_eq_diagHom]
    congr 1
    funext i
    fin_cases i
    · rfl
    · simp [h1, hμ]
    · simp [h2, hμ]
  · right
    have hμ2 : μ * μ ≠ 1 := by
      intro h'
      apply hμ
      rw [show μ = μ ^ 3 * (μ * μ)⁻¹ by rw [pow_three']; group, hμ3, h', inv_one, one_mul]
    have hμμ : μ ≠ μ * μ := by
      intro h'
      apply hμ
      have := congrArg (μ⁻¹ * ·) h'
      simpa using this.symm
    refine ⟨fun i => (d i : K), injective_of_ne ?_ ?_ ?_, by rw [hsd, coe_diagHom]⟩
    · intro e
      apply hμ
      have e' : d 0 = d 1 := Units.ext e
      rw [h1] at e'
      have := congrArg (· * (d 0)⁻¹) e'
      simpa using this.symm
    · intro e
      apply hμ2
      have e' : d 0 = d 2 := Units.ext e
      rw [h2] at e'
      have := congrArg (· * (d 0)⁻¹) e'
      simpa using this.symm
    · intro e
      apply hμμ
      have e' : d 1 = d 2 := Units.ext e
      rw [h1, h2] at e'
      have := congrArg (· * (d 0)⁻¹) e'
      simpa [mul_assoc] using this

omit h hPab in
theorem exists_scalar_of_commute {g : GL (Fin 3) K} {s : H} {δ : Fin 3 → K}
    (hδ : Function.Injective δ)
    (hsδ : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal δ)
    (hgs : g * (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * g)
    (hgx : g * (x₀ : GL (Fin 3) K) = (x₀ : GL (Fin 3) K) * g) :
    ∃ c : Kˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨t₀, ht₀, j, hj, hx₀eq⟩ := exists_x₀_eq hstd hx₀ hx₀T
  have hgd : IsDiag3 (g : Matrix (Fin 3) (Fin 3) K) := by
    refine isDiag3_of_commute_diagonal hδ ?_
    rw [← hsδ]
    have := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hgs
    simpa using this
  obtain ⟨e, rfl⟩ := exists_diagHom_of_isDiag3 hgd
  obtain ⟨d, -, -, rfl⟩ := (mem_torus3 M).1 ht₀
  have hcomm : diagHom 3 e * cycGL ^ j = cycGL ^ j * diagHom 3 e := by
    rw [hx₀eq] at hgx
    have h1 : diagHom 3 e * diagHom 3 d = diagHom 3 d * diagHom 3 e := by
      rw [← map_mul, ← map_mul, mul_comm]
    rw [← mul_assoc, h1, mul_assoc, mul_assoc] at hgx
    exact mul_left_cancel hgx
  have hconj : cycGL ^ j * diagHom 3 e * (cycGL ^ j)⁻¹ = diagHom 3 e := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨e 0, ?_⟩
  rw [scalar_eq_diagHom]
  congr 1
  rcases hj with rfl | rfl
  · rw [pow_one, cycGL_conj_diagHom] at hconj
    have hh := diagHom_injective 3 hconj
    have e0 := congrFun hh 0
    have e1 := congrFun hh 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    funext i
    fin_cases i
    · rfl
    · exact e1.symm
    · exact e0
  · rw [cycGL_sq_conj_diagHom] at hconj
    have hh := diagHom_injective 3 hconj
    have e0 := congrFun hh 0
    have e1 := congrFun hh 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    funext i
    fin_cases i
    · rfl
    · exact e0
    · exact e1.trans e0

theorem exists_regular_diag (hP : Nat.card P = 9) : ∃ s : H, proj H s ∈ P ∧
    ∃ δ : Fin 3 → K, Function.Injective δ ∧
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal δ := by
  classical
  by_contra hcon
  set N : Subgroup (GL (Fin 3) K) := torus3 M ⊔ Subgroup.zpowers cycGL with hNdef
  set Et : Subgroup (GL (Fin 3) K) := (P.comap (proj H)).map H.subtype with hEtdef
  have hEtN : Et ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hstd x hx
  have hEtcard : Nat.card Et = 27 := by
    rw [hEtdef, Subgroup.card_map_of_injective H.subtype_injective, h.card_comap, hP]
  have hTN : torus3 M ≤ N := le_sup_left
  have hidx : (torus3 M).relIndex N = 3 := by
    have h' := Subgroup.relIndex_mul_card (torus3 M) N
    rw [inf_eq_left.2 hTN, card_torus3, card_torus3_sup_cyc] at h'
    have hpos : 0 < Nat.card M ^ 2 := pow_pos Nat.card_pos 2
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  have hrel : (torus3 M).relIndex Et ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right (H := torus3 M) hEtN (by rw [hidx]; norm_num)
    rwa [hidx] at this
  have hmul := Subgroup.relIndex_mul_card (torus3 M) Et
  rw [hEtcard] at hmul
  have hle : torus3 M ⊓ Et ≤ (scal H).map H.subtype := by
    rintro y ⟨hyT, x, hx, rfl⟩
    rcases diag_cases hPab hstd hx₀ hx₀T hx hyT with hsc | hreg
    · exact ⟨x, hsc, rfl⟩
    · exact absurd ⟨x, hx, hreg⟩ hcon
  have h3 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective H.subtype_injective, h.card_scal] at h3
  nlinarith

theorem eq_one_of_involution_centralizes (hP : Nat.card P = 9) {v : StatedProj H}
    (hv : v ^ 2 = 1) (hvP : ∀ y ∈ P, v * y = y * v) : v = 1 := by
  obtain ⟨s, hs, δ, hδ, hsδ⟩ := h.exists_regular_diag hPab hstd hx₀ hx₀T hP
  obtain ⟨u, rfl, hu2⟩ := h.exists_involution_lift hv
  have hcomm : ∀ x : H, proj H x ∈ P → u * x = x * u := fun x hx =>
    mul_inv_eq_iff_eq_mul.1 (h.conj_eq_of_involution' hu2 (by
      rw [map_mul, map_mul, map_inv, hvP _ hx, mul_inv_cancel_right]))
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hstd hx₀ hx₀T hδ hsδ (g := (u : GL (Fin 3) K))
    (by simpa using congrArg Subtype.val (hcomm s hs))
    (by simpa using congrArg Subtype.val (hcomm x₀ hx₀))
  exact proj_eq_one_iff.2 (mem_scal_iff.2 ⟨c, hc⟩)

theorem isRegular_of_mem {y : H} (hy : proj H y ∈ P) (hy1 : y ∉ scal H) :
    IsRegular ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨ω, hω3, hω1⟩ := h.prim
  have hω := sq_add_add_one_eq_zero hω3 hω1
  obtain ⟨t, ht, k, hk, hyeq⟩ := exists_mem_torus3_mul_cyc M (hstd y hy)
  obtain ⟨d, hd, hdt⟩ := exists_diag_of_mem_torus3 ht
  have hdK : (d 0 : K) * d 1 * d 2 = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, hd, Units.val_one]
  have hfun : (fun i => (d i : K)) = ![(d 0 : K), d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  interval_cases k
  · rw [pow_zero, mul_one] at hyeq
    rcases diag_cases hPab hstd hx₀ hx₀T hy (by rw [hyeq]; exact ht) with hsc | ⟨δ, hδ, hyδ⟩
    · exact absurd hsc hy1
    · rw [hyδ]
      exact isRegular_diagonal hδ
  · rw [hyeq, pow_one, Units.val_mul, hdt, coe_diagHom, coe_cycGL, hfun]
    exact isRegular_diag_mul_cyc hdK hω h.three
  · rw [hyeq, Units.val_mul, hdt, coe_diagHom, Units.val_pow_eq_pow_val, coe_cycGL, hfun]
    exact isRegular_diag_mul_cyc_sq hdK hω h.three

theorem centralizes_of_involution (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    {v : StatedProj H} (hv : v ^ 2 = 1) (hvP : ∀ y ∈ P, v * y * v⁻¹ ∈ P)
    {a : StatedProj H} (ha : a ∈ P) (ha1 : a ≠ 1) (hva : v * a * v⁻¹ = a) :
    ∀ b ∈ P, v * b * v⁻¹ = b := by
  intro b hb
  obtain ⟨s, hs, δ, hδ, hsδ⟩ := h.exists_regular_diag hPab hstd hx₀ hx₀T hP
  obtain ⟨u, rfl, hu2⟩ := h.exists_involution_lift hv
  obtain ⟨x, rfl⟩ := proj_surjective a
  obtain ⟨y, rfl⟩ := proj_surjective b
  have hux : u * x * u⁻¹ = x :=
    h.conj_eq_of_involution' hu2 (by rw [map_mul, map_mul, map_inv]; exact hva)
  set z := u * y * u⁻¹ with hzdef
  have hz : proj H z ∈ P := by
    rw [hzdef, map_mul, map_mul, map_inv]
    exact hvP _ hb
  have hxy := commutator_mem_scal (hPab _ ha _ hb)
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hxz : x * z * x⁻¹ * z⁻¹ = c := by
    have e : x * z * x⁻¹ * z⁻¹ = u * c * u⁻¹ := by
      conv_lhs => rw [← hux]
      rw [hzdef, hcdef]
      group
    rw [e, ← mem_scal_commute hxy u, mul_inv_cancel_right]
  have hf : (z * y⁻¹) * x = x * (z * y⁻¹) := by
    have e1 : x * y⁻¹ * x⁻¹ * y = c⁻¹ := by
      have e : x * y⁻¹ * x⁻¹ * y = y⁻¹ * c⁻¹ * y := by rw [hcdef]; group
      rw [e, ← mem_scal_commute (inv_mem hxy) y⁻¹, inv_mul_cancel_right]
    have e2 : x * (z * y⁻¹) * x⁻¹ * (z * y⁻¹)⁻¹ = 1 := by
      calc x * (z * y⁻¹) * x⁻¹ * (z * y⁻¹)⁻¹ =
            (x * z * x⁻¹ * z⁻¹) * (z * (x * y⁻¹ * x⁻¹ * y) * z⁻¹) := by group
        _ = c * (z * c⁻¹ * z⁻¹) := by rw [hxz, e1]
        _ = 1 := by rw [← mem_scal_commute (inv_mem hxy) z]; group
    have e3 : x * (z * y⁻¹) = (x * (z * y⁻¹) * x⁻¹ * (z * y⁻¹)⁻¹) * ((z * y⁻¹) * x) := by group
    rw [e3, e2, one_mul]
  have hfa : proj H (z * y⁻¹) ∈ Subgroup.zpowers (proj H x) := by
    by_contra hnot
    set C := (Subgroup.centralizer {x}).map (proj H) ⊓ P with hCdef
    have hxC : proj H x ∈ C := ⟨⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl, rfl⟩, ha⟩
    have hfC : proj H (z * y⁻¹) ∈ C :=
      ⟨⟨z * y⁻¹, Subgroup.mem_centralizer_singleton_iff.2 hf, rfl⟩, mul_mem hz (inv_mem hb)⟩
    have hCP : C = P := by
      by_contra hne
      have h3 : Nat.card C = 3 := card_eq_three_of_lt hP inf_le_right (by
        intro hbot
        rw [hbot] at hxC
        exact ha1 hxC) hne
      have hzC : Subgroup.zpowers (proj H x) ≤ C := Subgroup.zpowers_le.2 hxC
      have : Finite C := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
      have hord : orderOf (proj H x) = 3 := orderOf_eq_prime (hexp _ ha) ha1
      have heq : Subgroup.zpowers (proj H x) = C := Subgroup.eq_of_le_of_card_ge hzC
        (by rw [h3, Nat.card_zpowers, hord])
      exact hnot (heq ▸ hfC)
    have hcomm : ∀ w : H, proj H w ∈ P → x * w = w * x := by
      intro w hw
      rw [← hCP] at hw
      obtain ⟨⟨w', hw', hw'w⟩, -⟩ := hw
      have hδw : w'⁻¹ * w ∈ scal H := proj_eq_proj_iff.1 hw'w
      have hw'' : w' * x = x * w' := Subgroup.mem_centralizer_singleton_iff.1 hw'
      calc x * w = (x * w') * (w'⁻¹ * w) := by group
        _ = (w' * x) * (w'⁻¹ * w) := by rw [← hw'']
        _ = w' * ((w'⁻¹ * w) * x) := by rw [mul_assoc, mem_scal_commute hδw x]
        _ = w * x := by group
    obtain ⟨c', hc'⟩ := exists_scalar_of_commute hstd hx₀ hx₀T hδ hsδ (g := (x : GL (Fin 3) K))
      (by simpa using congrArg Subtype.val (hcomm s hs))
      (by simpa using congrArg Subtype.val (hcomm x₀ hx₀))
    exact ha1 (proj_eq_one_iff.2 (mem_scal_iff.2 ⟨c', hc'⟩))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hfa
  have hvb : proj H u * proj H y * (proj H u)⁻¹ = proj H x ^ k * proj H y := by
    rw [hk, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hzdef]
    congr 1
    group
  have huu : proj H u * proj H u = 1 := by rw [← map_mul, ← sq, hu2, map_one]
  have huinv : (proj H u)⁻¹ = proj H u := inv_eq_of_mul_eq_one_right huu
  have hback : proj H y = proj H x ^ k * (proj H x ^ k * proj H y) := by
    have e : proj H y = proj H u * (proj H u * proj H y * (proj H u)⁻¹) * (proj H u)⁻¹ := by
      rw [huinv]
      calc proj H y = (proj H u * proj H u) * proj H y * (proj H u * proj H u) := by
            rw [huu, one_mul, mul_one]
        _ = proj H u * (proj H u * proj H y * proj H u) * proj H u := by group
    have hconj : ∀ g : StatedProj H, proj H u * g * (proj H u)⁻¹ = MulAut.conj (proj H u) g :=
      fun g => (MulAut.conj_apply _ _).symm
    have e2 : proj H u * (proj H x ^ k * proj H y) * (proj H u)⁻¹ =
        proj H x ^ k * (proj H x ^ k * proj H y) := by
      rw [hconj, map_mul, map_zpow, ← hconj, ← hconj, hva, hvb]
    conv_lhs => rw [e, hvb]
    exact e2
  have hk2 : proj H x ^ k * proj H x ^ k = 1 := by
    have e : (proj H x ^ k * proj H x ^ k) * proj H y = 1 * proj H y := by
      rw [one_mul, mul_assoc]
      exact hback.symm
    exact mul_right_cancel e
  have hk1 : proj H x ^ k = 1 := by
    have h3 : (proj H x ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hexp _ ha,
        _root_.one_zpow]
    calc proj H x ^ k = (proj H x ^ k) ^ 3 * (proj H x ^ k * proj H x ^ k)⁻¹ := by
          rw [pow_three']
          group
      _ = 1 := by rw [h3, hk2, inv_one, one_mul]
  rw [hvb, hk1, one_mul]

end Heis

end OddModel

end CFSG.Quasithin.F134.LieOdd
