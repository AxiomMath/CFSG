module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs520
public import CFSG.Quasithin.Background.HSU3Borel

public section

namespace CFSG.Quasithin.H13.H11

open CFSG.Quasithin CFSG.Quasithin.H.SU3
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipHom unipHom_apply unipHom_injective
  exists_conj_unip twist_conj coe_inv_mul_SL)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

@[expose] def ann (m : ℕ) (X : Subgroup (Multiplicative F)) : Set F :=
  {b | ∀ x ∈ X, Multiplicative.toAdd x * b ^ 2 ^ m + b * (Multiplicative.toAdd x) ^ 2 ^ m = 0}

theorem card_mul_card_ann_le (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2)
    {X : Subgroup (Multiplicative F)} (hX : X ≠ ⊥) :
    Nat.card X * Nat.card (ann m X) ≤ Nat.card F := by
  classical
  have hσ : ∀ x : F, bar m x = x ^ 2 ^ m := bar_apply
  have hinv : ∀ x : F, bar m (bar m x) = x := bar_bar hF
  have hF0 := card_fixed hm hF
  obtain ⟨⟨x₀, hx₀X⟩, hx₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX
  set a₀ := Multiplicative.toAdd (x₀ : Multiplicative F) with ha₀
  have ha₀0 : a₀ ≠ 0 := fun h => hx₀ (Subtype.ext (Multiplicative.toAdd.injective h))
  have hann : ∀ (x b : F), x * b ^ 2 ^ m + b * x ^ 2 ^ m = 0 → bar m (b * bar m x) =
      b * bar m x := by
    intro x b h
    rw [map_mul, hinv, hσ b, hσ x]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - (b * x ^ 2 ^ m) * h2
  by_cases hcase : ∀ x ∈ X, bar m (Multiplicative.toAdd x * a₀⁻¹) =
      Multiplicative.toAdd x * a₀⁻¹
  ·
    have h1 : Nat.card X ≤ 2 ^ m := by
      rw [← hF0]
      refine Nat.card_le_card_of_injective
        (fun x => (⟨Multiplicative.toAdd (x : Multiplicative F) * a₀⁻¹, hcase x x.2⟩ :
          {b : F // bar m b = b})) ?_
      intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only at h
      have h' := mul_right_cancel₀ (inv_ne_zero ha₀0) h
      exact Subtype.ext (Multiplicative.toAdd.injective h')
    have h2 : Nat.card (ann m X) ≤ 2 ^ m := by
      rw [← hF0]
      refine Nat.card_le_card_of_injective
        (fun b => (⟨b.1 * bar m a₀, hann a₀ b.1 (b.2 x₀ hx₀X)⟩ : {b : F // bar m b = b})) ?_
      intro b c hbc
      have h := congrArg Subtype.val hbc
      simp only at h
      have hσa₀ : bar m a₀ ≠ 0 := by
        rw [hσ]
        exact pow_ne_zero _ ha₀0
      exact Subtype.ext (mul_right_cancel₀ hσa₀ h)
    calc Nat.card X * Nat.card (ann m X) ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul h1 h2
      _ = Nat.card F := by rw [hF]; ring
  ·
    push Not at hcase
    obtain ⟨x₁, hx₁X, hx₁⟩ := hcase
    have h0 : ∀ b ∈ ann m X, b = 0 := by
      intro b hb
      by_contra hb0
      set r := Multiplicative.toAdd x₁ * a₀⁻¹ with hr
      have e0 := hann a₀ b (hb x₀ hx₀X)
      have e1 := hann _ b (hb x₁ hx₁X)
      have hx1 : Multiplicative.toAdd x₁ = r * a₀ := by
        rw [hr, mul_assoc, inv_mul_cancel₀ ha₀0, mul_one]
      rw [map_mul, hinv] at e0 e1
      rw [hx1, map_mul] at e1
      have e3 : (r - bar m r) * (bar m b * a₀) = 0 := by linear_combination e1 - bar m r * e0
      rcases mul_eq_zero.mp e3 with h | h
      · exact hx₁ (sub_eq_zero.mp h).symm
      · rcases mul_eq_zero.mp h with h' | h'
        · apply hb0
          rw [← hinv b, h', map_zero]
        · exact ha₀0 h'
    have h1 : Nat.card (ann m X) ≤ 1 := by
      refine (Nat.card_le_card_of_injective (fun _ : ann m X => ()) ?_).trans_eq Nat.card_unique
      intro b c _
      exact Subtype.ext (by rw [h0 b.1 b.2, h0 c.1 c.2])
    have h2 : Nat.card X ≤ Nat.card F :=
      Nat.card_le_card_of_injective (fun x : ↥X => Multiplicative.toAdd (x : Multiplicative F))
        (fun x y h => Subtype.ext (Multiplicative.toAdd.injective h))
    calc Nat.card X * Nat.card (ann m X) ≤ Nat.card F * 1 := Nat.mul_le_mul h2 h1
      _ = Nat.card F := mul_one _

omit [Finite F] [CharP F 2] in
theorem twist_unip_apply (x : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    ((unipSL x : Matrix (Fin 2) (Fin 2) F) * Y *
        (frobPow m (unipSL x : Matrix (Fin 2) (Fin 2) F))ᵀ) 0 1 = Y 0 1 + x * Y 1 1 ∧
      ((unipSL x : Matrix (Fin 2) (Fin 2) F) * Y *
        (frobPow m (unipSL x : Matrix (Fin 2) (Fin 2) F))ᵀ) 0 0 =
          Y 0 0 + x * Y 1 0 + (Y 0 1 + x * Y 1 1) * x ^ 2 ^ m := by
  constructor <;>
    simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
      Matrix.map_apply, Matrix.vecMul, dotProduct]

omit [Finite F] [CharP F 2] in
theorem fix_unip {X : Subgroup (Multiplicative F)} {x₀ : F} (hx₀ : Multiplicative.ofAdd x₀ ∈ X)
    (hx₀0 : x₀ ≠ 0) {Y : Matrix (Fin 2) (Fin 2) F} (hY : (frobPow m Y)ᵀ = Y)
    (hfix : ∀ x : F, Multiplicative.ofAdd x ∈ X → (unipSL x : Matrix (Fin 2) (Fin 2) F) * Y *
      (frobPow m (unipSL x : Matrix (Fin 2) (Fin 2) F))ᵀ = Y) :
    Y 1 1 = 0 ∧ Y 0 1 ∈ ann m X := by
  have hsym : Y 1 0 = Y 0 1 ^ 2 ^ m := by
    have := congrFun (congrFun hY 1) 0
    simpa [Matrix.transpose_apply, frobPow, Matrix.map_apply] using this.symm
  have h11 : Y 1 1 = 0 := by
    have e01 := (twist_unip_apply (m := m) x₀ Y).1
    rw [hfix x₀ hx₀] at e01
    have h1 : x₀ * Y 1 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp h1).resolve_left hx₀0
  refine ⟨h11, fun x hx => ?_⟩
  have e00 := (twist_unip_apply (m := m) (Multiplicative.toAdd x) Y).2
  rw [hfix (Multiplicative.toAdd x) hx, h11, hsym] at e00
  linear_combination -e00

theorem card_fix_unip_le (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2)
    {X : Subgroup (Multiplicative F)} (hX : X ≠ ⊥) :
    Nat.card {Y : ↥(hermSub m (Fin 2) F) // ∀ x : F, Multiplicative.ofAdd x ∈ X →
      (unipSL x : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
          (frobPow m (unipSL x : Matrix (Fin 2) (Fin 2) F))ᵀ =
        Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))} ≤
      2 ^ m * Nat.card (ann m X) := by
  classical
  obtain ⟨⟨x₀, hx₀X⟩, hx₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX
  have hx₀0 : Multiplicative.toAdd x₀ ≠ 0 :=
    fun h => hx₀ (Subtype.ext (Multiplicative.toAdd.injective h))
  have hx₀X' : Multiplicative.ofAdd (Multiplicative.toAdd x₀) ∈ X := hx₀X
  rw [← card_fixed hm hF, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun Y =>
    (⟨Multiplicative.toAdd (Y.1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 0 0, ?_⟩,
      ⟨Multiplicative.toAdd (Y.1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 0 1,
        (fix_unip hx₀X' hx₀0 ((mem_hermSub m).mp Y.1.2) Y.2).2⟩)) ?_
  · have h := congrFun (congrFun ((mem_hermSub m).mp Y.1.2) 0) 0
    rw [bar_apply]
    simpa [Matrix.transpose_apply, frobPow, Matrix.map_apply] using h
  · intro Y Y' hYY'
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hYY'
    obtain ⟨h00, h01⟩ := hYY'
    set M := Multiplicative.toAdd (Y.1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) with hM
    set M' := Multiplicative.toAdd (Y'.1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) with hM'
    have hsym : ∀ N : Matrix (Fin 2) (Fin 2) F, (frobPow m N)ᵀ = N → N 1 0 = N 0 1 ^ 2 ^ m := by
      intro N hN
      have := congrFun (congrFun hN 1) 0
      simpa [Matrix.transpose_apply, frobPow, Matrix.map_apply] using this.symm
    have hYh : (frobPow m M)ᵀ = M := (mem_hermSub m).mp Y.1.2
    have hY'h : (frobPow m M')ᵀ = M' := (mem_hermSub m).mp Y'.1.2
    have h11 := (fix_unip hx₀X' hx₀0 hYh Y.2).1
    have h11' := (fix_unip hx₀X' hx₀0 hY'h Y'.2).1
    have hMM : M = M' := mat2_ext h00 h01 (by rw [hsym M hYh, hsym M' hY'h, h01])
      (by rw [h11, h11'])
    exact Subtype.ext (Subtype.ext (Multiplicative.toAdd.injective hMM))

theorem card_herm_ge (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2) :
    2 ^ m * 2 ^ m * Nat.card F ≤ Nat.card ↥(hermSub m (Fin 2) F) := by
  classical
  have hinv : ∀ x : F, (x ^ 2 ^ m) ^ 2 ^ m = x := fun x => by
    have := bar_bar hF x
    rwa [bar_apply, bar_apply] at this
  rw [← card_fixed hm hF, ← Nat.card_prod, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p =>
    ⟨Multiplicative.ofAdd !![p.1.1.1, p.2; p.2 ^ 2 ^ m, p.1.2.1], ?_⟩) ?_
  · rw [mem_hermSub m, toAdd_ofAdd]
    have ha : p.1.1.1 ^ 2 ^ m = p.1.1.1 := by rw [← bar_apply]; exact p.1.1.2
    have hd : p.1.2.1 ^ 2 ^ m = p.1.2.1 := by rw [← bar_apply]; exact p.1.2.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose_apply, frobPow, Matrix.map_apply, ha, hd, hinv]
  · rintro ⟨⟨a, d⟩, b⟩ ⟨⟨a', d'⟩, b'⟩ h
    have h' := congrArg (fun Y : ↥(hermSub m (Fin 2) F) =>
      Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))) h
    simp only [toAdd_ofAdd] at h'
    have e00 := Matrix.ext_iff.mpr h' 0 0
    have e01 := Matrix.ext_iff.mpr h' 0 1
    have e11 := Matrix.ext_iff.mpr h' 1 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨⟨Subtype.ext e00, Subtype.ext e11⟩, e01⟩

theorem card_mul_card_fix_le (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ (2 * m))
    {B : Subgroup SL(2, F)} (hB : IsPGroup 2 B) (hB1 : B ≠ ⊥) :
    Nat.card B * 2 ^ m * Nat.card {Y : ↥(hermSub m (Fin 2) F) // ∀ γ ∈ B,
      (γ : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
          (frobPow m (γ : Matrix (Fin 2) (Fin 2) F))ᵀ =
        Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))} ≤
      Nat.card ↥(hermSub m (Fin 2) F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : Nat.card F = (2 ^ m) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
  obtain ⟨P, hBP⟩ := hB.exists_le_sylow
  obtain ⟨g, hgP, -⟩ := exists_conj_unip hF P.isPGroup' P.not_dvd_index
  set X : Subgroup (Multiplicative F) := (B.map (MulAut.conj g).toMonoidHom).comap unipHom
    with hXdef
  have hmemX : ∀ x : F, Multiplicative.ofAdd x ∈ X ↔ ∃ γ ∈ B, g * γ * g⁻¹ = unipSL x := by
    intro x
    rw [hXdef, Subgroup.mem_comap, unipHom_apply, toAdd_ofAdd]
    constructor
    · rintro ⟨γ, hγ, h⟩
      exact ⟨γ, hγ, h⟩
    · rintro ⟨γ, hγ, h⟩
      exact ⟨γ, hγ, h⟩
  have hXmap : X.map unipHom = B.map (MulAut.conj g).toMonoidHom := by
    rw [hXdef, Subgroup.map_comap_eq, inf_eq_right]
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨b, hb⟩ := hgP γ (hBP hγ)
    exact ⟨Multiplicative.ofAdd b, by rw [unipHom_apply, toAdd_ofAdd, ← hb]; rfl⟩
  have hXc : Nat.card X = Nat.card B := by
    rw [← Subgroup.card_map_of_injective unipHom_injective, hXmap,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hX1 : X ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hXc, Subgroup.one_lt_card_iff_ne_bot]
    exact hB1
  have hfix : Nat.card {Y : ↥(hermSub m (Fin 2) F) // ∀ γ ∈ B,
      (γ : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
          (frobPow m (γ : Matrix (Fin 2) (Fin 2) F))ᵀ =
        Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))} ≤
      Nat.card {Y : ↥(hermSub m (Fin 2) F) // ∀ x : F, Multiplicative.ofAdd x ∈ X →
        (unipSL x : Matrix (Fin 2) (Fin 2) F) *
            Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
            (frobPow m (unipSL x : Matrix (Fin 2) (Fin 2) F))ᵀ =
          Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))} := by
    refine Nat.card_le_card_of_injective (fun Y => ⟨⟨Multiplicative.ofAdd
      ((g : Matrix (Fin 2) (Fin 2) F) *
        Multiplicative.toAdd (Y.1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
        (frobPow m (g : Matrix (Fin 2) (Fin 2) F))ᵀ),
      (mem_hermSub m).mpr (twist_herm hF ((mem_hermSub m).mp Y.1.2) _)⟩, fun x hx => ?_⟩) ?_
    · obtain ⟨γ, hγ, hgγ⟩ := (hmemX x).mp hx
      have hU : (unipSL x : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (γ : Matrix (Fin 2) (Fin 2) F) := by
        rw [← hgγ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.mul_assoc, coe_inv_mul_SL, Matrix.mul_one]
      simp only [toAdd_ofAdd]
      rw [twist_conj m _ _ _ _ hU, Y.2 γ hγ]
    · intro Y Y' h
      have h' := congrArg (fun Z : {Y : ↥(hermSub m (Fin 2) F) // _} =>
        Multiplicative.toAdd (Z.1 : Multiplicative (Matrix (Fin 2) (Fin 2) F))) h
      simp only [toAdd_ofAdd] at h'
      have h2 := congrArg (fun Z => ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Z *
        (frobPow m ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ) h'
      simp only [twist_inv_twist] at h2
      exact Subtype.ext (Subtype.ext (Multiplicative.toAdd.injective h2))
  have hann := card_mul_card_ann_le hm hF2 hX1
  have hfixU := card_fix_unip_le hm hF2 hX1
  have hH := card_herm_ge hm hF2
  calc Nat.card B * 2 ^ m * Nat.card {Y : ↥(hermSub m (Fin 2) F) // ∀ γ ∈ B,
        (γ : Matrix (Fin 2) (Fin 2) F) *
            Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
            (frobPow m (γ : Matrix (Fin 2) (Fin 2) F))ᵀ =
          Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))} ≤
        Nat.card X * 2 ^ m * (2 ^ m * Nat.card (ann m X)) := by
          rw [hXc]
          exact Nat.mul_le_mul_left _ (hfix.trans hfixU)
    _ = 2 ^ m * 2 ^ m * (Nat.card X * Nat.card (ann m X)) := by ring
    _ ≤ 2 ^ m * 2 ^ m * Nat.card F := Nat.mul_le_mul_left _ hann
    _ ≤ Nat.card ↥(hermSub m (Fin 2) F) := hH

theorem h11ThreeFact : H11ThreeFact := by
  intro G _ _ L V A m horth hm hAN hAL hAe hAC
  obtain ⟨F, _, _, _, hF, eρ, E, hE⟩ := horth.exists_equiv
  set φ : SL(2, F) →* MulAut ↥V := (autOn L V).subtype.comp eρ.toMonoidHom with hφ
  have hφi : Function.Injective φ := Subtype.val_injective.comp eρ.injective
  have hφr : φ.range = autOn L V := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eρ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set B : Subgroup SL(2, F) := (autOn A V).comap φ with hBdef
  have hBmap : B.map φ = autOn A V := by
    rw [hBdef, Subgroup.map_comap_eq, hφr]
    exact inf_eq_right.mpr hAL
  have hBc : Nat.card B = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [← card_autOn_eq_relIndex hAN, ← hBmap, Subgroup.card_map_of_injective hφi]
  have hB2 : IsPGroup 2 B := by
    intro b
    refine ⟨1, Subtype.ext (hφi ?_)⟩
    rw [pow_one, Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact hAe.2 (φ b) b.2
  have hB1 : B ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hne : Nat.card B ≠ 1 := by
      rw [hBc, Ne, Subgroup.relIndex_eq_one]
      exact fun h => hAC (h.trans inf_le_right)
    omega
  have hfixc : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card {Y : ↥(hermSub m (Fin 2) F) // ∀ γ ∈ B,
        (γ : Matrix (Fin 2) (Fin 2) F) *
            Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
            (frobPow m (γ : Matrix (Fin 2) (Fin 2) F))ᵀ =
          Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F))} := by
    have e1 : ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≃ {w : ↥V // ∀ γ ∈ B, φ γ w = w} :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, fun γ hγ =>
          ((mem_centralizer_iff_autOn hAN ⟨x, x.2.1⟩).mp x.2.2) _ hγ⟩
        invFun := fun w => ⟨w.1, w.1.2, (mem_centralizer_iff_autOn hAN w.1).mpr fun y hy => by
          rw [← hBmap] at hy
          obtain ⟨γ, hγ, rfl⟩ := hy
          exact w.2 γ hγ⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    rw [Nat.card_congr e1]
    refine Nat.card_congr (Equiv.subtypeEquiv E.toEquiv fun w => forall₂_congr fun γ _ => ?_)
    have h1 := hE γ w
    constructor
    · intro h
      have h2 := congrArg (fun v => Multiplicative.toAdd
        ((E v : ↥(hermSub m (Fin 2) F)) : Multiplicative (Matrix (Fin 2) (Fin 2) F))) h
      have h3 : ((E (φ γ w) : ↥(hermSub m (Fin 2) F)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) F)) = _ := h1
      rw [h3, toAdd_ofAdd] at h2
      exact h2
    · intro h
      apply E.injective
      apply Subtype.ext
      have h3 : ((E (φ γ w) : ↥(hermSub m (Fin 2) F)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) F)) = _ := h1
      rw [h3]
      exact congrArg Multiplicative.ofAdd h
  have hcore := card_mul_card_fix_le (by omega) hF hB2 hB1
  rw [hBc, ← hfixc, ← Nat.card_congr E.toEquiv] at hcore
  have hcard := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
  rw [inf_of_le_left inf_le_left] at hcard
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  rw [← hcard] at hcore
  exact Nat.le_of_mul_le_mul_right hcore hpos

end CFSG.Quasithin.H13.H11
