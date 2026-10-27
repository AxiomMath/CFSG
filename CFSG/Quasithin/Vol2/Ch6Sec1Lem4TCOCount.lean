module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOSL

public section

namespace CFSG.Quasithin.H13.L216

open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self unipSL_zero)
open scoped MatrixGroups

section Orbit

variable {F : Type} [Field F] [Finite F]

theorem five_dvd_card_sub_one {c : F} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (W : AddSubgroup F)
    (hW : ∀ b ∈ W, c * b ∈ W) : 5 ∣ Nat.card W - 1 := by
  classical
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc5
  let f : Function.End {w : W // w ≠ 0} := fun x =>
    ⟨⟨c * x.1.1, hW _ x.1.2⟩, fun h => x.2 (Subtype.ext
      ((mul_eq_zero.mp (congrArg Subtype.val h)).resolve_left hc0))⟩
  have hiter : ∀ (k : ℕ) (x : {w : W // w ≠ 0}), ((f^[k] x).1 : F) = c ^ k * x.1.1 := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, one_mul]; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      simp only [f]
      rw [ih]
      ring
  have hf5 : (f^[5] : Function.End {w : W // w ≠ 0}) = id := by
    funext x
    apply Subtype.ext
    apply Subtype.ext
    rw [hiter, hc5, one_mul]
    rfl
  have hfix : ∀ x : {w : W // w ≠ 0}, f x = x → False := by
    intro x hx
    have h1 : c * x.1.1 = x.1.1 := congrArg (fun y => (y.1 : F)) hx
    have h2 : (c - 1) * x.1.1 = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc1 (sub_eq_zero.mp h3)
    · exact x.2 (Subtype.ext h3)
  haveI : Fintype W := Fintype.ofFinite _
  haveI : Fintype {w : W // w ≠ 0} := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hperm : f ^ 5 = 1 := by
    funext x
    exact congrFun hf5 x
  have hfixcard : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨x, hx⟩
    exact hfix x hx
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hperm
  rw [hfixcard] at hmod
  have hS : Fintype.card {w : W // w ≠ 0} = Nat.card W - 1 := by
    have hopt := Fintype.card_congr (Equiv.optionSubtypeNe (0 : W))
    rw [Fintype.card_option] at hopt
    rw [Nat.card_eq_fintype_card (α := ↥W)]
    omega
  rw [← hS]
  exact (Nat.modEq_zero_iff_dvd).mp hmod

end Orbit

section Galois

variable {F : Type} [Field F] [Finite F]

theorem eq_top_of_mul_closed {c : F} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hF : Nat.card F = 16)
    (W : AddSubgroup F) (hW : ∀ b ∈ W, c * b ∈ W) (hW0 : W ≠ ⊥) : W = ⊤ := by
  have h5 := five_dvd_card_sub_one hc5 hc1 W hW
  have hdvd : Nat.card W ∣ 16 := hF ▸ AddSubgroup.card_addSubgroup_dvd_card W
  have hpos : 2 ≤ Nat.card W := by
    have h1 : 1 < Nat.card W := (AddSubgroup.one_lt_card_iff_ne_bot W).mpr hW0
    omega
  obtain ⟨n, hn⟩ : ∃ n, Nat.card W = n := ⟨_, rfl⟩
  rw [hn] at hdvd h5 hpos
  have hn16 : n = 16 := by
    have hle : n ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> omega
  apply AddSubgroup.eq_top_of_card_eq
  rw [hn, hn16, hF]

theorem ringHom_eq_id_of_mul {c : F} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hF : Nat.card F = 16)
    (σ : F →+* F) (hσ : σ c = c) (x : F) : σ x = x := by
  let W : AddSubgroup F :=
    { carrier := {x | σ x = x}
      add_mem' := fun {a b} ha hb => by
        show σ (a + b) = a + b
        have ha' : σ a = a := ha
        have hb' : σ b = b := hb
        rw [map_add, ha', hb']
      zero_mem' := by
        show σ 0 = 0
        exact map_zero σ
      neg_mem' := fun {a} ha => by
        show σ (-a) = -a
        have ha' : σ a = a := ha
        rw [map_neg, ha'] }
  have hmem : ∀ b : F, b ∈ W ↔ σ b = b := fun b => Iff.rfl
  have hWc : ∀ b ∈ W, c * b ∈ W := by
    intro b hb
    rw [hmem] at hb ⊢
    rw [map_mul, hσ, hb]
  have hW0 : W ≠ ⊥ := by
    intro h
    have h1 : (1 : F) ∈ W := (hmem 1).mpr (map_one σ)
    rw [h, AddSubgroup.mem_bot] at h1
    exact one_ne_zero h1
  have htop := eq_top_of_mul_closed hc5 hc1 hF W hWc hW0
  have hx : x ∈ W := htop ▸ AddSubgroup.mem_top x
  exact (hmem x).mp hx

end Galois

section Unipotent

variable {F : Type} [Field F]

theorem unipSL_mul_unipSL' (b c : F) : unipSL b * unipSL c = unipSL (b + c) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipSL, coe_unipSL, coe_unipSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem not_comm_order_five [CharP F 2] {s : SL(2, F)} (hs : orderOf s = 5) {c : F} (hc : c ≠ 0)
    (hcomm : unipSL c * s = s * unipSL c) : False := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hdet := det_sl s
  have e00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hcomm
  have e01 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hcomm
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    at e00 e01
  have hγ : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h : c * (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e00
    exact (mul_eq_zero.mp h).resolve_left hc
  have hda : (s : Matrix (Fin 2) (Fin 2) F) 1 1 = (s : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have h : c * ((s : Matrix (Fin 2) (Fin 2) F) 1 1 - (s : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      linear_combination e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc)
  have hsq : (s : Matrix (Fin 2) (Fin 2) F) 0 0 * (s : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [hγ, hda, mul_zero, sub_zero] at hdet
    linear_combination hdet
  have ha1 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h : ((s : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hsq - (s : Matrix (Fin 2) (Fin 2) F) 0 0 * h2 + h2
    have := (pow_eq_zero_iff two_ne_zero).mp h
    linear_combination this
  have hseq : s = unipSL ((s : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_unipSL]
    fin_cases i <;> fin_cases j <;> simp [hγ, hda, ha1]
  have hs2 : s ^ 2 = 1 := by
    rw [hseq, sq, unipSL_mul_self]
  have hdvd := orderOf_dvd_of_pow_eq_one hs2
  rw [hs] at hdvd
  norm_num at hdvd

theorem not_normalized_order_five [CharP F 2] [Finite F] (hF : Nat.card F = 16) {s : SL(2, F)}
    (hs : orderOf s = 5) (hnorm : ∀ b : F, unipSL b * s * (unipSL b)⁻¹ ∈ Subgroup.zpowers s) :
    False := by
  classical
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  let Stab : AddSubgroup F :=
    { carrier := {c | unipSL c * s = s * unipSL c}
      add_mem' := fun {c d} hc hd => by
        show unipSL (c + d) * s = s * unipSL (c + d)
        have hc' : unipSL c * s = s * unipSL c := hc
        have hd' : unipSL d * s = s * unipSL d := hd
        rw [← unipSL_mul_unipSL', mul_assoc, hd', ← mul_assoc, hc', mul_assoc]
      zero_mem' := by
        show unipSL 0 * s = s * unipSL 0
        rw [unipSL_zero, one_mul, mul_one]
      neg_mem' := fun {c} hc => by
        have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
        have hneg : -c = c := neg_eq_of_add_eq_zero_left hcc
        show unipSL (-c) * s = s * unipSL (-c)
        rw [hneg]
        exact hc }
  have hStab : ∀ c : F, c ∈ Stab ↔ unipSL c * s = s * unipSL c := fun c => Iff.rfl
  let f : F → SL(2, F) := fun b => unipSL b * s * (unipSL b)⁻¹
  have hconjS : ∀ c ∈ Stab, unipSL c * s * (unipSL c)⁻¹ = s := by
    intro c hc
    rw [hStab] at hc
    rw [hc, mul_inv_cancel_right]
  have hfadd : ∀ b c, c ∈ Stab → f (b + c) = f b := by
    intro b c hc
    show unipSL (b + c) * s * (unipSL (b + c))⁻¹ = unipSL b * s * (unipSL b)⁻¹
    rw [← unipSL_mul_unipSL']
    calc unipSL b * unipSL c * s * (unipSL b * unipSL c)⁻¹
        = unipSL b * (unipSL c * s * (unipSL c)⁻¹) * (unipSL b)⁻¹ := by group
      _ = unipSL b * s * (unipSL b)⁻¹ := by rw [hconjS c hc]
  have hf1 : ∀ b, f b ≠ 1 := by
    intro b h1
    have h1' : unipSL b * s * (unipSL b)⁻¹ = 1 := h1
    have hs1 : s = 1 := by
      have h3 := mul_inv_eq_one.mp h1'
      calc s = (unipSL b)⁻¹ * (unipSL b * s) := by group
        _ = (unipSL b)⁻¹ * unipSL b := by rw [h3]
        _ = 1 := by group
    rw [hs1, orderOf_one] at hs
    norm_num at hs
  have hval : ∀ b, ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧ f b = s ^ m := by
    intro b
    have hb := hnorm b
    rw [Subgroup.mem_zpowers_iff] at hb
    obtain ⟨n, hn⟩ := hb
    have hnm : s ^ (n % 5) = f b := by
      have h5 : (5 : ℤ) = ((orderOf s : ℕ) : ℤ) := by rw [hs]; norm_num
      show s ^ (n % 5) = unipSL b * s * (unipSL b)⁻¹
      rw [← hn, h5, zpow_mod_orderOf]
    have hn0 : 0 ≤ n % 5 := Int.emod_nonneg n (by norm_num)
    have hn5 : n % 5 < 5 := Int.emod_lt_of_pos n (by norm_num)
    have hnat : s ^ (n % 5).toNat = f b := by
      rw [← hnm, ← zpow_natCast, Int.toNat_of_nonneg hn0]
    refine ⟨(n % 5).toNat, ?_, ?_, hnat.symm⟩
    · by_contra hcon
      have h0 : (n % 5).toNat = 0 := by omega
      rw [h0, pow_zero] at hnat
      exact hf1 b hnat.symm
    · omega
  let g : Fin 4 → SL(2, F) := fun k => s ^ ((k : ℕ) + 1)
  have hmemg : ∀ b, f b ∈ Set.range g := by
    intro b
    obtain ⟨m, hm1, hm4, hfm⟩ := hval b
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    simp only [g]
    rw [hfm]
    congr 1
    omega
  have key : ∀ a b : F, f a = f b → a - b ∈ Stab := by
    intro a b hab
    rw [hStab]
    have ha : unipSL a = unipSL b * unipSL (a - b) := by
      rw [unipSL_mul_unipSL']
      congr 1
      abel
    have h1 : f a = unipSL b * (unipSL (a - b) * s * (unipSL (a - b))⁻¹) * (unipSL b)⁻¹ := by
      show unipSL a * s * (unipSL a)⁻¹ = _
      rw [ha]
      group
    have h2 : unipSL b * (unipSL (a - b) * s * (unipSL (a - b))⁻¹) * (unipSL b)⁻¹
        = unipSL b * s * (unipSL b)⁻¹ := by
      rw [← h1]
      exact hab
    have h3 : unipSL (a - b) * s * (unipSL (a - b))⁻¹ = s :=
      mul_left_cancel (mul_right_cancel h2)
    calc unipSL (a - b) * s = (unipSL (a - b) * s * (unipSL (a - b))⁻¹) * unipSL (a - b) := by
          group
      _ = s * unipSL (a - b) := by rw [h3]
  let φ : F → Set.range g := fun b => ⟨f b, hmemg b⟩
  let e : F ⧸ Stab → Set.range g := Quotient.lift φ (by
    intro a b hab
    apply Subtype.ext
    have hab' : -a + b ∈ Stab := (QuotientAddGroup.leftRel_apply).mp hab
    have h := hfadd a (-a + b) hab'
    rw [add_neg_cancel_left] at h
    exact h.symm)
  have hinj : Function.Injective e := by
    intro q₁ q₂ hq
    induction q₁ using Quotient.inductionOn with
    | h a =>
      induction q₂ using Quotient.inductionOn with
      | h b =>
        have hf : f a = f b := congrArg Subtype.val hq
        have hmem := key a b hf
        apply Quotient.sound
        refine QuotientAddGroup.leftRel_apply.mpr ?_
        have hneg : -a + b = -(a - b) := by abel
        rw [hneg]
        exact Stab.neg_mem hmem
  have hidx : Stab.index ≤ 4 := by
    have h1 := Nat.card_le_card_of_injective e hinj
    have h2 : Nat.card (Set.range g) ≤ 4 := by
      have hsurj : Function.Surjective (fun k : Fin 4 => (⟨g k, k, rfl⟩ : Set.range g)) := by
        rintro ⟨x, k, rfl⟩
        exact ⟨k, rfl⟩
      have hle := Nat.card_le_card_of_surjective _ hsurj
      rw [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at hle
      exact hle
    exact le_trans h1 h2
  have hcard : Nat.card Stab * Stab.index = 16 := by
    rw [AddSubgroup.card_mul_index, hF]
  have hStabpos : 4 ≤ Nat.card Stab := by
    have : Nat.card Stab * Stab.index ≤ Nat.card Stab * 4 := Nat.mul_le_mul_left _ hidx
    omega
  have hne : Stab ≠ ⊥ := (AddSubgroup.one_lt_card_iff_ne_bot Stab).mp (by omega)
  have hex : ∃ c : F, c ∈ Stab ∧ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_bot_iff]
    intro x hx
    rw [AddSubgroup.mem_bot]
    by_contra hx0
    exact hx0 (hcon x hx)
  obtain ⟨c, hcS, hc0⟩ := hex
  exact not_comm_order_five hs hc0 ((hStab c).mp hcS)

theorem eq_one_of_central [CharP F 2] {g : SL(2, F)} (hg : ∀ x : SL(2, F), g * x = x * g) :
    g = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  let l : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hu := hg (unipSL 1)
  have hl := hg l
  have hu00 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have hu01 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hu
  have hlc : ((l : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
  have hl00 : ((g * l : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((l * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hl
  have hl01 : ((g * l : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      ((l * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 :=
    congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hlc] at hl00 hl01
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const] at hl00 hl01
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at hu00 hu01
  have hl' : l = l := rfl
  have g10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    first | linear_combination -hu00 | linear_combination hu00
  have g11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    first | linear_combination -hu01 | linear_combination hu01
  have g01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    first | linear_combination hl00 | linear_combination -hl00
  have hdet := det_sl g
  have hsq : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [g10, g01, g11] at hdet
    linear_combination hdet
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hsq - (g : Matrix (Fin 2) (Fin 2) F) 0 0 * h2 + h2
    linear_combination (pow_eq_zero_iff two_ne_zero).mp h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [g10, g01, g11, ha]

end Unipotent

end CFSG.Quasithin.H13.L216
