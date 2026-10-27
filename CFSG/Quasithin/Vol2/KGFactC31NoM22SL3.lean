module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.Quasithin.KGC31.NoM22

open Function Polynomial
open scoped MatrixGroups

section ExtW

variable {G : Type*} [Group G]

@[expose] def extW (D : Subgroup G) (w : G) (hw : w * w = 1) (hN : ∀ d ∈ D, w * d * w ∈ D) :
    Subgroup G where
  carrier := {g | g ∈ D ∨ g * w ∈ D}
  one_mem' := Or.inl D.one_mem
  mul_mem' := by
    intro g h hg hh
    change g ∈ D ∨ g * w ∈ D at hg
    change h ∈ D ∨ h * w ∈ D at hh
    change g * h ∈ D ∨ g * h * w ∈ D
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl (D.mul_mem hg hh)
    · exact Or.inr (by rw [mul_assoc]; exact D.mul_mem hg hh)
    · refine Or.inr ?_
      have e : g * h * w = g * w * (w * h * w) := by
        calc g * h * w = g * (w * w) * h * w := by rw [hw, mul_one]
          _ = g * w * (w * h * w) := by simp only [mul_assoc]
      rw [e]
      exact D.mul_mem hg (hN h hh)
    · refine Or.inl ?_
      have e : g * h = g * w * (w * (h * w) * w) := by
        calc g * h = g * (w * w) * h * (w * w) := by rw [hw, mul_one, mul_one]
          _ = g * w * (w * (h * w) * w) := by simp only [mul_assoc]
      rw [e]
      exact D.mul_mem hg (hN _ hh)
  inv_mem' := by
    intro g hg
    change g ∈ D ∨ g * w ∈ D at hg
    change g⁻¹ ∈ D ∨ g⁻¹ * w ∈ D
    rcases hg with hg | hg
    · exact Or.inl (D.inv_mem hg)
    · refine Or.inr ?_
      have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
      have e : g⁻¹ * w = (w * (g * w) * w)⁻¹ := by
        rw [show w * (g * w) * w = w * g * (w * w) by simp only [mul_assoc], hw, mul_one,
          mul_inv_rev, hwi]
      rw [e]
      exact D.inv_mem (hN _ hg)

theorem relIndex_extW {D : Subgroup G} {w : G} (hw : w * w = 1) (hN : ∀ d ∈ D, w * d * w ∈ D)
    (hwD : w ∉ D) : D.relIndex (extW D w hw hN) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨w, Or.inr (by rw [hw]; exact D.one_mem)⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  obtain ⟨b, hb | hb⟩ := b
  · refine Or.inr ⟨hb, fun h => hwD ?_⟩
    simpa using D.mul_mem (D.inv_mem hb) h
  · refine Or.inl ⟨hb, fun h => hwD ?_⟩
    simpa using D.mul_mem (D.inv_mem h) hb

theorem card_extW {D : Subgroup G} {w : G} (hw : w * w = 1) (hN : ∀ d ∈ D, w * d * w ∈ D)
    (hwD : w ∉ D) : Nat.card (extW D w hw hN) = 2 * Nat.card D := by
  have h1 := (D.subgroupOf (extW D w hw hN)).card_mul_index
  have h2 : (D.subgroupOf (extW D w hw hN)).index = 2 := relIndex_extW hw hN hwD
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun _ h => Or.inl h).toEquiv] at h1
  omega

end ExtW

theorem card_sq_eq_one_le_four {A : Type*} [Group A] {L : Type*} [Field L] (f : A →* Lˣ × Lˣ)
    (hf : Injective f) : Nat.card {x : A // x ^ 2 = 1} ≤ 4 := by
  classical
  have hpm : ∀ u : Lˣ, u ^ 2 = 1 → u = 1 ∨ u = -1 := fun u hu => by
    have h : (u : L) * u = 1 := by rw [← Units.val_mul, ← pow_two, hu, Units.val_one]
    rcases mul_self_eq_one_iff.mp h with h | h
    · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hsq : ∀ x : {x : A // x ^ 2 = 1}, (f x).1 ^ 2 = 1 ∧ (f x).2 ^ 2 = 1 := fun x => by
    have : f x ^ 2 = 1 := by rw [← map_pow, x.2, map_one]
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hpm' : ∀ u v : Lˣ, u ^ 2 = 1 → v ^ 2 = 1 → decide (u = 1) = decide (v = 1) → u = v := by
    intro u v hu hv h
    rcases hpm u hu with rfl | rfl <;> rcases hpm v hv with rfl | rfl <;> simp_all
  let g : {x : A // x ^ 2 = 1} → Bool × Bool := fun x =>
    (decide ((f x).1 = 1), decide ((f x).2 = 1))
  have hg : Injective g := fun x y h => by
    have h1 := hpm' _ _ (hsq x).1 (hsq y).1 (congrArg Prod.fst h)
    have h2 := hpm' _ _ (hsq x).2 (hsq y).2 (congrArg Prod.snd h)
    exact Subtype.ext (hf (Prod.ext h1 h2))
  have := Nat.card_le_card_of_injective g hg
  simpa using this

section SL3

variable {L : Type*} [Field L]

@[expose] def diag3 (a b : Lˣ) : SL(3, L) :=
  ⟨!![(a : L), 0, 0; 0, (b : L), 0; 0, 0, (((a * b)⁻¹ : Lˣ) : L)], by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const, mul_zero, zero_mul, sub_zero, add_zero]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩

@[expose] def monoW : SL(3, L) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by
    rw [Matrix.det_fin_three]
    simp⟩

@[expose] def diag3Hom : Lˣ × Lˣ →* SL(3, L) where
  toFun p := diag3 p.1 p.2
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag3]
  map_mul' p p' := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [diag3, Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem diag3Hom_apply (p : Lˣ × Lˣ) : diag3Hom p = diag3 p.1 p.2 := rfl

theorem diag3Hom_injective : Injective (diag3Hom (L := L)) := fun p p' h => by
  have h0 := congrArg (fun g : SL(3, L) => (g : Matrix (Fin 3) (Fin 3) L) 0 0) h
  have h1 := congrArg (fun g : SL(3, L) => (g : Matrix (Fin 3) (Fin 3) L) 1 1) h
  simp [diag3Hom_apply, diag3] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem monoW_mul_self : (monoW : SL(3, L)) * monoW = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [monoW, Matrix.mul_apply, Fin.sum_univ_three]

theorem monoW_conj (a b : Lˣ) : monoW * diag3 a b * monoW = diag3 b a := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [monoW, diag3, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem monoW_ne (a b : Lˣ) : monoW ≠ diag3 a b := fun h => by
  have h0 := congrArg (fun g : SL(3, L) => (g : Matrix (Fin 3) (Fin 3) L) 0 0) h
  simp [monoW, diag3] at h0
  exact a.ne_zero h0.symm

end SL3

theorem sl3_card_two_part {q a m : ℕ} (hq1 : 1 ≤ q) (hq : q - 1 = 2 ^ a * m) (ha : 2 ≤ a)
    (hm : Odd m) : ∃ t, Odd t ∧ (∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ))) / (q - 1) =
      2 ^ (2 * a + 1) * t := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  set R := 2 ^ (c + 2) * m with hR
  obtain rfl : q = R + 1 := by omega
  have hR0 : 0 < R := Nat.mul_pos (by positivity) hm.pos
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Nat.add_sub_cancel]
  have e1 : (R + 1) ^ 3 - 1 = R * (R ^ 2 + 3 * R + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (R + 1) ^ 3 - (R + 1) = R * ((R + 1) * (R + 2)) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (R + 1) ^ 3 - (R + 1) ^ 2 = R * (R + 1) ^ 2 := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, e3, show R * (R ^ 2 + 3 * R + 3) * (R * ((R + 1) * (R + 2))) * (R * (R + 1) ^ 2) =
    R * ((R ^ 2 + 3 * R + 3) * (R * ((R + 1) * (R + 2))) * (R * (R + 1) ^ 2)) by ring,
    Nat.mul_div_cancel_left _ hR0]
  have hRe : Even R := ⟨2 ^ (c + 1) * m, by rw [hR]; ring⟩
  refine ⟨(R ^ 2 + 3 * R + 3) * m ^ 2 * (R + 1) ^ 3 * (2 ^ (c + 1) * m + 1), ?_, ?_⟩
  · have hA : Odd (R ^ 2 + 3 * R + 3) :=
      Even.add_odd (Even.add (Nat.even_pow.mpr ⟨hRe, two_ne_zero⟩) (Even.mul_left hRe 3))
        (by decide)
    have hB : Odd (2 ^ (c + 1) * m + 1) :=
      Even.add_one (Even.mul_right (Nat.even_pow.mpr ⟨even_two, by omega⟩) m)
    exact Odd.mul (Odd.mul (Odd.mul hA (Odd.pow hm)) (Odd.pow (Even.add_one hRe))) hB
  · rw [hR]
    ring

theorem sl3_sylow_data {L : Type} [Field L] [Fintype L] [DecidableEq L]
    (hL : 4 ∣ Fintype.card L - 1) : ∃ W D : Subgroup SL(3, L), IsPGroup 2 W ∧ ¬ 2 ∣ W.index ∧
      D.relIndex W ≤ 2 ∧ (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧
      Nat.card {x : ↥D // x ^ 2 = 1} ≤ 4 := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 Lˣ))
  let C : Subgroup Lˣ := P
  let D : Subgroup SL(3, L) := (C.prod C).map diag3Hom
  have hN : ∀ d ∈ D, monoW * d * monoW ∈ D := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, ?_⟩
    rw [diag3Hom_apply, diag3Hom_apply, monoW_conj]
  have hwD : (monoW : SL(3, L)) ∉ D := by
    rintro ⟨p, -, hp⟩
    exact monoW_ne p.1 p.2 hp.symm
  let W := extW D monoW monoW_mul_self hN
  set q := Fintype.card L with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hU : Nat.card Lˣ = q - 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_units]
  set a := (q - 1).factorization 2 with ha
  have hq0 : q - 1 ≠ 0 := by omega
  have hm := Nat.ordProj_mul_ordCompl_eq_self (q - 1) 2
  have hmodd : Odd ((q - 1) / 2 ^ (q - 1).factorization 2) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hq0))
  have ha2 : 2 ≤ a :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hq0).mp (by simpa using hL)
  have hC : Nat.card C = 2 ^ a := by
    rw [show Nat.card C = Nat.card P from rfl, P.card_eq_multiplicity, hU]
  have hD : Nat.card D = 2 ^ a * 2 ^ a := by
    rw [Subgroup.card_map_of_injective diag3Hom_injective,
      Nat.card_congr (Subgroup.prodEquiv C C).toEquiv, Nat.card_prod, hC]
  have hW : Nat.card W = 2 ^ (2 * a + 1) := by
    rw [card_extW monoW_mul_self hN hwD, hD]
    ring
  obtain ⟨t, ht, hX⟩ := sl3_card_two_part (by omega) hm.symm ha2 hmodd
  have hcard := W.card_mul_index
  rw [hW, Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Matrix.card_SL_field, ← hq,
    hX] at hcard
  have hidx : W.index = t := Nat.eq_of_mul_eq_mul_left (by positivity) hcard
  refine ⟨W, D, IsPGroup.of_card hW, ?_, (relIndex_extW monoW_mul_self hN hwD).le, ?_, ?_⟩
  · rw [hidx]
    exact fun h => (Nat.not_even_iff_odd.mpr ht) (even_iff_two_dvd.mpr h)
  · rintro _ ⟨p, -, rfl⟩ _ ⟨p', -, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · let e := (C.prod C).equivMapOfInjective diag3Hom diag3Hom_injective
    exact card_sq_eq_one_le_four ((C.prod C).subtype.comp e.symm.toMonoidHom)
      ((C.prod C).subtype_injective.comp e.symm.injective)

theorem exists_ext_four_dvd {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    ∃ (L : Type) (_ : Field L) (_ : Fintype L) (_ : DecidableEq L) (_ : K →+* L),
      4 ∣ Fintype.card L - 1 := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hK
  rcases (by omega : Fintype.card K % 4 = 1 ∨ Fintype.card K % 4 = 3) with h | h
  · exact ⟨K, inferInstance, inferInstance, inferInstance, RingHom.id K, by omega⟩
  · have hsq : ∀ b : K, b ^ 2 ≠ -1 := fun b hb =>
      (FiniteField.isSquare_neg_one_iff.mp ⟨b, by rw [← hb, pow_two]⟩) h
    have hirr : Irreducible (X ^ 2 - C (-1 : K)) :=
      X_pow_sub_C_irreducible_of_prime Nat.prime_two hsq
    have : Fact (Irreducible (X ^ 2 - C (-1 : K))) := ⟨hirr⟩
    let pb := AdjoinRoot.powerBasis hirr.ne_zero
    have : Module.Finite K (AdjoinRoot (X ^ 2 - C (-1 : K))) := pb.finite
    have : Finite (AdjoinRoot (X ^ 2 - C (-1 : K))) := Module.finite_of_finite K
    let _ : Fintype (AdjoinRoot (X ^ 2 - C (-1 : K))) := Fintype.ofFinite _
    refine ⟨AdjoinRoot (X ^ 2 - C (-1 : K)), inferInstance, inferInstance, Classical.decEq _,
      AdjoinRoot.of _, ?_⟩
    have hcard : Fintype.card (AdjoinRoot (X ^ 2 - C (-1 : K))) = Fintype.card K ^ 2 := by
      rw [Module.card_eq_pow_finrank (K := K), pb.finrank, AdjoinRoot.powerBasis_dim,
        natDegree_X_pow_sub_C]
    rw [hcard]
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card K = 4 * k + 3 := ⟨Fintype.card K / 4, by omega⟩
    rw [hk]
    exact ⟨4 * k ^ 2 + 6 * k + 2, Nat.sub_eq_of_eq_add (by ring)⟩

section Embed

variable {K L : Type*} [Field K] [Field L]

@[expose] def toSL {n : ℕ} (H : Subgroup (GL (Fin n) K))
    (hH : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) K).det = 1) : ↥H →* SL(n, K) where
  toFun h := ⟨((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hH h h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toSL_injective {n : ℕ} (H : Subgroup (GL (Fin n) K))
    (hH : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) K).det = 1) : Injective (toSL H hH) :=
  fun _ _ e => Subtype.ext (Units.ext (congrArg Subtype.val e))

theorem slMap_injective {n : ℕ} (f : K →+* L) :
    Injective (Matrix.SpecialLinearGroup.map (n := Fin n) f) := fun _ _ e =>
  Subtype.ext (Matrix.map_injective f.injective (congrArg Subtype.val e))

@[expose] def blk (A : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 3) (Fin 3) L :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) L) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_mul (A B : Matrix (Fin 2) (Fin 2) L) : blk (A * B) = blk A * blk B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem det_blk (A : Matrix (Fin 2) (Fin 2) L) : (blk A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk]

@[expose] def blockHom : SL(2, L) →* SL(3, L) where
  toFun g := ⟨blk (g : Matrix (Fin 2) (Fin 2) L), by rw [det_blk]; exact g.2⟩
  map_one' := Subtype.ext blk_one
  map_mul' g g' := Subtype.ext (blk_mul _ _)

theorem blockHom_apply (g : SL(2, L)) :
    ((blockHom g : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = blk (g : Matrix (Fin 2) (Fin 2) L) :=
  rfl

theorem blockHom_injective : Injective (blockHom (L := L)) := fun g g' e => by
  ext i j
  have := congrArg (fun x : SL(3, L) => (x : Matrix (Fin 3) (Fin 3) L) (Fin.castSucc i)
    (Fin.castSucc j)) e
  fin_cases i <;> fin_cases j <;> simpa [blockHom_apply, blk] using this

end Embed

end CFSG.Quasithin.KGC31.NoM22

end
