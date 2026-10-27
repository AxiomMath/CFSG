module

public import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.He.FpSpec
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2106

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

@[expose, irreducible] noncomputable def matA : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  decode 5 133 1 HNSeed1

@[expose, irreducible] noncomputable def matB : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  decode 5 133 1 HNSeed2

theorem matA_eq : matA = decode 5 133 1 HNSeed1 := by unfold matA; rfl

theorem matB_eq : matB = decode 5 133 1 HNSeed2 := by unfold matB; rfl

theorem toMat_rowsA : toMat 5 133 rowsA = matA := by
  rw [rowsA, toMat_rowsOf, matA_eq]
  rfl

theorem toMat_rowsB : toMat 5 133 rowsB = matB := by
  rw [rowsB, toMat_rowsOf, matB_eq]
  rfl

theorem nat_all_true {n : ℕ} {f : (i : ℕ) → i < n → Bool} (h : ∀ i (hi : i < n), f i hi = true) :
    Nat.all n f = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ -
  exact h i hi

theorem toMat_ne_one_of_notIdM {X : Array (Array ℕ)} (h : notIdM 133 X = true) :
    toMat 5 133 X ≠ 1 := by
  intro e
  have hent : ∀ i < 133, ∀ j < 133, ((X[i]!)[j]! % 5 == if i = j then 1 else 0) = true := by
    intro i hi j hj
    have hij := congrFun (congrFun e ⟨i, hi⟩) ⟨j, hj⟩
    rw [toMat_apply, Matrix.one_apply] at hij
    simp only [Fin.mk.injEq] at hij
    rw [beq_iff_eq]
    split_ifs at hij ⊢
    · have := (ZMod.natCast_eq_natCast_iff' ((X[i]!)[j]!) 1 5).1 (hij.trans Nat.cast_one.symm)
      simpa using this
    · have := (ZMod.natCast_eq_natCast_iff' ((X[i]!)[j]!) 0 5).1 (hij.trans Nat.cast_zero.symm)
      simpa using this
  have key : (Nat.all 133 fun i _ => Nat.all 133 fun j _ =>
      (X[i]!)[j]! % 5 == if i = j then 1 else 0) = true :=
    nat_all_true fun i hi => nat_all_true fun j hj => hent i hi j hj
  unfold notIdM at h
  rw [key] at h
  exact Bool.noConfusion h

theorem toMat_wordM (Ms : ℕ → Array (Array ℕ)) (w : List ℕ) :
    toMat 5 133 (wordM Ms w) = (w.map fun l => toMat 5 133 (Ms l)).prod := by
  have key : ∀ (P : Array (Array ℕ)) (w : List ℕ),
      toMat 5 133 (w.foldl (fun P l => mulM 5 133 P (Ms l)) P) =
        toMat 5 133 P * (w.map fun l => toMat 5 133 (Ms l)).prod := by
    intro P w
    induction w generalizing P with
    | nil => simp
    | cons l w ih => rw [List.foldl_cons, ih, toMat_mulM, List.map_cons, List.prod_cons, mul_assoc]
  rw [wordM, key, toMat_idM, one_mul]

theorem toMat_seedSel (l : ℕ) (hl : l = 1 ∨ l = 2) :
    toMat 5 133 (seedSel rowsA rowsB l) = if l = 1 then matA else matB := by
  rcases hl with rfl | rfl
  · simp [seedSel, toMat_rowsA]
  · simp [seedSel, toMat_rowsB]

theorem toMat_wordM_seed (w : List ℕ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) :
    toMat 5 133 (wordM (seedSel rowsA rowsB) w) =
      (w.map fun l => if l = 1 then matA else matB).prod := by
  rw [toMat_wordM]
  congr 1
  exact List.map_congr_left fun l hl => toMat_seedSel l (hw l hl)

theorem seed_parts :
    let G := toMat 5 133 (wordM (seedSel rowsA rowsB) gWord)
    let G' := toMat 5 133 (wordM (seedSel rowsA rowsB) gInvWord)
    matA ^ 2 = 1 ∧ matA ≠ 1 ∧ matB ^ 3 = 1 ∧ matB ≠ 1 ∧ (matA * matB) ^ 22 = 1 ∧
      (matA * matB) ^ 11 ≠ 1 ∧ (matA * matB) ^ 2 ≠ 1 ∧ G * G' = 1 ∧
      (matA * G' * matB * G) ^ 19 = 1 ∧ matA * G' * matB * G ≠ 1 := by
  intro G G'
  have h := seed_orders_cert
  unfold seedChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have e1 := toMat_eq_of_beq (p := 5) (d := 133) h1
  have e3 := toMat_eq_of_beq (p := 5) (d := 133) h3
  have e5 := toMat_eq_of_beq (p := 5) (d := 133) h5
  have e8 := toMat_eq_of_beq (p := 5) (d := 133) h8
  have e9 := toMat_eq_of_beq (p := 5) (d := 133) h9
  have n2 := toMat_ne_one_of_notIdM h2
  have n4 := toMat_ne_one_of_notIdM h4
  have n6 := toMat_ne_one_of_notIdM h6
  have n7 := toMat_ne_one_of_notIdM h7
  have n10 := toMat_ne_one_of_notIdM h10
  simp only [toMat_powM, toMat_mulM, toMat_idM, toMat_rowsA, toMat_rowsB] at e1 e3 e5 e8 e9
  simp only [toMat_powM, toMat_mulM, toMat_rowsA, toMat_rowsB] at n2 n4 n6 n7 n10
  exact ⟨e1, n2, e3, n4, e5, n6, n7, e8, e9, n10⟩

theorem prime_dvd_22 {p : ℕ} (hp : p.Prime) (hpd : p ∣ 22) : p = 2 ∨ p = 11 := by
  have h22 : (22 : ℕ) = 2 * 11 := by norm_num
  rw [h22] at hpd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem prod_cons_cons {M : Type*} [Monoid M] (a b : M) (l : List M) :
    (a :: b :: l).prod = a * (b :: l).prod := List.prod_cons

theorem matrix_gWord :
    toMat 5 133 (wordM (seedSel rowsA rowsB) gWord) =
      matA * matB * matB * matA * matB * matA * matB * matA * matB * matA * matB * matA := by
  have hw : ∀ l ∈ gWord, l = 1 ∨ l = 2 := by
    intro l hl
    simp only [gWord, List.mem_cons, List.not_mem_nil, or_false] at hl
    omega
  rw [toMat_wordM_seed _ hw, gWord]
  have h21 : (2 : ℕ) ≠ 1 := by decide
  simp only [List.map_cons, List.map_nil, prod_cons_cons, List.prod_singleton, ↓reduceIte,
    h21, mul_assoc]

theorem fam_hn_explicit_seed_and_conjugate_product_orders :
    (∃ a b : GL (Fin 133) (ZMod 5), (a : Matrix (Fin 133) (Fin 133) (ZMod 5)) = matA ∧
      (b : Matrix (Fin 133) (Fin 133) (ZMod 5)) = matB) ∧
    ∀ a b : GL (Fin 133) (ZMod 5), (a : Matrix (Fin 133) (Fin 133) (ZMod 5)) = matA →
      (b : Matrix (Fin 133) (Fin 133) (ZMod 5)) = matB →
      orderOf a = 2 ∧ orderOf b = 3 ∧ orderOf (a * b) = 22 ∧
        orderOf (a * (a * b * b * a * b * a * b * a * b * a * b * a)⁻¹ * b *
          (a * b * b * a * b * a * b * a * b * a * b * a)) = 19 := by
  obtain ⟨hA2, hA1, hB3, hB1, hAB22, hAB11, hAB2, hGG, hX19, hX1⟩ := seed_parts
  refine ⟨⟨⟨matA, matA, by rw [← sq, hA2], by rw [← sq, hA2]⟩,
    ⟨matB, matB * matB, by rw [← pow_three, hB3], by rw [mul_assoc, ← pow_three, hB3]⟩, rfl,
    rfl⟩, ?_⟩
  intro a b ha hb
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set g := a * b * b * a * b * a * b * a * b * a * b * a with hg
  have hgm : ((g : GL (Fin 133) (ZMod 5)) : Matrix (Fin 133) (Fin 133) (ZMod 5)) =
      toMat 5 133 (wordM (seedSel rowsA rowsB) gWord) := by
    rw [matrix_gWord, hg]
    simp only [Units.val_mul, ha, hb]
  have hgi : ((g⁻¹ : GL (Fin 133) (ZMod 5)) : Matrix (Fin 133) (Fin 133) (ZMod 5)) =
      toMat 5 133 (wordM (seedSel rowsA rowsB) gInvWord) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hgm]; exact hGG)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← orderOf_units, ha]
    exact orderOf_eq_prime hA2 hA1
  · rw [← orderOf_units, hb]
    exact orderOf_eq_prime hB3 hB1
  · rw [← orderOf_units, Units.val_mul, ha, hb]
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hAB22 fun p hp hpd => ?_
    rcases prime_dvd_22 hp hpd with rfl | rfl
    · exact hAB11
    · exact hAB2
  · rw [← orderOf_units, Units.val_mul, Units.val_mul, Units.val_mul, hgi, hgm, ha, hb]
    exact orderOf_eq_prime hX19 hX1

end CFSG.Sporadic.HNSchreier
