module

public import CFSG.RankThree.PartOne.K1214.ActR
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.RankThree.PartOne.K128

open Subgroup

variable {p e : ℕ}

theorem card_pow_eq_one_le (hp : p.Prime) (r : ℕ) :
    Nat.card {v : Fin r → Multiplicative (ZMod (p ^ e)) // v ^ p = 1} ≤ p ^ r := by
  classical
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hiff : ∀ v : Fin r → Multiplicative (ZMod (p ^ e)), v ^ p = 1 ↔ ∀ i, v i ^ p = 1 := by
    intro v
    constructor
    · intro h i
      have := congrFun h i
      simpa using this
    · intro h
      funext i
      simpa using h i
  have e1 : {v : Fin r → Multiplicative (ZMod (p ^ e)) // v ^ p = 1} ≃
      (Fin r → {x : Multiplicative (ZMod (p ^ e)) // x ^ p = 1}) :=
    (Equiv.subtypeEquivRight hiff).trans
      (Equiv.subtypePiEquivPi (p := fun _ x => x ^ p = 1))
  have hS : Nat.card {x : Multiplicative (ZMod (p ^ e)) // x ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  rw [Nat.card_congr e1, Nat.card_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Nat.pow_le_pow_left hS r

@[expose] def pTorsion (p : ℕ) (R : Type*) [CommGroup R] : Subgroup R :=
  (powMonoidHom p : R →* R).ker

theorem mem_pTorsion {R : Type*} [CommGroup R] {x : R} : x ∈ pTorsion p R ↔ x ^ p = 1 := by
  simp [pTorsion, MonoidHom.mem_ker]

theorem comm_of_equiv {R : Type*} [Group R] {r : ℕ}
    (φ : R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) (x y : R) : x * y = y * x := by
  apply φ.injective
  rw [map_mul, map_mul, mul_comm]

theorem card_pTorsion_le (hp : p.Prime) {R : Type*} [CommGroup R]
    (φ : R ≃* (Fin 2 → Multiplicative (ZMod (p ^ e)))) : Nat.card (pTorsion p R) ≤ p ^ 2 := by
  have e1 : (pTorsion p R) ≃ {v : Fin 2 → Multiplicative (ZMod (p ^ e)) // v ^ p = 1} :=
    { toFun := fun x => ⟨φ x, by rw [← map_pow, mem_pTorsion.1 x.2, map_one]⟩
      invFun := fun v => ⟨φ.symm v, mem_pTorsion.2 (by
        apply φ.injective
        rw [map_pow, MulEquiv.apply_symm_apply, v.2, map_one])⟩
      left_inv := fun x => by simp
      right_inv := fun v => by simp }
  rw [Nat.card_congr e1]
  exact card_pow_eq_one_le hp 2

theorem exists_apply_mul_inv_eq [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e) {R : Type*} [Group R]
    [Finite R] (φ : R ≃* (Fin 2 → Multiplicative (ZMod (p ^ e)))) (σ : MulAut R) (hσ : σ ^ p = 1)
    (hcount : Nat.card (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id R)) ≤ p ^ (2 * (e - 1)))
    {d : R} (hd : d ^ p = 1) : ∃ y : R, σ y * y⁻¹ = d := by
  classical
  have hp : p.Prime := Fact.out
  let _ : CommGroup R := { ‹Group R› with mul_comm := comm_of_equiv φ }
  obtain ⟨hA, -⟩ := K1214.act_lemma_mul hp5 (Or.inr rfl) (by omega) (Or.inr he) φ σ hσ
  let δ : R →* R := σ.toMonoidHom / MonoidHom.id R
  have hδ : ∀ x, δ x = σ x * x⁻¹ := fun x => by
    simp [δ, div_eq_mul_inv]
  have hker : δ.ker = MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id R) := by
    ext x
    simp only [MonoidHom.mem_ker, hδ]
    constructor
    · intro h
      exact mul_inv_eq_one.1 h
    · intro h
      exact mul_inv_eq_one.2 h
  have hRcard : Nat.card R = p ^ (2 * e) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_pi, Nat.card_eq_fintype_card]
    simp [Finset.prod_const, ZMod.card, ← pow_mul, mul_comm]
  have hmul := card_ker_mul_card_range δ
  rw [hRcard, hker] at hmul
  have hrange : p ^ 2 ≤ Nat.card δ.range := by
    by_contra hlt
    have hlt : Nat.card δ.range < p ^ 2 := not_le.1 hlt
    have h1 : Nat.card (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id R)) * Nat.card δ.range <
        p ^ (2 * (e - 1)) * p ^ 2 + 0 := by
      calc _ ≤ p ^ (2 * (e - 1)) * Nat.card δ.range :=
            Nat.mul_le_mul_right _ hcount
        _ < p ^ (2 * (e - 1)) * p ^ 2 :=
            Nat.mul_lt_mul_of_pos_left hlt (pow_pos hp.pos _)
        _ = _ := by simp
    have h2 : p ^ (2 * (e - 1)) * p ^ 2 = p ^ (2 * e) := by
      rw [← pow_add]
      congr 1
      omega
    omega
  have hle : δ.range ≤ pTorsion p R := by
    rintro _ ⟨x, rfl⟩
    rw [mem_pTorsion, hδ]
    exact hA x
  have hcard : Nat.card (pTorsion p R) ≤ Nat.card δ.range :=
    (card_pTorsion_le hp φ).trans hrange
  have heq : δ.range = pTorsion p R := by
    have : Finite (pTorsion p R) := inferInstance
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hdm : d ∈ δ.range := by
    rw [heq]
    exact mem_pTorsion.2 hd
  obtain ⟨y, hy⟩ := hdm
  exact ⟨y, by rw [← hδ]; exact hy⟩

theorem pow_apply_eq_mul {R : Type*} [CommGroup R] (σ : MulAut R) {d y : R} (hd : σ d = d)
    (hy : σ y * y⁻¹ = d) (i : ℕ) : (σ ^ i) y = d ^ i * y := by
  have hσy : σ y = d * y := by
    rw [← hy]
    group
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hd, hσy]
    group

end CFSG.RankThree.PartOne.K128
