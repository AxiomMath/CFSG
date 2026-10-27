module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.StandardType

theorem kgLangC_pairing {d p : ℕ} {𝕂 : Type} [Field 𝕂] (hp : p.Prime) (hpd : ¬ p ∣ d)
    {x y : GL (Fin d) 𝕂} {c : 𝕂ˣ}
    (hxy : x * y = Matrix.GeneralLinearGroup.scalar (Fin d) c * (y * x))
    {μ : 𝕂ˣ} (hxp : x ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) μ) :
    x * y = y * x := by
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hpd; exact hpd (dvd_zero p)
  have hcd : c ^ d = 1 := by
    have h := congrArg Matrix.GeneralLinearGroup.det hxy
    simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    rw [mul_comm (Matrix.GeneralLinearGroup.det y) (Matrix.GeneralLinearGroup.det x)] at h
    exact mul_right_cancel (show c ^ d *
        (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y) =
        1 * (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y) by
      rw [h.symm, one_mul])
  have hcp : c ^ p = 1 := by
    letI : Bracket (GL (Fin d) 𝕂) (GL (Fin d) 𝕂) := commutatorElement
    have hcomm : ⁅x, y⁆ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [commutatorElement_def, hxy]; group
    have hcx : Commute x ⁅x, y⁆ := by
      rw [hcomm]; exact (Matrix.GeneralLinearGroup.scalar_commute c x).symm
    have hpow := Commute.commutatorElement_pow_left hcx p
    have hcommμ : ⁅Matrix.GeneralLinearGroup.scalar (Fin d) μ, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact Matrix.GeneralLinearGroup.scalar_commute μ y
    rw [hxp, hcommμ, hcomm] at hpow
    have hscalar : Matrix.GeneralLinearGroup.scalar (Fin d) (c ^ p) = 1 := by
      rw [map_pow]; exact hpow
    haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
    apply Units.ext
    have hmat : Matrix.scalar (Fin d) ((c ^ p : 𝕂ˣ) : 𝕂) = Matrix.scalar (Fin d) (1 : 𝕂) := by
      have h := congrArg (fun u : GL (Fin d) 𝕂 => (u : Matrix (Fin d) (Fin d) 𝕂)) hscalar
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_one] at h
      rw [← map_one (Matrix.scalar (Fin d))] at h
      exact h
    exact Matrix.scalar_inj.mp hmat
  have hc : c = 1 :=
    (pow_eq_one_iff_of_coprime (hp.coprime_iff_not_dvd.2 hpd)).mp ⟨hcp, hcd⟩
  simpa [hc] using hxy

theorem kgLangC_span_comm_reduced {d : ℕ} {𝕂 : Type} [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2]
    (P : Subgroup (GL (Fin d) 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (Nat.card P)) :
    (∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (P : Set _)),
      ∀ y ∈ Algebra.adjoin 𝕂 ((fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (P : Set _)),
        x * y = y * x) ∧
    ∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (P : Set _)),
      IsNilpotent x → x = 0 := by
  rcases eq_or_ne d 0 with rfl | hd0
  · haveI : Subsingleton (Matrix (Fin 0) (Fin 0) 𝕂) := inferInstance
    exact ⟨fun x _ y _ => Subsingleton.elim _ _, fun x _ _ => Subsingleton.elim _ _⟩
  · haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
    set s : Set (Matrix (Fin d) (Fin d) 𝕂) :=
      (fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (P : Set _) with hs
    let S : Subalgebra 𝕂 (Matrix (Fin d) (Fin d) 𝕂) := Algebra.adjoin 𝕂 s
    have hs_pair : s.Pairwise Commute := by
      intro a ha b hb _
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨h, hh, rfl⟩ := hb
      show Commute (↑g : Matrix (Fin d) (Fin d) 𝕂) (↑h : Matrix (Fin d) (Fin d) 𝕂)
      rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
        hab g hg h hh]
    have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      haveI : IsMulCommutative S := Algebra.isMulCommutative_adjoin 𝕂 hs_pair
      intro x hx y hy
      have hcommS : ∀ a b : S, a * b = b * a :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative S)
      simpa using congrArg Subtype.val (hcommS ⟨x, hx⟩ ⟨y, hy⟩)
    refine ⟨hcomm, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Algebra (ZMod 2) 𝕂 := ZMod.algebra 𝕂 2
    letI : Fintype 𝕂 := Fintype.ofFinite 𝕂
    let f := Module.finrank (ZMod 2) 𝕂
    let m := Nat.card P
    let k := f * Nat.totient m
    have hcard : 2 ^ f = Nat.card 𝕂 := FiniteField.pow_finrank_eq_natCard 2 𝕂
    have hm_pos : 0 < m := by
      haveI : Nonempty P := ⟨⟨1, one_mem P⟩⟩
      change 0 < Nat.card P
      exact Nat.card_pos
    have hf_pos : 0 < f := by
      change 0 < Module.finrank (ZMod 2) 𝕂
      exact Module.finrank_pos
    have hk_pos : 0 < k := by
      change 0 < f * Nat.totient m
      exact Nat.mul_pos hf_pos (Nat.totient_pos.mpr hm_pos)
    have hcop : Nat.Coprime 2 m := hodd.coprime_two_left
    have hk_mod : 2 ^ k ≡ 1 [MOD m] := by
      have h1 : (2 ^ Nat.totient m) ^ f ≡ 1 ^ f [MOD m] :=
        (Nat.ModEq.pow_totient hcop).pow f
      rw [one_pow] at h1
      have h2 : (2 ^ Nat.totient m) ^ f = 2 ^ k := by
        change (2 ^ Nat.totient m) ^ f = 2 ^ (f * Nat.totient m)
        rw [Nat.mul_comm, pow_mul]
      rwa [← h2]
    have hfixK : ∀ c : 𝕂, c ^ (2 ^ k) = c := by
      intro c
      have hq : 2 ^ k = (Nat.card 𝕂) ^ Nat.totient m := by
        change 2 ^ (f * Nat.totient m) = (Nat.card 𝕂) ^ Nat.totient m
        rw [← hcard, pow_mul]
      rw [hq, ← Fintype.card_eq_nat_card]
      exact FiniteField.pow_card_pow (Nat.totient m) c
    have hfixS : ∀ x ∈ S, x ^ (2 ^ k) = x := by
      intro x hxS
      refine Algebra.adjoin_induction (p := fun x _ => x ^ (2 ^ k) = x) ?_ ?_ ?_ ?_ hxS
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hy
        have hgm : (↑g : Matrix (Fin d) (Fin d) 𝕂) ^ m = 1 := by
          have h : g ^ m = 1 := by
            have h' := congrArg Subtype.val (pow_card_eq_one' (G := P) (x := ⟨g, hg⟩))
            simp only [Subgroup.coe_pow] at h'
            simpa [m] using h'
          have h2 := congrArg (fun u : GL (Fin d) 𝕂 => (u : Matrix (Fin d) (Fin d) 𝕂)) h
          simpa using h2
        have h := pow_eq_pow_of_modEq (x := (↑g : Matrix (Fin d) (Fin d) 𝕂)) hk_mod hgm
        rwa [pow_one] at h
      · intro r
        have hr : algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) r = Matrix.scalar (Fin d) r := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr, ← map_pow, hfixK r]
      · intro a b ha hb ha' hb'
        rw [add_pow_char_pow_of_commute (p := 2) (n := k) (hcomm a ha b hb), ha', hb']
      · intro a b ha hb ha' hb'
        rw [Commute.mul_pow (hcomm a ha b hb) (2 ^ k), ha', hb']
    intro x hxS hnil
    obtain ⟨n, hn⟩ := hnil
    have hiter : ∀ t : ℕ, x ^ ((2 ^ k) ^ t) = x := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, pow_mul, ih]; exact hfixS x hxS
    have h2k_ge_two : 2 ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_pos
    have hle : n ≤ (2 ^ k) ^ n :=
      (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left h2k_ge_two n)
    have hzero : x ^ ((2 ^ k) ^ n) = 0 := by
      rw [show (2 ^ k) ^ n = n + ((2 ^ k) ^ n - n) from (Nat.add_sub_cancel' hle).symm]
      rw [pow_add, hn, zero_mul]
    rw [hiter n] at hzero
    exact hzero

end CFSG.StandardType
