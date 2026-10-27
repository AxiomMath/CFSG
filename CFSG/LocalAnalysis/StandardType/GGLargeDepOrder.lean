module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
import CFSG.LocalAnalysis.StandardType.GGRCArith

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l04fD3_lin_aux : ∀ k : ℕ, 2 * (k + 13) ≤ 3 ^ (k + 9) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : (k + 1) + 13 = (k + 13) + 1 := by omega
    have h2 : (k + 1) + 9 = (k + 9) + 1 := by omega
    rw [h1, h2, pow_succ]
    nlinarith [ih]

private lemma l04fD3_lin (m : ℕ) (hm : 12 ≤ m) : 2 * (m + 1) ≤ 3 ^ (m - 3) := by
  have h := l04fD3_lin_aux (m - 12)
  have h1 : m - 12 + 13 = m + 1 := by omega
  have h2 : m - 12 + 9 = m - 3 := by omega
  rwa [h1, h2] at h

private lemma l04fD3_tri_aux (j : ℕ) : j + j * (j - 1) / 2 = (j + 1) * j / 2 := by
  have h1 : j * (j - 1) / 2 = j.choose 2 := (Nat.choose_two_right j).symm
  have h2 : (j + 1) * j / 2 = (j + 1).choose 2 := by
    rw [Nat.choose_two_right (j + 1)]
    simp
  rw [h1, h2, Nat.choose_succ_succ j 1, Nat.choose_one_right j]

private lemma l04fD3_tri (m : ℕ) (hm : 3 ≤ m) :
    (m - 2) + (m - 2) * (m - 3) / 2 = (m - 1) * (m - 2) / 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
  have h1 : 2 + j - 2 = j := by omega
  have h2 : 2 + j - 3 = j - 1 := by omega
  have h3 : 2 + j - 1 = j + 1 := by omega
  rw [h1, h2, h3]
  exact l04fD3_tri_aux j

private lemma l04fD3_base {p : ℕ} (hp3 : 3 ≤ p) :
    8 * (p ^ 12 * (6 * (p - 1) * (2 ^ 12 * Nat.factorial 12))) <
      p ^ ((12 - 2) * (12 - 3) / 2) := by
  have hp0 : 0 < p := by omega
  have hexp : (12 - 2) * (12 - 3) / 2 = 45 := by norm_num
  rw [hexp]
  have hcoef : 48 * (2 ^ 12 * Nat.factorial 12) < 3 ^ 32 := by norm_num
  have hcoefp : 48 * (2 ^ 12 * Nat.factorial 12) < p ^ 32 :=
    lt_of_lt_of_le hcoef (Nat.pow_le_pow_left hp3 32)
  calc
    8 * (p ^ 12 * (6 * (p - 1) * (2 ^ 12 * Nat.factorial 12)))
        ≤ 8 * (p ^ 12 * (6 * p * (2 ^ 12 * Nat.factorial 12))) := by
            gcongr
            exact Nat.sub_le p 1
    _ = 48 * (2 ^ 12 * Nat.factorial 12) * p ^ 13 := by ring
    _ < p ^ 32 * p ^ 13 := Nat.mul_lt_mul_of_pos_right hcoefp (pow_pos hp0 13)
    _ = p ^ 45 := by ring

private lemma l04fD3_step {p m : ℕ} (hp3 : 3 ≤ p) (hm : 12 ≤ m)
    (ih : 8 * (p ^ m * (6 * (p - 1) * (2 ^ m * m.factorial))) <
      p ^ ((m - 2) * (m - 3) / 2)) :
    8 * (p ^ (m + 1) * (6 * (p - 1) * (2 ^ (m + 1) * (m + 1).factorial))) <
      p ^ (((m + 1) - 2) * ((m + 1) - 3) / 2) := by
  have hp0 : 0 < p := by omega
  have htri : (m - 2) + (m - 2) * (m - 3) / 2 = (m - 1) * (m - 2) / 2 :=
    l04fD3_tri m (by omega)
  have hE : ((m + 1) - 2) * ((m + 1) - 3) / 2 = (m - 1) * (m - 2) / 2 := by
    have h1 : (m + 1) - 2 = m - 1 := by omega
    have h2 : (m + 1) - 3 = m - 2 := by omega
    rw [h1, h2]
  have hlin : 2 * (m + 1) ≤ 3 ^ (m - 3) := l04fD3_lin m hm
  have hbound : p * (2 * (m + 1)) ≤ p ^ (m - 2) := by
    calc
      p * (2 * (m + 1)) ≤ p * 3 ^ (m - 3) := Nat.mul_le_mul_left p hlin
      _ ≤ p * p ^ (m - 3) := Nat.mul_le_mul_left p (Nat.pow_le_pow_left hp3 (m - 3))
      _ = p ^ (m - 2) := by
            rw [mul_comm, ← pow_succ]
            congr 1
            omega
  have hident : 8 * (p ^ (m + 1) * (6 * (p - 1) * (2 ^ (m + 1) * (m + 1).factorial)))
      = p * (2 * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * (2 ^ m * m.factorial)))) := by
    rw [pow_succ, Nat.factorial_succ]
    ring
  calc
    8 * (p ^ (m + 1) * (6 * (p - 1) * (2 ^ (m + 1) * (m + 1).factorial)))
        = p * (2 * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * (2 ^ m * m.factorial)))) :=
          hident
    _ ≤ p ^ (m - 2) * (8 * (p ^ m * (6 * (p - 1) * (2 ^ m * m.factorial)))) :=
          Nat.mul_le_mul_right _ hbound
    _ < p ^ (m - 2) * p ^ ((m - 2) * (m - 3) / 2) :=
          Nat.mul_lt_mul_of_pos_left ih (pow_pos hp0 (m - 2))
    _ = p ^ ((m - 2) + (m - 2) * (m - 3) / 2) := by rw [← pow_add]
    _ = p ^ (((m + 1) - 2) * ((m + 1) - 3) / 2) := by rw [hE, ← htri]

lemma l04fD3_key12 {p N : ℕ} (hp3 : 3 ≤ p) (hN : 12 ≤ N) :
    8 * (p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial))) < p ^ ((N - 2) * (N - 3) / 2) := by
  refine Nat.le_induction (m := 12)
    (P := fun N _ => 8 * (p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial))) <
      p ^ ((N - 2) * (N - 3) / 2))
    (l04fD3_base hp3) ?step N hN
  intro m hm ih
  exact l04fD3_step hp3 hm ih

private lemma l04fD3_key {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ N) (hN : 11 ≤ N) :
    8 * (p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial))) < p ^ ((N - 2) * (N - 3) / 2) := by
  have hp3 : 3 ≤ p := by
    have h := hp.two_le
    omega
  rcases lt_or_ge N 12 with hlt | hge
  · have hN11 : N = 11 := by omega
    subst N
    have hp11 : p = 11 := by
      have h : p ∣ 11 := by simpa using hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11)).mp h
    rw [hp11]
    norm_num
  · exact l04fD3_key12 hp3 hge

theorem ggLargeDep_order {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) {d : ℕ} (hd1 : N - 2 ≤ d) (_hd2 : d ≤ N) :
    8 * Nat.card ↥(ggLargeGrp r s) < p ^ (d * (d - 1) / 2) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := C.lin.p_ne_two
  have hNge : 11 ≤ N := C.lin.N_ge
  have hpdvd : p ∣ N := C.lin.p_dvd
  have hcard : Nat.card ↥(ggLargeGrp r s) ≤
      p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial)) := by
    simpa only [GGLargeCardBound] using C.card
  have hkey := l04fD3_key hp hp2 hpdvd hNge
  have hexp : (N - 2) * (N - 3) / 2 ≤ d * (d - 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
  calc
    8 * Nat.card ↥(ggLargeGrp r s)
        < p ^ ((N - 2) * (N - 3) / 2) :=
          lt_of_le_of_lt (Nat.mul_le_mul_left 8 hcard) hkey
    _ ≤ p ^ (d * (d - 1) / 2) :=
          Nat.pow_le_pow_right (le_trans (by norm_num : 1 ≤ 2) hp.two_le) hexp

end CFSG.StandardType

end
