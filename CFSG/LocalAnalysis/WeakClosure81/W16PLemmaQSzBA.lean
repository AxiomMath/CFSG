module

public import CFSG.RepresentationTheory.SzMartineau.Relations
public import Mathlib.Algebra.CharP.Two

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix CFSG.CGT.PushingUpLit.SolKNA CFSG.RankThree.GF2n.SzExplicit
  CFSG.RepresentationTheory.SzMartineau

local macro "char2_norm" : tactic =>
  `(tactic| (ring_nf <;> try simp only [CharTwo.ofNat_eq_mod] <;> norm_num))

private abbrev matSz {a : ℕ} (g : ↥(Sz a)) : Matrix (Fin 4) (Fin 4) (F a) :=
  ((g : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a))

private lemma matSz_rootSz {a : ℕ} (u w : F a) : matSz (rootSz a u w) = rootMat a u w := rfl

private lemma mat_rootSz {a : ℕ} (u w : F a) :
    (((rootSz a u w : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      rootMat a u w := rfl

private lemma mat_torusSz {a : ℕ} (x : (F a)ˣ) :
    (((torusSz a x : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      torusMat a x := rfl

private lemma torusMat_mulVec (a : ℕ) (x : (F a)ˣ) (v : Fin 4 → F a) :
    torusMat a x *ᵥ v = ![(x : F a) ^ (1 + 2 ^ a) * v 0, (x : F a) ^ (2 ^ a) * v 1,
      ((x : F a) ^ (2 ^ a))⁻¹ * v 2, ((x : F a) ^ (1 + 2 ^ a))⁻¹ * v 3] := by
  ext i
  fin_cases i <;> simp [torusMat, Matrix.mulVec, Fin.sum_univ_four] <;> rfl

private lemma exists_pow_two_pow_ne_self (a : ℕ) {k : ℕ} (hk0 : 0 < k) (hk : k < 2 * a + 1) :
    ∃ u : F a, u ^ (2 ^ k) ≠ u := by
  classical
  haveI : Fintype (F a) := Fintype.ofFinite (F a)
  by_contra h
  rw [not_exists] at h
  simp only [ne_eq, not_not] at h
  let p : Polynomial (F a) := Polynomial.X ^ (2 ^ k) - Polynomial.X
  have hp : p ≠ 0 := by
    intro h0
    have h1 : (Polynomial.X ^ (2 ^ k) : Polynomial (F a)) = Polynomial.X := sub_eq_zero.mp h0
    have hdeg := congrArg Polynomial.natDegree h1
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at hdeg
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk0
    omega
  have hroots : p.roots.toFinset = Finset.univ := by
    ext u
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    simp only [Finset.mem_univ, iff_true]
    simp [p, h u]
  have hdeg : p.natDegree ≤ 2 ^ k := by
    calc p.natDegree ≤ max (Polynomial.X ^ (2 ^ k) : Polynomial (F a)).natDegree
          (Polynomial.X : Polynomial (F a)).natDegree := Polynomial.natDegree_sub_le _ _
      _ = max (2 ^ k) 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      _ = 2 ^ k := Nat.max_eq_left (Nat.one_le_two_pow)
  have hle : Nat.card (F a) ≤ 2 ^ k := by
    have h1 : (Finset.univ : Finset (F a)).card = Nat.card (F a) := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    rw [← h1, ← hroots]
    exact (Multiset.toFinset_card_le p.roots).trans ((Polynomial.card_roots' p).trans hdeg)
  rw [GaloisField.card 2 (2 * a + 1) (by omega)] at hle
  have hk' : 2 * a + 1 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  omega

private lemma add_self_eq_zero_vec (a : ℕ) (v : Fin 4 → F a) : v + v = 0 := by
  ext i
  show v i + v i = 0
  exact CharTwo.add_self_eq_zero (v i)

private lemma neg_eq_self_vec (a : ℕ) (v : Fin 4 → F a) : -v = v := by
  rw [neg_eq_iff_add_eq_zero]
  exact add_self_eq_zero_vec a v

private lemma nsmul_eq_self_of_odd_vec (a : ℕ) (v : Fin 4 → F a) {n : ℕ} (hn : Odd n) :
    n • v = v := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, add_nsmul, ih, two_nsmul,
        add_self_eq_zero_vec, add_zero]

theorem exists_eq_mulVec_sub_of_rootSz_torusSz {a : ℕ} (ha : 1 ≤ a)
    {δ : ↥(Sz a) → (Fin 4 → F a)}
    (hδ : ∀ x y : ↥(Sz a), δ (x * y) = δ x +
      (((x : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) *ᵥ δ y))
    (hδZ : ∀ b : F a, δ (rootSz a 0 b) = 0) :
    ∃ n : Fin 4 → F a,
      n 2 = 0 ∧ n 3 = 0 ∧
      (∀ u w : F a, δ (rootSz a u w) = rootMat a u w *ᵥ n - n) ∧
      (∀ x : (F a)ˣ, δ (torusSz a x) = torusMat a x *ᵥ n - n) := by
  classical
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    simp only [mul_one, Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one, one_mulVec] at h
    exact add_left_cancel (show δ 1 + δ 1 = δ 1 + 0 by rw [add_zero]; exact h.symm)
  let p : F a → F a := fun u => (δ (rootSz a u 0)) 0
  let r : F a → F a := fun u => (δ (rootSz a u 0)) 1
  have hmul0 : ∀ u w : F a, rootSz a u 0 * rootSz a 0 w = rootSz a u w := by
    intro u w
    rw [rootSz_mul_rootSz]
    congr 1 <;> simp
  have hcomm0 : ∀ u w : F a, rootSz a 0 w * rootSz a u 0 = rootSz a u 0 * rootSz a 0 w := by
    intro u w
    have h1 : rootSz a 0 w * rootSz a u 0 = rootSz a u w := by
      rw [rootSz_mul_rootSz]
      congr 1 <;> simp
    rw [h1, hmul0 u w]
  have hdep : ∀ u w : F a, δ (rootSz a u w) = δ (rootSz a u 0) := by
    intro u w
    rw [← hmul0 u w, hδ, hδZ w, Matrix.mulVec_zero, add_zero]
  have hconcat : ∀ u w : F a, rootMat a 0 w *ᵥ δ (rootSz a u 0) = δ (rootSz a u 0) := by
    intro u w
    calc rootMat a 0 w *ᵥ δ (rootSz a u 0)
        = matSz (rootSz a 0 w) *ᵥ δ (rootSz a u 0) := by rw [matSz_rootSz]
      _ = δ (rootSz a 0 w) + matSz (rootSz a 0 w) *ᵥ δ (rootSz a u 0) := by
          rw [hδZ w, zero_add]
      _ = δ (rootSz a 0 w * rootSz a u 0) := (hδ _ _).symm
      _ = δ (rootSz a u 0 * rootSz a 0 w) := by rw [hcomm0 u w]
      _ = δ (rootSz a u w) := by rw [hmul0 u w]
      _ = δ (rootSz a u 0) := hdep u w
  have h23 : ∀ u : F a, (δ (rootSz a u 0)) 2 = 0 ∧ (δ (rootSz a u 0)) 3 = 0 := by
    intro u
    have h3 : (δ (rootSz a u 0)) 3 = 0 := by
      have e := congrFun (hconcat u 1) 1
      rw [rootMat_mulVec] at e
      simp at e
      linear_combination e
    refine ⟨?_, h3⟩
    have e := congrFun (hconcat u 1) 0
    rw [rootMat_mulVec] at e
    simp [h3] at e
    linear_combination e
  have hvec : ∀ u : F a, δ (rootSz a u 0) = ![p u, r u, 0, 0] := by
    intro u
    ext i
    fin_cases i <;> simp [p, r, (h23 u).1, (h23 u).2]
  have hpadd : ∀ u c : F a, p (u + c) = p u + p c + u * r c := by
    intro u c
    have h1 : rootSz a u 0 * rootSz a c 0 = rootSz a (u + c) (u * c ^ 2 ^ (a + 1)) := by
      rw [rootSz_mul_rootSz]
      congr 1 <;> ring
    have h := hδ (rootSz a u 0) (rootSz a c 0)
    rw [h1, hdep (u + c) (u * c ^ 2 ^ (a + 1)), hvec c, mat_rootSz u 0, hvec u] at h
    have e := congrFun h 0
    rw [rootMat_mulVec] at e
    simp at e
    linear_combination e
  have hradd : ∀ u c : F a, r (u + c) = r u + r c := by
    intro u c
    have h1 : rootSz a u 0 * rootSz a c 0 = rootSz a (u + c) (u * c ^ 2 ^ (a + 1)) := by
      rw [rootSz_mul_rootSz]
      congr 1 <;> ring
    have h := hδ (rootSz a u 0) (rootSz a c 0)
    rw [h1, hdep (u + c) (u * c ^ 2 ^ (a + 1)), hvec c, mat_rootSz u 0, hvec u] at h
    have e := congrFun h 1
    rw [rootMat_mulVec] at e
    simp at e
    linear_combination e
  have hsym : ∀ u c : F a, u * r c = c * r u := by
    intro u c
    have h1 := hpadd u c
    have h2 := hpadd c u
    rw [add_comm c u] at h2
    have hsum : p u + p c + u * r c = p c + p u + c * r u := by rw [← h1, h2]
    linear_combination hsum
  have hrk : ∀ u : F a, r u = r 1 * u := by
    intro u
    have h := hsym u 1
    rw [one_mul] at h
    rw [← h]
    exact mul_comm u (r 1)
  have hpb : ∀ u c : F a, p (u + c) = p u + p c + r 1 * u * c := by
    intro u c
    rw [hpadd u c, hrk c]
    ring
  have hts : ∀ (x : (F a)ˣ) (u : F a),
      torusSz a x * rootSz a u 0 * (torusSz a x)⁻¹ = rootSz a ((x : F a) * u) 0 := by
    intro x u
    have h := torusSz_mul_rootSz a x u 0
    simp only [mul_zero] at h
    calc torusSz a x * rootSz a u 0 * (torusSz a x)⁻¹
        = (rootSz a ((x : F a) * u) 0 * torusSz a x) * (torusSz a x)⁻¹ := by rw [h]
      _ = rootSz a ((x : F a) * u) 0 := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hcomp : ∀ (x : (F a)ˣ) (u : F a) (i : Fin 4),
      (δ (torusSz a x) + torusMat a x *ᵥ δ (rootSz a u 0)) i =
      (δ (rootSz a ((x : F a) * u) 0) + rootMat a ((x : F a) * u) 0 *ᵥ
        δ (torusSz a x)) i := by
    intro x u i
    have h1 : δ (torusSz a x * rootSz a u 0) =
        δ (torusSz a x) + torusMat a x *ᵥ δ (rootSz a u 0) := by
      rw [hδ (torusSz a x) (rootSz a u 0), mat_torusSz]
    have h2 : δ (torusSz a x * rootSz a u 0) =
        δ (rootSz a ((x : F a) * u) 0) +
          rootMat a ((x : F a) * u) 0 *ᵥ δ (torusSz a x) := by
      have h := hδ (torusSz a x * rootSz a u 0 * (torusSz a x)⁻¹) (torusSz a x)
      have hassoc : (torusSz a x * rootSz a u 0 * (torusSz a x)⁻¹) * torusSz a x =
          torusSz a x * rootSz a u 0 := by group
      rw [hassoc, hts x u, mat_rootSz] at h
      exact h
    exact congrFun (h1.symm.trans h2) i
  have hd3 : ∀ x : (F a)ˣ, (δ (torusSz a x)) 3 = 0 := by
    intro x
    have e := hcomp x 1 2
    rw [mul_one, hvec 1, torusMat_mulVec, hvec x, rootMat_mulVec] at e
    simp at e
    have h0 : (x : F a) * (δ (torusSz a x)) 3 = 0 := by
      have h1 : (δ (torusSz a x)) 2 + 0 =
          (δ (torusSz a x)) 2 + (x : F a) * (δ (torusSz a x)) 3 := by simpa using e
      exact (add_left_cancel h1).symm
    exact (mul_eq_zero.mp h0).resolve_left (Units.ne_zero x)
  have hE1gen : ∀ (x : (F a)ˣ) (u : F a), (x : F a) ^ 2 ^ a * r u =
      r ((x : F a) * u) + ((x : F a) * u) ^ 2 ^ (a + 1) * (δ (torusSz a x)) 2 := by
    intro x u
    have e := hcomp x u 1
    rw [hvec u, hvec ((x : F a) * u), torusMat_mulVec, rootMat_mulVec] at e
    rw [hd3 x] at e
    simp at e
    linear_combination (norm := char2_norm) e
  have hd2 : ∀ x : (F a)ˣ, (δ (torusSz a x)) 2 = 0 := by
    intro x
    obtain ⟨y, hy⟩ := exists_pow_two_pow_ne_self a (k := a + 1) (by omega : 0 < a + 1)
      (by omega : a + 1 < 2 * a + 1)
    have hA := hE1gen x y
    have hB := hE1gen x 1
    rw [hrk y, hrk ((x : F a) * y)] at hA
    rw [mul_one, hrk x] at hB
    have hd2y : (x : F a) ^ 2 ^ (a + 1) * (δ (torusSz a x)) 2 *
        (y - y ^ 2 ^ (a + 1)) = 0 := by
      linear_combination (norm := char2_norm) hA - y * hB
    have h1 : (x : F a) ^ 2 ^ (a + 1) * (δ (torusSz a x)) 2 = 0 :=
      (mul_eq_zero.mp hd2y).resolve_right (sub_ne_zero.mpr (Ne.symm hy))
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (Units.ne_zero x))
  have hk : r 1 = 0 := by
    obtain ⟨x, hx⟩ := exists_pow_two_pow_ne_self a (k := a) (by omega : 0 < a)
      (by omega : a < 2 * a + 1)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by rw [zero_pow (by positivity)])
    have h := hE1gen (Units.mk0 x hx0) 1
    simp only [Units.val_mk0] at h
    rw [mul_one, hd2 (Units.mk0 x hx0), mul_zero, add_zero, hrk x] at h
    have hzero : r 1 * (x ^ 2 ^ a - x) = 0 := by
      linear_combination (norm := char2_norm) h
    exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hx)
  have hr0 : ∀ u : F a, r u = 0 := by
    intro u
    rw [hrk u, hk, zero_mul]
  have hpformula : ∀ (x : (F a)ˣ) u, p ((x : F a) * u) =
      (x : F a) ^ (1 + 2 ^ a) * p u + ((x : F a) * u) * (δ (torusSz a x)) 1 := by
    intro x u
    have e := hcomp x u 0
    rw [hvec u, hvec ((x : F a) * u), torusMat_mulVec, rootMat_mulVec] at e
    rw [hd3 x] at e
    simp at e
    have h1 : δ (torusSz a x) 0 + (x : F a) ^ (1 + 2 ^ a) * p u =
        δ (torusSz a x) 0 + (p ((x : F a) * u) +
          ((x : F a) * u) * δ (torusSz a x) 1) := by
      rw [e]; abel
    have h2 : (x : F a) ^ (1 + 2 ^ a) * p u =
        p ((x : F a) * u) + ((x : F a) * u) * δ (torusSz a x) 1 :=
      add_left_cancel h1
    have h3 : p ((x : F a) * u) =
        (x : F a) ^ (1 + 2 ^ a) * p u + ((x : F a) * u) * δ (torusSz a x) 1 := by
      have h4 := congrArg (fun z => z + ((x : F a) * u) * δ (torusSz a x) 1) h2
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h4
      exact h4.symm
    exact h3
  have hpu : ∀ (x : (F a)ˣ) u, p ((x : F a) * u) =
      (x : F a) ^ (1 + 2 ^ a) * p u + u * p x +
        u * ((x : F a) ^ (1 + 2 ^ a) * p 1) := by
    intro x u
    have h1 := hpformula x 1
    rw [mul_one] at h1
    have h2 := hpformula x u
    linear_combination (norm := char2_norm) h2 + u * h1
  have hp_lin : ∀ u : F a, p u = u * p 1 := by
    intro u
    obtain ⟨y, hy⟩ := exists_pow_two_pow_ne_self a (by omega : 0 < a)
      (by omega : a < 2 * a + 1)
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (by rw [zero_pow (by positivity)])
    have hy10 : (1 : F a) + y ≠ 0 := by
      intro h
      have : y = 1 := by linear_combination (norm := char2_norm) h
      exact hy (by rw [this, one_pow])
    have hp1y : p (1 + y) = p 1 + p y := by rw [hpb 1 y, hk]; ring
    have e1 := hpu (Units.mk0 (1 + y) hy10) u
    have e2 := hpu 1 u
    have e3 := hpu (Units.mk0 y hy0) u
    simp only [Units.val_mk0] at e1 e3
    simp only [Units.val_one, one_mul, one_pow] at e2
    have hadd : p ((1 + y) * u) = p (1 * u) + p (y * u) := by
      rw [show (1 + y) * u = 1 * u + y * u by ring, hpb, hk]
      ring
    simp only [one_mul] at hadd
    rw [e1, e2, e3, hp1y] at hadd
    rw [show (1 + y) ^ (1 + 2 ^ a) = (1 + y) * (1 + y) ^ 2 ^ a by
      rw [pow_add, pow_one]] at hadd
    rw [add_pow_char_pow] at hadd
    simp only [one_pow] at hadd
    have hzero : (y ^ 2 ^ a - y) * (p u + u * p 1) = 0 := by
      linear_combination (norm := char2_norm) hadd
    have hne : y ^ 2 ^ a - y ≠ 0 := sub_ne_zero.mpr hy
    have hsum : p u + u * p 1 = 0 := (mul_eq_zero.mp hzero).resolve_left hne
    linear_combination (norm := char2_norm) hsum
  let n0 : Fin 4 → F a := ![0, p 1, 0, 0]
  have hn0_2 : n0 2 = 0 := rfl
  have hn0_3 : n0 3 = 0 := rfl
  have hroot : ∀ u w : F a, δ (rootSz a u w) = rootMat a u w *ᵥ n0 - n0 := by
    intro u w
    rw [hdep u w, hvec u, hr0 u, hp_lin u]
    ext i
    fin_cases i <;> simp [n0, rootMat_mulVec]
  have hrootfix : ∀ (u w : F a) (v : Fin 4 → F a), v 1 = 0 → v 2 = 0 → v 3 = 0 →
      rootMat a u w *ᵥ v = v := by
    intro u w v hv1 hv2 hv3
    rw [rootMat_mulVec]
    ext i
    fin_cases i <;> simp [hv1, hv2, hv3]
  let δ₁ : ↥(Sz a) → (Fin 4 → F a) := fun g => δ g - (matSz g *ᵥ n0 - n0)
  have hδ₁ : ∀ x y : ↥(Sz a), δ₁ (x * y) = δ₁ x + matSz x *ᵥ δ₁ y := by
    intro x y
    simp only [δ₁, matSz]
    rw [hδ x y, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub]
    abel
  have hδ₁_root : ∀ u w : F a, δ₁ (rootSz a u w) = 0 := by
    intro u w
    simp only [δ₁, matSz_rootSz, hroot u w, sub_self]
  have hflag : ∀ x : (F a)ˣ, (δ₁ (torusSz a x)) 1 = 0 ∧ (δ₁ (torusSz a x)) 2 = 0 ∧
      (δ₁ (torusSz a x)) 3 = 0 := by
    intro x
    have hc : (x : F a) ^ (1 + 2 ^ (a + 1)) ≠ 0 := pow_ne_zero _ (Units.ne_zero x)
    have hf1 : matSz (rootSz a 1 0) *ᵥ δ₁ (torusSz a x) = δ₁ (torusSz a x) := by
      have h1 := hδ₁ (torusSz a x) (rootSz a x⁻¹ 0)
      have h2 := hδ₁ (torusSz a x * rootSz a x⁻¹ 0 * (torusSz a x)⁻¹) (torusSz a x)
      have hassoc : (torusSz a x * rootSz a x⁻¹ 0 * (torusSz a x)⁻¹) * torusSz a x =
          torusSz a x * rootSz a x⁻¹ 0 := by group
      rw [hassoc] at h2
      have hconj : torusSz a x * rootSz a x⁻¹ 0 * (torusSz a x)⁻¹ = rootSz a 1 0 := by
        have hc' := torusSz_mul_rootSz a x x⁻¹ 0
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero x),
          Units.val_one, mul_zero] at hc'
        calc torusSz a x * rootSz a x⁻¹ 0 * (torusSz a x)⁻¹
            = (rootSz a 1 0 * torusSz a x) * (torusSz a x)⁻¹ := by rw [hc']
          _ = rootSz a 1 0 := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hconj, hδ₁_root 1 0, zero_add] at h2
      rw [hδ₁_root x⁻¹ 0, Matrix.mulVec_zero, add_zero] at h1
      exact (h1.symm.trans h2).symm
    have hf2 : matSz (rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)))) *ᵥ δ₁ (torusSz a x) =
        δ₁ (torusSz a x) := by
      have h1 := hδ₁ (torusSz a x) (rootSz a 0 1)
      have h2 := hδ₁ (torusSz a x * rootSz a 0 1 * (torusSz a x)⁻¹) (torusSz a x)
      have hassoc : (torusSz a x * rootSz a 0 1 * (torusSz a x)⁻¹) * torusSz a x =
          torusSz a x * rootSz a 0 1 := by group
      rw [hassoc] at h2
      have hconj : torusSz a x * rootSz a 0 1 * (torusSz a x)⁻¹ =
          rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1))) := by
        have hc' := torusSz_mul_rootSz a x 0 1
        simp only [mul_zero, mul_one] at hc'
        calc torusSz a x * rootSz a 0 1 * (torusSz a x)⁻¹
            = (rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1))) * torusSz a x) *
                (torusSz a x)⁻¹ := by rw [hc']
          _ = rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1))) := by
              rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hconj, hδ₁_root 0 ((x : F a) ^ (1 + 2 ^ (a + 1))), zero_add] at h2
      rw [hδ₁_root 0 1, Matrix.mulVec_zero, add_zero] at h1
      exact (h1.symm.trans h2).symm
    have h3 : (δ₁ (torusSz a x)) 3 = 0 := by
      have e := congrFun hf2 1
      rw [matSz_rootSz, rootMat_mulVec] at e
      simp at e
      have hcv : (x : F a) ^ (1 + 2 ^ (a + 1)) * (δ₁ (torusSz a x)) 3 = 0 := by
        have hh : (δ₁ (torusSz a x)) 1 +
            (x : F a) ^ (1 + 2 ^ (a + 1)) * (δ₁ (torusSz a x)) 3 =
            (δ₁ (torusSz a x)) 1 + 0 := by rw [add_zero]; simpa using e
        exact add_left_cancel hh
      exact (mul_eq_zero.mp hcv).resolve_left hc
    have h2 : (δ₁ (torusSz a x)) 2 = 0 := by
      have e := congrFun hf2 0
      rw [matSz_rootSz, rootMat_mulVec] at e
      simp [h3] at e
      have hcv : (x : F a) ^ (1 + 2 ^ (a + 1)) * (δ₁ (torusSz a x)) 2 = 0 := by
        have hh : (δ₁ (torusSz a x)) 0 +
            (x : F a) ^ (1 + 2 ^ (a + 1)) * (δ₁ (torusSz a x)) 2 =
            (δ₁ (torusSz a x)) 0 + 0 := by rw [add_zero]; simpa using e
        exact add_left_cancel hh
      exact (mul_eq_zero.mp hcv).resolve_left hc
    have h1 : (δ₁ (torusSz a x)) 1 = 0 := by
      have e := congrFun hf1 0
      rw [matSz_rootSz, rootMat_mulVec] at e
      simp [h3] at e
      have hh : (δ₁ (torusSz a x)) 0 + (δ₁ (torusSz a x)) 1 =
          (δ₁ (torusSz a x)) 0 + 0 := by rw [add_zero]; simpa using e
      exact add_left_cancel hh
    exact ⟨h1, h2, h3⟩
  haveI : Fintype (F a) := Fintype.ofFinite (F a)
  have hodd : Odd (Fintype.card (F a)ˣ) := by
    rw [Fintype.card_units]
    have hcard : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 (2 * a + 1) (by omega)
    rw [hcard]
    refine ⟨2 ^ (2 * a) - 1, ?_⟩
    have h2 : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by rw [pow_succ]; ring
    rw [h2]
    have hX : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
    omega
  let m : Fin 4 → F a := ∑ y : (F a)ˣ, δ₁ (torusSz a y)
  have hmflag : m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 0 := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [m]; rw [Finset.sum_apply]
      exact Finset.sum_eq_zero (fun y _ => (hflag y).1)
    · dsimp only [m]; rw [Finset.sum_apply]
      exact Finset.sum_eq_zero (fun y _ => (hflag y).2.1)
    · dsimp only [m]; rw [Finset.sum_apply]
      exact Finset.sum_eq_zero (fun y _ => (hflag y).2.2)
  have hδ₁torus : ∀ x : (F a)ˣ, δ₁ (torusSz a x) = matSz (torusSz a x) *ᵥ m + m := by
    intro x
    have hterm : ∀ y : (F a)ˣ, matSz (torusSz a x) *ᵥ δ₁ (torusSz a y) =
        δ₁ (torusSz a (x * y)) + δ₁ (torusSz a x) := by
      intro y
      have h := hδ₁ (torusSz a x) (torusSz a y)
      rw [torusSz_mul_torusSz] at h
      linear_combination (norm := char2_norm) h
    have hsum : matSz (torusSz a x) *ᵥ m = m + δ₁ (torusSz a x) := by
      dsimp only [m]
      rw [Matrix.mulVec_sum]
      rw [Finset.sum_congr rfl (fun y _ => hterm y)]
      rw [Finset.sum_add_distrib]
      rw [Fintype.sum_equiv (Equiv.mulLeft x)
        (fun y => δ₁ (torusSz a (x * y))) (fun y => δ₁ (torusSz a y)) (fun y => rfl)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_self_of_odd_vec a _ hodd]
    have h' : matSz (torusSz a x) *ᵥ m + m = δ₁ (torusSz a x) := by
      linear_combination (norm := char2_norm) hsum
    exact h'.symm
  refine ⟨n0 + m, ?_, ?_, ?_, ?_⟩
  · show (n0 + m) 2 = 0
    rw [Pi.add_apply, hmflag.2.1, hn0_2, add_zero]
  · show (n0 + m) 3 = 0
    rw [Pi.add_apply, hmflag.2.2, hn0_3, add_zero]
  · intro u w
    rw [hroot u w]
    have hfix : rootMat a u w *ᵥ m = m := hrootfix u w m hmflag.1 hmflag.2.1 hmflag.2.2
    rw [Matrix.mulVec_add, hfix]
    abel
  · intro x
    have hδeq : δ (torusSz a x) = δ₁ (torusSz a x) +
        (matSz (torusSz a x) *ᵥ n0 - n0) := by
      simp only [δ₁]; abel
    rw [hδeq, hδ₁torus x]
    simp only [matSz]
    rw [mat_torusSz x, Matrix.mulVec_add]
    simp only [sub_eq_add_neg, neg_eq_self_vec]
    abel

end CFSG.LocalAnalysis.WeakClosure81

end
