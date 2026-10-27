module

public import CFSG.Quasithin.H13.L32NItems1442Models
public import CFSG.Quasithin.H13.L32NMat8
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.H13.L1442Q

open Matrix L1442M Mat8Cert

@[expose] noncomputable def polarB (Q : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) (Fin 8 → ZMod 2) :=
  Matrix.toLinearMap₂' (ZMod 2) (Q + Qᵀ)

theorem polarB_apply (Q : Matrix (Fin 8) (Fin 8) (ZMod 2)) (x y : Fin 8 → ZMod 2) :
    polarB Q x y = quadOf Q (x + y) + quadOf Q x + quadOf Q y := by
  have hx := CharTwo.add_self_eq_zero (x ⬝ᵥ (Q *ᵥ x))
  have hy := CharTwo.add_self_eq_zero (y ⬝ᵥ (Q *ᵥ y))
  have e1 : x ⬝ᵥ (Qᵀ *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  simp only [polarB, Matrix.toLinearMap₂'_apply', quadOf, Matrix.add_mulVec, dotProduct_add,
    Matrix.mulVec_add, add_dotProduct, e1]
  linear_combination -(hx + hy)

theorem polarB_def (Q : Matrix (Fin 8) (Fin 8) (ZMod 2)) (x y : Fin 8 → ZMod 2) :
    polarB Q x y = x ⬝ᵥ ((Q + Qᵀ) *ᵥ y) :=
  Matrix.toLinearMap₂'_apply' _ x y

theorem polarB_sub_left (Q : Matrix (Fin 8) (Fin 8) (ZMod 2)) (x x' y : Fin 8 → ZMod 2) :
    polarB Q (x - x') y = polarB Q x y - polarB Q x' y := by
  rw [polarB_def, polarB_def, polarB_def, sub_dotProduct]

theorem polarB_zero_left (Q : Matrix (Fin 8) (Fin 8) (ZMod 2)) (y : Fin 8 → ZMod 2) :
    polarB Q 0 y = 0 := by
  rw [polarB_def, zero_dotProduct]

theorem exists_eq_quad {S : Set (GL (Fin 8) (ZMod 2))} {Q₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hinv₀ : ∀ g ∈ S, ∀ x, quadOf Q₀ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) = quadOf Q₀ x)
    (hnd₀ : (polarB Q₀).Nondegenerate) {Minv : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hMinv : (Q₀ + Q₀ᵀ) * Minv = 1)
    {L : List (Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 8) (Fin 8) (ZMod 2))}
    (hcomm : ∀ A : Matrix (Fin 8) (Fin 8) (ZMod 2),
      (∀ g ∈ S, A * (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) * A) → A = 0 ∨ ∃ p ∈ L, A = p.1)
    (hLpol : ∀ p ∈ L, ∀ x y, quadOf Q₀ (p.2 *ᵥ (x + y)) + quadOf Q₀ (p.2 *ᵥ x) +
      quadOf Q₀ (p.2 *ᵥ y) = polarB Q₀ (p.1 *ᵥ y) x)
    (hLinv : ∀ p ∈ L, ∀ g ∈ S, ∀ x,
      quadOf Q₀ (p.2 *ᵥ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)) = quadOf Q₀ (p.2 *ᵥ x))
    (hcov : ∀ w : Fin 8 → ZMod 2,
      (∀ g ∈ S, (g : Matrix (Fin 8) (Fin 8) (ZMod 2))ᵀ *ᵥ w = w) → w = 0)
    {Q' : (Fin 8 → ZMod 2) → ZMod 2} {B' : LinearMap.BilinForm (ZMod 2) (Fin 8 → ZMod 2)}
    (hQ' : ∀ x y, Q' (x + y) = Q' x + Q' y + B' x y) (hB' : B' ≠ 0)
    (hinv' : ∀ g ∈ S, ∀ x, Q' ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) = Q' x) :
    ∃ p ∈ L, ∀ x, Q' x = quadOf Q₀ (p.2 *ᵥ x) := by
  classical
  have hB'inv : ∀ g ∈ S, ∀ x y,
      B' ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ y) =
        B' x y := by
    intro g hg x y
    have h1 := hQ' ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)
      ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ y)
    rw [← Matrix.mulVec_add, hinv' g hg, hinv' g hg, hinv' g hg, hQ' x y] at h1
    linear_combination -h1
  have hB₀inv : ∀ g ∈ S, ∀ x y,
      polarB Q₀ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)
        ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ y) = polarB Q₀ x y := by
    intro g hg x y
    rw [polarB_apply, polarB_apply, ← Matrix.mulVec_add, hinv₀ g hg, hinv₀ g hg, hinv₀ g hg]
  obtain ⟨M', hM'⟩ : ∃ M', M' = LinearMap.toMatrix₂' (ZMod 2) B' := ⟨_, rfl⟩
  have hB'mat : ∀ u v, B' u v = u ⬝ᵥ (M' *ᵥ v) := by
    intro u v
    have h1 : Matrix.toLinearMap₂' (ZMod 2) M' = B' := by
      rw [hM']
      exact (LinearMap.toMatrix₂' (ZMod 2)).symm_apply_apply B'
    rw [← Matrix.toLinearMap₂'_apply', h1]
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = Minv * M' := ⟨_, rfl⟩
  have hsym : (Q₀ + Q₀ᵀ)ᵀ = Q₀ + Q₀ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hvm : ∀ u, ((Q₀ + Q₀ᵀ) *ᵥ u) ᵥ* Minv = u := by
    intro u
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hsym, hMinv, Matrix.vecMul_one]
  have hA : ∀ u v, polarB Q₀ (Am *ᵥ v) u = B' u v := by
    intro u v
    rw [polarB_def, dotProduct_comm, hAm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvm,
      hB'mat]
  have hginv : ∀ g : GL (Fin 8) (ZMod 2), ∀ u,
      (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (((g⁻¹ : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u) = u := by
    intro g u
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hAcomm : ∀ g ∈ S, ∀ v, Am *ᵥ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) =
      (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (Am *ᵥ v) := by
    intro g hg v
    refine sub_eq_zero.mp (hnd₀.1 _ fun u => ?_)
    have h1 : polarB Q₀ (Am *ᵥ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) u =
        polarB Q₀ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (Am *ᵥ v)) u := by
      rw [hA, ← hginv g u, hB'inv g hg, ← hA, ← hB₀inv g hg, hginv g u]
    rw [polarB_sub_left, h1, sub_self]
  have hAmcomm : ∀ g ∈ S, Am * (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) * Am := by
    intro g hg
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hAcomm g hg]
  rcases hcomm Am hAmcomm with h0 | ⟨p, hpL, hp⟩
  · exfalso
    apply hB'
    refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
    rw [← hA, h0, Matrix.zero_mulVec, polarB_zero_left]
    rfl
  refine ⟨p, hpL, ?_⟩
  have hB'p : ∀ x y, B' x y = polarB Q₀ (p.1 *ᵥ y) x := fun x y => by
    rw [← hp, hA]
  let ℓ : (Fin 8 → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => Q' x + quadOf Q₀ (p.2 *ᵥ x)
      map_zero' := by
        have h0 := hQ' 0 0
        have hb0 : B' 0 0 = 0 := by simp
        rw [add_zero, hb0, add_zero] at h0
        have hQ0 : Q' 0 = 0 := by linear_combination -h0
        simp [hQ0, quadOf]
      map_add' := fun x y => by
        have h1 := hLpol p hpL x y
        have h2 := hB'p x y
        show Q' (x + y) + quadOf Q₀ (p.2 *ᵥ (x + y)) =
          Q' x + quadOf Q₀ (p.2 *ᵥ x) + (Q' y + quadOf Q₀ (p.2 *ᵥ y))
        rw [hQ', h2]
        have h3 := CharTwo.add_self_eq_zero (polarB Q₀ (p.1 *ᵥ y) x)
        have h4 := CharTwo.add_self_eq_zero (quadOf Q₀ (p.2 *ᵥ x))
        have h5 := CharTwo.add_self_eq_zero (quadOf Q₀ (p.2 *ᵥ y))
        linear_combination h1 + h3 - h4 - h5 }
  have hℓ : ∀ x, ℓ x = Q' x + quadOf Q₀ (p.2 *ᵥ x) := fun x => rfl
  have hℓinv : ∀ g ∈ S, ∀ x, ℓ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) = ℓ x := by
    intro g hg x
    rw [hℓ, hℓ, hinv' g hg, hLinv p hpL g hg]
  set w : Fin 8 → ZMod 2 := fun i => ℓ (Pi.single i 1) with hw
  have hsmul : ∀ (c : ZMod 2) v, ℓ (c • v) = c * ℓ v := by
    intro c v
    fin_cases c
    · show ℓ ((0 : ZMod 2) • v) = (0 : ZMod 2) * ℓ v
      rw [zero_smul, map_zero, zero_mul]
    · show ℓ ((1 : ZMod 2) • v) = (1 : ZMod 2) * ℓ v
      rw [one_smul, one_mul]
  have hei : ∀ i : Fin 8, (fun j => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  have hℓw : ∀ x, ℓ x = w ⬝ᵥ x := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, mul_comm, hei, hw]
  have hwfix : ∀ g ∈ S, (g : Matrix (Fin 8) (Fin 8) (ZMod 2))ᵀ *ᵥ w = w := by
    intro g hg
    funext i
    have h1 := hℓinv g hg (Pi.single i 1)
    rw [hℓw, hℓw, Matrix.dotProduct_mulVec, dotProduct_single, mul_one,
      dotProduct_single, mul_one] at h1
    rw [← h1, Matrix.mulVec_transpose]
  have hw0 := hcov w hwfix
  intro x
  have h1 := hℓw x
  rw [hw0, zero_dotProduct, hℓ] at h1
  linear_combination h1 - CharTwo.add_self_eq_zero (quadOf Q₀ (p.2 *ᵥ x))

theorem inv_of_codes {Q₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)} {qN : ℕ → Bool}
    (hq : ∀ n, b2z (qN n) = quadOf Q₀ (vec8 n)) {g : GL (Fin 8) (ZMod 2)}
    (h : ∀ n < 256, qN (mv8 (colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2))) n) = qN n) :
    ∀ x, quadOf Q₀ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) = quadOf Q₀ x := by
  intro x
  rw [← vec8_code8 x, mulVec_vec8, ← hq, ← hq, h _ (code8_lt x)]

theorem polarB_vec8 {Q₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)} {qN : ℕ → Bool}
    (hq : ∀ n, b2z (qN n) = quadOf Q₀ (vec8 n)) (n m : ℕ) :
    polarB Q₀ (vec8 n) (vec8 m) = b2z (qN (n ^^^ m) ^^ qN n ^^ qN m) := by
  rw [polarB_apply, ← vec8_xor, b2z_xor, b2z_xor, hq, hq, hq]

theorem polarB_symm (Q : Matrix (Fin 8) (Fin 8) (ZMod 2)) (x y : Fin 8 → ZMod 2) :
    polarB Q x y = polarB Q y x := by
  rw [polarB_apply, polarB_apply, add_comm x y]
  ring

theorem nondeg_of_codes {Q₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)} {qN : ℕ → Bool}
    (hq : ∀ n, b2z (qN n) = quadOf Q₀ (vec8 n))
    (h : ∀ n < 256, n ≠ 0 → ∃ k < 8, (qN (n ^^^ 2 ^ k) ^^ qN n ^^ qN (2 ^ k)) = true) :
    (polarB Q₀).Nondegenerate := by
  have hleft : ∀ x : Fin 8 → ZMod 2, (∀ y, polarB Q₀ x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    have hn : code8 x ≠ 0 := fun h0 => hne (by rw [← vec8_code8 x, h0, vec8_zero])
    obtain ⟨k, -, hk⟩ := h _ (code8_lt x) hn
    have h1 := hx (vec8 (2 ^ k))
    rw [← vec8_code8 x, polarB_vec8 hq, hk] at h1
    exact absurd h1 (by decide)
  exact ⟨hleft, fun y hy => hleft y fun x => by rw [polarB_symm]; exact hy x⟩

theorem comm_evalW {gens : List (List ℕ)} {A : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hA : ∀ c ∈ gens, A * dec8 c = dec8 c * A) (w : List ℕ) :
    A * dec8 (evalW gens w) = dec8 (evalW gens w) * A := by
  induction w with
  | nil => rw [show evalW gens [] = one8 from rfl, dec8_one8, Matrix.mul_one, Matrix.one_mul]
  | cons i w ih =>
    rw [evalW_cons, dec8_mul8 _ _ (length_evalW gens w)]
    have hi : A * dec8 (gens.getD i one8) = dec8 (gens.getD i one8) * A := by
      by_cases hlt : i < gens.length
      · rw [List.getD_eq_getElem _ _ hlt]
        exact hA _ (List.getElem_mem hlt)
      · rw [List.getD_eq_default _ _ (by omega), dec8_one8, Matrix.mul_one, Matrix.one_mul]
    rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, ih, Matrix.mul_assoc]

@[expose] def colsM (mats : List (List ℕ)) (v : ℕ) : List ℕ :=
  mats.map fun W => mv8 W v

theorem comm_of_codes {gens mats ws : List (List ℕ)} {allowed : List ℕ}
    (hval : ∀ c ∈ gens, Valid8 c) (hlen : mats.length = 8)
    (hmats : ∀ i < 8, mats.getD i [] = evalW gens (ws.getD i []))
    (hbasis : ∀ i < 8, mv8 (mats.getD i []) 1 = 2 ^ i)
    (h : ∀ v < 256, (∀ c ∈ gens, mul8 (colsM mats v) c = mul8 c (colsM mats v)) →
      v ∈ allowed)
    {A : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hA : ∀ c ∈ gens, A * dec8 c = dec8 c * A) :
    ∃ v ∈ allowed, A = dec8 (colsM mats v) := by
  obtain ⟨v, hv⟩ : ∃ v, v = code8 (A *ᵥ vec8 1) := ⟨_, rfl⟩
  have hcol : ∀ i < 8, A *ᵥ vec8 (2 ^ i) = vec8 (mv8 (mats.getD i []) v) := by
    intro i hi
    rw [← hbasis i hi, ← dec8_mulVec, Matrix.mulVec_mulVec, hmats i hi, comm_evalW hA,
      ← Matrix.mulVec_mulVec, ← vec8_code8 (A *ᵥ vec8 1), dec8_mulVec, ← hv, ← hmats i hi]
  have hsingle : ∀ i : Fin 8, vec8 (2 ^ (i : ℕ)) = Pi.single i 1 := by
    intro i
    funext k
    simp only [vec8, Nat.testBit_two_pow, Pi.single_apply]
    by_cases hik : k = i
    · subst hik; simp [b2z]
    · have : ¬ ((i : ℕ) = k) := fun h => hik (Fin.ext h).symm
      simp [b2z, this, hik]
  have hAeq : A = dec8 (colsM mats v) := by
    ext r i
    have h1 := congrFun (hcol i i.2) r
    rw [hsingle, Matrix.mulVec_single_one, Matrix.col_apply] at h1
    have hi : (i : ℕ) < mats.length := by rw [hlen]; exact i.2
    have hiW : (i : ℕ) < (colsM mats v).length := by
      rw [colsM, List.length_map]; exact hi
    have hget : (colsM mats v).getD i 0 = mv8 (mats.getD i []) v := by
      rw [List.getD_eq_getElem _ _ hiW, List.getD_eq_getElem _ _ hi]
      simp [colsM]
    rw [h1, dec8, Matrix.of_apply, hget]
  refine ⟨v, h v (by rw [hv]; exact code8_lt _) fun c hc => ?_, hAeq⟩
  have hlenW : (colsM mats v).length = 8 := by rw [colsM, List.length_map, hlen]
  have hvalW : Valid8 (colsM mats v) := by
    refine ⟨hlenW, fun x hx => ?_⟩
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hW
    have hi8 : i < 8 := hlen ▸ hi
    have := hmats i hi8
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this]
    exact mv8_lt (valid8_evalW gens hval _) v
  have h1 := hA c hc
  rw [hAeq, ← dec8_mul8 _ _ (hval c hc).1, ← dec8_mul8 _ _ hlenW] at h1
  exact dec8_injOn (valid8_mul8 hvalW (hval c hc)) (valid8_mul8 (hval c hc) hvalW) h1

end CFSG.Quasithin.H13.L1442Q
