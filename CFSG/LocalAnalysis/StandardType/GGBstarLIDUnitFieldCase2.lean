module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldIso

public section

namespace CFSG.StandardType

namespace LIDUF

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Foote.ModuleExclusions

variable {K : Type} [Field K] {d : ℕ}

section Iter

variable (φ : K →+* K)

theorem semF_iterate (φe : K ≃+* K) (hφe : ∀ x, φe x = φ x) (B : Matrix (Fin d) (Fin d) K)
    (m : ℕ) (x : Fin d → K) :
    (semF φ B)^[m] x = (Ai φe B m) *ᵥ (fun k => (φe ^ m) (x k)) := by
  induction m with
  | zero =>
    simp [Ai]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 : (fun k => φ (((Ai φe B m) *ᵥ (fun k => (φe ^ m) (x k))) k)) =
        ((Ai φe B m).map φe) *ᵥ (fun k => (φe ^ (m + 1)) (x k)) := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hφe, ← hφe, pow_succ', RingAut.mul_apply]
    rw [semF, h1, Matrix.mulVec_mulVec]
    rfl

theorem herm_iterate (b : K →+* K) (hφb : ∀ x, φ (b x) = b (φ x))
    {A : Matrix (Fin d) (Fin d) K} (hA : adjM b A * A = 1) (m : ℕ) (x y : Fin d → K) :
    herm b ((semF φ A)^[m] x) ((semF φ A)^[m] y) = φ^[m] (herm b x y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', herm_semF b φ hφb hA, ih,
      Function.iterate_succ_apply']

end Iter

theorem herm_single (b : K →+* K) (i l : Fin d) (a c : K) :
    herm b (Pi.single i a) (Pi.single l c) = if i = l then b a * c else 0 := by
  classical
  unfold herm
  by_cases hil : i = l
  · subst hil
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Pi.single_apply, hk]
    · simp
  · rw [if_neg hil]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [Pi.single_apply, Ne.symm hil]
    · simp [Pi.single_apply, hk]

theorem herm_pair_self [CharP K 2] (b : K →+* K) {i j : Fin d} (hij : i ≠ j) :
    herm b (Pi.single i (1 : K) + Pi.single j (1 : K))
      (Pi.single i (1 : K) + Pi.single j (1 : K)) = 0 := by
  simp only [herm_add_left, herm_add_right, herm_single, if_true, if_neg hij,
    if_neg (Ne.symm hij), map_one, mul_one]
  have : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  linear_combination this

section Diag

variable {p : ℕ}

theorem semF_diagonal (φ : K →+* K) {B : Matrix (Fin d) (Fin d) K} {σ : Fin d → K} {c : K}
    (hσφ : ∀ k, φ (σ k) = σ k) (hc : B * Matrix.diagonal σ = c • (Matrix.diagonal σ * B))
    (y : Fin d → K) :
    semF φ B (Matrix.diagonal σ *ᵥ y) = c • (Matrix.diagonal σ *ᵥ semF φ B y) := by
  have h1 : (fun k => φ ((Matrix.diagonal σ *ᵥ y) k)) =
      Matrix.diagonal σ *ᵥ (fun k => φ (y k)) := by
    funext k
    simp [Matrix.mulVec_diagonal, hσφ k]
  rw [semF, h1, Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  rfl

theorem conj_pow_diagonal {B : Matrix (Fin d) (Fin d) K} {σ : Fin d → K} {c : K}
    (hc : B * Matrix.diagonal σ = c • (Matrix.diagonal σ * B)) (m : ℕ) :
    B * (Matrix.diagonal σ) ^ m = c ^ m • ((Matrix.diagonal σ) ^ m * B) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc B * (Matrix.diagonal σ) ^ (m + 1)
        = (B * (Matrix.diagonal σ) ^ m) * Matrix.diagonal σ := by rw [pow_succ, Matrix.mul_assoc]
      _ = (c ^ m • ((Matrix.diagonal σ) ^ m * B)) * Matrix.diagonal σ := by rw [ih]
      _ = c ^ m • ((Matrix.diagonal σ) ^ m * (B * Matrix.diagonal σ)) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = c ^ m • ((Matrix.diagonal σ) ^ m * (c • (Matrix.diagonal σ * B))) := by rw [hc]
      _ = c ^ (m + 1) • ((Matrix.diagonal σ) ^ (m + 1) * B) := by
          rw [Matrix.mul_smul, smul_smul, ← pow_succ, pow_succ (Matrix.diagonal σ) m,
            Matrix.mul_assoc]

theorem pow_eq_one_of_conj {B : Matrix (Fin d) (Fin d) K} (hB : B ≠ 0) {σ : Fin d → K} {c : K}
    (hσ : ∀ k, σ k ^ p = 1) (hc : B * Matrix.diagonal σ = c • (Matrix.diagonal σ * B)) :
    c ^ p = 1 := by
  have h1 := conj_pow_diagonal hc p
  have h2 : (Matrix.diagonal σ) ^ p = 1 := by
    rw [Matrix.diagonal_pow]
    have : (σ ^ p) = 1 := funext fun k => by simpa using hσ k
    rw [this]
    rfl
  rw [h2, Matrix.mul_one, Matrix.one_mul] at h1
  by_contra hne
  have hdiff : c ^ p - 1 ≠ 0 := sub_ne_zero.mpr hne
  apply hB
  ext k l
  have := congrFun (congrFun h1 k) l
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  have h3 : (c ^ p - 1) * B k l = 0 := by linear_combination -this
  simpa [hdiff] using h3

theorem eigen_succ (φ : K →+* K) {B : Matrix (Fin d) (Fin d) K} {σ : Fin d → K} {c : K}
    (hσφ : ∀ k, φ (σ k) = σ k) (hc : B * Matrix.diagonal σ = c • (Matrix.diagonal σ * B))
    (hc0 : c ≠ 0) {y : Fin d → K} {lam : K} (hy : Matrix.diagonal σ *ᵥ y = lam • y)
    (hlam : φ lam = lam) :
    Matrix.diagonal σ *ᵥ semF φ B y = (c⁻¹ * lam) • semF φ B y := by
  have h1 := semF_diagonal φ hσφ hc y
  rw [hy, semF_smul, hlam] at h1
  have h2 : Matrix.diagonal σ *ᵥ semF φ B y = c⁻¹ • (lam • semF φ B y) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [h2, smul_smul]

end Diag

theorem adjM_diagonal (b : K →+* K) {m : Type*} [Fintype m] [DecidableEq m] (σ : m → K) :
    adjM b (Matrix.diagonal σ) = Matrix.diagonal (fun k => b (σ k)) := by
  rw [adjM, Matrix.diagonal_map (map_zero b), Matrix.diagonal_transpose]

section Orbit

variable {n : ℕ}

theorem exists_orbit_family (h : UnitaryFieldData 2 n K) [CharP K 2] {p : ℕ} (hp : p.Prime)
    {φ : K ≃+* K} (hφ : orderOf φ = p) (hφb : ∀ x, φ (h.bar x) = h.bar (φ x))
    (hpq : p ∣ 2 ^ n + 1) {B' : Matrix (Fin d) (Fin d) K} (hB' : adjM h.bar B' * B' = 1)
    {c₀ : K} (hc₀ : c₀ ^ (2 ^ n + 1) = 1) (hN : Ai φ B' p = c₀ • (1 : Matrix (Fin d) (Fin d) K))
    (W : Set (Fin d → K)) (hWp : ∀ σ ∈ W, ∀ k, σ k ^ p = 1) {i j : Fin d} (hij : i ≠ j)
    (hWij : ∀ σ ∈ W, σ i = σ j)
    (hWc : ∀ σ ∈ W, ∃ c : K, B' * Matrix.diagonal σ = c • (Matrix.diagonal σ * B'))
    (hnc : ∃ σ ∈ W, B' * Matrix.diagonal σ ≠ Matrix.diagonal σ * B') :
    ∃ U : Matrix (Fin d) (Fin p) K, adjM h.bar U * U = 0 ∧ tv h.bar U j i ≠ 0 ∧
      (∀ σ ∈ W, tv h.bar (Matrix.diagonal σ * U) = tv h.bar U) ∧
      tv h.bar (B' * U.map φ) = tv h.bar U := by
  classical
  have := Fact.mk hp
  have hb := h.bar_bar
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hp0 : 0 < p := hp.pos
  set φr : K →+* K := (φ : K →+* K) with hφr
  have hφb' : ∀ x, φr (h.bar x) = h.bar (φr x) := hφb
  have hfix : ∀ ζ : K, ζ ^ p = 1 → φ ζ = ζ := fun ζ hζ =>
    TableBUF.ringEquiv_apply_eq_of_pow_eq_one hp hφp hζ
  have hnorm1 : ∀ ζ : K, ζ ^ p = 1 → ζ * h.bar ζ = 1 := by
    intro ζ hζ
    obtain ⟨t, ht⟩ := hpq
    rw [h.bar_apply, ← pow_succ', ht, pow_mul, hζ, one_pow]
  have hB'0 : B' ≠ 0 := by
    rintro rfl
    have := congrFun (congrFun hB' i) i
    simp [adjM] at this
  have hne0 : ∀ ζ : K, ζ ^ p = 1 → ζ ≠ 0 := fun ζ hζ h0 => by
    rw [h0, zero_pow hp0.ne'] at hζ
    exact zero_ne_one hζ
  set v0 : Fin d → K := Pi.single i 1 + Pi.single j 1 with hv0
  set x : ℕ → Fin d → K := fun k => (semF φr B')^[k] v0 with hx
  have hD0 : ∀ σ ∈ W, Matrix.diagonal σ *ᵥ v0 = σ i • v0 := by
    intro σ hσ
    funext k
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, hv0, Pi.add_apply,
      Pi.single_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki, hWij σ hσ]
      · simp [hki, hkj]
  have heig : ∀ σ ∈ W, ∀ c : K, B' * Matrix.diagonal σ = c • (Matrix.diagonal σ * B') →
      ∀ k : ℕ, Matrix.diagonal σ *ᵥ x k = ((c ^ k)⁻¹ * σ i) • x k := by
    intro σ hσ c hc k
    have hcp := pow_eq_one_of_conj hB'0 (hWp σ hσ) hc
    have hc0 := hne0 c hcp
    induction k with
    | zero => simpa [hx] using hD0 σ hσ
    | succ k ih =>
      have hlam : φr (((c ^ k)⁻¹ * σ i)) = (c ^ k)⁻¹ * σ i := by
        rw [map_mul, map_inv₀, map_pow]
        have h1 : φr c = c := hfix c hcp
        have h2 : φr (σ i) = σ i := hfix _ (hWp σ hσ i)
        rw [h1, h2]
      have h3 := eigen_succ φr (fun k => hfix _ (hWp σ hσ k)) hc hc0 ih hlam
      have hxs : x (k + 1) = semF φr B' (x k) := Function.iterate_succ_apply' _ _ _
      rw [hxs, h3]
      congr 1
      ring
  obtain ⟨σ₁, hσ₁, hnc1⟩ := hnc
  obtain ⟨c₁, hc₁⟩ := hWc σ₁ hσ₁
  have hc₁ne : c₁ ≠ 1 := by
    rintro rfl
    exact hnc1 (by rw [hc₁, one_smul])
  have hc₁p : c₁ ^ p = 1 := pow_eq_one_of_conj hB'0 (hWp σ₁ hσ₁) hc₁
  have hc₁ord : orderOf c₁ = p := orderOf_eq_prime hc₁p hc₁ne
  have hσ₁i : σ₁ i ≠ 0 := hne0 _ (hWp σ₁ hσ₁ i)
  have hc₁0 : c₁ ≠ 0 := hne0 _ hc₁p
  have hiso : ∀ k, herm h.bar (x k) (x k) = 0 := by
    intro k
    simp only [hx]
    rw [herm_iterate φr h.bar hφb' hB' k, hv0, herm_pair_self h.bar hij]
    exact Function.iterate_fixed (map_zero φr) k
  have hD1u : adjM h.bar (Matrix.diagonal σ₁) * Matrix.diagonal σ₁ = 1 := by
    rw [adjM_diagonal, Matrix.diagonal_mul_diagonal]
    have : (fun k => h.bar (σ₁ k) * σ₁ k) = fun _ => 1 :=
      funext fun k => by rw [mul_comm]; exact hnorm1 _ (hWp σ₁ hσ₁ k)
    rw [this]
    exact Matrix.diagonal_one
  have hcpk : ∀ k : ℕ, (c₁ ^ k) ^ p = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hc₁p, one_pow]
  have hlamp : ∀ k : ℕ, ((c₁ ^ k)⁻¹ * σ₁ i) ^ p = 1 := fun k => by
    rw [mul_pow, inv_pow, hcpk, inv_one, one_mul, hWp σ₁ hσ₁ i]
  have hort : ∀ k l : ℕ, k < p → l < p → k ≠ l → herm h.bar (x k) (x l) = 0 := by
    intro k l hk hl hkl
    have e1 := herm_mulVec h.bar hD1u (x k) (x l)
    rw [heig σ₁ hσ₁ c₁ hc₁ k, heig σ₁ hσ₁ c₁ hc₁ l, herm_smul_left, herm_smul_right,
      ← mul_assoc] at e1
    by_contra hne
    have h2 : h.bar ((c₁ ^ k)⁻¹ * σ₁ i) * ((c₁ ^ l)⁻¹ * σ₁ i) = 1 :=
      mul_right_cancel₀ hne (by rw [one_mul]; exact e1)
    have h3 : ((c₁ ^ k)⁻¹ * σ₁ i) * h.bar ((c₁ ^ k)⁻¹ * σ₁ i) = 1 := hnorm1 _ (hlamp k)
    have hbne : h.bar ((c₁ ^ k)⁻¹ * σ₁ i) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h3
      exact zero_ne_one h3
    have h4 : (c₁ ^ l)⁻¹ * σ₁ i = (c₁ ^ k)⁻¹ * σ₁ i := by
      refine mul_left_cancel₀ hbne ?_
      rw [h2, mul_comm, h3]
    have h5 : c₁ ^ k = c₁ ^ l := by
      have h6 : (c₁ ^ l)⁻¹ = (c₁ ^ k)⁻¹ := mul_right_cancel₀ hσ₁i h4
      exact (inv_inj.mp h6.symm)
    exact hkl (pow_injOn_Iio_orderOf (x := c₁) (by rw [hc₁ord]; exact hk)
      (by rw [hc₁ord]; exact hl) h5)
  have hxi : ∀ k : ℕ, 0 < k → k < p → x k i = 0 := by
    intro k hk0 hkp
    have h1 := congrFun (heig σ₁ hσ₁ c₁ hc₁ k) i
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h1
    have hck : c₁ ^ k ≠ 1 := by
      intro h0
      have := (orderOf_dvd_iff_pow_eq_one.mpr h0)
      rw [hc₁ord] at this
      exact absurd (Nat.le_of_dvd hk0 this) (by omega)
    by_contra hne
    have h2 : σ₁ i = (c₁ ^ k)⁻¹ * σ₁ i := mul_right_cancel₀ hne h1
    have h3 : (c₁ ^ k)⁻¹ = 1 := by
      have : (c₁ ^ k)⁻¹ * σ₁ i = 1 * σ₁ i := by rw [one_mul]; exact h2.symm
      exact mul_right_cancel₀ hσ₁i this
    exact hck (inv_eq_one.mp h3)
  set U : Matrix (Fin d) (Fin p) K := Matrix.of fun l k => x (k : ℕ) l with hU
  have hUU : adjM h.bar U * U = 0 := by
    ext k k'
    simp only [Matrix.mul_apply, adjM, Matrix.transpose_apply, Matrix.map_apply, hU,
      Matrix.of_apply, Matrix.zero_apply]
    change herm h.bar (x k) (x k') = 0
    by_cases hkk : k = k'
    · subst hkk
      exact hiso _
    · exact hort k k' k.2 k'.2 (fun e => hkk (Fin.ext e))
  have hoff : tv h.bar U j i ≠ 0 := by
    have h1 : tv h.bar U j i = ∑ k : Fin p, x k j * h.bar (x k i) := by
      simp [tv, Matrix.add_apply, Matrix.mul_apply, adjM, Matrix.one_apply, hij.symm, hU]
    rw [h1, Finset.sum_eq_single (⟨0, hp0⟩ : Fin p)]
    · simp [hx, hv0, Pi.single_apply, hij, hij.symm]
    · intro k _ hk
      have hk0 : 0 < (k : ℕ) := by
        rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
        · exact absurd (Fin.ext h0) hk
        · exact h0
      rw [hxi k hk0 k.2, map_zero, mul_zero]
    · simp
  have hDU : ∀ σ ∈ W, tv h.bar (Matrix.diagonal σ * U) = tv h.bar U := by
    intro σ hσ
    obtain ⟨c, hc⟩ := hWc σ hσ
    have hcp := pow_eq_one_of_conj hB'0 (hWp σ hσ) hc
    set lam : Fin p → K := fun k => (c ^ (k : ℕ))⁻¹ * σ i with hlam
    have hlamp' : ∀ k : Fin p, lam k ^ p = 1 := fun k => by
      simp only [hlam]
      have hcpk : (c ^ (k : ℕ)) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hcp, one_pow]
      rw [mul_pow, inv_pow, hcpk, inv_one, one_mul, hWp σ hσ i]
    have hDU' : Matrix.diagonal σ * U = U * Matrix.diagonal lam := by
      ext l k
      have h1 := congrFun (heig σ hσ c hc k) l
      simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h1
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hU, Matrix.of_apply, hlam]
      rw [h1, mul_comm]
    rw [hDU']
    refine tv_mul_unitary h.bar ?_
    rw [adjM_diagonal, Matrix.diagonal_mul_diagonal]
    have : (fun k => lam k * h.bar (lam k)) = fun _ => 1 :=
      funext fun k => hnorm1 _ (hlamp' k)
    rw [this]
    exact Matrix.diagonal_one
  have hFU : tv h.bar (B' * U.map φ) = tv h.bar U := by
    have hxp : x p = c₀ • x 0 := by
      have h1 := semF_iterate φr φ (fun _ => rfl) B' p v0
      have h2 : (fun k => (φ ^ p) (v0 k)) = v0 := by
        funext k
        rw [hφp]
        rfl
      rw [h2, hN, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      simpa [hx] using h1
    have hf : ∀ l l' : Fin d, x p l * h.bar (x p l') = x 0 l * h.bar (x 0 l') := by
      intro l l'
      rw [hxp]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      have : c₀ * h.bar c₀ = 1 := by rw [h.bar_apply, ← pow_succ']; exact hc₀
      calc c₀ * x 0 l * (h.bar c₀ * h.bar (x 0 l'))
          = (c₀ * h.bar c₀) * (x 0 l * h.bar (x 0 l')) := by ring
        _ = _ := by rw [this, one_mul]
    obtain ⟨W', hW'def⟩ : ∃ W' : Matrix (Fin d) (Fin p) K, W' = B' * U.map φ := ⟨_, rfl⟩
    rw [← hW'def]
    have hW' : ∀ (l : Fin d) (k : Fin p), W' l k = x ((k : ℕ) + 1) l := by
      intro l k
      have hxs : x ((k : ℕ) + 1) = semF φr B' (x k) := Function.iterate_succ_apply' _ _ _
      rw [hW'def, hxs]
      simp only [semF, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, hU,
        Matrix.of_apply]
      rfl
    unfold tv
    congr 1
    ext l l'
    simp only [Matrix.mul_apply, adjM, Matrix.transpose_apply, Matrix.map_apply, hW', hU,
      Matrix.of_apply]
    set f : ℕ → K := fun k => x k l * h.bar (x k l') with hfdef
    have e1 : ∑ k ∈ Finset.range (p + 1), f k = ∑ k ∈ Finset.range p, f (k + 1) + f 0 :=
      Finset.sum_range_succ' f p
    have e2 : ∑ k ∈ Finset.range (p + 1), f k = ∑ k ∈ Finset.range p, f k + f p :=
      Finset.sum_range_succ f p
    have e3 : f p = f 0 := hf l l'
    have e4 : ∑ k ∈ Finset.range p, f (k + 1) = ∑ k ∈ Finset.range p, f k := by
      have e5 := e1.symm.trans e2
      rw [e3] at e5
      exact add_right_cancel e5
    calc ∑ k : Fin p, x ((k : ℕ) + 1) l * h.bar (x ((k : ℕ) + 1) l')
        = ∑ k : Fin p, f ((k : ℕ) + 1) := rfl
      _ = ∑ k ∈ Finset.range p, f (k + 1) := Fin.sum_univ_eq_sum_range (fun k => f (k + 1)) p
      _ = ∑ k ∈ Finset.range p, f k := e4
      _ = ∑ k : Fin p, f k := (Fin.sum_univ_eq_sum_range f p).symm
  exact ⟨U, hUU, hoff, hDU, hFU⟩

end Orbit

end LIDUF

end CFSG.StandardType

end
