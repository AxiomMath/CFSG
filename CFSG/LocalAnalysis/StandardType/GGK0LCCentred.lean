module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LCAct
public import CFSG.LocalAnalysis.StandardType.GGK0LCAffine

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma lk0xlccen_sum_single {τ : Tag} (A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (i t : Fin τ.rank) :
    ∑ j, A i j * (Pi.single t 1 : Fin τ.rank → ℤ) j = A i t := by
  rw [← Matrix.mulVec_apply_eq_sum, Matrix.mulVec_single_one]
  rfl

private lemma lk0xlccen_sum_mul_reflect {τ : Tag} (i : Fin τ.rank) (f u : Fin τ.rank → ℤ) :
    ∑ k, f k * reflect τ i u k
      = ∑ k, f k * u k - f i * (∑ j, τ.cartan i j * u j) := by
  have hk : ∀ k, f k * reflect τ i u k
      = f k * u k
        - (f i * (∑ j, τ.cartan i j * u j)) * (Pi.single i 1 : Fin τ.rank → ℤ) k := by
    intro k
    rw [reflect]
    by_cases h : k = i
    · subst h; simp; ring
    · simp [h]
  calc ∑ k, f k * reflect τ i u k
      = ∑ k, (f k * u k
          - (f i * (∑ j, τ.cartan i j * u j))
            * (Pi.single i 1 : Fin τ.rank → ℤ) k) :=
          Finset.sum_congr rfl (fun k _ => hk k)
    _ = ∑ k, f k * u k
          - ∑ k, (f i * (∑ j, τ.cartan i j * u j))
            * (Pi.single i 1 : Fin τ.rank → ℤ) k := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ k, f k * u k - f i * (∑ j, τ.cartan i j * u j) := by
          congr 1
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [Pi.single_eq_of_ne, hj]
          · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma lk0xlccen_coroot_step {τ : Tag} (i : Fin τ.rank) (f : Fin τ.rank → ℤ)
    {n' n'' : Fin τ.rank → ℤ} {γ u : Fin τ.rank → ℤ}
    (h1 : ∑ k, f k * γ k - ∑ k, f k * u k
        = ∑ m, n' m * ∑ j, τ.cartan m j * γ j)
    (h2 : ∑ j, τ.cartan i j * γ j - ∑ j, τ.cartan i j * u j
        = ∑ m, n'' m * ∑ j, τ.cartan m j * γ j) :
    ∑ k, f k * γ k - ∑ k, f k * (reflect τ i u) k
      = ∑ m, (n' m - f i * n'' m + (if m = i then f i else 0))
          * ∑ j, τ.cartan m j * γ j := by
  have hcpu : (∑ j, τ.cartan i j * u j)
      = (∑ j, τ.cartan i j * γ j)
        - (∑ m, n'' m * ∑ j, τ.cartan m j * γ j) := by
    linarith [h2]
  have hL : (∑ k, f k * γ k - ∑ k, f k * (reflect τ i u) k)
      = (∑ m, n' m * ∑ j, τ.cartan m j * γ j)
        + f i * (∑ j, τ.cartan i j * γ j)
        - f i * (∑ m, n'' m * ∑ j, τ.cartan m j * γ j) := by
    rw [lk0xlccen_sum_mul_reflect, hcpu]
    linear_combination h1
  have hR : (∑ m, (n' m - f i * n'' m + (if m = i then f i else 0))
        * ∑ j, τ.cartan m j * γ j)
      = (∑ m, n' m * ∑ j, τ.cartan m j * γ j)
        + f i * (∑ j, τ.cartan i j * γ j)
        - f i * (∑ m, n'' m * ∑ j, τ.cartan m j * γ j) := by
    have hterm : ∀ m, (n' m - f i * n'' m + (if m = i then f i else 0))
          * ∑ j, τ.cartan m j * γ j
        = ((n' m * ∑ j, τ.cartan m j * γ j)
            - (f i * n'' m) * ∑ j, τ.cartan m j * γ j)
          + (if m = i then f i else 0) * ∑ j, τ.cartan m j * γ j := by
      intro m; ring
    rw [Finset.sum_congr rfl (fun m _ => hterm m),
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h2' : (∑ m, (f i * n'' m) * ∑ j, τ.cartan m j * γ j)
        = f i * (∑ m, n'' m * ∑ j, τ.cartan m j * γ j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    have h3' : (∑ m, (if m = i then f i else 0) * ∑ j, τ.cartan m j * γ j)
        = f i * (∑ j, τ.cartan i j * γ j) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro m _ hm; simp [hm]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h2', h3']
    ring
  rw [hL, hR]

private lemma lk0xlccen_exists_single_of_sum_one {τ : Tag}
    (hhr : ∀ i, 0 < hr τ i) {v : Fin τ.rank → ℤ}
    (hv : ∀ i, v i = 0 ∨ v i = 1)
    (hsum : ∑ i, (hr τ i : ℤ) * v i = 1) :
    ∃ i₀, hr τ i₀ = 1 ∧ v = Pi.single i₀ 1 := by
  classical
  have hnn : ∀ i, 0 ≤ (hr τ i : ℤ) * v i := by
    intro i
    rcases hv i with h | h
    · simp [h]
    · rw [h, mul_one]; exact_mod_cast Nat.zero_le _
  have hle : ∀ i, (hr τ i : ℤ) * v i ≤ 1 := by
    intro i
    have := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => (hr τ j : ℤ) * v j) (fun j _ => hnn j) (Finset.mem_univ i)
    linarith [hsum]
  have hex : ∃ i, v i = 1 := by
    by_contra hc
    push Not at hc
    have hz : ∀ i, v i = 0 := fun i => by
      rcases hv i with h | h
      · exact h
      · exact absurd h (hc i)
    have h0 : ∑ i, (hr τ i : ℤ) * v i = 0 := by simp [hz]
    omega
  obtain ⟨i₀, hi₀⟩ := hex
  have hri₀ : hr τ i₀ = 1 := by
    have h := hle i₀
    rw [hi₀, mul_one] at h
    have h' : hr τ i₀ ≤ 1 := by exact_mod_cast h
    have hpos := hhr i₀
    omega
  refine ⟨i₀, hri₀, ?_⟩
  ext j
  by_cases hj : j = i₀
  · subst hj; simp [hi₀]
  · have hvj : v j = 0 := by
      by_contra hvj
      have hvj1 : v j = 1 := by
        rcases hv j with h | h
        · exact absurd h hvj
        · exact h
      have hpair : ((hr τ i₀ : ℤ) * v i₀ + (hr τ j : ℤ) * v j)
          ≤ ∑ i, (hr τ i : ℤ) * v i := by
        have hsub : ({i₀, j} : Finset (Fin τ.rank)) ⊆ Finset.univ :=
          fun x _ => Finset.mem_univ x
        have := Finset.sum_le_sum_of_subset_of_nonneg (s := ({i₀, j} : Finset (Fin τ.rank)))
          (t := Finset.univ) (f := fun i => (hr τ i : ℤ) * v i) hsub
          (fun i _ _ => hnn i)
        rwa [Finset.sum_pair (fun h : i₀ = j => hj h.symm)] at this
      rw [hi₀, hvj1, mul_one, mul_one, hsum] at hpair
      have hri₀' : (hr τ i₀ : ℤ) = 1 := by exact_mod_cast hri₀
      rw [hri₀'] at hpair
      have hrj : (1 : ℤ) ≤ (hr τ j : ℤ) := by exact_mod_cast hhr j
      omega
    rw [hvj, Pi.single_eq_of_ne]
    exact hj

private lemma lk0xlccen_shift_sum {τ : Tag} (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) (s : Finset (Fin τ.rank)) (g : Fin τ.rank → ℤ) :
    K.shift z (∑ i ∈ s, g i • (Pi.single i 1 : Fin τ.rank → ℤ))
      = ∑ i ∈ s, g i * K.shift z (Pi.single i 1) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : K.shift z (0 : Fin τ.rank → ℤ) = 0 := by
        have h := KacPt.shift_add K hz (0 : Fin τ.rank → ℤ) 0
        simpa using h
      simpa using h0
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [KacPt.shift_add K hz, KacPt.shift_smul K hz, ih]

private lemma lk0xlccen_shift_eq_sum {τ : Tag} (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) (γ : Fin τ.rank → ℤ) :
    K.shift z γ = ∑ i, γ i * K.shift z (Pi.single i 1) := by
  have hdecomp : (∑ i, γ i • (Pi.single i 1 : Fin τ.rank → ℤ)) = γ := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      have hjk : k ≠ j := fun h => hj h.symm
      rw [Pi.single_eq_of_ne hjk]
      ring
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have h : K.shift z γ
      = K.shift z (∑ i, γ i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by rw [hdecomp]
  rw [h, lk0xlccen_shift_sum K hz Finset.univ γ]

theorem exists_coroot_comb
    {τ : Tag} (z : WeylGroup τ) (f : Fin τ.rank → ℤ) :
    ∃ n : Fin τ.rank → ℤ, ∀ γ : Fin τ.rank → ℤ,
      ∑ k, f k * γ k - ∑ k, f k * (z • γ) k = ∑ i, n i * ∑ j, τ.cartan i j * γ j := by
  have key : ∀ w : WeylGroup τ, ∀ f : Fin τ.rank → ℤ,
      ∃ n : Fin τ.rank → ℤ, ∀ γ : Fin τ.rank → ℤ,
        ∑ k, f k * γ k - ∑ k, f k * (w • γ) k
          = ∑ i, n i * ∑ j, τ.cartan i j * γ j := by
    intro w
    induction w using (coxeterSystem τ).simple_induction_left with
    | one =>
        intro f
        exact ⟨0, fun γ => by simp⟩
    | mul_simple_left w i ih =>
        intro f
        obtain ⟨n', hn'⟩ := ih f
        obtain ⟨n'', hn''⟩ := ih (fun j => τ.cartan i j)
        refine ⟨fun m => n' m - f i * n'' m + (if m = i then f i else 0), fun γ => ?_⟩
        have h1 := hn' γ
        have h2 := hn'' γ
        rw [show (simple τ i * w) • γ = reflect τ i (w • γ) by rw [mul_smul, simple_smul]]
        exact lk0xlccen_coroot_step i f h1 h2
  exact key z f

theorem shift_of_inv_empty
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) (h : K.inv z = ∅) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpos : 0 < height γ) :
    (K.shift z γ = 0 ∧ 0 < height (z • γ)) ∨ (K.shift z γ = 1 ∧ height (z • γ) < 0) := by
  have key : ∀ a : AffPair τ, IsRoot τ a.1 → AffPos a → AffPos (K.act z a) := by
    intro a ha hposa
    have hmem : a ∉ K.inv z := by rw [h]; exact Set.notMem_empty a
    have hnneg : ¬ AffNeg (K.act z a) := by
      intro hneg
      exact hmem ⟨ha, hposa, hneg⟩
    exact (affPos_iff_not_affNeg (IsRoot.smul ha z)).2 hnneg
  have hsh : K.shift z (-γ) = -K.shift z γ := by
    have := KacPt.shift_smul K hz (-1) γ
    simpa using this
  have h1 : 0 < K.shift z γ ∨ (K.shift z γ = 0 ∧ 0 < height (z • γ)) := by
    have := key (γ, 0) hγ (Or.inr ⟨rfl, hpos⟩)
    simpa [KacPt.act, AffPos] using this
  have h2 : K.shift z γ < 1 ∨ (K.shift z γ = 1 ∧ height (z • γ) < 0) := by
    have hmem := key (-γ, 1) (IsRoot.neg hγ) (Or.inl (by norm_num))
    rw [KacPt.act, hsh, AffPos] at hmem
    simp only [smul_neg, height_neg] at hmem
    rcases hmem with hlt | ⟨heq, hgt⟩
    · left; omega
    · right; constructor <;> omega
  rcases h1 with h1 | ⟨h1a, h1b⟩
  · rcases h2 with h2 | ⟨h2a, h2b⟩
    · omega
    · exact Or.inr ⟨h2a, h2b⟩
  · rcases h2 with h2 | ⟨h2a, h2b⟩
    · exact Or.inl ⟨h1a, h1b⟩
    · omega

theorem inv_eq_empty_imp_one
    {τ : Tag} (hT : KacBox τ) {d : ℕ} (hc : KacCentred τ d)
    (K : KacPt τ) (hp : K.p.Prime) (hd : ¬ K.p ∣ d) {z : WeylGroup τ} (hz : z ∈ K.stab)
    (h : K.inv z = ∅) : z = 1 := by
  let v : Fin τ.rank → ℤ := fun i => K.shift z (Pi.single i 1)
  have hv01 : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i
    rcases shift_of_inv_empty hT K hz h (isRoot_single τ i) (by simp) with h' | h'
    · exact Or.inl h'.1
    · exact Or.inr h'.1
  have hsum_eq : K.shift z (theta τ) = ∑ i, (hr τ i : ℤ) * v i := by
    simpa [v, theta] using lk0xlccen_shift_eq_sum K hz (theta τ)
  have hthpos : 0 < height (theta τ) :=
    (IsRoot.height_pos_iff hT.2.1).2 (fun j => by
      change (0 : ℤ) ≤ (hr τ j : ℤ)
      exact_mod_cast Nat.zero_le (hr τ j))
  rcases shift_of_inv_empty hT K hz h hT.2.1 hthpos with ⟨hsh0, _⟩ | ⟨hsh1, _⟩
  · have hS : ∑ i, (hr τ i : ℤ) * v i = 0 := by rw [← hsum_eq]; exact hsh0
    have hvzero : ∀ i, v i = 0 := by
      intro i
      have hnn : ∀ j, 0 ≤ (hr τ j : ℤ) * v j := by
        intro j
        rcases hv01 j with h' | h'
        · simp [h']
        · rw [h', mul_one]; exact_mod_cast Nat.zero_le _
      have hterm : (hr τ i : ℤ) * v i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun j => (hr τ j : ℤ) * v j) (fun j _ => hnn j)).1 hS i (Finset.mem_univ i)
      rcases hv01 i with h' | h'
      · exact h'
      · rw [h', mul_one] at hterm
        have : hr τ i = 0 := by exact_mod_cast hterm
        exact absurd this (Nat.ne_of_gt (hT.2.2 i))
    exact eq_one_of_forall_height_pos (fun i => by
      rcases shift_of_inv_empty hT K hz h (isRoot_single τ i) (by simp) with ⟨_, hh⟩ | ⟨hone, _⟩
      · exact hh
      · have h0 : K.shift z (Pi.single i 1) = 0 := hvzero i
        rw [h0] at hone
        exact absurd hone (by norm_num))
  · have hS : ∑ i, (hr τ i : ℤ) * v i = 1 := by rw [← hsum_eq]; exact hsh1
    obtain ⟨i₀, hri₀, hv_eq⟩ := lk0xlccen_exists_single_of_sum_one hT.2.2 hv01 hS
    obtain ⟨n, hn⟩ := exists_coroot_comb (τ := τ) z (fun k => (K.s k : ℤ))
    have hE : ∀ γ : Fin τ.rank → ℤ,
        (K.p : ℤ) * K.shift z γ = ∑ i, n i * ∑ j, τ.cartan i j * γ j := by
      intro γ
      rw [KacPt.shift_spec K hz γ]
      exact hn γ
    have hAt : ∀ t, (K.p : ℤ) * v t = ∑ i, n i * τ.cartan i t := by
      intro t
      have h := hE (Pi.single t 1)
      rw [Finset.sum_congr rfl
        (fun i _ => by rw [lk0xlccen_sum_single τ.cartan i t])] at h
      exact h
    have hpx : (K.p : ℤ) • v = Matrix.mulVec (τ.cartan).transpose n := by
      ext t
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum]
      rw [hAt t]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.transpose_apply]
      ring
    obtain ⟨B, hBA, hBunit⟩ := hc
    have hmain : (d : ℤ) • n = (K.p : ℤ) • Matrix.mulVec B v := by
      calc (d : ℤ) • n
          = Matrix.mulVec ((d : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) n := by simp
        _ = Matrix.mulVec (B * (τ.cartan).transpose) n := by rw [← hBA]
        _ = Matrix.mulVec B (Matrix.mulVec (τ.cartan).transpose n) := by
              rw [← Matrix.mulVec_mulVec]
        _ = Matrix.mulVec B ((K.p : ℤ) • v) := by rw [← hpx]
        _ = (K.p : ℤ) • Matrix.mulVec B v := by rw [Matrix.mulVec_smul]
    have hcomp : ∀ k, (d : ℤ) * n k = (K.p : ℤ) * (B k i₀) := by
      intro k
      have h := congrFun hmain k
      simp only [Pi.smul_apply, smul_eq_mul] at h
      have hBv : (Matrix.mulVec B v) k = B k i₀ := by
        rw [show v = Pi.single i₀ (1 : ℤ) from hv_eq, Matrix.mulVec_single_one]
        rfl
      rw [hBv] at h
      exact h
    have hdiv : ∀ k, (K.p : ℤ) ∣ n k := by
      intro k
      have hpmul : (K.p : ℤ) ∣ (d : ℤ) * n k := by
        rw [hcomp k]
        exact dvd_mul_right _ _
      rcases Int.Prime.dvd_mul' hp hpmul with h | h
      · rw [Int.natCast_dvd_natCast] at h
        exact absurd h hd
      · exact h
    have hdvd : ∀ k, (d : ℤ) ∣ B k i₀ := by
      intro k
      obtain ⟨m, hm⟩ := hdiv k
      refine ⟨m, ?_⟩
      have h := hcomp k
      rw [hm] at h
      have hpne : (K.p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hcancel : (K.p : ℤ) * ((d : ℤ) * m) = (K.p : ℤ) * (B k i₀) := by
        linear_combination h
      exact (mul_left_cancel₀ hpne hcancel).symm
    obtain ⟨k, hk⟩ := hBunit i₀ hri₀
    exact absurd (hdvd k) hk

end CFSG.StandardType.GGK0LC

end
