module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BL2
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.EvenBN.Common CFSG.SL2MinimalFaithful Subgroup
open scoped MatrixGroups

theorem uc22r8100b_eq_of_swap {G : Type*} [Group G] (ψ : MulAut G) {p : ℕ} (hp : Odd p)
    (hψp : ψ ^ p = 1) {A B : Subgroup G} (hAB : ∀ x, x ∈ A ↔ ψ x ∈ B)
    (hBA : ∀ x, x ∈ B ↔ ψ x ∈ A) : A = B := by
  obtain ⟨k, rfl⟩ := hp
  have hk : ∀ k : ℕ, ∀ x, x ∈ A ↔ (ψ ^ (2 * k + 1)) x ∈ B := by
    intro k
    induction k with
    | zero => simpa using hAB
    | succ k ih =>
      intro x
      have e : ψ ^ (2 * (k + 1) + 1) = ψ ^ (2 * k + 1) * (ψ * ψ) := by
        rw [← pow_two, ← pow_add]
        exact congrArg (ψ ^ ·) (by omega)
      rw [e, MulAut.mul_apply, MulAut.mul_apply, ← ih, ← hBA, ← hAB]
  exact Subgroup.ext fun x => by simpa [hψp] using hk k x

theorem uc22r8100b_preserves_upper {K : Type} [Field K] [Finite K] [CharP K 2] {μ : Kˣ}
    (hμ : μ ≠ 1) {p : ℕ} (hp : Odd p) (ψ : MulAut SL(2, K))
    (hψT : ∀ x, x ∈ torusSL K ↔ ψ x ∈ torusSL K) (hψp : ψ ^ p = 1) :
    ∀ x, x ∈ upperSL K ↔ ψ x ∈ upperSL K := by
  have himg : ∀ U : Subgroup SL(2, K), torusSL K ≤ normalizer (U : Set SL(2, K)) →
      Nat.card U = Nat.card K →
      Subgroup.map ψ.toMonoidHom U = upperSL K ∨ Subgroup.map ψ.toMonoidHom U = lowerSL K := by
    intro U hUN hUc
    refine eq_upperSL_or_eq_lowerSL (μ := μ) ?_ hμ ?_
    · rw [Subgroup.card_map_of_injective ψ.injective, hUc]
    · have h1 : ψ.symm (diagSL μ) ∈ torusSL K :=
        (hψT _).2 (by simpa using diagSL_mem_torusSL μ)
      have h2 := Subgroup.mem_map_of_mem ψ.toMonoidHom (hUN h1)
      rw [Subgroup.map_equiv_normalizer_eq] at h2
      simpa using h2
  have hup := himg _ torusSL_le_normalizer_upperSL card_upperSL
  have hlow := himg _ torusSL_le_normalizer_lowerSL card_lowerSL
  have hmem : ∀ U : Subgroup SL(2, K), ∀ x, x ∈ U ↔ ψ x ∈ Subgroup.map ψ.toMonoidHom U :=
    fun U x => (Subgroup.mem_map_iff_mem ψ.injective).symm
  rcases hup with h | h
  · intro x
    rw [hmem (upperSL K) x, h]
  · exfalso
    rcases hlow with h' | h'
    · refine upperSL_ne_lowerSL (k := K) (uc22r8100b_eq_of_swap ψ hp hψp (fun x => ?_) fun x => ?_)
      · rw [hmem (upperSL K) x, h]
      · rw [hmem (lowerSL K) x, h']
    · exact upperSL_ne_lowerSL (k := K) (Subgroup.map_injective ψ.injective (h.trans h'.symm))

theorem uc22r8100b_unipotent_mem_torus {K : Type} [Field K] {c : K}
    (h : unipotent c ∈ torusSL K) : c = 0 := by
  obtain ⟨ν, hν⟩ := mem_torusSL_iff.1 h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hν
  simpa [coe_diagSL, coe_unipotent] using this.symm

theorem uc22r8100b_diag_image {K : Type} [Field K] [Finite K] [CharP K 2] {μ : Kˣ}
    (hμ : μ ≠ 1) {p : ℕ} (hp : Odd p) (ψ : MulAut SL(2, K))
    (hψT : ∀ x, x ∈ torusSL K ↔ ψ x ∈ torusSL K) (hψp : ψ ^ p = 1) :
    ∃ i : ℕ, ∀ s : Kˣ, ψ (diagSL s) = diagSL (s ^ 2 ^ i) := by
  obtain ⟨i, hi⟩ := uc22pwr1_sl2_frob ψ (uc22r8100b_preserves_upper hμ hp ψ hψT hψp)
  refine ⟨i, fun s => ?_⟩
  obtain ⟨c, hc⟩ := hi s
  have hpow : (diagSL s) ^ 2 ^ i = diagSL (s ^ 2 ^ i) :=
    (map_pow (diagSLHom (k := K)) s (2 ^ i)).symm
  have hT : unipotent c ∈ torusSL K := by
    have h1 : unipotent c = ψ (diagSL s) * ((diagSL s) ^ 2 ^ i)⁻¹ := by
      rw [hc]
      group
    rw [h1, hpow]
    exact Subgroup.mul_mem _ ((hψT _).1 (diagSL_mem_torusSL s))
      (Subgroup.inv_mem _ (diagSL_mem_torusSL _))
  rw [hc, uc22r8100b_unipotent_mem_torus hT, unipotent_zero, one_mul, hpow]

theorem uc22r8100b_pow_diag {K : Type} [Field K] (ψ : MulAut SL(2, K)) {i : ℕ}
    (h : ∀ s : Kˣ, ψ (diagSL s) = diagSL (s ^ 2 ^ i)) :
    ∀ (j : ℕ) (s : Kˣ), (ψ ^ j) (diagSL s) = diagSL (s ^ 2 ^ (i * j)) := by
  intro j
  induction j with
  | zero => intro s; simp
  | succ j ih =>
    intro s
    rw [pow_succ, MulAut.mul_apply, h, ih, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]

theorem uc22r8100b_dvd_of_fix {K : Type} [Field K] [Finite K] {n N : ℕ}
    (hK : Nat.card K = 2 ^ n) (hfix : ∀ s : Kˣ, s ^ 2 ^ N = s) : n ∣ N := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hpos : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have hg1 : g ^ (2 ^ N - 1) = 1 := by
    refine (mul_left_inj g).1 ?_
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel hpos]
    exact hfix g
  have hd : 2 ^ n - 1 ∣ 2 ^ N - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hg1
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one 2 n N
  rw [Nat.gcd_eq_left hd] at hgcd
  have h4 : 2 ^ Nat.gcd n N = 2 ^ n := by
    have := Nat.one_le_two_pow (n := Nat.gcd n N)
    have := Nat.one_le_two_pow (n := n)
    omega
  have h5 : Nat.gcd n N = n := Nat.pow_right_injective (le_refl 2) h4
  exact h5 ▸ Nat.gcd_dvd_right n N

theorem uc22r8100b_sl2_fixes {K : Type} [Field K] [Finite K] [CharP K 2] {n m p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2) {μ : Kˣ}
    (hμ : μ ≠ 1) (ψ : MulAut SL(2, K)) (hψT : ∀ x, x ∈ torusSL K ↔ ψ x ∈ torusSL K)
    (hψp : ψ ^ p = 1) {τ : Kˣ} (hτ : τ ^ 2 ^ m = τ) : ψ (diagSL τ) = diagSL τ := by
  obtain ⟨i, hi⟩ := uc22r8100b_diag_image hμ (hp.odd_of_ne_two hp2) ψ hψT hψp
  have hfix : ∀ s : Kˣ, s ^ 2 ^ (i * p) = s := by
    intro s
    have h1 := uc22r8100b_pow_diag ψ hi p s
    rw [hψp, MulAut.one_apply] at h1
    exact (diagSL_injective h1).symm
  have hdvd : n ∣ i * p := uc22r8100b_dvd_of_fix hK hfix
  have hmi : m ∣ i := by
    rw [hn, mul_comm i p] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
  obtain ⟨t, rfl⟩ := hmi
  have hat : ∀ t : ℕ, τ ^ 2 ^ (m * t) = τ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul', hτ, ih]
  rw [hi τ, hat]

theorem uc22r8100b_fixes_of_aut {X : Type} [Group X] [Finite X] {n m p q : ℕ} (h : IsL2 X n)
    (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2) [Fact q.Prime] (hqm : q ∣ 2 ^ m - 1)
    (Q : Sylow q X) (ψ : MulAut X) (hψQ : ∀ x, x ∈ (Q : Subgroup X) ↔ ψ x ∈ (Q : Subgroup X))
    (hψp : ψ ^ p = 1) {t : X} (ht : t ∈ (Q : Subgroup X)) (hto : orderOf t = q) : ψ t = t := by
  have hq : q ∣ 2 ^ n - 1 :=
    hqm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨p, by rw [hn, mul_comm]⟩)
  obtain ⟨K, hKf, hKfin, hKc, e, hK, ⟨μ, hμ, -⟩, hST, hC⟩ := uc22r8100b_torus_frame h hq Q
  set S' : Subgroup SL(2, K) := Subgroup.map e.toMonoidHom (Q : Subgroup X) with hS'
  have hmemS : ∀ g, g ∈ S' ↔ e.symm g ∈ (Q : Subgroup X) := fun g => Subgroup.mem_map_equiv
  let ψ' : MulAut SL(2, K) := MulAut.congr e ψ
  have hψ'a : ∀ g, ψ' g = e (ψ (e.symm g)) := fun g => rfl
  have hψ'S : ∀ g, g ∈ S' ↔ ψ' g ∈ S' := by
    intro g
    rw [hmemS, hmemS, hψ'a, e.symm_apply_apply]
    exact hψQ _
  have hpres : ∀ φ : MulAut SL(2, K), (∀ g, g ∈ S' ↔ φ g ∈ S') → ∀ x ∈ torusSL K,
      φ x ∈ torusSL K := by
    intro φ hφ x hx
    refine hC _ fun s hs => ?_
    obtain ⟨s₀, rfl⟩ : ∃ s₀, φ s₀ = s := ⟨φ.symm s, φ.apply_symm_apply s⟩
    have h1 : x * s₀ = s₀ * x :=
      mul_comm_of_mem_isMulCommutative (torusSL K) hx (hST ((hφ s₀).2 hs))
    rw [← map_mul, ← map_mul, h1]
  have hψ'T : ∀ x, x ∈ torusSL K ↔ ψ' x ∈ torusSL K := by
    refine fun x => ⟨hpres ψ' hψ'S x, fun hx => ?_⟩
    have hsymm : ∀ g, g ∈ S' ↔ ψ'.symm g ∈ S' := fun g => by
      rw [hψ'S (ψ'.symm g), ψ'.apply_symm_apply]
    simpa using hpres ψ'.symm hsymm _ hx
  have hψ'p : ψ' ^ p = 1 := by
    have : ψ' ^ p = MulAut.congr e (ψ ^ p) := (map_pow (MulAut.congr e) ψ p).symm
    rw [this, hψp, map_one]
  obtain ⟨τ, hτ⟩ : ∃ τ : Kˣ, diagSL τ = e t := mem_torusSL_iff.1 (hST ⟨t, ht, rfl⟩)
  have ht1 : t ^ q = 1 := by simpa [hto] using pow_orderOf_eq_one t
  have hτq : τ ^ q = 1 := by
    apply diagSL_injective
    have h1 : (diagSL τ) ^ q = 1 := by rw [hτ, ← map_pow e t q, ht1, map_one]
    rw [diagSL_one]
    exact (map_pow (diagSLHom (k := K)) τ q).trans h1
  have hτ2 : τ ^ 2 ^ m = τ := by
    obtain ⟨c, hc⟩ := hqm
    have h1 : τ ^ (2 ^ m - 1) = 1 := by rw [hc, pow_mul, hτq, one_pow]
    calc τ ^ 2 ^ m = τ ^ (2 ^ m - 1 + 1) := by rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      _ = τ := by rw [pow_succ, h1, one_mul]
  have hfix := uc22r8100b_sl2_fixes hK hn hp hp2 hμ ψ' hψ'T hψ'p hτ2
  rw [hτ, hψ'a, e.symm_apply_apply] at hfix
  exact e.injective hfix

end CFSG.LocalAnalysis.UniquenessCase.UC22
