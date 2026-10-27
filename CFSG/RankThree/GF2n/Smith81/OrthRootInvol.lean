module

public import CFSG.Timmesfeld.Defs
public import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Smith81

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.Timmesfeld (IsRootInvolutionSet)

section RingPair

variable {R : Type*} [Ring R]

private theorem pair_EE {φ ψ c : R} (hφ : φ * φ = 0) (hψ : ψ * ψ = 0)
    (h1 : φ * ψ * φ = c * φ) (h2 : ψ * φ * ψ = c * ψ) :
    (φ * ψ + ψ * φ) * (φ * ψ + ψ * φ) = c * (φ * ψ + ψ * φ) := by
  have e : (φ * ψ + ψ * φ) * (φ * ψ + ψ * φ) =
      (φ * ψ * φ) * ψ + φ * (ψ * ψ) * φ + ψ * (φ * φ) * ψ + (ψ * φ * ψ) * φ := by
    noncomm_ring
  rw [e, h1, h2, hψ, hφ]
  noncomm_ring

private theorem pair_NN {φ ψ c : R} (hφ : φ * φ = 0) (hψ : ψ * ψ = 0)
    (h1 : φ * ψ * φ = c * φ) (h2 : ψ * φ * ψ = c * ψ) :
    (φ + ψ + φ * ψ) * (φ + ψ + φ * ψ) =
      (φ * ψ + ψ * φ) + c * (φ + ψ + φ * ψ) := by
  have e : (φ + ψ + φ * ψ) * (φ + ψ + φ * ψ) =
      φ * φ + φ * ψ + (φ * φ) * ψ + ψ * φ + ψ * ψ + ψ * φ * ψ + φ * ψ * φ + φ * (ψ * ψ) +
        (φ * ψ * φ) * ψ := by
    noncomm_ring
  rw [e, h1, h2, hψ, hφ]
  noncomm_ring

private theorem add_pow_two_pow_of_commute (h2R : ∀ x : R, x + x = 0) {x y : R}
    (hxy : Commute x y) (n : ℕ) : (x + y) ^ (2 ^ n) = x ^ (2 ^ n) + y ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hab : Commute (x ^ (2 ^ n)) (y ^ (2 ^ n)) := hxy.pow_pow _ _
    have e3 : x ^ (2 ^ n) * y ^ (2 ^ n) + y ^ (2 ^ n) * x ^ (2 ^ n) = 0 := by
      rw [← hab.eq]
      exact h2R _
    calc (x + y) ^ (2 ^ (n + 1)) = ((x + y) ^ (2 ^ n)) ^ 2 := by
          rw [pow_succ 2 n, pow_mul]
      _ = (x ^ (2 ^ n) + y ^ (2 ^ n)) * (x ^ (2 ^ n) + y ^ (2 ^ n)) := by
          rw [ih, _root_.sq]
      _ = x ^ (2 ^ n) * x ^ (2 ^ n) + (x ^ (2 ^ n) * y ^ (2 ^ n) + y ^ (2 ^ n) * x ^ (2 ^ n)) +
            y ^ (2 ^ n) * y ^ (2 ^ n) := by noncomm_ring
      _ = (x ^ (2 ^ n)) ^ 2 + (y ^ (2 ^ n)) ^ 2 := by
          rw [e3, add_zero, _root_.sq, _root_.sq]
      _ = x ^ (2 ^ (n + 1)) + y ^ (2 ^ (n + 1)) := by
          rw [← pow_mul, ← pow_mul, ← pow_succ 2 n]

private theorem pow_sq_eq_of_quadratic {q n : ℕ} (hn : q = 2 ^ n) (h2R : ∀ x : R, x + x = 0)
    {c T E : R} (hcT : ∀ x : R, Commute c x) (hq1 : 1 ≤ q) (hcq : c ^ q = c)
    (hcq1 : c ^ (q - 1) = 1) (hEE : E * E = c * E) (hTT : T * T + c * T = 1 + c + E) :
    T ^ (q ^ 2) = T := by
  have frob : ∀ {x y : R}, Commute x y → (x + y) ^ q = x ^ q + y ^ q := by
    intro x y hxy
    rw [hn]
    exact add_pow_two_pow_of_commute h2R hxy n
  have hEpow : ∀ k : ℕ, E ^ (k + 1) = c ^ k * E := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, mul_assoc, hEE, ← mul_assoc, ← pow_succ]
  have hEq : E ^ q = E := by
    have := hEpow (q - 1)
    rw [Nat.sub_add_cancel hq1] at this
    rw [this, hcq1, one_mul]
  have hcomm1 : Commute (T * T) (c * T) :=
    (((hcT T).symm).mul_left ((hcT T).symm)).mul_right
      ((Commute.refl T).mul_left (Commute.refl T))
  have hFrobT : (T * T + c * T) ^ q = T ^ q * T ^ q + c * T ^ q := by
    rw [frob hcomm1, (Commute.refl T).mul_pow, (hcT T).mul_pow, hcq]
  have hcomm2 : Commute (1 + c) E := (Commute.one_left E).add_left (hcT E)
  have hΦ : T ^ q * T ^ q + c * T ^ q = T * T + c * T := by
    rw [← hFrobT, hTT, frob hcomm2, frob (Commute.one_left c), one_pow, hcq, hEq]
  obtain ⟨s, hs⟩ : ∃ s : R, s = T ^ q + T := ⟨_, rfl⟩
  have hTqT : T ^ q * T = T * T ^ q := ((Commute.refl T).pow_left q).eq
  have hss : s * s = c * s := by
    have e1 : s * s + c * s =
        (T ^ q * T ^ q + c * T ^ q) + (T * T + c * T) + (T ^ q * T + T * T ^ q) := by
      rw [hs]; noncomm_ring
    have e2 : T ^ q * T + T * T ^ q = 0 := by
      rw [← hTqT]
      exact h2R _
    have e3 : s * s + c * s = 0 := by
      rw [e1, hΦ, e2, h2R, add_zero]
    rw [eq_neg_of_add_eq_zero_left e3, neg_eq_of_add_eq_zero_right (h2R (c * s))]
  have hspow : ∀ k : ℕ, s ^ (k + 1) = c ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, mul_assoc, hss, ← mul_assoc, ← pow_succ]
  have hsq : s ^ q = s := by
    have := hspow (q - 1)
    rw [Nat.sub_add_cancel hq1] at this
    rw [this, hcq1, one_mul]
  have hTq : T ^ q = T + s := by
    calc T ^ q = T ^ q + (T + T) := by rw [h2R, add_zero]
      _ = T + s := by rw [hs]; abel
  have hsT : Commute T s := by
    rw [hs]
    exact ((Commute.refl T).pow_right q).add_right (Commute.refl T)
  calc T ^ (q ^ 2) = (T ^ q) ^ q := by rw [← pow_mul, _root_.sq]
    _ = (T + s) ^ q := by rw [← hTq]
    _ = T ^ q + s ^ q := frob hsT
    _ = (T + s) + s := by rw [hsq, hTq]
    _ = T := by rw [add_assoc, h2R, add_zero]

private theorem sq_of_pair (h2 : ∀ x : R, x + x = 0) {φ ψ : R} (hφ : φ * φ = 0)
    (hψ : ψ * ψ = 0) (hφψφ : φ * ψ * φ = 0) (hψφψ : ψ * φ * ψ = 0) :
    (1 + φ) * (1 + ψ) * ((1 + φ) * (1 + ψ)) = 1 + φ * ψ + ψ * φ := by
  have e : (1 + φ) * (1 + ψ) * ((1 + φ) * (1 + ψ)) = 1 + φ * ψ + ψ * φ + (φ + φ) + (ψ + ψ) +
      (φ * ψ + φ * ψ) + φ * φ + ψ * ψ + φ * ψ * φ + ψ * φ * ψ + φ * (ψ * ψ) + φ * φ * ψ +
      φ * ψ * φ * ψ := by noncomm_ring
  rw [e, hφψφ, hψφψ, hφ, hψ, h2, h2, h2]
  simp

private theorem sq_sq_of_pair (h2 : ∀ x : R, x + x = 0) {φ ψ : R} (hφ : φ * φ = 0)
    (hψ : ψ * ψ = 0) (hφψφ : φ * ψ * φ = 0) (hψφψ : ψ * φ * ψ = 0) :
    (1 + φ * ψ + ψ * φ) * (1 + φ * ψ + ψ * φ) = 1 := by
  have e : (1 + φ * ψ + ψ * φ) * (1 + φ * ψ + ψ * φ) = 1 + (φ * ψ + φ * ψ) + (ψ * φ + ψ * φ) +
      φ * ψ * φ * ψ + φ * (ψ * ψ) * φ + ψ * (φ * φ) * ψ + ψ * φ * ψ * φ := by noncomm_ring
  rw [e, hφψφ, hψφψ, hφ, hψ, h2, h2]
  simp

private theorem sub_one_mul_sub_one (h2 : ∀ x : R, x + x = 0) {a : R} (h : a * a = 1) :
    (a - 1) * (a - 1) = 0 := by
  have e : (a - 1) * (a - 1) = a * a - (a + a) + 1 := by noncomm_ring
  rw [e, h, h2, sub_zero, h2]

end RingPair

section Algebra

variable {K R : Type*} [Field K] [CharP K 2] [Ring R] [Algebra K R]

variable (K) in
include K in
private theorem algebra_add_self (x : R) : x + x = 0 := by
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  rw [← two_smul K x, h2, zero_smul]

variable [Fintype K]

private theorem pair_pow_card_sq {φ ψ : R} {d : K} (hd : d ≠ 0) (hφ : φ * φ = 0)
    (hψ : ψ * ψ = 0) (h1 : φ * ψ * φ = algebraMap K R d * φ)
    (h2 : ψ * φ * ψ = algebraMap K R d * ψ) :
    ((1 + φ) * (1 + ψ)) ^ (Fintype.card K ^ 2) = (1 + φ) * (1 + ψ) := by
  obtain ⟨c, hcdef⟩ : ∃ c : R, c = algebraMap K R d := ⟨_, rfl⟩
  rw [← hcdef] at h1 h2
  have hcT : ∀ x : R, Commute c x := fun x => by rw [hcdef]; exact Algebra.commutes d x
  have h2R : ∀ x : R, x + x = 0 := algebra_add_self K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hcq : c ^ Fintype.card K = c := by
    rw [hcdef, ← map_pow, FiniteField.pow_card]
  have hcq1 : c ^ (Fintype.card K - 1) = 1 := by
    rw [hcdef, ← map_pow, FiniteField.pow_card_sub_one_eq_one d hd, map_one]
  obtain ⟨E, hE⟩ : ∃ E : R, E = φ * ψ + ψ * φ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : R, N = φ + ψ + φ * ψ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : R, T = (1 + φ) * (1 + ψ) := ⟨_, rfl⟩
  have hEE : E * E = c * E := by rw [hE]; exact pair_EE hφ hψ h1 h2
  have hNN : N * N = E + c * N := by rw [hE, hN]; exact pair_NN hφ hψ h1 h2
  have hTN : T = 1 + N := by rw [hT, hN]; noncomm_ring
  have hTT : T * T + c * T = 1 + c + E := by
    have e1 : T * T = 1 + (N + N) + N * N := by rw [hTN]; noncomm_ring
    have e2 : c * N + c * N = 0 := by rw [← mul_add, h2R, mul_zero]
    have e3 : T * T + c * T = 1 + (N + N) + (E + c * N) + (c + c * N) := by
      rw [e1, hNN, hTN]; noncomm_ring
    rw [e3, h2R N]
    calc 1 + 0 + (E + c * N) + (c + c * N) = 1 + c + E + (c * N + c * N) := by abel
      _ = 1 + c + E := by rw [e2, add_zero]
  rw [← hT]
  exact pow_sq_eq_of_quadratic hn h2R hcT Fintype.card_pos hcq hcq1 hEE hTT

end Algebra

section A2

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure IsOrthA2 (Q : QuadraticForm K V) (t : V ≃ₗ[K] V) : Prop where
  mem : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  mul_self : t * t = 1
  finrank_eq : finrank K (commSpace t) = 2
  vanish : ∀ x ∈ commSpace t, Q x = 0

private theorem commSpace_one_eq_bot : commSpace (1 : V ≃ₗ[K] V) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]

theorem IsOrthA2.ne_one {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} (h : IsOrthA2 Q t) : t ≠ 1 := by
  intro h1
  have h2 := h.finrank_eq
  rw [h1, commSpace_one_eq_bot, finrank_bot] at h2
  exact absurd h2 (by norm_num)

theorem IsOrthA2.orderOf_eq_two {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} (h : IsOrthA2 Q t) :
    orderOf t = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.mul_self) h.ne_one

theorem IsOrthA2.conj {Q : QuadraticForm K V} {g t : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht : IsOrthA2 Q t) :
    IsOrthA2 Q (g * t * g⁻¹) := by
  refine ⟨mul_mem (mul_mem hg ht.mem) (inv_mem hg), ?_, ?_, ?_⟩
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht.mul_self]; group
  · rw [commSpace_conj, LinearEquiv.finrank_map_eq]
    exact ht.finrank_eq
  · rw [commSpace_conj]
    rintro _ ⟨x, hx, rfl⟩
    change Q (g x) = 0
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x]
    exact ht.vanish x hx

theorem isOrthA2_iff_suzukiLetter {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} :
    IsOrthA2 Q t ↔ t ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ orderOf t = 2 ∧
      suzukiLetter Q t = .a ∧ finrank K (commSpace t) = 2 := by
  constructor
  · intro h
    refine ⟨h.mem, h.orderOf_eq_two, suzukiLetter_eq_a_iff.mpr ⟨?_, h.vanish⟩, h.finrank_eq⟩
    rw [h.finrank_eq]
    exact even_two
  · rintro ⟨hO, ho, hs, hr⟩
    exact ⟨hO, by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp ho).1, hr,
      (suzukiLetter_eq_a_iff.mp hs).2⟩

variable [CharP K 2]

theorem IsOrthA2.mem_omegaGroup [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V} (h : IsOrthA2 Q t) :
    t ∈ omegaGroup Q hQ :=
  ⟨h.mem, by rw [h.finrank_eq]; exact even_two⟩

private theorem linearIndependent_pair_symm {x y : V} (h : LinearIndependent K ![x, y]) :
    LinearIndependent K ![y, x] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have := h t s (by rw [add_comm]; exact hst)
  exact ⟨this.2, this.1⟩

private theorem finrank_span_pair {x y : V} (h : LinearIndependent K ![x, y]) :
    finrank K (Submodule.span K {x, y}) = 2 := by
  have := finrank_span_eq_card h
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at this

private theorem exists_pair_of_finrank_eq_two [FiniteDimensional K V] {U : Submodule K V}
    (hU2 : finrank K U = 2) :
    ∃ v w : V, LinearIndependent K ![v, w] ∧ Submodule.span K {v, w} = U := by
  let b := Module.finBasisOfFinrankEq K U hU2
  have hli : LinearIndependent K ![(b 0 : V), (b 1 : V)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h : s • b 0 + t • b 1 = 0 := Subtype.ext (by simpa using hst)
    have := Fintype.linearIndependent_iff.mp b.linearIndependent ![s, t]
      (by simpa [Fin.sum_univ_two] using h)
    exact ⟨this 0, this 1⟩
  refine ⟨b 0, b 1, hli, ?_⟩
  have hle : Submodule.span K {(b 0 : V), (b 1 : V)} ≤ U := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact (b 0).2
    · exact (b 1).2
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair hli, hU2])

private theorem exists_polar_eq_one_polar_eq_zero [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {v w : V} (h : LinearIndependent K ![v, w]) :
    ∃ x, polar Q x v = 1 ∧ polar Q x w = 0 := by
  have hv : v ∉ K ∙ w := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := (LinearIndependent.pair_iff.mp h) 1 (-c) (by
      rw [one_smul, neg_smul, ← hc]
      exact add_neg_cancel _)
    exact one_ne_zero this.1
  obtain ⟨z, hz, hvz⟩ := exists_polar_ne_zero hQ hv
  have hwz : polar Q w z = 0 := hz w (Submodule.mem_span_singleton_self w)
  refine ⟨(polar Q v z)⁻¹ • z, ?_, ?_⟩
  · rw [polar_smul_left, smul_eq_mul, polar_comm Q z v, inv_mul_cancel₀ hvz]
  · rw [polar_smul_left, smul_eq_mul, polar_comm Q z w, hwz, mul_zero]

theorem IsOrthA2.exists_apply_sub [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V} (ht : IsOrthA2 Q t) :
    ∃ a b : V, LinearIndependent K ![a, b] ∧ commSpace t = Submodule.span K {a, b} ∧
      Q a = 0 ∧ Q b = 0 ∧ polar Q a b = 0 ∧
      ∀ v, t v - v = polar Q v a • b + polar Q v b • a := by
  obtain ⟨hO, htt, h2, hzero⟩ := id ht
  obtain ⟨v, w, hli, hspan⟩ := exists_pair_of_finrank_eq_two h2
  have hvA : v ∈ commSpace t := hspan ▸ Submodule.subset_span (by simp)
  have hwA : w ∈ commSpace t := hspan ▸ Submodule.subset_span (by simp)
  have hqv : Q v = 0 := hzero v hvA
  have hqw : Q w = 0 := hzero w hwA
  have hvw : polar Q v w = 0 := by
    have h := hzero (v + w) (add_mem hvA hwA)
    rwa [map_add_eq, hqv, hqw, zero_add, zero_add] at h
  obtain ⟨xv, hxvv, hxvw⟩ := exists_polar_eq_one_polar_eq_zero hQ hli
  obtain ⟨xw, hxww, hxwv⟩ := exists_polar_eq_one_polar_eq_zero hQ (linearIndependent_pair_symm hli)
  have hself : ∀ y, polar Q (t y - y) y = 0 := by
    intro y
    have h0 : Q (t y - y) = 0 := hzero _ (sub_mem_commSpace t y)
    rw [map_sub_eq_polar hO] at h0
    rw [QuadraticMap.polar_sub_left, h0, polar_self_eq_zero, sub_zero]
  obtain ⟨β, hβ⟩ : ∃ β : K, t xv - xv = β • w := by
    have hmem : t xv - xv ∈ Submodule.span K {v, w} := hspan ▸ sub_mem_commSpace t xv
    obtain ⟨s, r, hsr⟩ := Submodule.mem_span_pair.mp hmem
    have h0 := hself xv
    rw [← hsr] at h0
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_comm Q v xv, hxvv,
      polar_comm Q w xv, hxvw, mul_one, mul_zero, add_zero] at h0
    refine ⟨r, ?_⟩
    rw [← hsr, h0, zero_smul, zero_add]
  obtain ⟨γ, hγ⟩ : ∃ γ : K, t xw - xw = γ • v := by
    have hmem : t xw - xw ∈ Submodule.span K {v, w} := hspan ▸ sub_mem_commSpace t xw
    obtain ⟨s, r, hsr⟩ := Submodule.mem_span_pair.mp hmem
    have h0 := hself xw
    rw [← hsr] at h0
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_comm Q v xw, hxwv,
      polar_comm Q w xw, hxww, mul_one, mul_zero, zero_add] at h0
    refine ⟨s, ?_⟩
    rw [← hsr, h0, zero_smul, add_zero]
  have hβγ : γ = β := by
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO xv xw
    have e1 : t xv = xv + β • w := by rw [← hβ]; abel
    have e2 : t xw = xw + γ • v := by rw [← hγ]; abel
    rw [e1, e2] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      hxvv, polar_comm Q w xw, hxww, polar_comm Q w v, hvw, mul_one, mul_zero, add_zero] at h
    have h' : γ + β = 0 := by linear_combination h
    rw [eq_neg_of_add_eq_zero_left h', CharTwo.neg_eq]
  have hgen : ∀ y, t y - y = polar Q y v • (β • w) + polar Q y (β • w) • v := by
    intro y
    obtain ⟨c, hc⟩ : ∃ c, c = polar Q y v := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = polar Q y w := ⟨_, rfl⟩
    obtain ⟨y', hy'⟩ : ∃ y', y' = y - c • xv - d • xw := ⟨_, rfl⟩
    have hv' : polar Q v y' = 0 := by
      rw [hy', QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right, polar_smul_right,
        polar_smul_right, polar_comm Q v xv, hxvv, polar_comm Q v xw, hxwv, polar_comm Q v y,
        ← hc]
      simp
    have hw' : polar Q w y' = 0 := by
      rw [hy', QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right, polar_smul_right,
        polar_smul_right, polar_comm Q w xv, hxvw, polar_comm Q w xw, hxww, polar_comm Q w y,
        ← hd]
      simp
    have hy'perp : y' ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace t) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [← hspan] at hn
      obtain ⟨s, r, rfl⟩ := Submodule.mem_span_pair.mp hn
      show polar Q (s • v + r • w) y' = 0
      rw [polar_add_left, polar_smul_left, polar_smul_left, hv', hw', smul_zero, smul_zero,
        add_zero]
    have hy'fix : t y' = y' := by
      rw [← mem_fixSpace, fixSpace_eq_orthogonal_commSpace hQ hO htt]
      exact hy'perp
    have hy : y = y' + c • xv + d • xw := by rw [hy']; abel
    have hty : t y = t y' + c • t xv + d • t xw := by
      conv_lhs => rw [hy]
      rw [map_add, map_add, map_smul, map_smul]
    have key : t y - y = c • (t xv - xv) + d • (t xw - xw) + (t y' - y') := by
      calc t y - y = (t y' + c • t xv + d • t xw) - (y' + c • xv + d • xw) := by
            rw [← hty, ← hy]
        _ = c • (t xv - xv) + d • (t xw - xw) + (t y' - y') := by module
    rw [key, hy'fix, sub_self, add_zero, hβ, hγ, hβγ, polar_smul_right, ← hc, ← hd]
    module
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply ht.ne_one
    refine LinearEquiv.ext fun y => ?_
    have := hgen y
    simp only [zero_smul, smul_zero, polar_zero_right, add_zero, sub_eq_zero] at this
    rw [LinearEquiv.coe_one, id]
    exact this
  refine ⟨v, β • w, ?_, ?_, hqv, ?_, ?_, hgen⟩
  · rw [LinearIndependent.pair_iff]
    intro s r hsr
    have := (LinearIndependent.pair_iff.mp hli) s (r * β) (by rw [mul_smul]; exact hsr)
    exact ⟨this.1, (mul_eq_zero.mp this.2).resolve_right hβ0⟩
  · rw [← hspan]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [hx]
        have hmem : β • w ∈ Submodule.span K {v, β • w} :=
          Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
        have := Submodule.smul_mem (Submodule.span K {v, β • w}) β⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hβ0, one_smul] at this
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [hx]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  · rw [QuadraticMap.map_smul, hqw, smul_zero]
  · rw [polar_smul_right, hvw, smul_zero]

private theorem comp_comp_eq_smul {Q : QuadraticForm K V} {φ ψ : V →ₗ[K] V} {a1 a2 b1 b2 : V}
    (hφ : ∀ v, φ v = polar Q v a1 • a2 + polar Q v a2 • a1)
    (hψ : ∀ v, ψ v = polar Q v b1 • b2 + polar Q v b2 • b1) (v : V) :
    φ (ψ (φ v)) =
      (polar Q a1 b1 * polar Q a2 b2 + polar Q a1 b2 * polar Q a2 b1) • φ v := by
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have h1 : φ (ψ a1) =
      (polar Q a1 b1 * polar Q a2 b2 + polar Q a1 b2 * polar Q a2 b1) • a1 := by
    rw [hψ, map_add, map_smul, map_smul, hφ, hφ, polar_comm Q b2 a1, polar_comm Q b2 a2,
      polar_comm Q b1 a1, polar_comm Q b1 a2]
    match_scalars <;>
      first | ring1 | linear_combination (polar Q a1 b1 * polar Q a1 b2) * h2
  have h3 : φ (ψ a2) =
      (polar Q a1 b1 * polar Q a2 b2 + polar Q a1 b2 * polar Q a2 b1) • a2 := by
    rw [hψ, map_add, map_smul, map_smul, hφ, hφ, polar_comm Q b2 a1, polar_comm Q b2 a2,
      polar_comm Q b1 a1, polar_comm Q b1 a2]
    match_scalars <;>
      first | ring1 | linear_combination (polar Q a2 b1 * polar Q a2 b2) * h2
  rw [hφ v, map_add, map_smul, map_smul, map_add, map_smul, map_smul, h1, h3, smul_add,
    smul_comm _ (polar Q v a1), smul_comm _ (polar Q v a2)]

end A2

section Pair

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem end_add_self (x : Module.End K V) : x + x = 0 := algebra_add_self K x

private theorem sub_one_mul_sub_one_of_mul_self {t : V ≃ₗ[K] V} (htt : t * t = 1) :
    ((t : V →ₗ[K] V) - 1) * ((t : V →ₗ[K] V) - 1) = 0 := by
  refine sub_one_mul_sub_one end_add_self ?_
  rw [← LinearEquiv.coe_toLinearMap_mul, htt]
  rfl

private theorem coe_eq_one_add_sub_one (t : V ≃ₗ[K] V) :
    (t : V →ₗ[K] V) = 1 + ((t : V →ₗ[K] V) - 1) := by
  abel

private theorem sub_one_apply (α : V ≃ₗ[K] V) (v : V) :
    ((α : V →ₗ[K] V) - 1) v = α v - v :=
  rfl

theorem exists_pair_scalar_of_isOrthA2 (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) :
    ∃ d : K,
      ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
        d • ((α : V →ₗ[K] V) - 1) ∧
      ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) =
        d • ((β : V →ₗ[K] V) - 1) := by
  obtain ⟨a1, a2, -, -, -, -, -, ha⟩ := hα.exists_apply_sub hQ
  obtain ⟨b1, b2, -, -, -, -, -, hb⟩ := hβ.exists_apply_sub hQ
  refine ⟨polar Q a1 b1 * polar Q a2 b2 + polar Q a1 b2 * polar Q a2 b1, ?_, ?_⟩
  · refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
    exact comp_comp_eq_smul (Q := Q) (φ := (α : V →ₗ[K] V) - 1)
      (ψ := (β : V →ₗ[K] V) - 1) (fun v => ha v) (fun v => hb v) v
  · refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
    have h := comp_comp_eq_smul (Q := Q) (φ := (β : V →ₗ[K] V) - 1)
      (ψ := (α : V →ₗ[K] V) - 1) (fun v => hb v) (fun v => ha v) v
    rw [polar_comm Q b1 a1, polar_comm Q b2 a2, polar_comm Q b1 a2, polar_comm Q b2 a1,
      mul_comm (polar Q a2 b1)] at h
    exact h

private theorem coe_mul_sq_of_scalar_zero {α β : V ≃ₗ[K] V} (hαα : α * α = 1)
    (hββ : β * β = 1)
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) = 0)
    (h2 : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) = 0) :
    (((α * β) ^ 2 : V ≃ₗ[K] V) : V →ₗ[K] V) =
      1 + ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) +
        ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) := by
  rw [pow_two]
  change (α : V →ₗ[K] V) * β * ((α : V →ₗ[K] V) * β) = _
  rw [coe_eq_one_add_sub_one α, coe_eq_one_add_sub_one β, add_sub_cancel_left,
    add_sub_cancel_left]
  exact sq_of_pair end_add_self (sub_one_mul_sub_one_of_mul_self hαα)
    (sub_one_mul_sub_one_of_mul_self hββ) h1 h2

private theorem mul_pow_four_eq_one_of_scalar_zero {α β : V ≃ₗ[K] V} (hαα : α * α = 1)
    (hββ : β * β = 1)
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) = 0)
    (h2 : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) = 0) :
    (α * β) ^ 4 = 1 := by
  have h := coe_mul_sq_of_scalar_zero hαα hββ h1 h2
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  apply LinearEquiv.toLinearMap_injective
  rw [LinearEquiv.coe_toLinearMap_mul, h]
  exact sq_sq_of_pair end_add_self (sub_one_mul_sub_one_of_mul_self hαα)
    (sub_one_mul_sub_one_of_mul_self hββ) h1 h2

private theorem sub_one_apply_sub_one_apply_eq_zero (hQ : Q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[K] V} (hαO : α ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hαα : α * α = 1)
    (horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar Q a b = 0) (v : V) :
    α (β v - v) - (β v - v) = 0 := by
  have hmem : β v - v ∈ fixSpace α := by
    rw [fixSpace_eq_orthogonal_commSpace hQ hαO hαα, LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    exact horth a ha _ (sub_mem_commSpace β v)
  rw [mem_fixSpace.mp hmem, sub_self]

theorem isOrthA2_mul_sq_of_scalar_zero (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β)
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) = 0)
    (h2 : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) = 0)
    (hne : (α * β) ^ 2 ≠ 1) :
    IsOrthA2 Q ((α * β) ^ 2) ∧ commSpace ((α * β) ^ 2) ≤ commSpace α ⊔ commSpace β := by
  have hαO := hα.mem
  have hβO := hβ.mem
  have hαα := hα.mul_self
  have hββ := hβ.mul_self
  have hγO : (α * β) ^ 2 ∈ TauCeti.QuadraticMap.orthogonalGroup Q := pow_mem (mul_mem hαO hβO) 2
  have hγγ : (α * β) ^ 2 * (α * β) ^ 2 = 1 := by
    rw [← pow_add]
    exact mul_pow_four_eq_one_of_scalar_zero hαα hββ h1 h2
  have hform : ∀ v, ((α * β) ^ 2) v - v =
      (α (β v - v) - (β v - v)) + (β (α v - v) - (α v - v)) := by
    intro v
    have h := LinearMap.congr_fun (coe_mul_sq_of_scalar_zero hαα hββ h1 h2) v
    rw [LinearEquiv.coe_coe] at h
    rw [h]
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, sub_one_apply]
    abel
  have hle : commSpace ((α * β) ^ 2) ≤ commSpace α ⊔ commSpace β := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [hform]
    exact Submodule.add_mem_sup (sub_mem_commSpace α _) (sub_mem_commSpace β _)
  have hzero : ∀ x ∈ commSpace ((α * β) ^ 2), Q x = 0 := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [hform, map_add_eq, hα.vanish _ (sub_mem_commSpace α _),
      hβ.vanish _ (sub_mem_commSpace β _), zero_add, zero_add,
      ← polar_sub_eq_polar_sub hβO hββ]
    have h := LinearMap.congr_fun h2 v
    simp only [Module.End.mul_apply, sub_one_apply, LinearMap.zero_apply] at h
    rw [h, polar_zero_left]
  have hev := even_finrank_commSpace_of_forall_eq_zero hQ hγO hγγ hzero
  have hpos := one_le_finrank_commSpace hne
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
  rw [hα.finrank_eq, hβ.finrank_eq] at hsup
  have hmono := Submodule.finrank_mono hle
  have hne4 : finrank K (commSpace ((α * β) ^ 2)) ≠ 4 := by
    intro h4
    apply hne
    have heq : commSpace ((α * β) ^ 2) = commSpace α ⊔ commSpace β :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar Q a b = 0 := by
      intro a ha b hb
      have hab := hzero (a + b) (heq ▸ Submodule.add_mem_sup ha hb)
      rwa [map_add_eq, hzero a (heq ▸ Submodule.mem_sup_left ha),
        hzero b (heq ▸ Submodule.mem_sup_right hb), zero_add, zero_add] at hab
    have horth' : ∀ b ∈ commSpace β, ∀ a ∈ commSpace α, polar Q b a = 0 := fun b hb a ha => by
      rw [polar_comm]
      exact horth a ha b hb
    refine LinearEquiv.ext fun v => ?_
    have e := hform v
    rw [sub_one_apply_sub_one_apply_eq_zero hQ hαO hαα horth v,
      sub_one_apply_sub_one_apply_eq_zero hQ hβO hββ horth' v, add_zero, sub_eq_zero] at e
    exact e
  obtain ⟨r, hr⟩ := hev
  refine ⟨⟨hγO, hγγ, ?_, hzero⟩, hle⟩
  omega

theorem mul_pow_card_sq_eq_of_scalar_ne_zero [Fintype K] {α β : V ≃ₗ[K] V} (hαα : α * α = 1)
    (hββ : β * β = 1) {d : K} (hd : d ≠ 0)
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
      d • ((α : V →ₗ[K] V) - 1))
    (h2 : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) =
      d • ((β : V →ₗ[K] V) - 1)) :
    (α * β) ^ (Fintype.card K ^ 2) = α * β := by
  have h := pair_pow_card_sq (R := Module.End K V) hd
    (sub_one_mul_sub_one_of_mul_self hαα) (sub_one_mul_sub_one_of_mul_self hββ)
    (by rw [← Algebra.smul_def]; exact h1) (by rw [← Algebra.smul_def]; exact h2)
  rw [← coe_eq_one_add_sub_one α, ← coe_eq_one_add_sub_one β] at h
  apply LinearEquiv.toLinearMap_injective
  have e := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V))
    (α * β) (Fintype.card K ^ 2)
  simp only [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, map_mul] at e
  exact e.trans h

theorem orderOf_mul_isOrthA2 [Finite K] (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) :
    (orderOf (α * β) ∣ 4 ∧ (orderOf (α * β) = 4 → IsOrthA2 Q ((α * β) ^ 2))) ∨
      Odd (orderOf (α * β)) := by
  haveI := Fintype.ofFinite K
  obtain ⟨d, h1, h2⟩ := exists_pair_scalar_of_isOrthA2 hQ hα hβ
  by_cases hd : d = 0
  · subst hd
    rw [zero_smul] at h1 h2
    left
    have h4 := mul_pow_four_eq_one_of_scalar_zero hα.mul_self hβ.mul_self h1 h2
    refine ⟨orderOf_dvd_of_pow_eq_one h4, fun ho => ?_⟩
    exact (isOrthA2_mul_sq_of_scalar_zero hQ hα hβ h1 h2
      (pow_ne_one_of_lt_orderOf (by norm_num) (by omega))).1
  · right
    have h := mul_pow_card_sq_eq_of_scalar_ne_zero hα.mul_self hβ.mul_self hd h1 h2
    have hq : 1 ≤ Fintype.card K := Fintype.card_pos
    have hpow : (α * β) ^ (Fintype.card K ^ 2 - 1) = 1 := by
      have hN : 1 ≤ Fintype.card K ^ 2 := Nat.one_le_pow _ _ hq
      apply mul_right_cancel (b := α * β)
      rw [← pow_succ, Nat.sub_add_cancel hN, h, one_mul]
    refine Odd.of_dvd_nat ?_ (orderOf_dvd_of_pow_eq_one hpow)
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have h2dvd : 2 ∣ Fintype.card K := by
      rw [hn]
      exact dvd_pow_self 2 n.ne_zero
    have hq2 : Even (Fintype.card K ^ 2) :=
      Nat.even_pow.mpr ⟨even_iff_two_dvd.mpr h2dvd, two_ne_zero⟩
    have hN : 1 ≤ Fintype.card K ^ 2 := Nat.one_le_pow _ _ hq
    have h3 : Even (Fintype.card K ^ 2 - 1 + 1) := by rwa [Nat.sub_add_cancel hN]
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h3)

theorem isRootInvolutionSet_isOrthA2 [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (H : Subgroup (V ≃ₗ[K] V)) :
    IsRootInvolutionSet {t : V ≃ₗ[K] V | t ∈ H ∧ IsOrthA2 Q t} := by
  refine ⟨fun d hd => hd.2.orderOf_eq_two, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rcases orderOf_mul_isOrthA2 hQ hd.2 he.2 with ⟨hdvd, -⟩ | hodd
    · obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (by simpa using hdvd : orderOf (d * e) ∣ 2 ^ 2)
      interval_cases i
      · exact Or.inr (Or.inr (by rw [hi']; exact odd_one))
      · exact Or.inl (by rw [hi']; norm_num)
      · exact Or.inr (Or.inl (by rw [hi']; norm_num))
    · exact Or.inr (Or.inr hodd)
  · rcases orderOf_mul_isOrthA2 hQ hd.2 he.2 with ⟨-, h⟩ | hodd
    · exact ⟨pow_mem (mul_mem hd.1 he.1) 2, h h4⟩
    · rw [h4] at hodd
      exact absurd hodd (by decide)

theorem isRootInvolutionSet_preimage {G H : Type*} [Group G] [Group H] (f : H →* G)
    (hf : Function.Injective f) {D : Set G} (hD : IsRootInvolutionSet D) :
    IsRootInvolutionSet (f ⁻¹' D) := by
  obtain ⟨h1, h2, h3⟩ := hD
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx y hy h4 => ?_⟩
  · rw [← orderOf_injective f hf]
    exact h1 _ hx
  · have := h2 _ hx _ hy
    rwa [← map_mul, orderOf_injective f hf (x * y)] at this
  · rw [← orderOf_injective f hf, map_mul] at h4
    have := h3 _ hx _ hy h4
    rwa [← map_mul, ← map_pow] at this

theorem isOrthA2_conj_omega [Finite K] (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hn : finrank K V = 2 * m) (hm : m ≠ 2) {s t : V ≃ₗ[K] V} (hs : IsOrthA2 Q s)
    (ht : IsOrthA2 Q t) : ∃ g ∈ omegaGroup Q hQ, g * t * g⁻¹ = s := by
  have hO : ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = s := by
    refine (isConj_iff_suzukiLetter_eq hQ ht.mem ht.orderOf_eq_two hs.mem
      hs.orderOf_eq_two).mpr ?_
    exact ⟨(isOrthA2_iff_suzukiLetter.mp hs).2.2.1.trans
      (isOrthA2_iff_suzukiLetter.mp ht).2.2.1.symm, hs.finrank_eq.trans ht.finrank_eq.symm⟩
  have hset := omega_conj_eq_of_not_typeA_half hQ hn (ht.mem_omegaGroup hQ) ht.orderOf_eq_two
    (by
      rintro ⟨-, h⟩
      rw [ht.finrank_eq] at h
      exact hm h.symm)
  have : s ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x} := hO
  rw [← hset] at this
  exact this

end Pair

section Eichler

open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_zero_left eichler_mem_orthogonalGroup eichler_conj eichler_mem_elementaryGroup
  eichler_add_smul_self elementaryGroup elementaryGroup_le_of_eichler_mem HypPair)

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

private theorem eichler_apply_charTwo {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (x : V) :
    eichler Q u w x = x + polar Q x u • w + polar Q x w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero, sub_eq_add_neg, neg_vec_eq K]

private theorem eichler_mul_self' {u w : V} (huw : polar Q u w = 0) :
    eichler Q u w * eichler Q u w = 1 := by
  rw [eichler_mul huw huw, add_self_vec K, eichler_zero_right]

theorem isOrthA2_eichler [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate) {a b : V}
    (ha : Q a = 0) (hb : Q b = 0) (hab : polar Q a b = 0) (hli : LinearIndependent K ![a, b]) :
    IsOrthA2 Q (eichler Q a b) ∧ commSpace (eichler Q a b) = Submodule.span K {a, b} := by
  have hsub : ∀ x, eichler Q a b x - x = polar Q x a • b + polar Q x b • a := fun x => by
    rw [eichler_apply_charTwo ha hb hab x, add_assoc, add_sub_cancel_left]
  have hcomm : commSpace (eichler Q a b) = Submodule.span K {a, b} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
      rw [hsub x]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      rintro y (rfl | rfl)
      · obtain ⟨x, hxb, hxa⟩ :=
          exists_polar_eq_one_polar_eq_zero hQ (linearIndependent_pair_symm hli)
        have h := sub_mem_commSpace (eichler Q y b) x
        rwa [hsub, hxb, hxa, zero_smul, one_smul, zero_add] at h
      · obtain ⟨x, hxa, hxb⟩ := exists_polar_eq_one_polar_eq_zero hQ hli
        have h := sub_mem_commSpace (eichler Q a y) x
        rwa [hsub, hxa, hxb, zero_smul, one_smul, add_zero] at h
  refine ⟨⟨eichler_mem_orthogonalGroup Q a b, eichler_mul_self' hab, by
    rw [hcomm, finrank_span_pair hli], fun x hx => ?_⟩, hcomm⟩
  rw [hcomm] at hx
  obtain ⟨s, r, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, ha, hb, polar_smul_left,
    polar_smul_right, hab]
  simp

theorem IsOrthA2.exists_eq_eichler [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {t : V ≃ₗ[K] V} (ht : IsOrthA2 Q t) :
    ∃ a b : V, LinearIndependent K ![a, b] ∧ Q a = 0 ∧ Q b = 0 ∧ polar Q a b = 0 ∧
      t = eichler Q a b := by
  obtain ⟨a, b, hli, -, ha, hb, hab, h⟩ := ht.exists_apply_sub hQ
  refine ⟨a, b, hli, ha, hb, hab, LinearEquiv.ext fun v => ?_⟩
  rw [eichler_apply_charTwo ha hb hab v, add_assoc, ← h v]
  abel

theorem IsOrthA2.mem_elementaryGroup [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {t : V ≃ₗ[K] V} (ht : IsOrthA2 Q t) : t ∈ elementaryGroup Q := by
  obtain ⟨a, b, -, -, -, -, rfl⟩ := ht.exists_eq_eichler hQ
  exact eichler_mem_elementaryGroup Q a b

end Eichler

end CFSG.RankThree.GF2n.Smith81
