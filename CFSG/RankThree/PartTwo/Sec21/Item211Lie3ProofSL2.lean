module

import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3PlusInn

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement MatrixGroups

namespace Item211Lie3Proof

open Matrix

variable {K : Type} [Field K]

@[expose] def IsScalar2 (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1

theorem commute_of_commute_nonscalar {M N N' : Matrix (Fin 2) (Fin 2) K} (hM : ¬ IsScalar2 M)
    (hN : M * N = N * M) (hN' : M * N' = N' * M) : N * N' = N' * N := by
  have a1 := congrFun (congrFun hN 0) 0
  have a2 := congrFun (congrFun hN 0) 1
  have a3 := congrFun (congrFun hN 1) 0
  have b1 := congrFun (congrFun hN' 0) 0
  have b2 := congrFun (congrFun hN' 0) 1
  have b3 := congrFun (congrFun hN' 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3 b1 b2 b3
  have key : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 ∧
      N' 0 1 * (N 0 0 - N 1 1) = N 0 1 * (N' 0 0 - N' 1 1) ∧
      N 1 0 * (N' 0 0 - N' 1 1) = N' 1 0 * (N 0 0 - N 1 1) := by
    by_cases ha : M 0 1 = 0
    · by_cases hb : M 1 0 = 0
      · have hc : M 0 0 - M 1 1 ≠ 0 := fun hc => hM ⟨ha, hb, sub_eq_zero.mp hc⟩
        have hx : N 0 1 = 0 := by
          have : N 0 1 * (M 0 0 - M 1 1) = 0 := by rw [ha] at a2; linear_combination a2
          exact (mul_eq_zero.mp this).resolve_right hc
        have hy : N 1 0 = 0 := by
          have : N 1 0 * (M 0 0 - M 1 1) = 0 := by rw [hb] at a3; linear_combination -a3
          exact (mul_eq_zero.mp this).resolve_right hc
        have hx' : N' 0 1 = 0 := by
          have : N' 0 1 * (M 0 0 - M 1 1) = 0 := by rw [ha] at b2; linear_combination b2
          exact (mul_eq_zero.mp this).resolve_right hc
        have hy' : N' 1 0 = 0 := by
          have : N' 1 0 * (M 0 0 - M 1 1) = 0 := by rw [hb] at b3; linear_combination -b3
          exact (mul_eq_zero.mp this).resolve_right hc
        refine ⟨?_, ?_, ?_⟩ <;> simp [hx, hy, hx', hy']
      · have t1 : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 := by
          refine mul_left_cancel₀ hb ?_
          linear_combination N 1 0 * b1 - N' 1 0 * a1
        refine ⟨t1, mul_left_cancel₀ hb ?_, mul_left_cancel₀ hb ?_⟩
        · linear_combination N' 0 1 * a3 - N 0 1 * b3 - (M 0 0 - M 1 1) * t1
        · linear_combination N 1 0 * b3 - N' 1 0 * a3
    · have t1 : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 := by
        refine mul_left_cancel₀ ha ?_
        linear_combination N 0 1 * b1 - N' 0 1 * a1
      refine ⟨t1, mul_left_cancel₀ ha ?_, mul_left_cancel₀ ha ?_⟩
      · linear_combination N 0 1 * b2 - N' 0 1 * a2
      · linear_combination -(M 0 0 - M 1 1) * t1 - N 1 0 * b2 + N' 1 0 * a2
  obtain ⟨k1, k2, k3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination k1 | linear_combination -k1 | linear_combination k2 |
      linear_combination -k2 | linear_combination k3

theorem eq_one_or_trace_eq_neg_one {x : Matrix (Fin 2) (Fin 2) K} (hdet : x.det = 1)
    (hx3 : x * x * x = 1) : x = 1 ∨ x.trace = -1 := by
  have hch : x * x = x.trace • x - 1 := by
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
      first | ring1 | linear_combination hd | linear_combination -hd
  set t := x.trace with ht
  have h3 : x * x * x = (t ^ 2 - 1) • x - t • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hch, Matrix.sub_mul, Matrix.smul_mul, hch, Matrix.one_mul, smul_sub, smul_smul]
    module
  rw [hx3] at h3
  by_cases ht2 : t ^ 2 - 1 = 0
  · right
    have h4 : (t ^ 2 - 1) • x = 0 := by rw [ht2, zero_smul]
    rw [h4, zero_sub] at h3
    have := congrFun (congrFun h3 0) 0
    simp at this
    linear_combination this
  · left
    have h5 : (t ^ 2 - 1) • x = (1 + t) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [add_smul, one_smul]
      exact (eq_sub_iff_add_eq.mp h3).symm
    set c := (t ^ 2 - 1)⁻¹ * (1 + t) with hc
    have hxc : x = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [hc, ← smul_smul, ← h5, smul_smul, inv_mul_cancel₀ ht2, one_smul]
    have hc2 : c * c = 1 := by
      have := hdet
      rw [hxc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
      linear_combination this
    have hc3 : c * c * c = 1 := by
      have := congrFun (congrFun hx3 0) 0
      rw [hxc] at this
      simp [Matrix.smul_apply] at this
      linear_combination this
    have hc1 : c = 1 := by
      rw [hc2, one_mul] at hc3
      exact hc3
    rw [hxc, hc1, one_smul]

theorem isScalar2_of_commute_transvections {M : Matrix (Fin 2) (Fin 2) K}
    (hu : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M) (hl : M * !![1, 0; 1, 1] = !![1, 0; 1, 1] * M) :
    IsScalar2 M := by
  have e1 := congrFun (congrFun hu 0) 0
  have e2 := congrFun (congrFun hu 0) 1
  have e3 := congrFun (congrFun hl 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e3
  · linear_combination e1
  · linear_combination e2

theorem eq_top_of_normal_not_le_center [Finite K] (hK4 : 4 ≤ Nat.card K) (N : Subgroup SL(2, K))
    [hNn : N.Normal] (hN : ¬ N ≤ Subgroup.center SL(2, K)) : N = ⊤ := by
  have h34 : 3 ≤ 2 ∨ ∃ s : Finset K, s.card = 4 :=
    Or.inr (CFSG.LinearGroups.exists_finset_card_eq_four hK4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2)
    le_rfl h34
  have hperf : Group.IsPerfect SL(2, K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect
      (CFSG.LinearGroups.exists_finset_card_eq_four hK4)
  set Z := Subgroup.center SL(2, K)
  have hnorm : (N.map (QuotientGroup.mk' Z)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective Z)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · exfalso
    apply hN
    intro a ha
    have : QuotientGroup.mk' Z a = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem _ ha
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  ·
    have hNZ : ∀ A : SL(2, K), ∃ B ∈ N, B⁻¹ * A ∈ Z := by
      intro A
      obtain ⟨B, hB, hBA⟩ : QuotientGroup.mk' Z A ∈ N.map (QuotientGroup.mk' Z) :=
        h ▸ Subgroup.mem_top _
      exact ⟨B, hB, QuotientGroup.eq.mp hBA⟩
    rw [eq_top_iff]
    intro A _
    have hA : A ∈ commutator SL(2, K) := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact Subgroup.mem_top A
    rw [commutator_def] at hA
    refine (Subgroup.commutator_le.mpr fun a _ b _ => ?_) hA
    obtain ⟨a', ha', haz⟩ := hNZ a
    obtain ⟨b', hb', hbz⟩ := hNZ b
    have ha1 : QuotientGroup.mk' N a' = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha'
    have hb1 : QuotientGroup.mk' N b' = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hb'
    have e1 : QuotientGroup.mk' N a = QuotientGroup.mk' N (a'⁻¹ * a) := by
      rw [map_mul, map_inv, ha1, inv_one, one_mul]
    have e2 : QuotientGroup.mk' N b = QuotientGroup.mk' N (b'⁻¹ * b) := by
      rw [map_mul, map_inv, hb1, inv_one, one_mul]
    have hc : (⁅a'⁻¹ * a, b'⁻¹ * b⁆ : SL(2, K)) = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp haz _).symm
    have key : QuotientGroup.mk' N (⁅a, b⁆ : SL(2, K)) = 1 := by
      rw [map_commutatorElement, e1, e2, ← map_commutatorElement, hc, map_one]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at key
    exact key

theorem not_isScalar2_of_root (h3 : (3 : K) ≠ 0) {m : Matrix (Fin 2) (Fin 2) K} (hdet : m.det = 1)
    (hm : m * m + m + 1 = 0) : ¬ IsScalar2 m := by
  rintro ⟨h01, h10, h00⟩
  have e := congrFun (congrFun hm 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, h01] at e
  rw [h00] at e
  rw [Matrix.det_fin_two, h01, h00] at hdet
  apply h3
  linear_combination (2 - m 1 1) * e + (m 1 1 - 1) * hdet

theorem mem_of_normalizer [Finite K] (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {M : Type*}
    [Group M] (Ψ : SL(2, K) →* M) {C : Subgroup M}
    (hN : ∀ a, Ψ a ∈ Subgroup.normalizer (C : Set M)) {X : SL(2, K)}
    (hX : ¬ IsScalar2 (X : Matrix (Fin 2) (Fin 2) K)) (hX3 : X ^ 3 = 1) {z : M}
    (hz : ∀ a, Ψ a * z = z * Ψ a) (hXz : Ψ X * z ∈ C) (a : SL(2, K)) : Ψ a ∈ C := by
  set N := C.comap Ψ with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    change Ψ (g * n * g⁻¹) ∈ C
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN g) _).mp hn⟩
  have hcomm : ∀ g : SL(2, K), g * X * g⁻¹ * X⁻¹ ∈ N := by
    intro g
    change Ψ (g * X * g⁻¹ * X⁻¹) ∈ C
    have hz' : z * (Ψ g)⁻¹ = (Ψ g)⁻¹ * z := by
      rw [← map_inv]
      exact (hz _).symm
    have e : Ψ (g * X * g⁻¹ * X⁻¹) = Ψ g * (Ψ X * z) * (Ψ g)⁻¹ * (Ψ X * z)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc Ψ g * Ψ X * (Ψ g)⁻¹ * (Ψ X)⁻¹ = Ψ g * Ψ X * ((Ψ g)⁻¹ * z) * z⁻¹ * (Ψ X)⁻¹ := by group
        _ = Ψ g * Ψ X * (z * (Ψ g)⁻¹) * z⁻¹ * (Ψ X)⁻¹ := by rw [hz']
        _ = Ψ g * (Ψ X * z) * (Ψ g)⁻¹ * (Ψ X * z)⁻¹ := by group
    rw [e]
    exact C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN g) _).mp hXz) (C.inv_mem hXz)
  have hX1 : (X : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    hX ⟨by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl⟩
  have hXX : (X : Matrix (Fin 2) (Fin 2) K) * X * X = 1 := by
    have e := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hX3
    simpa [pow_succ] using e
  have htr : (X : Matrix (Fin 2) (Fin 2) K).trace = -1 :=
    (eq_one_or_trace_eq_neg_one X.2 hXX).resolve_left hX1
  have hcen : ∀ g : SL(2, K), g * X * g⁻¹ * X⁻¹ ∈ Subgroup.center SL(2, K) →
      (g : Matrix (Fin 2) (Fin 2) K) * X = X * g := by
    intro g hg
    have hgX : g * X * g⁻¹ = X := by
      rcases Item211Lie2Proof.eq_one_or_eq_neg_one_of_mem_center hg with h1 | h1
      · calc g * X * g⁻¹ = g * X * g⁻¹ * X⁻¹ * X := by group
          _ = X := by rw [h1, one_mul]
      · exfalso
        have e : g * X * g⁻¹ = -X := by
          calc g * X * g⁻¹ = g * X * g⁻¹ * X⁻¹ * X := by group
            _ = -X := by rw [h1, neg_one_mul]
        have e' := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K).trace) e
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.trace_neg] at e'
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, htr] at e'
        apply h2
        linear_combination -e'
    have e := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hgX
    calc (g : Matrix (Fin 2) (Fin 2) K) * X = ((g * X * g⁻¹ : SL(2, K)) :
          Matrix (Fin 2) (Fin 2) K) * g := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
            Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul g⁻¹, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
      _ = X * g := by rw [hgX]
  have htop : N = ⊤ := by
    refine eq_top_of_normal_not_le_center hK4 N fun hle => hX ?_
    let u : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let l : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    exact isScalar2_of_commute_transvections (hcen u (hle (hcomm u))).symm
      (hcen l (hle (hcomm l))).symm
  have ha : a ∈ N := htop ▸ Subgroup.mem_top a
  exact ha

theorem mem_center_of_pairHom [Finite K] (hK4 : 4 ≤ Nat.card K) {M : Type*} [Group M]
    (Φ : SL(2, K) × SL(2, K) →* M) {Q : Subgroup M} (hQ : IsPGroup 2 Q)
    (hN : ∀ a, Φ (a, 1) ∈ Subgroup.normalizer (Q : Set M))
    (hker : ∀ a b, Φ (a, b) = 1 → a = 1 ∨ a = -1) {a b : SL(2, K)} (hab : Φ (a, b) ∈ Q) :
    a ∈ Subgroup.center SL(2, K) := by
  set N := (Q.comap Φ).map (MonoidHom.fst SL(2, K) SL(2, K)) with hNdef
  have hNn : N.Normal := ⟨by
    rintro _ ⟨⟨a', b'⟩, hab', rfl⟩ g
    refine ⟨(g * a' * g⁻¹, b'), ?_, rfl⟩
    change Φ (g * a' * g⁻¹, b') ∈ Q
    have e : ((g * a' * g⁻¹, b') : SL(2, K) × SL(2, K)) = (g, 1) * (a', b') * (g, 1)⁻¹ := by
      ext1 <;> simp
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN g) _).mp hab'⟩
  have h2 : ∀ c ∈ N, ∃ e : ℕ, c ^ 2 ^ e = 1 := by
    rintro _ ⟨⟨a', b'⟩, hab', rfl⟩
    obtain ⟨k, hk⟩ := hQ ⟨_, hab'⟩
    have hk' : Φ (a' ^ 2 ^ k, b' ^ 2 ^ k) = 1 := by
      rw [← Prod.pow_mk, map_pow]
      exact congrArg Subtype.val hk
    refine ⟨k + 1, ?_⟩
    change a' ^ 2 ^ (k + 1) = 1
    rw [pow_succ, pow_mul]
    rcases hker _ _ hk' with h | h
    · rw [h, one_pow]
    · rw [h]
      apply Subtype.ext
      simp [sq]
  exact Item211Lie2Proof.le_center_of_normal_two hK4 N h2 ⟨(a, b), hab, rfl⟩

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
