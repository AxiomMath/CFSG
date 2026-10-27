module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.StandardType.QTwo

variable {G : Type} [Group G]

@[expose] def qTwoNbrRec_Delta (K : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ K ∧ (∀ k ∈ K, z * k = k * z) ∧ ∃ n : ℕ, z ^ 2 ^ n = 1}
  mul_mem' := by
    rintro a b ⟨haK, hac, n, hn⟩ ⟨hbK, hbc, m, hm⟩
    refine ⟨K.mul_mem haK hbK, fun k hk => ?_, n + m, ?_⟩
    · rw [mul_assoc, hbc k hk, ← mul_assoc, hac k hk, mul_assoc]
    · have hab : Commute a b := hac b hbK
      have h1 : a ^ 2 ^ (n + m) = 1 := by
        rw [pow_add, pow_mul, hn, one_pow]
      have h2 : b ^ 2 ^ (n + m) = 1 := by
        rw [add_comm, pow_add, pow_mul, hm, one_pow]
      rw [hab.mul_pow, h1, h2, one_mul]
  one_mem' := ⟨K.one_mem, fun k _ => by rw [one_mul, mul_one], 0, by simp⟩
  inv_mem' := by
    rintro a ⟨haK, hac, n, hn⟩
    refine ⟨K.inv_mem haK, fun k hk => ?_, n, by rw [inv_pow, hn, inv_one]⟩
    have h := hac k⁻¹ (K.inv_mem hk)
    calc a⁻¹ * k = a⁻¹ * k * (a * a⁻¹) := by group
      _ = a⁻¹ * (k * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * k) * a⁻¹ := by
        have h' := hac k hk
        rw [← h']
      _ = k * a⁻¹ := by group

theorem qTwoNbrRec_mem_Delta_iff {K : Subgroup G} {z : G} :
    z ∈ qTwoNbrRec_Delta K ↔
      z ∈ K ∧ (∀ k ∈ K, z * k = k * z) ∧ ∃ n : ℕ, z ^ 2 ^ n = 1 :=
  Iff.rfl

theorem qTwoNbrRec_Delta_le (K : Subgroup G) : qTwoNbrRec_Delta K ≤ K := fun _ hz => hz.1

theorem qTwoNbrRec_Delta_central {K : Subgroup G} {d : G} (hd : d ∈ qTwoNbrRec_Delta K) :
    ∀ k ∈ K, d * k = k * d := hd.2.1

theorem qTwoNbrRec_Delta_isPGroup (K : Subgroup G) : IsPGroup 2 (qTwoNbrRec_Delta K) := by
  intro g
  obtain ⟨n, hn⟩ := g.2.2.2
  exact ⟨n, Subtype.ext (by simpa [Subgroup.coe_pow] using hn)⟩

theorem qTwoNbrRec_mem_Delta_of_pow {K : Subgroup G} {z : G} (hz : z ∈ K)
    (hc : ∀ k ∈ K, z * k = k * z) {n : ℕ} (hn : z ^ 2 ^ n = 1) : z ∈ qTwoNbrRec_Delta K :=
  ⟨hz, hc, n, hn⟩

theorem qTwoNbrRec_Delta_conj {K : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) {z : G} (hz : z ∈ qTwoNbrRec_Delta K) :
    b * z * b⁻¹ ∈ qTwoNbrRec_Delta K := by
  obtain ⟨hzK, hzc, n, hn⟩ := hz
  refine ⟨?_, ?_, n, ?_⟩
  · exact (Subgroup.mem_set_normalizer_iff.mp hb z).mp hzK
  · intro k hk
    have hbk : b⁻¹ * k * b ∈ K := by
      have h := (Subgroup.mem_set_normalizer_iff.mp (inv_mem hb) k).mp hk
      simpa using h
    have hcomm := hzc (b⁻¹ * k * b) hbk
    calc b * z * b⁻¹ * k = b * (z * (b⁻¹ * k * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * k * b) * z) * b⁻¹ := by rw [hcomm]
      _ = k * (b * z * b⁻¹) := by group
  · rw [conj_pow, hn, mul_one, mul_inv_cancel]

private theorem qTwoNbrRec_delta_normalizer_le (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((qTwoNbrRec_Delta K : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_set_normalizer_iff] at hb ⊢
  intro h
  refine ⟨fun hh => qTwoNbrRec_Delta_conj hb hh, fun hh => ?_⟩
  have h' := qTwoNbrRec_Delta_conj (inv_mem hb) hh
  have heq : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
  rw [heq] at h'
  exact h'

theorem qTwoNbrRec_Delta_normal_sup {K Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ((qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs)).Normal := by
  have hΔle : qTwoNbrRec_Delta K ≤ K ⊔ Bs := (qTwoNbrRec_Delta_le K).trans le_sup_left
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hΔle]
  exact (sup_le Subgroup.le_normalizer hN).trans (qTwoNbrRec_delta_normalizer_le K)

theorem qTwoNbrRec_exists_quot {K Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (Q : Type) (_ : Group Q) (q : ↥(K ⊔ Bs) →* Q), Function.Surjective q ∧
      q.ker = (qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs) := by
  let N := (qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs)
  haveI : N.Normal := qTwoNbrRec_Delta_normal_sup hN
  exact ⟨↥(K ⊔ Bs) ⧸ N, inferInstance, QuotientGroup.mk' N,
    QuotientGroup.mk'_surjective N, QuotientGroup.ker_mk' N⟩

end CFSG.StandardType.QTwo

end
