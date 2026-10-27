module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofSylow

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

theorem exists_conj_normalizes_torsion3 {Γ : Type*} [Group Γ] [Finite Γ] (T : Subgroup Γ)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hidx : ¬ 9 ∣ T.index) {y : Γ} (hy : y ^ 3 = 1) :
    ∃ g : Γ, ∀ t ∈ torsion3 T hT, g⁻¹ * y * g * t * (g⁻¹ * y * g)⁻¹ ∈ torsion3 T hT := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := torsion3 T hT with hA
  have hAp : IsPGroup 3 (A.subgroupOf T) := by
    intro t
    refine ⟨1, ?_⟩
    have h3 : ((t : T) : Γ) ^ 3 = 1 := (Subgroup.mem_subgroupOf.1 t.2).2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h3
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  set T₃ := (S : Subgroup T).map T.subtype with hT₃
  have hT₃p : IsPGroup 3 T₃ := S.isPGroup'.map T.subtype
  obtain ⟨P, hT₃P⟩ := hT₃p.exists_le_sylow
  have hAT₃ : A ≤ T₃ := by
    intro t ht
    exact ⟨⟨t, ht.1⟩, hAS (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hT₃T : T₃ ≤ T := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hnorm : (T₃.subgroupOf (P : Subgroup Γ)).Normal :=
    normal_of_index_dvd_prime P.isPGroup' _ (relindex_dvd_three T hidx S P hT₃P)
  have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P Q
  have hyQ : y ∈ (Q : Subgroup Γ) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
  have hy₁P : g⁻¹ * y * g ∈ (P : Subgroup Γ) := by
    have : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
      simp [MulAut.smul_def]
    rw [← this]
    exact hyQ
  refine ⟨g, fun t ht => ?_⟩
  have h1 : g⁻¹ * y * g * t * (g⁻¹ * y * g)⁻¹ ∈ T₃ := by
    have := hnorm.conj_mem ⟨t, hT₃P (hAT₃ ht)⟩ (Subgroup.mem_subgroupOf.2 (hAT₃ ht))
      ⟨g⁻¹ * y * g, hy₁P⟩
    exact Subgroup.mem_subgroupOf.1 this
  refine ⟨hT₃T h1, ?_⟩
  rw [conj_pow, ht.2]
  group

theorem commute_of_conj_eq_or_sq {G : Type*} [Group G] {y a : G} (hy : y ^ 3 = 1)
    (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (h : y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a ^ 2) :
    y * a = a * y := by
  rcases h with h | h
  · calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h]
  · exfalso
    apply ha1
    have hc : ∀ n : ℕ, y * a ^ n * y⁻¹ = a ^ (2 * n) := by
      intro n
      rw [← conj_pow, h, ← pow_mul]
    have h3 : y ^ 3 * a * (y ^ 3)⁻¹ = a ^ 8 := by
      have e : y ^ 3 * a * (y ^ 3)⁻¹ = y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ := by
        rw [pow_three']
        group
      rw [e, h, hc 2, hc]
    rw [hy, one_mul, inv_one, mul_one] at h3
    have h8 : a ^ 8 = a ^ 2 := by
      rw [show 8 = 3 * 2 + 2 from rfl, pow_add, pow_mul, ha, one_pow, one_mul]
    rw [h8] at h3
    have h4 : a * a = a * 1 := by rw [mul_one, ← sq, ← h3]
    exact mul_left_cancel h4

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
