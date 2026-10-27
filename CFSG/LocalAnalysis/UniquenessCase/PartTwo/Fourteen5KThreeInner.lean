module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Inputs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner conjOnNormalizer
  conjOnNormalizer_apply conjOnNormalizer_iterate)

theorem kThreeInner_of_autThreePowInner
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsCatalogGroup S → (Nat.card S).factorization 3 = 1 → AutThreePowInner S) :
    KThreeInner := by
  intro A _ _ hK J hJ h3 h9 x hx hx3
  haveI := hJ
  let ψ : ↥J ≃* ↥J := conjOnNormalizer J x hx
  have hψ3 : ∀ a : ↥J, ψ^[3] a = a := by
    intro a
    apply Subtype.ext
    show (((conjOnNormalizer J x hx)^[3] a : ↥J) : A) = ((a : ↥J) : A)
    rw [conjOnNormalizer_iterate J x hx 3 a]
    simp [hx3]
  by_cases hab : ∃ a b : ↥J, a * b ≠ b * a
  · have hcat : IsCatalogGroup ↥J :=
      hK.isCatalogGroup_of_surjective J hab (MonoidHom.id ↥J) Function.surjective_id
    have hfac : (Nat.card ↥J).factorization 3 = 1 := by
      have hn : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
      have h1 : 1 ≤ (Nat.card ↥J).factorization 3 := by
        have := Nat.Prime.factorization_pos_of_dvd Nat.prime_three hn h3
        omega
      have h2 : ¬ 2 ≤ (Nat.card ↥J).factorization 3 := by
        intro hle
        have hdvd : 3 ^ 2 ∣ Nat.card ↥J := by
          rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn]
          exact hle
        have h9' : 9 ∣ Nat.card ↥J := by simpa using hdvd
        exact h9 h9'
      omega
    have hψ := h ↥J hJ hab hcat hfac ψ 1 (by simpa using hψ3)
    obtain ⟨a, ha⟩ := hψ
    refine ⟨(a : A), a.2, ?_⟩
    intro y hy
    have h1 : x * y * x⁻¹ = ((ψ ⟨y, hy⟩ : ↥J) : A) := by
      simp [ψ, conjOnNormalizer_apply]
    rw [h1, ha ⟨y, hy⟩]
    simp
  · have hcomm : ∀ a b : ↥J, a * b = b * a := by
      intro a b
      exact not_not.mp (not_exists.mp (not_exists.mp hab a) b)
    letI : CommGroup ↥J := { (inferInstance : Group ↥J) with mul_comm := hcomm }
    have hprime : (Nat.card ↥J).Prime := IsSimpleGroup.prime_card
    have hcard : Nat.card ↥J = 3 := by
      have h3' : 3 ∣ Nat.card ↥J := h3
      have := Nat.Prime.eq_one_or_self_of_dvd hprime 3 h3'
      rcases this with h | h
      · omega
      · exact h.symm
    haveI : Fact (Nat.card ↥J).Prime := ⟨hprime⟩
    have hnt : Nontrivial ↥J := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    obtain ⟨g, hg_ne⟩ := exists_ne (1 : ↥J)
    have hg_gen : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hcard hg_ne
    have hg : ∀ x : ↥J, x ∈ Subgroup.zpowers g := fun x => by rw [hg_gen]; exact Subgroup.mem_top x
    have hg3 : g ^ (3 : ℕ) = 1 := by
      have horder : orderOf g = 3 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
      rw [← horder]
      exact pow_orderOf_eq_one g
    have hψg : ψ g = g := by
      have hmem : ψ g ∈ Subgroup.zpowers g := hg (ψ g)
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      have hk_mod : g ^ k = g ^ (k % 3 : ℤ) := by
        conv_lhs => rw [← Int.emod_add_ediv_mul k 3]
        rw [zpow_add, zpow_mul]
        have h1 : (g ^ (k / 3)) ^ (3 : ℤ) = 1 := by
          rw [← zpow_mul, mul_comm, zpow_mul]
          rw [show g ^ (3 : ℤ) = g ^ (3 : ℕ) from zpow_natCast g 3]
          rw [hg3]
          simp
        rw [h1, mul_one]
      have hk0 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
        have h1 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
        have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
        omega
      rcases hk0 with h0 | h1 | h2
      · exfalso
        have hψg1 : ψ g = 1 := by rw [← hk, hk_mod, h0]; simp
        have : g = 1 := ψ.injective (by rw [hψg1, map_one])
        exact hg_ne this
      · rw [← hk, hk_mod, h1]; simp
      · exfalso
        have hg2 : ψ g = g ^ 2 := by rw [← hk, hk_mod, h2]; simp
        have h2' : ψ^[2] g = g := by
          rw [Function.iterate_succ_apply', Function.iterate_one, hg2, map_pow, hg2, ← pow_mul]
          norm_num
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hg3]
          simp
        have h3' : ψ^[3] g = g ^ 2 := by
          rw [Function.iterate_succ_apply', h2', hg2]
        have := hψ3 g
        rw [h3'] at this
        have : g = 1 := by
          have := congrArg (fun x => x * g⁻¹) this
          simpa [pow_succ, mul_assoc] using this
        exact hg_ne this
    have hψid : ∀ y : ↥J, ψ y = y := by
      intro y
      have hy : y ∈ Subgroup.zpowers g := hg y
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨n, hn⟩ := hy
      rw [← hn, map_zpow, hψg]
    refine ⟨1, Subgroup.one_mem J, ?_⟩
    intro y hy
    have h1 : x * y * x⁻¹ = ((ψ ⟨y, hy⟩ : ↥J) : A) := by
      simp [ψ, conjOnNormalizer_apply]
    rw [h1, hψid ⟨y, hy⟩]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
