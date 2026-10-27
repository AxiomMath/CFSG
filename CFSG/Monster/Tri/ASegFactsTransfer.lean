module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.Monster.Tri

open Subgroup

section Abstract

variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
theorem not_index_two_of_perfect (hJ : commutator J = ⊤) (N : Subgroup J) [N.Normal]
    (hN : N.index = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (J ⧸ N) = 2 := by rw [← Subgroup.index, hN]
  have hcyc : IsCyclic (J ⧸ N) := isCyclic_of_prime_card hcard
  let _ : CommGroup (J ⧸ N) := IsCyclic.commGroup
  have hle : commutator J ≤ (QuotientGroup.mk' N).ker :=
    Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [hJ, QuotientGroup.ker_mk', top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hN
  omega

theorem exists_conj_mem_of_not_four_dvd_index {I : Subgroup J} (hidx : ¬ 4 ∣ I.index)
    (hperf : 2 ∣ I.index → ∀ N : Subgroup J, N.Normal → N.index = 2 → False) {t : J}
    (ht2 : orderOf t = 2) :
    ∃ g : J, g * t * g⁻¹ ∈ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 I) := inferInstance
  set P₀ : Subgroup J := (S : Subgroup I).map I.subtype with hP₀
  have hP₀p : IsPGroup 2 P₀ := S.isPGroup'.map I.subtype
  obtain ⟨T, hPT⟩ := hP₀p.exists_le_sylow
  have hP₀I : P₀ ≤ I := Subgroup.map_subtype_le _
  have hrel : P₀.relIndex (T : Subgroup J) = 1 ∨
      (P₀.relIndex (T : Subgroup J) = 2 ∧ 2 ∣ I.index) := by
    have h1 : P₀.relIndex (T : Subgroup J) * (T : Subgroup J).index = P₀.index :=
      Subgroup.relIndex_mul_index hPT
    have h2 : P₀.index = (S : Subgroup I).index * I.index := Subgroup.index_map_subtype _
    have hT : ¬ 2 ∣ (T : Subgroup J).index := Sylow.not_dvd_index T
    have hS : ¬ 2 ∣ (S : Subgroup I).index := Sylow.not_dvd_index S
    obtain ⟨n, hn⟩ := (T.isPGroup').index (P₀.subgroupOf (T : Subgroup J))
    have hn' : P₀.relIndex (T : Subgroup J) = 2 ^ n := hn
    by_cases hn2 : 2 ≤ n
    · exfalso
      apply hidx
      have h4 : 4 ∣ 2 ^ n := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn2
        exact ⟨2 ^ k, by ring⟩
      have h5 : 4 ∣ (S : Subgroup I).index * I.index := by
        rw [← h2, ← h1, hn']
        exact h4.mul_right _
      have hcop : Nat.Coprime 4 (S : Subgroup I).index := by
        have : Nat.Coprime 2 (S : Subgroup I).index := (Nat.Prime.coprime_iff_not_dvd
          Nat.prime_two).2 hS
        simpa using this.pow_left 2
      exact hcop.dvd_of_dvd_mul_left h5
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · exact Or.inl (by simpa using hn')
      · refine Or.inr ⟨by simpa using hn', ?_⟩
        have h5 : 2 ∣ (S : Subgroup I).index * I.index := by
          rw [← h2, ← h1, hn']
          exact Dvd.dvd.mul_right (by simp) _
        have hcop : Nat.Coprime 2 (S : Subgroup I).index :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hS
        exact hcop.dvd_of_dvd_mul_left h5
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨T', hT'⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J T' T
  have htT : g * t * g⁻¹ ∈ (T : Subgroup J) := by
    have h2 : g * t * g⁻¹ ∈ ((g • T' : Sylow 2 J) : Set J) := by
      rw [Sylow.coe_smul]
      exact Set.mem_smul_set.2 ⟨t, hT' (Subgroup.mem_zpowers t), by simp⟩
    rw [hg] at h2
    exact h2
  rcases hrel with h1 | ⟨h2, h2d⟩
  ·
    exact ⟨g, hP₀I ((Subgroup.relIndex_eq_one.1 h1) htT)⟩
  · by_cases hex : ∃ g' : J, g'⁻¹ * (g * t * g⁻¹) * g' ∈ P₀
    · obtain ⟨g', hg'⟩ := hex
      refine ⟨g'⁻¹ * g, hP₀I ?_⟩
      convert hg' using 1
      group
    · push Not at hex
      exfalso
      have hord : orderOf (g * t * g⁻¹) = 2 := by
        rw [← ht2]
        simpa using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
      obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
        T.isPGroup' (Sylow.not_dvd_index T) hPT h2 htT (by simpa using hex 1)
        (fun y hyT hyU => by
          rw [hord]
          have hy1 : y ≠ 1 := fun e => hyU (e ▸ P₀.one_mem)
          have hy2 : orderOf y ≠ 1 := fun e => hy1 (orderOf_eq_one_iff.1 e)
          have := orderOf_pos y
          omega)
        hex
      exact hperf h2d N hN hNidx

end Abstract

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_relIndex {J I : Subgroup G} (hidx : ¬ 4 ∣ I.relIndex J)
    (hperf : 2 ∣ I.relIndex J → ⁅J, J⁆ = J) {t : G} (htJ : t ∈ J) (ht2 : orderOf t = 2) :
    ∃ g ∈ J, g * t * g⁻¹ ∈ I := by
  have hperf' : 2 ∣ I.relIndex J → commutator J = ⊤ := by
    intro h2
    have hp := hperf h2
    have h1 := Subgroup.map_commutator (⊤ : Subgroup J) (⊤ : Subgroup J) J.subtype
    simp only [Subgroup.map_top, Subgroup.range_subtype] at h1
    have h2' : (commutator J).map J.subtype = J := by
      rw [commutator_def, h1, hp]
    apply Subgroup.map_injective J.subtype_injective
    rw [h2', Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_four_dvd_index (J := J) (I := I.subgroupOf J)
    (by simpa [Subgroup.relIndex] using hidx)
    (fun h2 N hN hNi => by
      have := hN
      exact not_index_two_of_perfect (hperf' (by simpa [Subgroup.relIndex] using h2)) N hNi)
    (t := ⟨t, htJ⟩) (by rw [Subgroup.orderOf_mk]; exact ht2)
  refine ⟨g, g.2, ?_⟩
  simpa [Subgroup.mem_subgroupOf] using hg

end Ambient

end CFSG.Monster.Tri
