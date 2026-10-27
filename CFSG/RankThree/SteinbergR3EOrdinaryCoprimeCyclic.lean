module

public import CFSG.RankThree.SteinbergR3ECoprimeRankOne
public import CFSG.LieType.Chevalley.IntrinsicDiagramPermutation

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ordinary_Chevalley_coprime_large_prime_automorphism_subgroups_cyclic (τ : Tag)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K)) :
    (∀ P : Subgroup (MulAut (adjointGroup τ K)), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (adjointGroup τ K), p ≤ Nat.card α.ker := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_modGL (τ := τ) (K := K)
  have hp2 : p ≠ 2 := by omega
  have h24 : ¬ p ∣ 24 := not_dvd_factorial_of_le_four hp hp3 (n := 4) le_rfl
  have hrank : 0 < τ.rank := by cases τ <;> decide
  obtain ⟨ρ, -, -, -, -, hρrange, hρker, -⟩ :=
    exceptional_ordinary_rank_one_central_image (τ := τ) (K := K) ⟨0, hrank⟩
  have hρC : ρ.range ≤ adjointGroup τ K := by
    rw [hρrange, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_adjointGroup _ c
    · exact yUnit_mem_adjointGroup _ c
  have hpq : Nat.Coprime (Nat.card K - 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_sub_one_of_range_le ρ hρker hρC hp hp2 hpC)).symm
  obtain ⟨-, δ, -, hδcyc, -, -, -, hδker⟩ := ordinary_Chevalley_root_pair_common_field_parameter τ K
  have hkercop : Nat.Coprime (Nat.card δ.ker) p :=
    Nat.Coprime.coprime_dvd_left hδker (Nat.Coprime.pow_left _ hpq)
  obtain ⟨-, φ, hφ, -⟩ := exceptional_ordinary_intrinsic_simple_pairs τ K
  have hφ24 : ∀ β : unipotentPairAut τ K, φ β ^ 24 = 1 := by
    intro β
    by_cases hE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8
    · obtain ⟨-, h6, h7, h8⟩ := exceptional_E_intrinsic_diagram_permutation K
      rcases hE with rfl | rfl | rfl
      · have h2 : (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) ^ 2 = 1 :=
          TwistTag.E6.perm_pow_order
        rcases h6 β β.2 (φ β) (hφ β) with h | h
        · rw [h, one_pow]
        · have h2' : φ β ^ 2 = 1 := by
            rw [h]
            exact h2
          rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, h2', one_pow]
      · rw [h7 β β.2 (φ β) (hφ β), one_pow]
      · rw [h8 β β.2 (φ β) (hφ β), one_pow]
    · have hr : τ.rank ≤ 4 := by cases τ <;> simp_all [Tag.rank]
      obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hr
      rw [show (24 : ℕ) = (4 : ℕ).factorial from rfl, hm, pow_mul, perm_pow_card_factorial,
        one_pow]
  have hA₀ : ∀ Q : Subgroup (MulAut (adjointGroup τ K)), Q ≤ unipotentPairAut τ K →
      IsPGroup p Q → Q ≤ rootPairAut τ K := by
    intro Q hQA hQ α hα
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨α, hα⟩
    rw [Subgroup.orderOf_mk] at hk
    have hβk : φ ⟨α, hQA hα⟩ ^ p ^ k = 1 := by
      rw [← map_pow, ← hk, ← Subgroup.orderOf_mk α (hQA hα), pow_orderOf_eq_one, map_one]
    have hπ := eq_one_of_pow_eq_one_of_pow_prime_pow_eq_one hp h24 (hφ24 _) hβk
    refine mem_rootPairAut.2 fun i => ?_
    obtain ⟨hX, hY⟩ := hφ ⟨α, hQA hα⟩ i
    rw [hπ, Equiv.Perm.coe_one, id] at hX hY
    exact ⟨hX, hY⟩
  have hA : ∀ Q : Subgroup (MulAut (adjointGroup τ K)), Q ≤ unipotentPairAut τ K →
      IsPGroup p Q → IsCyclic Q := fun Q hQA hQ =>
    isCyclic_of_le_of_coprime_ker δ hδcyc hkercop (hA₀ Q hQA hQ) hQ
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨-, -, -, -, -, hopp⟩ := exceptional_ordinary_Sylow_opposition τ K (ringChar K) w₀ hw₀
  have hIA : ∀ α : MulAut (adjointGroup τ K), ∃ c : adjointGroup τ K,
      ∃ β ∈ unipotentPairAut τ K, α = MulAut.conj c * β := by
    intro α
    obtain ⟨c, β, hβU, hβV, rfl⟩ := hopp α
    exact ⟨c, β, ⟨hβU, hβV⟩, rfl⟩
  have hcyc : ∀ P : Subgroup (MulAut (adjointGroup τ K)), IsPGroup p P → IsCyclic P :=
    fun P hP => isCyclic_of_isPGroup_of_conj_mul hp hpC hIA hA hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
