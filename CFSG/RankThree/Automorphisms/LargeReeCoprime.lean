module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeCommonField
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (card_SL_eq)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_opposite_Sylow_stabilizer_common_field_parameter)
open CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog (largeReeOppAut U1_le_reeGamma)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem large_Ree_coprime_odd_prime_automorphism_subgroups_cyclic (a : ℕ) (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hpΓ : ¬ p ∣ Nat.card (F4.reeGamma K a)) :
    (∀ P : Subgroup (MulAut (F4.reeGamma K a)), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (F4.reeGamma K a), p ≤ Nat.card α.ker := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨-, -, -, ⟨R, -⟩, -⟩ := large_Ree_A1_pair_automorphism_bound a K hK
  have hM : largeReeA1M K a ≤ F4.reeGamma K a :=
    sup_le U1_le_reeGamma fun x hx => (Subgroup.mem_inf.1 hx).2
  have hqΓ : Nat.card K - 1 ∣ Nat.card (F4.reeGamma K a) := by
    have h1 := card_SL_eq (K := K) (n := 2) (by norm_num)
    have h2 : Nat.card K ^ 2 - 1 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1) (by simp)).trans
        (Dvd.intro_left _ h1.symm)
    have h3 := Nat.pow_sub_one_dvd_pow_sub_one (x := Nat.card K) (one_dvd 2)
    rw [pow_one] at h3
    refine h3.trans (h2.trans ?_)
    rw [Nat.card_congr R.toEquiv]
    exact Subgroup.card_dvd_of_le hM
  have hpq : Nat.Coprime (2 ^ (2 * a + 1) - 1) p := by
    rw [← hK]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpΓ (h.trans hqΓ)).symm
  obtain ⟨-, -, -, -, -, δ, -, hδcyc, hδker⟩ :=
    large_Ree_opposite_Sylow_stabilizer_common_field_parameter a ha K hK
  have hkercop : Nat.Coprime (Nat.card δ.ker) p :=
    Nat.Coprime.coprime_dvd_left hδker (Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)) (Nat.Coprime.pow_left 2 hpq))
  have hA : ∀ Q : Subgroup (MulAut (F4.reeGamma K a)), Q ≤ largeReeOppAut K a →
      IsPGroup p Q → IsCyclic Q := by
    intro Q hQA hQ
    have e : Q.subgroupOf (largeReeOppAut K a) ≃* Q := Subgroup.subgroupOfEquivOfLe hQA
    have : IsCyclic δ.range := hδcyc
    have : IsCyclic (Q.subgroupOf (largeReeOppAut K a)) :=
      isCyclic_of_injective _ (injective_comp_of_isPGroup δ.rangeRestrict
        (by rw [MonoidHom.ker_rangeRestrict]; exact hkercop) (hQ.of_equiv e.symm))
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨-, -, -, -, -, hopp⟩ := large_Ree_Sylow_opposition F4 a K w₀ hw₀
  have hIA : ∀ α : MulAut (F4.reeGamma K a), ∃ i ∈ inner (F4.reeGamma K a),
      ∃ β ∈ largeReeOppAut K a, α = i * β := by
    intro α
    obtain ⟨c, β, hβU, hβV, rfl⟩ := hopp α
    exact ⟨MulAut.conj c, ⟨c, rfl⟩, β, ⟨hβU, hβV⟩, rfl⟩
  have hcyc : ∀ P : Subgroup (MulAut (F4.reeGamma K a)), IsPGroup p P → IsCyclic P :=
    fun P hP => isCyclic_of_isPGroup_of_normal_mul (coprime_card_inner hp hpΓ) hIA hA hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
