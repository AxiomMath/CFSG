module

public import CFSG.RankThree.SteinbergR3ECoprimeRankOne
public import CFSG.LieType.Chevalley.GraphFixedCommonBaseField

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem diagram_fixed_coprime_large_prime_automorphism_subgroups_cyclic (t : TwistTag)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpC : ¬ p ∣ Nat.card (graphFixedRootGroup t K σ.toRingHom)) :
    (∀ P : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)), IsPGroup p P →
      IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (graphFixedRootGroup t K σ.toRingHom), p ≤ Nat.card α.ker := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have := finite_modGL (τ := t.tag) (K := K)
  have hp2 : p ≠ 2 := by omega
  have h24 : ¬ p ∣ 24 := not_dvd_factorial_of_le_four hp hp3 (n := 4) le_rfl
  have hLa : ∀ a, Nat.Coprime (Nat.card (orbitField t K σ.toRingHom a) - 1) p := by
    intro a
    obtain ⟨R, -, -, -, -, -, hRrange, hRle, hRker, -⟩ :=
      exceptional_fixed_rank_one_central_image t K σ.toRingHom a
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_sub_one_of_range_le R hRker (hRrange ▸ hRle) hp hp2 hpC)).symm
  have hda : ∀ a, Nat.Coprime (t.orbit a).card p := by
    intro a
    have h3 : (t.orbit a).card ≤ 3 := by
      revert a
      cases t <;> decide
    have h0 := t.card_orbit_pos a
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
      have := Nat.le_of_dvd h0 h
      omega).symm
  obtain ⟨-, k, -, -, δ, -, hδcyc, hδker⟩ :=
    diagram_fixed_simple_pairs_common_base_field_parameter t hℓ hf K hK σ hσ
  have hkercop : Nat.Coprime (Nat.card δ.ker) p :=
    Nat.Coprime.coprime_dvd_left hδker
      (Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (hda a) (hLa a))
  obtain ⟨-, ⟨φ, hφ⟩, -, -⟩ := diagram_fixed_intrinsic_simple_pairs t K σ
  have hφ24 : ∀ β, φ β ^ 24 = 1 := by
    intro β
    have hr : t.foldedTag.rank ≤ 4 := by cases t <;> decide
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hr
    rw [show (24 : ℕ) = (4 : ℕ).factorial from rfl, hm, pow_mul, perm_pow_card_factorial,
      one_pow]
  have hA₀ : ∀ Q : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)),
      Q ≤ graphFixedUnipotentStabilizer t K σ.toRingHom → IsPGroup p Q →
        Q ≤ graphFixedPairAut t K σ.toRingHom := by
    intro Q hQA hQ α hα
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨α, hα⟩
    rw [Subgroup.orderOf_mk] at hk
    have hβk : φ ⟨α, hQA hα⟩ ^ p ^ k = 1 := by
      rw [← map_pow, ← hk, ← Subgroup.orderOf_mk α (hQA hα), pow_orderOf_eq_one, map_one]
    have hπ := eq_one_of_pow_eq_one_of_pow_prime_pow_eq_one hp h24 (hφ24 _) hβk
    refine Subgroup.mem_iInf.2 fun a => ?_
    obtain ⟨hX, hY⟩ := hφ ⟨α, hQA hα⟩ a
    rw [hπ, Equiv.Perm.coe_one, id] at hX hY
    exact ⟨hX, hY⟩
  have hA : ∀ Q : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)),
      Q ≤ graphFixedUnipotentStabilizer t K σ.toRingHom → IsPGroup p Q → IsCyclic Q :=
    fun Q hQA hQ => isCyclic_of_le_of_coprime_ker δ hδcyc hkercop (hA₀ Q hQA hQ) hQ
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  obtain ⟨-, -, -, -, -, hopp⟩ := exceptional_fixed_Sylow_opposition t K (ringChar K) σ w₀ hw₀
  have hIA : ∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
      ∃ c : graphFixedRootGroup t K σ.toRingHom,
        ∃ β ∈ graphFixedUnipotentStabilizer t K σ.toRingHom, α = MulAut.conj c * β := by
    intro α
    obtain ⟨c, β, hβU, hβV, rfl⟩ := hopp α
    exact ⟨c, β, ⟨hβU, hβV⟩, rfl⟩
  have hcyc : ∀ P : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)), IsPGroup p P →
      IsCyclic P :=
    fun P hP => isCyclic_of_isPGroup_of_conj_mul hp hpC hIA hA hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
