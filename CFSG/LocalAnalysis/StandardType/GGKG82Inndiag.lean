module

public import CFSG.LocalAnalysis.StandardType.GGKG82InndiagTorus

public section

namespace CFSG.StandardType.KG82

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_zeta {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ Units.map σ.toRingHom.toMonoidHom ζ = ζ⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.one_le_two_pow (n := n))
    rw [hk, Nat.add_sub_cancel_left]
    ring_nf
    omega
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units K, hK, hsq]
    exact h3.mul_right _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  refine ⟨ζ, hζ3, fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  · have h1 : ζ ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ h3)
    have h2 : ζ ^ 2 ^ n = ζ⁻¹ := by
      rw [pow_succ] at h1
      exact eq_inv_of_mul_eq_one_left h1
    refine Units.ext ?_
    change σ (ζ : K) = ((ζ⁻¹ : Kˣ) : K)
    rw [hσ, ← Units.val_pow_eq_pow_val, h2]

theorem exists_inndiag_rankFive
    {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ E : Subgroup (MulAut (TwE6Delta.RecipeR K n)), (∀ φ ∈ E, φ ∈ TwE6Delta.RecipeI K n) ∧
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ GGTwoLocalAut E := by
  classical
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  obtain ⟨ζ, hζ3, hζ1, hσζ⟩ := exists_zeta hK h3 σ hσ
  have hAΓ := rankFiveGroup_le_twInndiagGroup (K := K) σ hσζ
  have htC : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    CFSG.SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom
      isRoot_e6HighestRoot permLattice_e6HighestRoot (map_one _)
  have htA : ∀ x ∈ rankFiveGroup (K := K) ζ,
      Commute (pinnedX TwistTag.E6.tag K e6HighestRoot 1) x := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (rankFiveGroup_le_centralizer ζ hx)).symm
  refine ⟨TwE6Transport.matRecipe σ ε (rankFiveGroup ζ), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact (hε _).1 ⟨w, rfl⟩
  · exact ((isElemAbelian_rankFiveGroup hζ3).comap (Subgroup.subtype_injective _)).map _
  · rw [TwE6Transport.card_matRecipe σ ε hn hK hσ hAΓ]
    exact card_rankFiveGroup hζ3 hζ1
  · set t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom := ⟨_, htC⟩ with ht
    have ht2 : t ^ 2 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, pow_two, ht, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
      rfl
    have ht1 : t ≠ 1 := fun h => by
      have h' : pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
          pinnedX TwistTag.E6.tag K e6HighestRoot 0 :=
        (congrArg Subtype.val h).trans (pinnedX_zero TwistTag.E6.tag K e6HighestRoot).symm
      exact one_ne_zero (pinnedX_injective TwistTag.E6.tag K e6HighestRoot h')
    refine ⟨Subgroup.zpowers (ε t), ?_, ?_, ?_⟩
    · rw [Ne, Subgroup.zpowers_eq_bot, map_eq_one_iff ε ε.injective]
      exact ht1
    · refine (CFSG.Open.isElemAbelian_zpowers ?_).isPGroup
      rw [← map_pow, ht2, map_one]
    · intro e he v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [map_zpow, TwE6Transport.apply_eq_of_forall_commute σ ε htC htA he]
      exact Subgroup.zpow_mem_zpowers _ k

end CFSG.StandardType.KG82
