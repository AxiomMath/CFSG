module

public import CFSG.Quasithin.EmptyFaithful.S152TOpp
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatRee

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog

theorem S152T.mem_normalizer_inf {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ B) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA ⊢
  intro x
  have hB' : g * x * g⁻¹ ∈ B ↔ x ∈ B := by
    constructor
    · intro h
      have := B.mul_mem (B.mul_mem (B.inv_mem hB) h) hB
      simpa [mul_assoc] using this
    · intro h
      exact B.mul_mem (B.mul_mem hB h) (B.inv_mem hB)
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB']

section Ree


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem borelCentralizerTrivial_ree (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    BorelCentralizerTrivial (F4.reeGamma K a) := by
  classical
  have := finite_modGL (τ := F4.tag) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, hUV, -, hopp, -⟩ := large_Ree_Sylow_opposition F4 a K w₀ hw₀
  obtain ⟨Φ, -, -, -, hodd⟩ := large_Ree_opposite_Sylow_parameters_faithful a ha K hK
  have hU : IsSylowTwoOf ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
    rw [← hPU]
    exact isSylowTwoOf_top_iff.mpr ⟨PU.isPGroup', PU.not_dvd_index⟩
  have hV : IsSylowTwoOf ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
    rw [← hPV]
    exact isSylowTwoOf_top_iff.mpr ⟨PV.isPGroup', PV.not_dvd_index⟩
  have hUV' : (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) ⊓
      (F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a ⊓ F4.reeFixedNegUnipotent K a :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [hUV, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  refine bct_of_opposition hU hV hUV' ?_ ?_ (large_Ree_fixed_group_center_trivial a K hK) ?_
  · intro S hS hUS
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hS
    have hcoe : ((hp.toSylow hi : Sylow 2 (F4.reeGamma K a)) : Subgroup (F4.reeGamma K a)) = S :=
      IsPGroup.toSylow_coe hp hi
    obtain ⟨u, hu, hSu⟩ := (hopp (hp.toSylow hi)).1 (by rw [hcoe]; exact hUS)
    exact ⟨u, hu, hcoe ▸ hSu⟩
  · rintro δ hUδ hVδ ⟨w, hwU, hw⟩
    have hδA : δ ∈ largeReeOppAut K a := ⟨hUδ, hVδ⟩
    have hfin : Finite (largeReeOppAut K a) := Nat.finite_of_card_ne_zero (Odd.pos hodd).ne'
    have hpow : (⟨δ, hδA⟩ : largeReeOppAut K a) ^ Nat.card (largeReeOppAut K a) = 1 :=
      pow_card_eq_one'
    have hδm : δ ^ Nat.card (largeReeOppAut K a) = 1 := by
      have h := congrArg Subtype.val hpow
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
    have hfix := fix_of_odd_pow (isSylowTwoOf_top_iff.mp hU).1 hodd hδm hwU hw
    have h1 : ∀ c, ((δ ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ : F4.reeGamma K a) :
        ModGL F4.tag K) = largeReeA1X a c := fun c =>
      congrArg Subtype.val (hfix _ (Subgroup.mem_subgroupOf.2
        (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ (largeReeA1X_mem_U1 hK c))))
    have h2 : ∀ g, largeReeRestrictU2 ha hK ⟨δ, hδA⟩ g = g := by
      intro g
      apply Subtype.ext
      rw [coe_largeReeRestrictU2]
      exact congrArg Subtype.val (hfix ⟨(g : ModGL F4.tag K), U2_le_reeGamma g.2⟩
        (Subgroup.mem_subgroupOf.2
          (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ g.2)))
    exact congrArg Subtype.val (eq_one_of_forall_fix ha hK ⟨δ, hδA⟩ h1 h2)
  · intro u hu hc
    have hu' : (u : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := Subgroup.mem_subgroupOf.1 hu
    have h1 : (u : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a ⊓
        Subgroup.centralizer (F4.reeFixedTorus K a : Set (ModGL F4.tag K)) := by
      refine ⟨hu', Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      obtain ⟨hT, hΓ⟩ := Subgroup.mem_inf.1 hh
      have hNU : (⟨h, hΓ⟩ : F4.reeGamma K a) ∈ Subgroup.normalizer
          (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) : Subgroup _) :
            Set (F4.reeGamma K a)) :=
        S152T.mem_normalizer_subgroupOf inf_le_right
          (S152T.mem_normalizer_inf ((triangular_borel_structure.{0, 0} F4.tag K).2.2.1 hT) hΓ)
      have hNV : (⟨h, hΓ⟩ : F4.reeGamma K a) ∈ Subgroup.normalizer
          (((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) : Subgroup _) :
            Set (F4.reeGamma K a)) :=
        S152T.mem_normalizer_subgroupOf inf_le_right
          (S152T.mem_normalizer_inf (torusGroup_le_normalizer_negUnipotent hT) hΓ)
      exact congrArg Subtype.val (hc _ hNU hNV)
    rw [(ree_positive_fixed_torus_centralizer F4 a ha K hK).2, Subgroup.mem_bot] at h1
    exact Subtype.ext h1

end Ree

section ReeFam


theorem bctFam2F4_proof : BCTFam2F4 := by
  intro f _ hf3 X _ _ hmodel
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier X 2 f hmodel
  obtain ⟨-, a, hfa, hmodel'⟩ := hmodel
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have ha : 1 ≤ a := by omega
  exact BorelCentralizerTrivial.of_mulEquiv E.symm (borelCentralizerTrivial_ree ha hK')

end ReeFam

end CFSG.Quasithin
