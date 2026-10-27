module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Base

public section

namespace CFSG.Quasithin.H13.Sec53F.ReeF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.BA
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (levi_hom)
open CFSG.QuasithinUnique.Setup.X6 (large_Ree_opposite_simple_blocks_generate_rank_one_model)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem commute_conj_aux {G : Type*} [Group G] {z zc n τ : G} (hz : z = τ⁻¹ * zc * τ)
    (hcomm : n * zc = zc * n) : z * (τ⁻¹ * n * τ) = (τ⁻¹ * n * τ) * z := by
  calc z * (τ⁻¹ * n * τ) = τ⁻¹ * (zc * n) * τ := by rw [hz]; group
    _ = τ⁻¹ * (n * zc) * τ := by rw [hcomm]
    _ = (τ⁻¹ * n * τ) * z := by rw [hz]; group

theorem eq_centralZ_of_mem_center_perfectCore (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {j : Fin F4.fixedOrbitCount}
    (hS : F4.reeLocalParabolic K a j ⊓ Subgroup.centralizer
      (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) ≤
        F4.reeFixedOrbitComplementUnipotent K a j)
    (hU : F4.reeFixedPosUnipotent K a ≤ perfectCore (F4.reeLocalParabolic K a j))
    {x : ModGL F4.tag K} (hx : x ∈ perfectCore (F4.reeLocalParabolic K a j))
    (hxC : ∀ y ∈ perfectCore (F4.reeLocalParabolic K a j), y * x = x * y) :
    ∃ c : K, centralZ K a c = x := by
  have hxV : x ∈ F4.reeFixedOrbitComplementUnipotent K a j :=
    hS ⟨perfectCore_le _ hx, Subgroup.mem_centralizer_iff.2 fun v hv =>
      hxC v (hU (reeFixedOrbitComplementUnipotent_le j hv))⟩
  have hxU : x ∈ F4.reeFixedPosUnipotent K a := reeFixedOrbitComplementUnipotent_le j hxV
  have hmem : x ∈ ((Subgroup.center ↥(F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) :=
    ⟨⟨x, hxU⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hxC g (hU g.2)), rfl⟩
  rw [coe_center_eq_range_centralZ ha hK] at hmem
  exact hmem

theorem pow_two_mul_two_pow_pow (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    (x ^ (2 * 2 ^ a)) ^ 2 ^ a = x := by
  have := Fintype.ofFinite K
  rw [← pow_mul]
  have h1 : 2 * 2 ^ a * 2 ^ a = Nat.card K := by rw [hK]; ring
  rw [h1, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem torusPair_mem_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) (u v : Kˣ) :
    torusPair a (u, v) ∈ F4.reeLocalParabolic K a j := by
  rw [← reeParabolic_singleton]
  exact F4.reeFixedBorel_le_reeParabolic K a {j} (reeFixedTorus_le_reeFixedBorel
    (rankOne_torusPair_mem_reeFixedTorus hK u v))

theorem exists_conj_centralZ_one (hK : Nat.card K = 2 ^ (2 * a + 1)) {c c' : K} (hc : c ≠ 0)
    (hc' : c' ≠ 0) : ∃ m ∈ F4.reeLocalParabolic K a ⟨1, by decide⟩,
      m * centralZ K a c * m⁻¹ = centralZ K a c' := by
  have hu0 : (c' / c) ^ (2 * 2 ^ a) ≠ 0 := pow_ne_zero _ (div_ne_zero hc' hc)
  refine ⟨torusPair a (Units.mk0 _ hu0, 1), torusPair_mem_reeLocalParabolic hK _ _ _, ?_⟩
  rw [torusPair_conj_centralZ hK, Units.val_mk0, pow_two_mul_two_pow_pow hK,
    div_mul_cancel₀ _ hc]

theorem no_central_centralZ_zero (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {c : K}
    (hc : c ≠ 0) (h : ∀ y ∈ perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩),
      y * centralZ K a c = centralZ K a c * y) : False := by
  have hsimple := isSimpleGroup_rankOneGroupOne ha hK
  have := hsimple.1
  obtain ⟨⟨h0eq, hn0, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hMP := (levi_hom ha hK ⟨0, by decide⟩ (M := rankOneGroupOne K a) h0eq hsimple.2).2
  have hn := hMP (h0eq ▸ hn0)
  have hcomm := h _ hn
  set n := canonicalRep (coxeterSystem F4.tag) K
    (F4.fixedOrbitElement ⟨0, by decide⟩) with hn_def
  have hu0 : c ^ (2 * 2 ^ a) ≠ 0 := pow_ne_zero _ hc
  set τ := torusPair a (Units.mk0 _ hu0, 1) with hτ
  have hτz : τ * centralZ K a 1 * τ⁻¹ = centralZ K a c := by
    rw [hτ, torusPair_conj_centralZ hK, Units.val_mk0, mul_one, pow_two_mul_two_pow_pow hK]
  have hz : centralZ K a 1 = τ⁻¹ * centralZ K a c * τ := by rw [← hτz]; group
  have hτΓ : τ ∈ F4.reeGamma K a := LargeReeCover.torusPair_mem_reeGamma a hK _
  have hnΓ : n ∈ F4.reeGamma K a := reeLocalParabolic_le_reeGamma _ (perfectCore_le _ hn)
  have hg : τ⁻¹ * n * τ ∈ F4.reeGamma K a ⊓ Subgroup.centralizer {centralZ K a 1} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hτΓ) hnΓ) hτΓ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_conj_aux hz hcomm).symm
  have hP1 := reeGamma_inf_centralizer_le_reeLocalParabolic ha hK hg
  have hτP := torusPair_mem_reeLocalParabolic (K := K) (a := a) hK ⟨1, by decide⟩
    (Units.mk0 _ hu0) 1
  have hn1 : n ∈ F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
    have := mul_mem (mul_mem hτP hP1) (inv_mem hτP)
    rwa [← hτ, show τ * (τ⁻¹ * n * τ) * τ⁻¹ = n by group] at this
  rw [← reeParabolic_singleton, hn_def, canonicalRep_mem_reeParabolic_iff] at hn1
  exact absurd (congrArg Fin.val (Set.mem_singleton_iff.1 hn1)) (by decide)

end CFSG.Quasithin.H13.Sec53F.ReeF4
