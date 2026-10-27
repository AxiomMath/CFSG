module

public import CFSG.Quasithin.Vol2.RootDataF4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.Quasithin.H13.Ch4.F4A

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem eq_zero_of_commute_weyl
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] {c : K}
    (h : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        centralZ K a c = centralZ K a c *
          canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)) :
    c = 0 := by
  by_contra hc
  set k : Fin F4.fixedWeylOrder := ⟨1, by decide⟩ with hk
  have hw : F4.fixedRelWord k = [⟨0, by decide⟩] := rfl
  have hrep : centralWeylRep K k =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) := by
    show canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) = _
    rw [fixedRelElt, hw, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have key : centralWeylRep K k * centralZ K a c * (centralWeylRep K k)⁻¹ = centralZ K a c := by
    rw [hrep, h, mul_inv_cancel_right]
  rw [weylRep_conj_centralZ] at key
  have hroot44 : IsRoot F4.tag (centralWeylImage k centralRoot44) := by
    rw [← fixedRelElt_smul_eq_centralWeylImage]
    exact CFSG.LieType.Chevalley.IsRoot.smul isRoot_centralRoot44.1 _
  have hroot47 : IsRoot F4.tag (centralWeylImage k centralRoot47) := by
    rw [← fixedRelElt_smul_eq_centralWeylImage]
    exact CFSG.LieType.Chevalley.IsRoot.smul isRoot_centralRoot47.1 _
  have hpos := not_neg_of_mul_eq_centralZ hroot44 hroot47 hc (pow_ne_zero _ hc) hc key
  rcases centralZ_weyl_check k with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩
  · rw [hw] at h1
    exact List.cons_ne_nil _ _ h1
  · rw [hw] at h1
    exact absurd h1 (by decide)
  · exact absurd h1 (not_lt.2 hpos.1.le)
  · exact absurd h1 (not_lt.2 hpos.2.le)
  · have hne : centralWeylImage k centralRoot44 ≠ centralWeylImage k centralRoot47 := by
      intro he
      rw [← fixedRelElt_smul_eq_centralWeylImage, ← fixedRelElt_smul_eq_centralWeylImage] at he
      exact (by decide : centralRoot44 ≠ centralRoot47) (MulAction.injective _ he)
    exact hc (eq_zero_of_mul_eq_centralZ ⟨hroot44, hpos.1⟩ ⟨hroot47, hpos.2⟩ hne h1 h2 h3 h4 key)

theorem rankOneGroupOne_le_perfectCore_zero
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩) := by
  obtain ⟨⟨h0eq, -, -⟩, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
  have hMperf : ⁅rankOneGroupOne K a, rankOneGroupOne K a⁆ = rankOneGroupOne K a :=
    CFSG.QuasithinUnique.Vol2Native.A312L.perfect_of_isSimpleGroup_nonabelian
      (isSimpleGroup_rankOneGroupOne ha hK).2
  have hMP : rankOneGroupOne K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
    rw [← h0eq, ← reeParabolic_singleton]
    exact (CFSG.QuasithinUnique.Setup.X6.reeLocalBlock_le_reePosWeylGroup _).trans
      (CFSG.QuasithinUnique.Setup.X6.reePosWeylGroup_le_reeParabolic _)
  exact le_perfectCore_of_perfect hMP hMperf

theorem reeFixedPosUnipotent_le_perfectCore_zero
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedPosUnipotent K a ≤ perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩) := by
  obtain ⟨⟨h0eq, -, -⟩, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  obtain ⟨hF0, -⟩ := CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeReeParabolicFacts a K ha hK
  rw [← reeFixedOrbitComplementUnipotent_sup ⟨0, by decide⟩]
  refine sup_le ?_ (((reeFixedOrbitUnipotent_le_reeLocalBlock _).trans h0eq.le).trans
    (rankOneGroupOne_le_perfectCore_zero ha hK))
  refine (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.generation_zero ha hK).trans
    (Subgroup.commutator_le.2 fun q hq y hy => ?_)
  have hqN : q ∈ Subgroup.normalizer
      (perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩) : Set (ModGL F4.tag K)) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer (hF0.le hq))
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.1 hqN y).1 hy) (inv_mem hy)

theorem aut_eq_one_of_fixes
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ψ : MulAut ↥(F4.reeGamma K a)) {m : ℕ}
    (hm : ψ ^ (2 ^ m) = 1)
    (hψ : ∀ x : ↥(F4.reeGamma K a),
      (x : ModGL F4.tag K) ∈ perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩) → ψ x = x) :
    ψ = 1 := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF ψ
  have hΨψ : Ψ ⟨x, β⟩ = ψ := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut ↥(F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘψ : Θ ψ = β := by
    show SemidirectProduct.rightHom (Ψ.symm ψ) = β
    rw [← hΨψ, MulEquiv.symm_apply_apply]
    rfl
  have hβm : β ^ 2 ^ m = 1 := by rw [← hΘψ, ← map_pow, hm, map_one]
  have hcard :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hβ1 : β = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hβm)
    have hd : orderOf β ∣ 2 * a + 1 := by
      rw [← hcard]
      exact orderOf_dvd_natCard β
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, pow_zero] at hi
      exact orderOf_eq_one_iff.1 hi
    · exfalso
      rw [hi] at hd
      have h2 : 2 ∣ 2 * a + 1 := (dvd_pow_self 2 hpos.ne').trans hd
      omega
  subst hβ1
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  rw [hone, mul_one] at hxβ
  have hxc : ∀ y : ↥(F4.reeGamma K a),
      (y : ModGL F4.tag K) ∈ perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩) →
      (y : ModGL F4.tag K) * x = x * y := by
    intro y hy
    have h1 := congrArg Subtype.val (hψ y hy)
    rw [hxβ, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (y : ModGL F4.tag K) * x = x * y * (x : ModGL F4.tag K)⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hUP := reeFixedPosUnipotent_le_perfectCore_zero ha hK
  have hUΓ : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hcU : ∀ y ∈ F4.reeFixedPosUnipotent K a, y * (x : ModGL F4.tag K) = x * y := fun y hy =>
    hxc ⟨y, hUΓ hy⟩ (hUP hy)
  have hxU := CFSG.Quasithin.H13.RootData.F4.mem_reeFixedPosUnipotent_of_centralizer ha hK x.2 hcU
  have hxZ : (x : ModGL F4.tag K) ∈ ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) :=
    ⟨⟨x, hxU⟩, Subgroup.mem_center_iff.2 fun u => Subtype.ext (hcU u u.2), rfl⟩
  rw [coe_center_eq_range_centralZ ha hK] at hxZ
  obtain ⟨c, hc⟩ := hxZ
  obtain ⟨⟨h0eq, hn0, -⟩, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hn0P := rankOneGroupOne_le_perfectCore_zero ha hK (h0eq ▸ hn0)
  have hn0Γ : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
      F4.reeGamma K a := by
    refine reeParabolic_le F4 K a {⟨0, by decide⟩} ?_
    rw [reeParabolic_singleton]
    exact CFSG.Quasithin.perfectCore_le _ hn0P
  have h := hxc ⟨_, hn0Γ⟩ hn0P
  rw [← hc] at h
  have hc0 := eq_zero_of_commute_weyl h
  have hx1 : x = 1 := Subtype.ext (by rw [← hc, hc0, centralZ_zero]; rfl)
  rw [hxβ, hx1, map_one]

end CFSG.Quasithin.H13.Ch4.F4A
