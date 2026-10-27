module

public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Quasithin.SteinbergCCPerfectCentralization
public import CFSG.LinearAlgebra.LinearGroups.OddPStableActionsSupport
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.QuasithinUnique

theorem short_Ccomponent_centralizes_every_distinct_Ccomponent {H : Type*} [Group H] [Finite H]
    {K₁ K₂ : Subgroup H} (hK₁ : CFSG.IsCComponent K₁) (hK₂ : CFSG.IsCComponent K₂)
    (hne : K₁ ≠ K₂) (hS : IsShort2 K₁) : ⁅K₁, K₂⁆ = ⊥ := by
  classical
  set C := CFSG.pCore 2 H
  have hCsolv : Group.IsSolvable (QuotientGroup.mk' C).ker := by
    rw [QuotientGroup.ker_mk']
    have : Group.IsNilpotent C := (CFSG.pCore_isPGroup (p := 2) (G := H)).isNilpotent
    infer_instance
  set π := QuotientGroup.mk' C with hπ
  have hK₁c := mem_cComp_top_iff_isCComponent.mpr hK₁
  have hK₂c := mem_cComp_top_iff_isCComponent.mpr hK₂
  have hJ₁ := mem_cComp_top_iff_isCComponent.mp
    (map_mem_cComp_top π (QuotientGroup.mk'_surjective C) hCsolv hK₁c)
  have hJ₂ := mem_cComp_top_iff_isCComponent.mp
    (map_mem_cComp_top π (QuotientGroup.mk'_surjective C) hCsolv hK₂c)
  have hinj := map_injOn_cComp_top π hCsolv
  have hQ : blockQ K₁ = (CFSG.pCore 2 K₁).map K₁.subtype := by
    show (CFSG.Open.pCore 2 K₁).map K₁.subtype = _
    try with_reducible rfl
  have hQC : blockQ K₁ = K₁ ⊓ C := by
    have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {⟨2, Nat.prime_two⟩}
      hK₁.2.2.1
    rw [← CFSG.LinearGroups.pCore_eq_piCore Nat.prime_two,
      ← CFSG.LinearGroups.pCore_eq_piCore Nat.prime_two] at h
    rw [hQ]
    exact h
  have hker : (π.subgroupMap K₁).ker = CFSG.pCore 2 K₁ := by
    apply Subgroup.map_injective K₁.subtype_injective
    rw [← hQ, hQC]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      have h1 : π (y : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      exact (QuotientGroup.eq_one_iff (y : H)).mp h1
    · intro hx
      obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxK⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      exact (QuotientGroup.eq_one_iff x).mpr hxC
  have hJ₁q : CFSG.IsQuasisimple (K₁.map π) := by
    let e : (K₁ ⧸ CFSG.pCore 2 K₁) ≃* K₁.map π :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (π.subgroupMap_surjective K₁))
    rcases hS.2.2.2.1 with hq | h3
    · exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp hq
    · exfalso
      have : Group.IsPerfect K₁ := Subgroup.isPerfect_iff.mpr hK₁.2.1
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic (K₁ ⧸ CFSG.pCore 2 K₁) := isCyclic_of_prime_card h3
      have : Nontrivial (K₁ ⧸ CFSG.pCore 2 K₁) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
      exact Group.IsPerfect.not_isMulCommutative (G := K₁ ⧸ CFSG.pCore 2 K₁) inferInstance
  have hJ : ⁅K₁.map π, K₂.map π⁆ = ⊥ := by
    rcases CFSG.LocalCores.component_subnormal_subgroup ⟨hJ₁q, hJ₁.2.2.1⟩ hJ₂.2.2.1 with
      hle | hc
    · exfalso
      have heq : K₁.map π = K₂.map π := by
        by_contra hlt
        exact hJ₂.2.2.2 _ (lt_of_le_of_ne hle hlt) hJ₁.1 hJ₁.2.1 hJ₁.2.2.1
      exact hne (hinj hK₁c hK₂c heq)
    · exact hc
  have hcent : ∀ a ∈ K₁, ∀ b ∈ K₂, π b * π a = π a * π b := by
    intro a ha b hb
    have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJ)
      (Subgroup.mem_map_of_mem π ha)
    exact (Subgroup.mem_centralizer_iff.mp h1 _ (Subgroup.mem_map_of_mem π hb))
  have hK₂N : K₂ ≤ normalizer (K₁ : Set H) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hc : K₁.map (MulAut.conj k).toMonoidHom ∈ cComp (⊤ : Subgroup H) := by
      have hsurj : Function.Surjective (MulAut.conj k).toMonoidHom := (MulAut.conj k).surjective
      have h1 := cComp_map_mulEquiv (MulAut.conj k) hK₁c
      rwa [Subgroup.map_top_of_surjective _ hsurj] at h1
    refine hinj hc hK₁c ?_
    ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      change π a = π (k * a * k⁻¹)
      rw [map_mul, map_mul, map_inv, hcent a ha k hk, mul_inv_cancel_right]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨k * a * k⁻¹, ⟨a, ha, rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, hcent a ha k hk, mul_inv_cancel_right]
  have hcommQ : ⁅K₁, K₂⁆ ≤ blockQ K₁ := by
    rw [hQC]
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      have h1 : b * a⁻¹ * b⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp (hK₂N hb) _).mp
        (inv_mem ha)
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact mul_mem ha (by rw [← mul_assoc]; exact h1)
    · have h1 : (⁅K₁, K₂⁆).map π = ⊥ := by rw [Subgroup.map_commutator]; exact hJ
      have h2 := (Subgroup.map_eq_bot_iff _).mp h1
      rwa [hπ, QuotientGroup.ker_mk'] at h2
  have hK₂NQ : K₂ ≤ normalizer (blockQ K₁ : Set H) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hQC, Subgroup.mem_inf, Subgroup.mem_inf]
    have hC : q ∈ C ↔ k * q * k⁻¹ ∈ C :=
      ⟨fun h => (CFSG.pCore_normal (p := 2) (G := H)).conj_mem q h k, fun h => by
        have := (CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ h k⁻¹
        simpa [mul_assoc] using this⟩
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hK₂N hk) q) hC
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -, hZU, hirr⟩ := hS
  have hQX : blockQ K₁ ≤ K₁ := by
    rw [hQ]
    exact Subgroup.map_subtype_le _
  have hQn : ((blockQ K₁).subgroupOf K₁).Normal := by
    have h1 : ((CFSG.pCore 2 K₁).map K₁.subtype).subgroupOf K₁ = CFSG.pCore 2 K₁ :=
      Subgroup.comap_map_eq_self_of_injective K₁.subtype_injective _
    rw [hQ, h1]
    infer_instance
  have : IsMulCommutative (⁅blockQ K₁, K₁⁆ : Subgroup H) := ⟨⟨fun a b => Subtype.ext (by
    have ha := (Subgroup.mem_inf.mp (hUQ a.2)).2
    have hb := (Subgroup.mem_inf.mp (hUQ b.2)).1
    exact ((Subgroup.mem_centralizer_iff.mp ha) _ hb).symm)⟩⟩
  have hU : IsElementaryAbelian 2 (⁅blockQ K₁, K₁⁆ : Subgroup H) :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hU2 _ a.2)⟩
  have hUZ : ⁅blockQ K₁, K₁⁆ ≤ (center (blockQ K₁)).map (blockQ K₁).subtype := by
    intro u hu
    obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.mp (hUQ hu)
    refine ⟨⟨u, huQ⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp huC) _ g.2
  have hne' : ¬ ⁅blockQ K₁, K₁⁆ ≤ centralizer (K₁ : Set H) := by
    intro h
    apply hZU.ne
    show ⁅blockQ K₁, K₁⁆ ⊓ centralizer (K₁ : Set H) = ⁅blockQ K₁, K₁⁆
    exact inf_eq_left.mpr h
  have hirr' : ∀ M : Subgroup H, ⁅blockQ K₁, K₁⁆ ⊓ centralizer (K₁ : Set H) ≤ M →
      M ≤ ⁅blockQ K₁, K₁⁆ → (∀ x ∈ K₁, ∀ m ∈ M, x * m * x⁻¹ ∈ M) →
        M = ⁅blockQ K₁, K₁⁆ ⊓ centralizer (K₁ : Set H) ∨ M = ⁅blockQ K₁, K₁⁆ := by
    intro M hZM hMU hMinv
    refine hirr M hZM hMU fun x hx => Subgroup.mem_normalizer_iff.mpr fun m =>
      ⟨hMinv x hx m, fun hm => ?_⟩
    have h1 := hMinv x⁻¹ (inv_mem hx) _ hm
    simpa [mul_assoc] using h1
  exact SteinbergCC.perfect_normalizer_centralization_through_irreducible_core_commutator
    Nat.prime_two (Subgroup.isPerfect_iff.mpr hK₁.2.1) (Subgroup.isPerfect_iff.mpr hK₂.2.1) hK₂N
    hQX hQn hK₂NQ hU hUZ hne' hirr' hcommQ

end CFSG.Quasithin.H13.NQTerm
