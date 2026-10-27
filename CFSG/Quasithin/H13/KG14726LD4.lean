module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726CPar
public import CFSG.Quasithin.Vol2.RootDataD4

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

theorem mem_centerOf_Q0_of_centralizer
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    {g : ModGL TwistTag.D4.tag K} (hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hcU : ∀ y ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, y * g = g * y) :
    g ∈ CFSG.Quasithin.centerOf (Q0 σ) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨-, -, -, -, -, -, hNU, -⟩ := fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀
  have hgN : g ∈ Subgroup.normalizer
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [show g * h * g⁻¹ = h by rw [← hcU h hh]; group]
      exact hh
    · intro hh
      have h1 := hcU _ hh
      have e : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h1]
          _ = g * h * g⁻¹ := by group
      rw [e]
      exact hh
  have hgB : g ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    rw [← hNU]
    exact ⟨hgC, hgN⟩
  obtain ⟨-, -, -, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hgP : g ∈ P0 σ := graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hgB
  have hQU : Q0 σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedPosUnipotent _
  have hgCQ : g ∈ Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcU y (hQU hy)
  exact ⟨hsc ⟨hgP, hgCQ⟩, hgCQ⟩

theorem isSimpleGroup_specialLinear_two_charTwo {F : Type*} [Field F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hc : center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, scalars_two_eq_bot]
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem exists_prime_mem_perfectCore_P0
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) {f : ℕ}
    (hK : Nat.card K = 2 ^ (3 * f)) (hf : 1 ≤ f) :
    ∃ ℓ ∈ CFSG.Quasithin.perfectCore (P0 σ), ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p := by
  have htop : orbitField TwistTag.D4 K σ.toRingHom fa0 = ⊤ :=
    orbitField_D4_zero_eq_top σ (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
  have hLcard : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) = 2 ^ (3 * f) := by
    rw [htop, Nat.card_congr Subfield.topEquiv.toEquiv, hK]
  have hL4 : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) := by
    rw [hLcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨R, -, -, -, hMP, hsimple, -⟩ := levi_package σ fa0 hU
    (CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hL4)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2)
      ↥(orbitField TwistTag.D4 K σ.toRingHom fa0)) := isSimpleGroup_specialLinear_two_charTwo hL4
  have hRinj : Function.Injective R := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff R).mp h
    · exfalso
      have : Nontrivial ↥R.range := IsSimpleGroup.toNontrivial
      obtain ⟨⟨_, x, rfl⟩, hx⟩ := exists_ne (1 : ↥R.range)
      apply hx
      apply Subtype.ext
      have hxk : x ∈ R.ker := h ▸ mem_top x
      exact hxk
  obtain ⟨p, hp, hp5, A, hA⟩ := exists_prime_orderOf_sl2 hLcard (by omega)
  exact ⟨R A, hMP ⟨A, rfl⟩, p, hp, hp5, by rw [orderOf_injective R hRinj, hA]⟩

theorem kg115D4Input_holds :
    KG115D4Input := by
  intro f X _ hf h
  obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model h
  refine kg115Excluded_of_mulEquiv e ?_
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨-, hS₀, hS₀i⟩ := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hUsyl
  have hS₀i' : ¬ 2 ∣ ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index := by
    rwa [show (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).subgroupOf ⊤).index =
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index from
      Subgroup.relIndex_top_right _] at hS₀i
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
      id_eq, RingHom.one_def, RingHom.id_apply]
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    let _ := Fintype.ofFinite K
    have hq : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [hq]
    exact FiniteField.pow_card c
  have hc : center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hcU : ∀ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ s ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), s * y = y * s) →
      ∀ z ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
        z * (y : ModGL TwistTag.D4.tag K) = y * z := by
    intro y hy z hz
    have := hy ⟨z, hUC hz⟩ (mem_subgroupOf.mpr hz)
    exact congrArg Subtype.val this
  refine kg115Excluded_of_at hc (sylowTwoNoThree_of_conj hS₀ hS₀i' fun y hy3 hyS => ?_) ?_
  · have h1 := RootData.D4.eq_one_of_centralizer_of_odd σ hσ3 y.2 (hcU y hyS)
      (by rw [Subgroup.orderOf_coe, hy3]; decide)
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  · intro S hS hSi l hl hlc hl1
    refine kg115At_of_prime (forall_center_of_conj hS₀ hS₀i'
      (Q := fun u => ∃ ℓ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ℓ * u = u * ℓ ∧
        ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) (fun g _ hu => prime_conj g hu) ?_
      S hS hSi l hl hlc hl1)
    intro u _ huc _
    have huZ := mem_centerOf_Q0_of_centralizer σ u.2 (hcU u huc)
    obtain ⟨ℓ, hℓP, p, hp, hp5, hℓp⟩ := exists_prime_mem_perfectCore_P0 σ hσ3 hUsyl.2.1 hK3 hf
    have hℓC : ℓ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedParabolic_le _ _ _ _ (CFSG.Quasithin.perfectCore_le _ hℓP)
    refine ⟨⟨ℓ, hℓC⟩, Subtype.ext ?_, p, hp, hp5, by rw [Subgroup.orderOf_mk, hℓp]⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact ((mem_centralizer_iff.mp
      (CFSG.Quasithin.H13.NQCat.D4Irred.perfectCore_le_centralizer σ hσ3 hℓP)) _ huZ).symm

end CFSG.Quasithin.H13.KG14726

end
