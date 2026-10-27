module

public import CFSG.Walter.AStar.N1
public import CFSG.Walter.AStar.CenterOdd
public import CFSG.Walter.AStar.Subnormal
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.Walter

open GorensteinWalter

variable {Y : Type*} [Group Y]

theorem isComponent_iff_isComponentOf_top (K : Subgroup Y) :
    CFSG.IsComponent K ↔ IsComponentOf K ⊤ :=
  (CFSG.isComponent_iff_open K).trans (CFSG.Adapters.isComponentOf_top_iff K)

theorem isSubnormal_of_isComponentOf {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    K.IsSubnormal :=
  Subgroup.IsSubnormal.trans le_top hK.2.1 Subgroup.IsSubnormal.top

theorem nonabelian_of_isComponentOf {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have : Nontrivial K := hK.2.2.1
  have hperf : commutator K = ⊤ := hK.2.2.2.1
  have hbot : commutator K = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact h y x
  exact bot_ne_top (hbot.symm.trans hperf)

variable [Finite Y]

theorem center_eq_bot_of_isComponentOf (hO : pPrimeCore 2 Y = ⊥) (hY : HasAbelianSylowTwo Y)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : Subgroup.center K = ⊥ := by
  have hperf : commutator K = ⊤ := hK.2.2.2.1
  have hodd := odd_card_center_of_perfect hperf (hY.subgroup K)
  have hsub : ((Subgroup.center K).map K.subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_
      (isSubnormal_of_isComponentOf hK)
    change (((Subgroup.center K).map K.subtype).comap K.subtype).IsSubnormal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact (Subgroup.center K).normal_of_characteristic.isSubnormal
  have hodd' : Odd (Nat.card ((Subgroup.center K).map K.subtype)) := by
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have := eq_bot_of_isSubnormal_of_odd hO hsub hodd'
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp this

theorem isSimpleGroup_of_isComponentOf (hO : pPrimeCore 2 Y = ⊥) (hY : HasAbelianSylowTwo Y)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : IsSimpleGroup K := by
  have hZ := center_eq_bot_of_isComponentOf hO hY hK
  have := hK.2.2.2.2
  let e : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact e.isSimpleGroup

section TypeZero

variable {Y : Type} [Group Y] [Finite Y]

theorem sylow_le_normalizer_of_isComponentOf (hO : pPrimeCore 2 Y = ⊥)
    (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    (S : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := center_eq_bot_of_isComponentOf hO hY hK
  have hS := hY S
  have hKc : CFSG.IsComponent K := (isComponent_iff_isComponentOf_top K).mpr hK
  have heven : 2 ∣ Nat.card K := by
    have := isSimpleGroup_of_isComponentOf hO hY hK
    exact even_iff_two_dvd.mp (even_card_of_isSimpleGroup (nonabelian_of_isComponentOf hK))
  obtain ⟨⟨t, htS, htK⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (sylow_inf_ne_bot_of_isSubnormal S (isSubnormal_of_isComponentOf hK) heven)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  set K' := K.map (MulAut.conj s).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hKc
  rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with heq | hcomm
  · intro h
    constructor
    · intro hh
      rw [heq]
      exact ⟨h, hh, MulAut.conj_apply s h⟩
    · intro hh
      rw [heq] at hh
      obtain ⟨k, hk, hkeq⟩ := hh
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkeq
      have : k = h := by simpa using hkeq
      rwa [← this]
  · exfalso
    have hst : s * t * s⁻¹ = t := by
      rw [setLike_mul_comm hs htS, mul_inv_cancel_right]
    have htK' : t ∈ K' := ⟨t, htK, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hst]⟩
    have hcent : (⟨t, htK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hkC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm k.2
      exact ((Subgroup.mem_centralizer_iff.mp hkC) t htK').symm
    rw [hZ, Subgroup.mem_bot] at hcent
    exact ht1' (congrArg Subtype.val hcent)

theorem exists_mem_componentLayerOf_conj_eq (hO : pPrimeCore 2 Y = ⊥)
    (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) {s : Y} (hs : s ∈ (S : Subgroup Y)) :
    ∃ e ∈ componentLayerOf (⊤ : Subgroup Y), ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      ∀ x ∈ K, e * x * e⁻¹ = s * x * s⁻¹ := by
  classical
  have hinner : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := fun K hK => by
    have := isSimpleGroup_of_isComponentOf hO hY hK
    exact exists_inner_of_sylow_le_normalizer hY K (nonabelian_of_isComponentOf hK) S
      (sylow_le_normalizer_of_isComponentOf hO hY S hK) s hs
  have hfin : Set.Finite {K : Subgroup Y | IsComponentOf K ⊤} := Set.toFinite _
  suffices h : ∀ F : Finset (Subgroup Y), (∀ K ∈ F, IsComponentOf K ⊤) →
      ∃ e ∈ (⨆ K ∈ F, K), ∀ K ∈ F, ∀ x ∈ K, e * x * e⁻¹ = s * x * s⁻¹ by
    obtain ⟨e, he, hconj⟩ := h hfin.toFinset (fun K hK => hfin.mem_toFinset.mp hK)
    refine ⟨e, ?_, fun K hK => hconj K (hfin.mem_toFinset.mpr hK)⟩
    have hle : (⨆ K ∈ hfin.toFinset, K) ≤ componentLayerOf (⊤ : Subgroup Y) :=
      iSup₂_le fun K hK => le_sSup (hfin.mem_toFinset.mp hK)
    exact hle he
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, one_mem _, fun K hK => absurd hK (Finset.notMem_empty K)⟩
  | insert K₀ F hK₀F ih =>
    intro hF
    obtain ⟨e', he', hconj'⟩ := ih (fun K hK => hF K (Finset.mem_insert_of_mem hK))
    have hK₀ := hF K₀ (Finset.mem_insert_self K₀ F)
    obtain ⟨k₀, hk₀, hk₀conj⟩ := hinner K₀ hK₀
    have hcommF : ∀ K ∈ F, K ≤ Subgroup.centralizer (K₀ : Set Y) := by
      intro K hK
      rcases CFSG.LocalCores.distinct_components_commute
          ((isComponent_iff_isComponentOf_top K).mpr (hF K (Finset.mem_insert_of_mem hK)))
          ((isComponent_iff_isComponentOf_top K₀).mpr hK₀) with h | h
      · exact absurd (h ▸ hK) hK₀F
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have he'C : e' ∈ Subgroup.centralizer (K₀ : Set Y) := (iSup₂_le hcommF) he'
    refine ⟨e' * k₀, ?_, ?_⟩
    · apply mul_mem
      · have hle : (⨆ K ∈ F, K) ≤ (⨆ K ∈ insert K₀ F, K) :=
          iSup₂_le fun K hK => le_iSup₂ (f := fun K (_ : K ∈ insert K₀ F) => K) K
            (Finset.mem_insert_of_mem hK)
        exact hle he'
      · exact (le_iSup₂ (f := fun K (_ : K ∈ insert K₀ F) => K) K₀
          (Finset.mem_insert_self K₀ F)) hk₀
    · intro K hK x hx
      rcases Finset.mem_insert.mp hK with rfl | hKF
      · rw [hk₀conj x hx]
        have hy : k₀ * x * k₀⁻¹ ∈ K := mul_mem (mul_mem hk₀ hx) (inv_mem hk₀)
        have hc := (Subgroup.mem_centralizer_iff.mp he'C) _ hy
        calc e' * k₀ * x * (e' * k₀)⁻¹ = e' * (k₀ * x * k₀⁻¹) * e'⁻¹ := by group
          _ = k₀ * x * k₀⁻¹ := by rw [← hc, mul_inv_cancel_right]
      · have hxC := hcommF K hKF hx
        have hc := (Subgroup.mem_centralizer_iff.mp hxC) k₀ hk₀
        calc e' * k₀ * x * (e' * k₀)⁻¹ = e' * (k₀ * x * k₀⁻¹) * e'⁻¹ := by group
          _ = e' * x * e'⁻¹ := by rw [hc, mul_inv_cancel_right]
          _ = s * x * s⁻¹ := hconj' K hKF x hx

theorem sylow_le_generalizedFittingSubgroupOf (hO : pPrimeCore 2 Y = ⊥)
    (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) :
    (S : Subgroup Y) ≤ generalizedFittingSubgroupOf (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hY S
  have hFit : CFSG.fittingSubgroupOf (⊤ : Subgroup Y) = CFSG.fittingSubgroup Y :=
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations Y
  have hF2 : IsPGroup 2 (CFSG.fittingSubgroup Y) :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO
  have hFS : CFSG.fittingSubgroup Y ≤ (S : Subgroup Y) := hF2.le_sylow_of_normal S
  have hEF : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      K ≤ Subgroup.centralizer (CFSG.fittingSubgroup Y : Set Y) := by
    intro K hK
    have := (CFSG.LocalCores.component_solvable_centralizer (R := CFSG.fittingSubgroup Y)
      inferInstance (CFSG.fittingSubgroup_normal).isSubnormal).1 K
      ((isComponent_iff_isComponentOf_top K).mpr hK)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  intro s hs
  obtain ⟨e, he, hconj⟩ := exists_mem_componentLayerOf_conj_eq hO hY S hs
  have heC : e ∈ Subgroup.centralizer (CFSG.fittingSubgroup Y : Set Y) :=
    (sSup_le fun K hK => hEF K hK) he
  have hc : e⁻¹ * s ∈
      Subgroup.centralizer (generalizedFittingSubgroupOf (⊤ : Subgroup Y) : Set Y) := by
    suffices hle : generalizedFittingSubgroupOf (⊤ : Subgroup Y) ≤
        Subgroup.centralizer ({e⁻¹ * s} : Set Y) by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    apply sup_le
    · try rw [show CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup Y) =
        CFSG.fittingSubgroupOf (⊤ : Subgroup Y) from rfl]
      rw [hFit]
      intro f hf
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : f * s = s * f := setLike_mul_comm (hFS hf) hs
      have h2 : f * e = e * f := Subgroup.mem_centralizer_iff.mp heC f hf
      have h2' : f * e⁻¹ = e⁻¹ * f := Commute.inv_right h2
      calc f * (e⁻¹ * s) = f * e⁻¹ * s := by rw [mul_assoc]
        _ = e⁻¹ * f * s := by rw [h2']
        _ = e⁻¹ * (s * f) := by rw [mul_assoc, h1]
        _ = e⁻¹ * s * f := by rw [mul_assoc]
    · apply sSup_le
      intro K hK x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hconj K hK x hx
      calc x * (e⁻¹ * s) = e⁻¹ * (e * x * e⁻¹) * s := by group
        _ = e⁻¹ * (s * x * s⁻¹) * s := by rw [h]
        _ = e⁻¹ * s * x := by group
  have hcF := CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le hc
  have heF : e ∈ generalizedFittingSubgroupOf (⊤ : Subgroup Y) :=
    (le_sup_right : componentLayerOf (⊤ : Subgroup Y) ≤ _) he
  have : s = e * (e⁻¹ * s) := by group
  rw [this]
  exact mul_mem heF hcF

theorem odd_index_generalizedFittingSubgroupOf (hO : pPrimeCore 2 Y = ⊥)
    (hY : HasAbelianSylowTwo Y) :
    Odd (generalizedFittingSubgroupOf (⊤ : Subgroup Y)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hdvd := Subgroup.index_dvd_of_le (sylow_le_generalizedFittingSubgroupOf hO hY S)
  have hSodd : Odd (S : Subgroup Y).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  exact Odd.of_dvd_nat hSodd hdvd

end TypeZero

end CFSG.Walter
