module

public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.LocalComponent.Layer

public section

namespace CFSG.Quasithin.SBd17

open scoped commutatorElement

theorem le_pCore_two {X : Type*} [Group X] {M : Subgroup X} [M.Normal] (hM : IsPGroup 2 M) :
    M ≤ CFSG.pCore 2 X :=
  le_sSup ⟨inferInstance, hM⟩

theorem exists_zpowers_eq_of_card_two {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    (hN2 : Nat.card ↥N = 2) : ∃ z : H, z ∈ N ∧ orderOf z = 2 ∧ Subgroup.zpowers z = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (by rw [hN2])
  have hzo : orderOf (z : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  refine ⟨z, z.2, hzo, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2) ?_⟩
  rw [Nat.card_zpowers, hzo, hN2]

theorem centralizer_pCore_central_quotient_le {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hNc : N ≤ Subgroup.center H) (hN2 : Nat.card ↥N = 2)
    (hchar : Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H) :
    Subgroup.centralizer (CFSG.pCore 2 (H ⧸ N) : Set (H ⧸ N)) ≤ CFSG.pCore 2 (H ⧸ N) := by
  obtain ⟨z, hzN, hzo, hzN'⟩ := exists_zpowers_eq_of_card_two N hN2
  have hchar' : CFSG.Assembly.Dichotomy.dichotomyCharP 2 H := by
    unfold CFSG.Assembly.Dichotomy.dichotomyCharP
    exact hchar
  have hker := (CFSG.Assembly.Dichotomy.central_involution_core_action_kernel hchar'
    (hNc hzN) hzo).2.1
  have hQπ : (CFSG.pCore 2 H).map (QuotientGroup.mk' N) ≤ CFSG.pCore 2 (H ⧸ N) := by
    have : ((CFSG.pCore 2 H).map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective N)
    exact le_pCore_two (CFSG.pCore_isPGroup.map _)
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : y ∈ CFSG.pCore 2 H := by
    refine hker y fun q hq => ?_
    rw [hzN', ← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' N) ⁅q, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hx _ (hQπ ⟨q, hq, rfl⟩)
  exact hQπ ⟨y, hy, rfl⟩

theorem oddCore_eq_bot_of_centralizer_pCore_le {X : Type*} [Group X] [Finite X]
    (h : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) :
    CFSG.Open.componentClassificationOddCore X = ⊥ := by
  have hOodd : Odd (Nat.card (CFSG.Open.componentClassificationOddCore X)) :=
    CFSG.ComponentClassification.OddCore.odd_card X
  have hdisj : ∀ x ∈ CFSG.Open.componentClassificationOddCore X, x ∈ CFSG.pCore 2 X → x = 1 :=
    fun x hxO hxP => CFSG.Assembly.Dichotomy.CentralizerContainment.eq_one_of_mem_of_odd_orderOf
      CFSG.pCore_isPGroup hxP (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ hxO))
  refine eq_bot_iff.mpr fun o ho => ?_
  refine Subgroup.mem_bot.mpr (hdisj o ho (h ?_))
  refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
  have h1 : p * o * p⁻¹ * o⁻¹ ∈ CFSG.Open.componentClassificationOddCore X :=
    mul_mem ((CFSG.Open.componentClassificationOddCore_normal X).conj_mem o ho p)
      (inv_mem ho)
  have h2 : p * o * p⁻¹ * o⁻¹ ∈ CFSG.pCore 2 X := by
    have : p * o * p⁻¹ * o⁻¹ = p * (o * p⁻¹ * o⁻¹) := by group
    rw [this]
    exact mul_mem hp (CFSG.pCore_normal.conj_mem _ (inv_mem hp) o)
  have h3 := hdisj _ h1 h2
  calc p * o = (p * o * p⁻¹ * o⁻¹) * (o * p) := by group
    _ = o * p := by rw [h3, one_mul]

theorem layer_eq_bot_of_centralizer_pCore_le {X : Type*} [Group X] [Finite X]
    (h : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) :
    CFSG.ComponentClassification.Layer.subgroup X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  have hcomm : ⁅CFSG.ComponentClassification.Layer.subgroup X, CFSG.pCore 2 X⁆ = ⊥ :=
    CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal _
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
        (CFSG.pCore_normal (p := 2) (G := X)).isSubnormal)
  have hle : CFSG.ComponentClassification.Layer.subgroup X ≤ CFSG.pCore 2 X :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans h
  by_contra hne
  have : Nontrivial (CFSG.ComponentClassification.Layer.subgroup X) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have : Group.IsPerfect (CFSG.ComponentClassification.Layer.subgroup X) :=
    CFSG.ComponentClassification.Layer.perfect X
  have : Group.IsNilpotent (CFSG.ComponentClassification.Layer.subgroup X) :=
    (CFSG.pCore_isPGroup.to_le hle).isNilpotent
  exact Group.IsPerfect.not_isSolvable (CFSG.ComponentClassification.Layer.subgroup X)
    inferInstance

theorem no_twoComponent_of_charTwo_quotient {H : Type} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNc : N ≤ Subgroup.center H) (hN2 : Nat.card ↥N = 2)
    (hchar : Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H)
    {t : H ⧸ N} (ht1 : t ≠ 1) (ht2 : t * t = 1) {K : Subgroup (H ⧸ N)}
    (hKC : K ≤ Subgroup.centralizer ({t} : Set (H ⧸ N)))
    (hK : CFSG.ComponentClassification.TwoComponents.IsTwoComponent
      (K.subgroupOf (Subgroup.centralizer ({t} : Set (H ⧸ N))))) : False := by
  have _ := ht1
  have hcharX := centralizer_pCore_central_quotient_le N hNc hN2 hchar
  have hcore := oddCore_eq_bot_of_centralizer_pCore_le hcharX
  have hlayer := layer_eq_bot_of_centralizer_pCore_le hcharX
  have h1 := CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
    CFSG.ClassicalInvolution.l2PrimeBalance hcore ht2 rfl hK
  rw [hlayer, le_bot_iff, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKC] at h1
  have hbot : K.subgroupOf (Subgroup.centralizer ({t} : Set (H ⧸ N))) = ⊥ := by
    rw [h1]
    exact Subgroup.bot_subgroupOf _
  have hnt := CFSG.ComponentClassification.TwoComponents.nontrivial hK
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hbot

theorem inf_oddCore_eq_bot_of_quasisimple {Γ : Type*} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    [K.Normal] (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 2 ↥(Subgroup.center ↥K))
    (hK2 : 2 ∣ Nat.card ↥K) : K ⊓ CFSG.Open.componentClassificationOddCore Γ = ⊥ := by
  have hOodd : Odd (Nat.card (CFSG.Open.componentClassificationOddCore Γ)) :=
    CFSG.ComponentClassification.OddCore.odd_card Γ
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      ((K ⊓ CFSG.Open.componentClassificationOddCore Γ).subgroupOf K) with hcen | htop
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxK, hxO⟩ := hx
    have hxc : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := hcen (Subgroup.mem_subgroupOf.mpr ⟨hxK, hxO⟩)
    have hodd : Odd (orderOf (⟨x, hxK⟩ : ↥K)) := by
      rw [Subgroup.orderOf_mk]
      exact Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ hxO)
    have h1 := CFSG.Assembly.Dichotomy.CentralizerContainment.eq_one_of_mem_of_odd_orderOf hZ hxc
      hodd
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · exfalso
    have hKle : K ≤ CFSG.Open.componentClassificationOddCore Γ := fun x hx => by
      have : (⟨x, hx⟩ : ↥K) ∈
          (K ⊓ CFSG.Open.componentClassificationOddCore Γ).subgroupOf K := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    obtain ⟨c, hc⟩ := hK2.trans (Subgroup.card_dvd_of_le hKle)
    obtain ⟨d, hd⟩ := hOodd
    omega

theorem isTwoComponent_of_normal_quasisimple {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    [K.Normal] (hq : CFSG.IsQuasisimple ↥K) (hZ : IsPGroup 2 ↥(Subgroup.center ↥K))
    (hK2 : 2 ∣ Nat.card ↥K) :
    CFSG.ComponentClassification.TwoComponents.IsTwoComponent K := by
  have hqo : CFSG.Open.IsQuasisimple ↥K := ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hKO : K ⊓ CFSG.Open.componentClassificationOddCore Γ = ⊥ :=
    inf_oddCore_eq_bot_of_quasisimple hqo hZ hK2
  have hsub : CFSG.Open.IsSubnormal K ⊤ :=
    CFSG.Open.IsSubnormal.step le_top Subgroup.normal_subgroupOf (CFSG.Open.IsSubnormal.refl ⊤)
  have hOK : CFSG.Open.componentClassificationOddCore ↥K = ⊥ := by
    have h := CFSG.ComponentClassification.OddCore.normal_intersection Γ K
    rw [hKO] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h
  refine ⟨hsub, (CFSG.ComponentClassification.Components.quotient_component_iff K hsub).mpr ?_, ?_⟩
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot) hqo
  · intro smaller hle _ hmap
    refine le_antisymm hle fun x hx => ?_
    have hπx : QuotientGroup.mk' (CFSG.Open.componentClassificationOddCore Γ) x ∈
        smaller.map (QuotientGroup.mk' (CFSG.Open.componentClassificationOddCore Γ)) := by
      rw [hmap]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hπx
    have h1 : s⁻¹ * x ∈ CFSG.Open.componentClassificationOddCore Γ := QuotientGroup.eq.mp hsx
    have h2 : s⁻¹ * x ∈ K ⊓ CFSG.Open.componentClassificationOddCore Γ :=
      ⟨K.mul_mem (K.inv_mem (hle hs)) hx, h1⟩
    rw [hKO, Subgroup.mem_bot, inv_mul_eq_one] at h2
    rw [← h2]
    exact hs

end CFSG.Quasithin.SBd17
