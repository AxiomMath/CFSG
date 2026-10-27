module

public import CFSG.Quasithin.H13.NQTermInternalModule
public import CFSG.Quasithin.SteinbergCDConfinedInvolutionOddCore
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qtnqU_le_t {T L M : Subgroup G} (h : QTNQ T L M) : qtnqU L M ≤ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨-, hUM, hUn, hUel⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  set T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2 with hT'
  have hT'T : (T' : Subgroup G) = T := IsPGroup.toSylow_coe h.sylow.1 h.sylow.2
  have hU2 : IsPGroup 2 (qtnqU L M) := by
    have := hUel
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  have hTU : (T' : Subgroup G) ≤ normalizer (qtnqU L M : Set G) := by
    rw [hT'T]
    exact h.t_le.trans ((normal_subgroupOf_iff_le_normalizer hUM).mp hUn)
  have h1 := T'.is_maximal' (T'.isPGroup'.to_sup_of_normal_right' hU2 hTU) le_sup_left
  rw [← hT'T, ← h1]
  exact le_sup_right

theorem internal_centralizer_Fitting_containment_kills_odd_core {T L M : Subgroup G}
    (h : QTNQ T L M) {v : G} (hv : v ∈ qtnqU L M) (_hv1 : v ≠ 1)
    (hF : (CFSG.fittingSubgroup (centralizer ({v} : Set G) ⧸
        CFSG.pCore 2 (centralizer ({v} : Set G)))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 (centralizer ({v} : Set G)))) ≤
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G))) :
    CFSG.pPrimeCore 2 (centralizer ({v} : Set G)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({v} : Set G) with hC
  obtain ⟨-, -, -, -, ⟨hU1, hUM, -, hUel⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hUT := qtnqU_le_t h
  have hvT : v ∈ T := hUT hv
  have hvM : v ∈ M := hUM hv
  have hv2 : v ^ 2 = 1 := by
    have := hUel
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  have hT : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hchar : QuasithinUnique.CharTwo M :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT h.max_two_local.1
      h.t_le
  have hX2 : IsPGroup 2 (zpowers v) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hv2, one_zpow]
    rfl
  have hA := QuasithinUnique.CharTwo.inf_centralizer hchar (zpowers_le.mpr hvM) hX2
  rw [zpowers_eq_closure, centralizer_closure] at hA
  have hA' : CFSG.IsCharacteristicP 2 ((M ⊓ C).subgroupOf C) :=
    LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
      (subgroupOfEquivOfLe inf_le_right).symm
      (QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hA)
  have hT2 : IsPGroup 2 T := h.sylow.1
  have : Nontrivial T := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    exact ⟨⟨⟨u, hUT u.2⟩, 1, fun he => hu1 (Subtype.ext (congrArg (fun t : T => (t : G)) he))⟩⟩
  have : Nontrivial (center T) := hT2.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := (hT2.to_subgroup (center T)).nontrivial_iff_card.mp inferInstance
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  set z : G := ((w : T) : G) with hz
  have hzord : orderOf z = 2 := by rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hzT : z ∈ T := (w : T).2
  have hzcen : ∀ t ∈ T, t * z = z * t := fun t ht =>
    congrArg Subtype.val (mem_center_iff.mp w.2 ⟨t, ht⟩)
  have hzZ : z ∈ quasithinOmegaOneCenter T := by
    refine subset_closure ⟨mem_inf.mpr ⟨hzT, mem_centralizer_iff.mpr fun t ht => hzcen t ht⟩, ?_⟩
    rw [← hzord]
    exact pow_orderOf_eq_one z
  have hzC : z ∈ C := by
    rw [hC, mem_centralizer_singleton_iff]
    exact (hzcen v hvT).symm
  have hzne : zpowers z ≠ ⊥ := by
    intro he
    have : z = 1 := by
      have := mem_zpowers z
      rwa [he, mem_bot] at this
    rw [this, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hZ2 : IsPGroup 2 (zpowers z) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    have hz2 : z ^ 2 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    rw [SubgroupClass.coe_pow, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hz2, one_zpow]
    rfl
  have hAZ : (centralizer (quasithinOmegaOneCenter T : Set G) : Set G) ⊆
      (centralizer (zpowers z : Set G) : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hx z hzZ).symm
  have hMset : {K : Subgroup G | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
      (centralizer (quasithinOmegaOneCenter T : Set G) : Set G) ⊆ (K : Set G)} = {M} := by
    ext K
    constructor
    · rintro ⟨hK, hCK⟩
      exact h.centralizer_unique K hK hCK
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨h.max_two_local, h.centralizer_le⟩
  obtain ⟨hCN, hNM, -, -⟩ := QuasithinUnique.maxTwoLocal_centralizer_transfer hzne hZ2 hAZ hMset
  have hCz : centralizer ({⟨z, hzC⟩} : Set C) ≤ (M ⊓ C).subgroupOf C := by
    intro x hx
    rw [mem_centralizer_singleton_iff] at hx
    have hx' : (x : G) ∈ centralizer (zpowers z : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hx
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hNM (hCN hx'), x.2⟩)
  have hzord' : orderOf (⟨z, hzC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk, hzord]
  exact SteinbergCD.confined_involution_quotient_fitting_kill_odd_core (CFSG.pCore 2 C)
    ((M ⊓ C).subgroupOf C) hA' ⟨z, hzC⟩ hzord' hCz hF

end CFSG.Quasithin.H13.NQSetup
