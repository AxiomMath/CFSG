module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)
open scoped commutatorElement

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem bar_A_comm' (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {a b : m.Hbar}
    (ha : a ∈ m.bar m.A) (hb : b ∈ m.bar m.A) : a * b = b * a :=
  m.bar_A_comm h69 ha (m.bar_mono m.A_le_R hb)

theorem pow_eq_one_of_mem_bar_A {a : m.Hbar} (ha : a ∈ m.bar m.A) : a ^ m.r = 1 := by
  obtain ⟨a, haA, rfl⟩ := ha
  rw [← map_pow]
  have : a ^ m.r = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact m.isElemAbelian_A.2 _ haA)
  rw [this, map_one]

theorem isPGroup_center_component {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    IsPGroup m.r (center ↥K) := by
  have h1 : (center ↥K).map K.subtype ≤ CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar) := by
    rintro _ ⟨z, hz, rfl⟩
    exact N588.mem_fitting_of_mem_center_component hK z.2 fun k hk =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨k, hk⟩).symm
  have h2 := m.isPGroup_fittingSubgroupOf.to_le h1
  exact h2.of_equiv ((center ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm

theorem pRank_top_le_three (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (K : Subgroup m.Hbar) :
    CFSG.Open.pRank m.r (⊤ : Subgroup ↥K) ≤ 3 := by
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective m.r m.hr
    K.subtype K.subtype_injective (⊤ : Subgroup ↥K)
  exact h1.trans (m.pRank_Hbar_le_three h69 _)

theorem center_component_eq_bot (hKM : UCK.KMult) (hK3 : UCK.KMult3)
    (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    center ↥K = ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨-, hperf, hsimple⟩ := hK.2.2
  have hq : CFSG.Open.IsQuasisimple ↥K := ⟨hperf, hsimple⟩
  have hKk : CFSG.Open.IsKGroup (↥K ⧸ center ↥K) :=
    (m.isKGroup_Hbar.subgroup K).quotient (center ↥K)
  have hZp := m.isPGroup_center_component hK
  have hrank := m.pRank_top_le_three h69 K
  by_cases hr3 : m.r = 3
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨T, hT⟩ := exists_isSylowOf 3 (⊤ : Subgroup ↥K)
    have hZp3 : IsPGroup 3 (center ↥K) := by
      have h := congrArg (fun p => IsPGroup p (center ↥K)) hr3
      exact (cast h hZp : IsPGroup 3 (center ↥K))
    have hrank3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
      have h := congrArg (fun p => CFSG.Open.pRank p (⊤ : Subgroup ↥K)) hr3
      rw [← h]
      exact hrank
    refine hK3 ↥K hq hKk hZp3 hrank3 T hT fun x hx hx3 y hy => ?_
    have hTp3 : IsPGroup 3 (T.map K.subtype) := hT.isPGroup.map K.subtype
    have hTp : IsPGroup m.r (T.map K.subtype) := by
      have h := congrArg (fun p => IsPGroup p (T.map K.subtype)) hr3.symm
      exact (cast h hTp3 : IsPGroup m.r (T.map K.subtype))
    have hxr : (x : m.Hbar) ^ m.r = 1 := by
      have h := congrArg (fun n => (x : m.Hbar) ^ n) hr3
      rw [h]
      exact congrArg Subtype.val hx3
    have h1 := m.comm_of_pow_eq_one h69 hTp ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxr
    exact Subtype.ext h1
  · exact hKM ↥K hq hKk m.r m.hr (m.five_le_r hr3) hZp hrank

theorem isSimpleGroup_component (hKM : UCK.KMult) (hK3 : UCK.KMult3)
    (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    IsSimpleGroup ↥K := by
  haveI : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.2.2.2
  have hc := m.center_component_eq_bot hKM hK3 h69 hK
  let e : ↥K ⧸ center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot)
  exact (MulEquiv.isSimpleGroup_congr e).mp inferInstance

theorem r_dvd_card_component {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    m.r ∣ Nat.card K := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  by_contra hnd
  have hsn : K.IsSubnormal := CFSG.Walter.isSubnormal_of_isComponentOf hK
  have h1 := N588.map_pPrimeCore_le_of_isSubnormal m.r hsn
  have htop : CFSG.pPrimeCore m.r ↥K = ⊤ := by
    rw [eq_top_iff]
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd m.hr).2 hnd
  rw [htop, m.pPrimeCore_Hbar, ← MonoidHom.range_eq_map, range_subtype] at h1
  obtain ⟨-, -, hnt⟩ := hK.2.2
  rw [le_bot_iff] at h1
  subst h1
  obtain ⟨a, b, hab⟩ := hK.2.2.1.exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem bar_R_inf_component_sylow (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) : IsSylowOf m.r (m.bar m.R ⊓ K) K := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hEn' : (componentLayerOf (⊤ : Subgroup m.Hbar)).Normal :=
    ⟨fun n hn g => (CFSG.GorensteinWalter.componentLayerOf_isNormalIn ⊤).2 g (mem_top g) n hn⟩
  have hEn : (⊤ : Subgroup m.Hbar) ≤ normalizer (componentLayerOf (⊤ : Subgroup m.Hbar) :
      Set m.Hbar) := le_top.trans (normalizer_eq_top (H := componentLayerOf ⊤)).ge
  have h1 := (m.bar_R_sylow h69).inf_of_le_normalizer le_top hEn
  have hKE : K ≤ componentLayerOf (⊤ : Subgroup m.Hbar) := le_sSup hK
  have h2 := h1.inf_of_le_normalizer hKE (CFSG.Walter.componentLayerOf_top_le_normalizer hK)
  rwa [inf_assoc, inf_of_le_right hKE] at h2

theorem exists_mem_component (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    ∃ y ∈ m.bar m.R, y ∈ K ∧ y ≠ 1 ∧ y ^ m.r = 1 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hS := m.bar_R_inf_component_sylow h69 hK
  have hdvd : m.r ∣ Nat.card ↥(m.bar m.R ⊓ K) := by
    rw [hS.card_eq]
    have hK0 : 0 < (Nat.card K).factorization m.r :=
      m.hr.factorization_pos_of_dvd Nat.card_pos.ne' (m.r_dvd_card_component hK)
    exact dvd_pow_self _ hK0.ne'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' m.r hdvd
  have hy' : orderOf (y : m.Hbar) = m.r := by rw [Subgroup.orderOf_coe]; exact hy
  refine ⟨y, y.2.1, y.2.2, fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hy'
    exact m.hr.one_lt.ne hy'
  · calc (y : m.Hbar) ^ m.r = (y : m.Hbar) ^ orderOf (y : m.Hbar) := by rw [hy']
      _ = 1 := pow_orderOf_eq_one _

theorem bar_Z_inf_component (hKM : UCK.KMult) (hK3 : UCK.KMult3)
    (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤)
    {z : m.Hbar} (hz : z ∈ m.bar m.Z) (hzK : z ∈ K) : z = 1 := by
  have hc := m.center_component_eq_bot hKM hK3 h69 hK
  have h1 : (⟨z, hzK⟩ : ↥K) ∈ center ↥K := Subgroup.mem_center_iff.2 fun k =>
    Subtype.ext (m.bar_Z_comm hz k).symm
  rw [hc, mem_bot] at h1
  exact congrArg Subtype.val h1

theorem pre_le_M_of_centralizer (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    {K : Subgroup m.Hbar} {a : m.Hbar} (ha : a ∈ m.bar m.A) (haZ : a ∉ m.bar m.Z)
    (hac : ∀ k ∈ K, a * k = k * a) : m.pre K ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set B : Subgroup m.Hbar := m.bar m.Z ⊔ zpowers a with hB
  have hBc : B ≤ centralizer (K : Set m.Hbar) := by
    refine sup_le (fun z hz => mem_centralizer_iff.2 fun k _ => (m.bar_Z_comm hz k).symm) ?_
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun k hk => (hac k hk).symm
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ (m.bar m.Z).one_mem)
  have hacard : Nat.card (zpowers a) = m.r := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (m.pow_eq_one_of_mem_bar_A ha) ha1
  have hZa : m.bar m.Z ⊓ zpowers a = ⊥ := by
    have h := inf_eq_bot_of_not_le_of_card_prime m.hr hacard
      (fun h => haZ (h (mem_zpowers a)))
    rw [inf_comm] at h
    exact h
  have hBA : B ≤ m.bar m.A := sup_le (m.bar_mono m.Z_le_A) (zpowers_le.2 ha)
  have hcommB : ∀ x ∈ m.bar m.Z, ∀ y ∈ zpowers a, x * y = y * x := fun x hx y _ =>
    m.bar_Z_comm hx y
  have hBcard : Nat.card B = m.r ^ 2 := by
    rw [hB, card_sup_of_commute_of_disjoint hcommB hZa, m.card_bar_Z, hacard, pow_two]
  have hBE : B ⊓ m.bar m.E ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ x ∈ B, ∀ y ∈ m.bar m.E, x * y = y * x := fun x hx y hy =>
      m.bar_A_comm' h69 (hBA hx) (m.bar_mono m.E_le_A hy)
    have hcard := card_sup_of_commute_of_disjoint hcomm hbot
    rw [hBcard, m.card_bar_E] at hcard
    have hle : Nat.card ↥(B ⊔ m.bar m.E) ≤ Nat.card ↥(m.bar m.A) :=
      Subgroup.card_le_of_le (sup_le hBA (m.bar_mono m.E_le_A))
    rw [hcard, m.card_bar_A] at hle
    have : m.r ^ 3 < m.r ^ 2 * m.r ^ 2 := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right m.hr.one_lt (by norm_num)
    omega
  obtain ⟨⟨x, hxB, hxE⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBE
  obtain ⟨e', he'E, rfl⟩ := hxE
  have he : (e' : G) ∈ m.E := he'E
  have he1 : (e' : G) ≠ 1 := by
    intro h
    apply hx1
    have : e' = 1 := Subtype.ext h
    simp [this]
  refine m.pre_le_M he he1 fun y hy => ?_
  have h1 := mem_centralizer_iff.1 (hBc hxB) y hy
  have h2 : (⟨(e' : G), m.hZ.E_le_centralizer he⟩ : ↥m.H) = e' := rfl
  rw [h2]
  exact h1

theorem component_unique (hKM : UCK.KMult) (hK3 : UCK.KMult3)
    (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {K₁ K₂ : Subgroup m.Hbar}
    (hK₁ : IsComponentOf K₁ ⊤) (hK₂ : IsComponentOf K₂ ⊤) : K₁ = K₂ := by
  by_contra hne
  have hpre : ∀ K : Subgroup m.Hbar, IsComponentOf K ⊤ → m.pre K ≤ m.M := by
    intro K hK
    obtain ⟨K', hK', hKK'⟩ : ∃ K' : Subgroup m.Hbar, IsComponentOf K' ⊤ ∧ K ≠ K' := by
      by_cases h : K = K₁
      · exact ⟨K₂, hK₂, h ▸ hne⟩
      · exact ⟨K₁, hK₁, h⟩
    obtain ⟨y, hyR, hyK', hy1, hyr⟩ := m.exists_mem_component h69 hK'
    have hyA : y ∈ m.bar m.A := m.mem_bar_A_of_pow h69 hyR hyr
    have hyZ : y ∉ m.bar m.Z := fun hz =>
      hy1 (m.bar_Z_inf_component hKM hK3 h69 hK' hz hyK')
    have hcomm : ⁅K, K'⁆ = ⊥ := by
      rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot hK hK' with h | h
      · exact absurd h hKK'
      · exact h
    refine m.pre_le_M_of_centralizer h69 hyA hyZ fun k hk => ?_
    have h1 : ⁅k, y⁆ = 1 := by
      have := commutator_mem_commutator hk hyK'
      rwa [hcomm, mem_bot] at this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  set W : Subgroup G := ⨆ K : {K : Subgroup m.Hbar // IsComponentOf K ⊤}, m.pre K.1 with hW
  have hWM : W ≤ m.M := iSup_le fun K => hpre K.1 K.2
  have hWH : W ≤ m.H := iSup_le fun K => m.pre_le_H K.1
  have hE : componentLayerOf (⊤ : Subgroup m.Hbar) ≤ m.bar W :=
    sSup_le fun K hK => (m.le_bar_pre K).trans (m.bar_mono (le_iSup_of_le ⟨K, hK⟩ le_rfl))
  have hpreE : m.pre (componentLayerOf (⊤ : Subgroup m.Hbar)) ≤ m.M :=
    ((Subgroup.map_mono (Subgroup.comap_mono hE)).trans (m.pre_bar_le hWH)).trans
      (sup_le hWM m.OHG_le_M)
  obtain ⟨y, hyR, hyK, hy1, hyr⟩ := m.exists_mem_component h69 hK₁
  obtain ⟨a, haA, rfl⟩ := m.mem_bar_A_of_pow h69 hyR hyr
  have hEn : (componentLayerOf (⊤ : Subgroup m.Hbar)).Normal :=
    ⟨fun n hn g => (CFSG.GorensteinWalter.componentLayerOf_isNormalIn ⊤).2 g (mem_top g) n hn⟩
  have hK₁E : K₁ ≤ componentLayerOf (⊤ : Subgroup m.Hbar) := le_sSup hK₁
  refine m.hZ.not_le (m.H_le_M_of_le_M (m.pre_le_H _) (m.H_le_normalizer_pre hEn) hpreE
    (t := (a : G)) ((m.mem_pre).2 ⟨a.2, hK₁E hyK⟩) haA ?_)
  intro haZ
  exact hy1 (m.bar_Z_inf_component hKM hK3 h69 hK₁ (m.mem_bar_of_mem haZ) hyK)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
