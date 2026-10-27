module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.RankThree.GF2n.Parrott.E27LineCount
public import CFSG.GroupTheory.InvolutionPair
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.Quasithin.H13.J4Core
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

theorem J_inf_centralizer_sigma1Nine_mul_eq_centerIn_J (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G) =
      centerIn (J z) := by
  let y : ↥(H z) := sigma1Nine (z := z) D * σ₂
  have hE27 : E27LineCountData (z := z) (D := D) h σ₂ :=
    e27LineCountData_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  have hy3 : orderOf y = 3 := by
    change orderOf (sigma1Nine (z := z) D * σ₂) = 3
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂)]
    exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  have hZy : conjZ z y = 1 := by
    have h2 : conjZ z σ₂ = 1 :=
      conjZ_eq_one_of_mem_Q (z := z) D h σ₂
        (Subgroup.mem_subgroupOf.mpr (by rw [hq₂]; exact sigma2_mem_Q))
    change conjZ z (sigma1Nine (z := z) D * σ₂) = 1
    rw [map_mul, conjZ_sigma1Nine h D, h2, mul_one]
  have hfix : fixDimV h y = 0 :=
    fixDimV_sigma1Nine_mul_sigma2_eq_zero_of_not_equalityBranch (z := z) D h hIII
      hσ₂ hq₂ hc₂ hE27
  have hcenter_le : Subgroup.center (J z) ≤ centralizerJ y := by
    intro j hj
    rw [mem_centralizerJ_iff]
    have hjZ : (j : G) ∈ centerIn (J z) := by
      have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
        rwa [QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mp hj'
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := y) hZy hjZ)
  have hJcard : Nat.card (centralizerJ y) = 4 := by
    rw [card_centralizerJ_eq_card_inf_mul_card_pow_fixDim_of_orderOf_eq_three
      (z := z) (h := h) (x := y) hy3]
    have hcenter : Nat.card ↥(centralizerJ y ⊓ Subgroup.center (J z)) = 4 := by
      rw [inf_eq_right.mpr hcenter_le, card_center_subgroupOf_J h]
    rw [hcenter, hfix]
    norm_num
  have hcard_inf :
      Nat.card ↥(J z ⊓ centralizer ({(y : G)} : Set G)) = 4 := by
    rw [← hJcard, centralizerJ, inf_comm]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have hle : centerIn (J z) ≤ J z ⊓ centralizer ({(y : G)} : Set G) := by
    intro e he
    exact Subgroup.mem_inf.mpr
      ⟨he.1, centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := y) hZy he⟩
  change J z ⊓ centralizer ({(y : G)} : Set G) = centerIn (J z)
  exact (Subgroup.eq_of_le_of_card_ge (K := J z ⊓ centralizer ({(y : G)} : Set G)) hle
    (by rw [hcard_inf, card_centerIn_J h])).symm

theorem exists_elementaryAbelian_or_isSylowOf_centralizer_sigma1Nine_mul_of_involution
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hτ2 : (τ : G) * (τ : G) = 1)
    (hqτ : qH (z := z) D τ = (⟨t, t_mem_A⟩ : QA45.originalSubgroup))
    (hτσ : (τ : G) ∈
      centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G)) :
    (∃ E : Subgroup G,
        E ≤ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G) ∧
        Nat.card E = 16 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1) ∨
      ∃ T : Subgroup G,
        IsSylowOf 2 T (centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G)) ∧
        Nat.card T = 2 ^ 5 := by
  classical
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have hordz := h.1
    rw [hz1, orderOf_one] at hordz
    exact absurd hordz (by norm_num)
  have hz_sq : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h2
  let σ₃ : ↥(H z) := sigma1Nine (z := z) D * σ₂
  have hσ₃ : orderOf σ₃ = 3 := by
    change orderOf (sigma1Nine (z := z) D * σ₂) = 3
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂)]
    exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  have hq₃ : qH D σ₃ = s1A * s2A := by
    change qH D (sigma1Nine (z := z) D * σ₂) = s1A * s2A
    rw [map_mul, qH_sigma1Nine, hq₂]
  have hI1 : J z ⊓ centralizer ({((σ₃ : ↥(H z)) : G)} : Set G) = centerIn (J z) :=
    J_inf_centralizer_sigma1Nine_mul_eq_centerIn_J (z := z) D h hIII hσ₂ hq₂ hc₂
  let K : Subgroup ↥(H z) := Subgroup.centralizer ({σ₃} : Set ↥(H z))
  have memC_of_K : ∀ {w : ↥(H z)}, w ∈ K →
      (w : G) ∈ Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hw)
  have hτK : τ ∈ K := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hτσ)
  let X₄ : Subgroup A45 := Subgroup.closure ({tA, uA} : Set A45)
  let X₈ : Subgroup A45 := Subgroup.closure ({tA, uA, vA * bA} : Set A45)
  have ht2 : tA * tA = 1 := Subtype.ext t_sq
  have hu2 : uA * uA = 1 := Subtype.ext u_sq
  have htu : tA * uA = uA * tA := Subtype.ext t_commute_u
  have ht1 : tA ≠ 1 := by
    intro h1
    have h2 : (t : Equiv.Perm (Fin 45)) 3 = (1 : Equiv.Perm (Fin 45)) 3 :=
      congrArg (fun e => e 3) (congrArg Subtype.val h1)
    exact (by decide : (t : Equiv.Perm (Fin 45)) 3 ≠ (1 : Equiv.Perm (Fin 45)) 3) h2
  have hu1 : uA ≠ 1 := by
    intro h1
    have h2 : (u : Equiv.Perm (Fin 45)) 3 = (1 : Equiv.Perm (Fin 45)) 3 :=
      congrArg (fun e => e 3) (congrArg Subtype.val h1)
    exact (by decide : (u : Equiv.Perm (Fin 45)) 3 ≠ (1 : Equiv.Perm (Fin 45)) 3) h2
  have htune : tA ≠ uA := by
    intro h1
    have h2 : (t : Equiv.Perm (Fin 45)) 1 = (u : Equiv.Perm (Fin 45)) 1 :=
      congrArg (fun e => e 1) (congrArg Subtype.val h1)
    exact (by decide : (t : Equiv.Perm (Fin 45)) 1 ≠ u 1) h2
  have hX4card : Nat.card X₄ = 4 := by
    change Nat.card (Subgroup.closure ({tA, uA} : Set A45)) = 4
    exact CFSG.GroupTheory.card_closure_pair_eq_four ht2 hu2 htu ht1 hu1 htune
  have hX4eq : (X₄ : Set A45) = {1, tA, uA, tA * uA} := by
    change (Subgroup.closure ({tA, uA} : Set A45) : Set A45) = {1, tA, uA, tA * uA}
    exact CFSG.GroupTheory.coe_closure_pair_eq ht2 hu2 htu ht1 hu1 htune
  obtain ⟨hX8le, hX8card, -, hX8center⟩ :=
    qa45_sigma_centralizer_sylow.2.2
  have hX8cent : X₈ ≤ Subgroup.centralizer ({qH D σ₃} : Set QA45.originalSubgroup) := by
    change Subgroup.closure ({tA, uA, vA * bA} : Set A45) ≤
      Subgroup.centralizer ({qH D σ₃} : Set QA45.originalSubgroup)
    rw [hq₃]
    exact hX8le
  have hX4le : X₄ ≤ X₈ := by
    change Subgroup.closure ({tA, uA} : Set A45) ≤
      Subgroup.closure ({tA, uA, vA * bA} : Set A45)
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  have hX4cent : X₄ ≤ Subgroup.centralizer ({qH D σ₃} : Set QA45.originalSubgroup) :=
    hX4le.trans hX8cent
  have hut : Commute tA uA := htu
  have hutut : (uA * tA) * (uA * tA) = 1 := by
    rw [Commute.mul_mul_mul_comm hut uA tA, hu2, ht2, one_mul]
  have hut1 : uA * tA ≠ 1 := by
    intro h1
    obtain ⟨-, hC2, -, -⟩ := qa45_involution_centralizers
    have hcard : Nat.card (Subgroup.centralizer ({uA * tA} : Set A45)) = 51840 := by
      rw [h1]
      have htop : Subgroup.centralizer ({(1 : A45)} : Set A45) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
      rw [htop, Subgroup.card_top, card_QA45]
    rw [hC2] at hcard
    norm_num at hcard
  have hordut : orderOf (uA * tA) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hutut) hut1
  let yA : A45 := vA * bA
  have hyA2 : yA * yA = 1 := Subtype.ext qa45L1Facts.vbeta_sq
  have htv : (tA * yA) * (tA * yA) = uA * tA :=
    Subtype.ext qa45L1Facts.tvbeta_sq
  have hconj_yA : yA * tA * yA⁻¹ = uA := by
    have h1 : tA * (yA * tA * yA) = uA * tA := by
      calc tA * (yA * tA * yA) = (tA * yA) * (tA * yA) := by group
        _ = uA * tA := htv
    have h3 : tA * (uA * tA) = uA := by
      calc tA * (uA * tA) = (tA * uA) * tA := by group
        _ = (uA * tA) * tA := by rw [htu]
        _ = uA := by rw [mul_assoc, ht2, mul_one]
    have h4 : tA * (tA * (yA * tA * yA)) = tA * (uA * tA) := by rw [h1]
    have h5 : tA * (tA * (yA * tA * yA)) = yA * tA * yA := by
      rw [← mul_assoc, ht2, one_mul]
    have h2 : yA * tA * yA = uA := by
      rw [← h5, h4, h3]
    calc yA * tA * yA⁻¹ = yA * tA * yA := by rw [inv_eq_of_mul_eq_one_right hyA2]
      _ = uA := h2
  have hyA_Kmap : yA ∈ K.map (qH D) := by
    rw [map_centralizer_qH_of_orderOf_three (z := z) D σ₃ hσ₃]
    rw [show qH D σ₃ = s1A * s2A from hq₃]
    exact hX8le (Subgroup.subset_closure (by simp [yA]))
  obtain ⟨ŷ, hŷK, hqŷ⟩ := Subgroup.mem_map.mp hyA_Kmap
  let τ' : ↥(H z) := ŷ * τ * ŷ⁻¹
  have hτ'K : τ' ∈ K := by
    exact K.mul_mem (K.mul_mem hŷK hτK) (K.inv_mem hŷK)
  have hqτ' : qH D τ' = uA := by
    change qH D (ŷ * τ * ŷ⁻¹) = uA
    rw [map_mul, map_mul, map_inv, hqŷ, hqτ]
    exact hconj_yA
  have hτ'2 : (τ' : G) * (τ' : G) = 1 := by
    have hH : τ' * τ' = 1 := by
      change (ŷ * τ * ŷ⁻¹) * (ŷ * τ * ŷ⁻¹) = 1
      have hτ2' : τ * τ = 1 := Subtype.ext hτ2
      calc (ŷ * τ * ŷ⁻¹) * (ŷ * τ * ŷ⁻¹) = ŷ * (τ * τ) * ŷ⁻¹ := by group
        _ = 1 := by rw [hτ2']; group
    simpa using congrArg Subtype.val hH
  have hτconjZ : conjZ z τ = 1 :=
    conjZ_eq_one_of_mem_Q (z := z) D h τ
      (Subgroup.mem_subgroupOf.mpr (by rw [hqτ]; exact t_mem_Q))
  have hτ'conjZ : conjZ z τ' = 1 :=
    conjZ_eq_one_of_mem_Q (z := z) D h τ'
      (Subgroup.mem_subgroupOf.mpr (by rw [hqτ']; exact u_mem_Q))
  have hcentτ : centerIn (J z) ≤ Subgroup.centralizer ({(τ : G)} : Set G) :=
    centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := τ) hτconjZ
  have hcentτ' : centerIn (J z) ≤ Subgroup.centralizer ({(τ' : G)} : Set G) :=
    centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := τ') hτ'conjZ
  let P : Subgroup A45 → Subgroup G := fun X =>
    (X.comap (qH D) ⊓ K).map (H z).subtype
  have card_P : ∀ (X : Subgroup A45),
      X ≤ Subgroup.centralizer ({qH D σ₃} : Set A45) →
      Nat.card ↥(P X) = 4 * Nat.card X := by
    intro X hX
    let Q : Subgroup ↥(H z) := X.comap (qH D) ⊓ K
    have hPQ : Nat.card ↥(P X) = Nat.card ↥Q := by
      change Nat.card ↥(Q.map (H z).subtype) = Nat.card ↥Q
      exact Subgroup.card_map_of_injective (H z).subtype_injective
    let f : ↥Q →* ↥X :=
      { toFun := fun q => ⟨qH D (q : ↥(H z)), Subgroup.mem_comap.mp q.2.1⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [map_mul] }
    have hsurj : Function.Surjective f := by
      intro x
      have hxK : (x : A45) ∈ K.map (qH D) := by
        rw [map_centralizer_qH_of_orderOf_three (z := z) D σ₃ hσ₃]
        exact hX x.2
      obtain ⟨k, hkK, hqk⟩ := Subgroup.mem_map.mp hxK
      have hkcomap : k ∈ X.comap (qH D) := by
        rw [Subgroup.mem_comap]
        rw [hqk]
        exact x.2
      refine ⟨⟨k, Subgroup.mem_inf.mpr ⟨hkcomap, hkK⟩⟩, ?_⟩
      apply Subtype.ext
      exact hqk
    have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    have hker : f.ker = ((J z).subgroupOf (H z) ⊓ Q).subgroupOf Q := by
      ext q
      rw [MonoidHom.mem_ker]
      constructor
      · intro hq
        have hq' : ((f q : ↥X) : QA45.originalSubgroup) = 1 := by
          rw [hq]
          rfl
        have hq'' : qH D (q : ↥(H z)) = 1 := by
          simpa [f] using hq'
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mpr ⟨(J_mem_iff D (q : ↥(H z))).mpr hq'', q.2⟩)
      · intro hq
        obtain ⟨hqJ, -⟩ := Subgroup.mem_subgroupOf.mp hq
        apply Subtype.ext
        exact (J_mem_iff D (q : ↥(H z))).mp hqJ
    have hkercard : Nat.card ↥f.ker = 4 := by
      rw [hker]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      have hJX : (J z).subgroupOf (H z) ≤ X.comap (qH D) := by
        intro j hj
        rw [Subgroup.mem_comap, (J_mem_iff D j).mp hj]
        exact Subgroup.one_mem X
      have hQeq : (J z).subgroupOf (H z) ⊓ Q =
          (J z).subgroupOf (H z) ⊓ K := by
        change (J z).subgroupOf (H z) ⊓ (X.comap (qH D) ⊓ K) = _
        rw [← inf_assoc, inf_eq_left.mpr hJX]
      rw [hQeq]
      have hmap : ((J z).subgroupOf (H z) ⊓ K).map (H z).subtype =
          J z ⊓ Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G) := by
        ext g
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact Subgroup.mem_inf.mpr ⟨hk.1, memC_of_K hk.2⟩
        · rintro ⟨hgJ, hgC⟩
          have hgH : g ∈ H z := J_le_H hgJ
          have hgK : (⟨g, hgH⟩ : ↥(H z)) ∈ K := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)
          exact Subgroup.mem_map.mpr
            ⟨⟨g, hgH⟩, ⟨Subgroup.mem_subgroupOf.mpr hgJ, hgK⟩, rfl⟩
      rw [← Subgroup.card_map_of_injective (H z).subtype_injective
        (K := (J z).subgroupOf (H z) ⊓ K)]
      rw [hmap, hI1]
      exact card_centerIn_J h
    have hmul := Subgroup.card_ker_mul_card_range f
    rw [hkercard, hrange, Subgroup.card_top] at hmul
    rw [hPQ]
    exact hmul.symm
  have mem_centerIn_of_qH_one : ∀ {w : ↥(H z)}, w ∈ K → qH D w = 1 →
      (w : G) ∈ centerIn (J z) := by
    intro w hwK hwq
    rw [← hI1]
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp ((J_mem_iff D w).mpr hwq), memC_of_K hwK⟩
  by_cases hc : (τ' : G) * (τ : G) = (τ : G) * (τ' : G)
  ·
    let S : Set G := ({(τ : G), (τ' : G)} : Set G) ∪ (centerIn (J z) : Set G)
    have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      have hcenterτ : ∀ c ∈ centerIn (J z), c * (τ : G) = (τ : G) * c := by
        intro c hc'
        exact Subgroup.mem_centralizer_singleton_iff.mp (hcentτ hc')
      have hcenterτ' : ∀ c ∈ centerIn (J z), c * (τ' : G) = (τ' : G) * c := by
        intro c hc'
        exact Subgroup.mem_centralizer_singleton_iff.mp (hcentτ' hc')
      have hcentercenter : ∀ c ∈ centerIn (J z), ∀ d ∈ centerIn (J z), c * d = d * c := by
        intro c hc' d hd
        exact Subgroup.mem_centralizer_iff.mp hd.2 c hc'.1
      rcases hx with hx | hx
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · rcases hy with hy | hy
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · rfl
            · exact hc.symm
          · exact (hcenterτ y hy).symm
        · rcases hy with hy | hy
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact hc
            · rfl
          · exact (hcenterτ' y hy).symm
      · rcases hy with hy | hy
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact hcenterτ x hx
          · exact hcenterτ' x hx
        · exact hcentercenter x hx y hy
    have hSsq : ∀ x ∈ S, x * x = 1 := by
      intro x hx
      rcases hx with hx | hx
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hτ2
        · exact hτ'2
      · exact centerIn_J_sq h hx
    have hEA : CFSG.Open.IsElemAbelian 2 (Subgroup.closure S) :=
      CFSG.Open.IsElemAbelian.closure_of_commute hScomm
        (fun a ha => by rw [pow_two]; exact hSsq a ha)
    have hEsub : P X₄ ≤ Subgroup.closure S := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
      have hhK : h ∈ K := hh.2
      have hqhX : qH D h ∈ X₄ := Subgroup.mem_comap.mp hh.1
      have hq4 : qH D h = 1 ∨ qH D h = tA ∨ qH D h = uA ∨ qH D h = tA * uA := by
        have hh' : qH D h ∈ (X₄ : Set A45) := hqhX
        rw [hX4eq] at hh'
        simpa using hh'
      have hmemτS : (τ : G) ∈ Subgroup.closure S :=
        Subgroup.subset_closure (by simp [S])
      have hmemτ'S : (τ' : G) ∈ Subgroup.closure S :=
        Subgroup.subset_closure (by simp [S])
      have hmemττ'S : ((τ * τ' : ↥(H z)) : G) ∈ Subgroup.closure S := by
        have hprod := Subgroup.mul_mem (Subgroup.closure S) hmemτS hmemτ'S
        simpa using hprod
      rcases hq4 with hq | hq | hq | hq
      · exact Subgroup.subset_closure (Set.mem_union_right _ (mem_centerIn_of_qH_one hhK hq))
      · let w : ↥(H z) := τ⁻¹ * h
        have hwK : w ∈ K := K.mul_mem (K.inv_mem hτK) hhK
        have hwq : qH D w = 1 := by
          change qH D (τ⁻¹ * h) = 1
          rw [map_mul, map_inv, hqτ, hq]
          exact inv_mul_cancel _
        have hwS : (w : G) ∈ Subgroup.closure S :=
          Subgroup.subset_closure (Set.mem_union_right _ (mem_centerIn_of_qH_one hwK hwq))
        have hEq : (h : G) = (τ : G) * (w : G) := by
          change (h : G) = (τ : G) * ((τ⁻¹ * h : ↥(H z)) : G)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        change (h : G) ∈ Subgroup.closure S
        rw [hEq]
        exact Subgroup.mul_mem _ hmemτS hwS
      · let w : ↥(H z) := τ'⁻¹ * h
        have hwK : w ∈ K := K.mul_mem (K.inv_mem hτ'K) hhK
        have hwq : qH D w = 1 := by
          change qH D (τ'⁻¹ * h) = 1
          rw [map_mul, map_inv, hqτ', hq]
          exact inv_mul_cancel _
        have hwS : (w : G) ∈ Subgroup.closure S :=
          Subgroup.subset_closure (Set.mem_union_right _ (mem_centerIn_of_qH_one hwK hwq))
        have hEq : (h : G) = (τ' : G) * (w : G) := by
          change (h : G) = (τ' : G) * ((τ'⁻¹ * h : ↥(H z)) : G)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        change (h : G) ∈ Subgroup.closure S
        rw [hEq]
        exact Subgroup.mul_mem _ hmemτ'S hwS
      · let w : ↥(H z) := (τ * τ')⁻¹ * h
        have hwK : w ∈ K := K.mul_mem (K.inv_mem (K.mul_mem hτK hτ'K)) hhK
        have hwq : qH D w = 1 := by
          change qH D ((τ * τ')⁻¹ * h) = 1
          rw [map_mul, map_inv, map_mul, hqτ, hqτ', hq]
          exact inv_mul_cancel _
        have hwS : (w : G) ∈ Subgroup.closure S :=
          Subgroup.subset_closure (Set.mem_union_right _ (mem_centerIn_of_qH_one hwK hwq))
        have hEq : (h : G) = ((τ * τ' : ↥(H z)) : G) * (w : G) := by
          change (h : G) = ((τ * τ' : ↥(H z)) : G) * (((τ * τ')⁻¹ * h : ↥(H z)) : G)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        change (h : G) ∈ Subgroup.closure S
        rw [hEq]
        exact Subgroup.mul_mem _ hmemττ'S hwS
    have hEcard : Nat.card ↥(P X₄) = 16 := by
      rw [card_P X₄ hX4cent, hX4card]
    have hEcent : P X₄ ≤ Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G) := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
      exact memC_of_K hh.2
    exact Or.inl ⟨P X₄, hEcent, hEcard,
      fun x hx y hy => hEA.comm (hEsub hx) (hEsub hy),
      fun x hx => hEA.mul_self_eq_one (hEsub hx)⟩
  ·
    obtain ⟨z₁, hz₁sup, hz₁z, hz₁ord⟩ := exists_z1 (z := z) h
    have hz₁ : z₁ ∈ centerIn (J z) := by
      rw [hz₁sup]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
    have hyA_not_Q : yA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      intro hmem
      have hbP : bA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := beta_mem_Q
      have hvP : vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
        have h1 : (vA * bA) * bA⁻¹ ∈
            QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
          Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hbP)
        rwa [mul_inv_cancel_right] at h1
      exact v_not_mem_Q hvP
    have hŷ_not_cent : (ŷ : G) ∉ Subgroup.centralizer ({z₁} : Set G) := by
      intro hcent
      apply hyA_not_Q
      rw [← hqŷ]
      exact (mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hz₁ hz₁z hz₁ord ŷ).mp hcent
    have hŷconj_z1 : (ŷ : G) * z₁ * (ŷ : G)⁻¹ = z * z₁ :=
      conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hz₁ord ŷ.2 hŷ_not_cent
    let T : Subgroup G := P X₈
    have hTle : T ≤ H z ⊓ Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G) := by
      intro g hg
      change g ∈ (X₈.comap (qH D) ⊓ K).map (H z).subtype at hg
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
      exact Subgroup.mem_inf.mpr ⟨h.2, memC_of_K hh.2⟩
    have hTcard : Nat.card ↥T = 32 := by
      change Nat.card ↥(P X₈) = 32
      rw [card_P X₈ hX8cent, hX8card]
    have hTcard5 : Nat.card ↥T = 2 ^ 5 := by
      rw [hTcard]
      norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T₃, hT₃syl⟩ := exists_isSylowOf 2
      (H z ⊓ Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G))
    have hT₃card : Nat.card T₃ = 2 ^ 5 :=
      card_isSylowOf_centralizer_sigma1Nine_mul (z := z) D h hIII hσ₂ hq₂ hc₂
        (e27LineCountData_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂) hT₃syl
    have hTsyl : IsSylowOf 2 T
        (H z ⊓ Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G)) := by
      refine isSylowOf_of_card hTle ?_
      rw [hTcard5, ← hT₃syl.card_eq, hT₃card]
    have memT_of_mem_K : ∀ {w : ↥(H z)}, w ∈ K → qH D w ∈ X₈ → (w : G) ∈ T := by
      intro w hwK hqw
      change (w : G) ∈ (X₈.comap (qH D) ⊓ K).map (H z).subtype
      exact Subgroup.mem_map.mpr
        ⟨w, Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr hqw, hwK⟩, rfl⟩
    have hτT : (τ : G) ∈ T :=
      memT_of_mem_K hτK (by rw [hqτ]; exact Subgroup.subset_closure (by simp))
    have hτ'T : (τ' : G) ∈ T :=
      memT_of_mem_K hτ'K (by rw [hqτ']; exact Subgroup.subset_closure (by simp))
    have hŷT : (ŷ : G) ∈ T :=
      memT_of_mem_K hŷK (by rw [hqŷ]; exact Subgroup.subset_closure (by simp [yA]))
    have hzT : z ∈ centerIn T := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · let zH : ↥(H z) := ⟨z, z_mem_H (z := z)⟩
        have hzK : zH ∈ K := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext
            (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (σ₃ : G) σ₃.2).symm
        have hzq : qH D zH = 1 :=
          (J_mem_iff D zH).mp (Subgroup.mem_subgroupOf.mpr (z_mem_J h))
        have hzT' := memT_of_mem_K hzK (by rw [hzq]; exact Subgroup.one_mem X₈)
        simpa [zH] using hzT'
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) x (hTle hx).1
    have hcenter_le : centerIn T ≤ Subgroup.zpowers z := by
      intro x hx
      have hxT : x ∈ T := hx.1
      have hxcent : x ∈ Subgroup.centralizer (T : Set G) := hx.2
      change x ∈ (X₈.comap (qH D) ⊓ K).map (H z).subtype at hxT
      obtain ⟨hLift, hh, hxval⟩ := Subgroup.mem_map.mp hxT
      let xH : ↥(H z) := ⟨x, (hTle hx.1).1⟩
      have hxH_eq_h : xH = hLift := Subtype.ext hxval.symm
      have hqX8 : qH D xH ∈ X₈ := by
        rw [hxH_eq_h]
        exact Subgroup.mem_comap.mp hh.1
      have hxHK : xH ∈ K := by
        rw [hxH_eq_h]
        exact hh.2
      have comm_qH_of_comm : ∀ {w : ↥(H z)}, (w : G) ∈ T →
          qH D xH * qH D w = qH D w * qH D xH := by
        intro w hwT
        have hcomm : (w : G) * x = x * (w : G) :=
          Subgroup.mem_centralizer_iff.mp hxcent (w : G) hwT
        have hcommH : w * xH = xH * w := Subtype.ext hcomm
        simpa using (congrArg (qH D) hcommH).symm
      have hcommgen : ∀ y ∈ ({tA, uA, vA * bA} : Set A45),
          y * qH D xH = qH D xH * y := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · simpa [hqτ] using (comm_qH_of_comm hτT).symm
        · simpa [hqτ'] using (comm_qH_of_comm hτ'T).symm
        · simpa [hqŷ, yA] using (comm_qH_of_comm hŷT).symm
      have hmem_center : (⟨qH D xH, hqX8⟩ : X₈) ∈ Subgroup.center ↥X₈ := by
        change (⟨qH D xH, hqX8⟩ :
            Subgroup.closure ({tA, uA, vA * bA} : Set A45)) ∈
          Subgroup.center (Subgroup.closure ({tA, uA, vA * bA} : Set A45))
        exact CFSG.GroupTheory.mem_center_closure_of_forall hqX8 hcommgen
      have hmem_map : qH D xH ∈ (Subgroup.center ↥X₈).map X₈.subtype :=
        Subgroup.mem_map.mpr ⟨⟨qH D xH, hqX8⟩, hmem_center, rfl⟩
      rw [hX8center] at hmem_map
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hordut).mp hmem_map with hq1 | hqu
      · have hxJ : x ∈ J z := by
          have hxJ' : xH ∈ (J z).subgroupOf (H z) := (J_mem_iff D xH).mpr hq1
          have := Subgroup.mem_subgroupOf.mp hxJ'
          simpa [xH] using this
        have hxCenterJ : x ∈ centerIn (J z) := by
          rw [← hI1]
          exact Subgroup.mem_inf.mpr ⟨hxJ, (hTle hx.1).2⟩
        have hxŷ : (ŷ : G) * x = x * (ŷ : G) :=
          Subgroup.mem_centralizer_iff.mp hxcent (ŷ : G) hŷT
        have hconjx : (ŷ : G) * x * (ŷ : G)⁻¹ = x := by
          rw [hxŷ, mul_inv_cancel_right]
        rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁ord).mp hxCenterJ with h1 | h2 | h3 | h4
        · rw [h1]
          exact Subgroup.one_mem _
        · rw [h2]
          exact Subgroup.mem_zpowers z
        · exfalso
          have hEq : z₁ = z * z₁ := by
            rw [h3] at hconjx
            exact hconjx.symm.trans hŷconj_z1
          have h1z : (1 : G) * z₁ = z * z₁ := by simpa using hEq
          exact hz_ne_one (mul_right_cancel h1z).symm
        · exfalso
          have hzŷ : (ŷ : G) * z = z * (ŷ : G) :=
            Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (ŷ : G) ŷ.2
          have hzconj : (ŷ : G) * z * (ŷ : G)⁻¹ = z := by
            rw [hzŷ, mul_inv_cancel_right]
          have hzz1 : (ŷ : G) * (z * z₁) * (ŷ : G)⁻¹ = z₁ := by
            have hgroup : (ŷ : G) * (z * z₁) * (ŷ : G)⁻¹ =
                ((ŷ : G) * z * (ŷ : G)⁻¹) * ((ŷ : G) * z₁ * (ŷ : G)⁻¹) := by
              group
            rw [hgroup, hzconj, hŷconj_z1]
            calc z * (z * z₁) = (z * z) * z₁ := by group
              _ = z₁ := by rw [hz_sq, one_mul]
          have hEq : z * z₁ = z₁ := by
            rw [h4] at hconjx
            exact hconjx.symm.trans hzz1
          have h1z : (1 : G) * z₁ = z * z₁ := by simpa using hEq.symm
          exact hz_ne_one (mul_right_cancel h1z).symm
      · exfalso
        let w : ↥(H z) := (τ' * τ)⁻¹ * xH
        have hwK : w ∈ K := K.mul_mem (K.inv_mem (K.mul_mem hτ'K hτK)) hxHK
        have hwq : qH D w = 1 := by
          change qH D ((τ' * τ)⁻¹ * xH) = 1
          rw [map_mul, map_inv, map_mul, hqτ', hqτ, hqu]
          exact inv_mul_cancel _
        have hwCenter : (w : G) ∈ centerIn (J z) := mem_centerIn_of_qH_one hwK hwq
        have hτw : (τ : G) * (w : G) = (w : G) * (τ : G) :=
          (Subgroup.mem_centralizer_singleton_iff.mp
            (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := τ) hτconjZ
              hwCenter)).symm
        have hmulH : ((τ' * τ) * w) = xH := by
          change ((τ' * τ) * ((τ' * τ)⁻¹ * xH)) = xH
          group
        have hxeq : x = ((τ' : G) * (τ : G)) * (w : G) := by
          have hval := congrArg (fun u : ↥(H z) => (u : G)) hmulH.symm
          simpa [xH, Subgroup.coe_mul] using hval
        have hxw : x * (w : G)⁻¹ = (τ' : G) * (τ : G) := by
          rw [hxeq]
          group
        have hcommxτ : (τ : G) * x = x * (τ : G) :=
          Subgroup.mem_centralizer_iff.mp hxcent (τ : G) hτT
        have hτx : Commute (τ : G) x := hcommxτ
        have hτwC : Commute (τ : G) (w : G) := hτw
        have hτxw : Commute (τ : G) (x * (w : G)⁻¹) :=
          hτx.mul_right (Commute.inv_right_iff.mpr hτwC)
        have hcomm : (τ : G) * ((τ' : G) * (τ : G)) =
            ((τ' : G) * (τ : G)) * (τ : G) := by
          rw [← hxw]
          exact hτxw.eq
        have h4' : (τ : G) * (τ' : G) = (τ' : G) * (τ : G) := by
          have hc' : (τ : G) * (τ' : G) * (τ : G) = (τ' : G) := by
            simpa [mul_assoc, hτ2] using hcomm
          have h5 := congrArg (fun z => z * (τ : G)) hc'
          simpa [mul_assoc, hτ2] using h5
        exact hc h4'.symm
    have hZcenter : centerIn T = Subgroup.zpowers z :=
      le_antisymm hcenter_le (Subgroup.zpowers_le.mpr hzT)
    have hTsyl' : IsSylowOf 2 T (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({((σ₃ : ↥(H z)) : G)} : Set G)) := by
      simpa [H] using hTsyl
    exact Or.inr ⟨T,
      isSylowOf_centralizer_of_centerIn_eq_zpowers h.1 hTsyl' hZcenter, hTcard5⟩

end CFSG.RankThree.GF2n.Parrott
