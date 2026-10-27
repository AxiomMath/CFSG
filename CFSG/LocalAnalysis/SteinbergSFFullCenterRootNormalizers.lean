module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterRootNormalizersAffine
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenter

open Subgroup GomiFusion RootAxisTwoCore
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf [Finite G] (H K : Subgroup G) (hK : K ≤ normalizer (H : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) * Nat.card (H ⊓ K : Subgroup G) = Nat.card H * Nat.card K := by
  have := normal_subgroupOf_of_le_normalizer hK
  have := normal_subgroupOf_sup_of_le_normalizer hK
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient K H hK
  have h1 := card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K)
  have h2 := card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (K ⊔ H))
  have h3 : Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
    rw [← inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have h4 : Nat.card (H.subgroupOf (K ⊔ H)) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  have h5 : Nat.card (↥K ⧸ H.subgroupOf K) = Nat.card (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) :=
    Nat.card_congr e.toEquiv
  rw [sup_comm, h2, h4, ← h5, h1, h3]
  ring

theorem isElementaryAbelian_of {R : Subgroup G} (hc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (h2 : ∀ x ∈ R, x * x = 1) : IsElementaryAbelian 2 R :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hc h2

end General

namespace FCHyp

section Pairs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
local notation "𝐘" => normalizer ((pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G) : Set G) ⊓
  normalizer (((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Subgroup G) : Set G) ⊓
  normalizer (((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

omit [Finite G] [Finite K] in
theorem Q_comm_ZP (h : FCHyp L K n φ t) {q : G} (hq : q ∈ 𝐐) {z : G} (hz : z ∈ 𝐙) :
    q * z = z * q := by
  obtain ⟨p, hp, c, hc, rfl⟩ := h.setup.mem_Q.mp hq
  have h1 : p * z = z * p := Setup.comm_P_ZP hp hz
  have h2 : c * z = z * c := h.twoCore.zpowers_comm hc (pull_le φ _ hz)
  calc p * c * z = p * (c * z) := mul_assoc _ _ _
    _ = p * (z * c) := by rw [h2]
    _ = (p * z) * c := (mul_assoc _ _ _).symm
    _ = z * (p * c) := by rw [h1, mul_assoc]

omit [Finite K] in
theorem Q_le_M (h : FCHyp L K n φ t) (i : Axis) : 𝐐 ≤ 𝐌[i] := by
  intro q hq
  have hqC : q ∈ 𝐂 := h.setup.Q_le_C hq
  refine (h.twoCore.mem_normalizer_zpowers_sup_iff hqC (pull_le φ _)).mpr ?_
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun u hu => ?_
  rw [h.Q_comm_ZP hq (pull_mono φ (rootU_le_center i) hu), mul_inv_cancel_right]
  exact hu

theorem card_Q (h : FCHyp L K n φ t) : Nat.card 𝐐 = 2 * Nat.card K ^ 4 := by
  rw [sup_comm, card_sup_of_commute (H := zpowers t) (K := pull φ (antiUnipotent K))
    (fun y hy p hp => h.twoCore.zpowers_comm hy (pull_le φ _ hp))
    (h.twoCore.zpowers_inf (pull_le φ _)), Nat.card_zpowers, h.setup.order_t, card_pull,
    (card_radicals (K := K)).1]

theorem D_le_normalizer_Q (h : FCHyp L K n φ t) (i : Axis) :
    𝐃[i] ≤ normalizer (𝐐 : Set G) := by
  have key : ∀ d ∈ 𝐃[i], ∀ q ∈ 𝐐, d * q * d⁻¹ ∈ 𝐐 := by
    intro d hd q hq
    have hqM := h.Q_le_M i hq
    have hqC : q * t = t * q := mem_centralizer_singleton_iff.mp (h.setup.Q_le_C hq)
    have hy : q⁻¹ * d * q ∈ 𝐃[i] := by
      have := conj_mem_pCore_map (inv_mem hqM) hd
      rwa [inv_inv] at this
    have hu : t * ((d⁻¹)⁻¹ * t * d⁻¹) ∈ 𝐔[i] :=
      h.twoCore.conj_t_mem φ i (inv_mem (map_subtype_le _ hd))
    have hu' : t * (d⁻¹ * t * d) ∈ 𝐔[i] := h.twoCore.conj_t_mem φ i (map_subtype_le _ hd)
    have hqu := h.Q_comm_ZP hq (pull_mono φ (rootU_le_center i) hu')
    have hdt : d⁻¹ * t * d = t * (t * (d⁻¹ * t * d)) := by
      rw [← mul_assoc, h.setup.t_mul_t, one_mul]
    have hyt : (q⁻¹ * d * q)⁻¹ * t * (q⁻¹ * d * q) = d⁻¹ * t * d := by
      have hqt : q⁻¹ * t * q = t := by rw [mul_assoc, ← hqC, inv_mul_cancel_left]
      calc (q⁻¹ * d * q)⁻¹ * t * (q⁻¹ * d * q) = q⁻¹ * (d⁻¹ * (q * t * q⁻¹) * d) * q := by group
        _ = q⁻¹ * (d⁻¹ * t * d) * q := by rw [hqC, mul_inv_cancel_right]
        _ = q⁻¹ * (t * (t * (d⁻¹ * t * d))) * q := by rw [← hdt]
        _ = (q⁻¹ * t * q) * (q⁻¹ * (t * (d⁻¹ * t * d)) * q) := by group
        _ = t * (t * (d⁻¹ * t * d)) := by
            rw [hqt, show q⁻¹ * (t * (d⁻¹ * t * d)) * q = t * (d⁻¹ * t * d) by
              rw [mul_assoc, ← hqu, inv_mul_cancel_left]]
        _ = d⁻¹ * t * d := hdt.symm
    have hC : q⁻¹ * d * q * d⁻¹ ∈ 𝐂 := by
      have h3 : (q⁻¹ * d * q * d⁻¹)⁻¹ * t * (q⁻¹ * d * q * d⁻¹) = t := by
        calc (q⁻¹ * d * q * d⁻¹)⁻¹ * t * (q⁻¹ * d * q * d⁻¹)
            = d * ((q⁻¹ * d * q)⁻¹ * t * (q⁻¹ * d * q)) * d⁻¹ := by group
          _ = d * (d⁻¹ * t * d) * d⁻¹ := by rw [hyt]
          _ = t := by group
      rw [mem_centralizer_singleton_iff]
      calc q⁻¹ * d * q * d⁻¹ * t
          = q⁻¹ * d * q * d⁻¹ * ((q⁻¹ * d * q * d⁻¹)⁻¹ * t * (q⁻¹ * d * q * d⁻¹)) := by
            rw [h3]
        _ = t * (q⁻¹ * d * q * d⁻¹) := by group
    have hB : q⁻¹ * d * q * d⁻¹ ∈ 𝐁[i] := by
      rw [← h.D_inf_C i]
      exact mem_inf.mpr ⟨mul_mem hy (inv_mem hd), hC⟩
    have e : d * q * d⁻¹ = q * (q⁻¹ * d * q * d⁻¹) := by group
    rw [e]
    exact mul_mem hq (B_le_Q i hB)
  intro d hd
  exact RootAxisTwoCore.mem_normalizer_of_conj_le (key d hd)

theorem Q_inf_D (h : FCHyp L K n φ t) (i : Axis) : 𝐐 ⊓ 𝐃[i] = 𝐁[i] := by
  apply le_antisymm
  · intro x hx
    rw [← h.D_inf_C i]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, h.setup.Q_le_C (mem_inf.mp hx).1⟩
  · exact le_inf (B_le_Q i) (h.B_le_D i)

theorem Qi_facts (h : FCHyp L K n φ t) (i : Axis) :
    (𝐐 : Set G) * (𝐃[i] : Set G) = ((𝐐 ⊔ 𝐃[i] : Subgroup G) : Set G) ∧
      IsPGroup 2 (𝐐 ⊔ 𝐃[i] : Subgroup G) ∧
      Nat.card (𝐐 ⊔ 𝐃[i] : Subgroup G) = 2 * Nat.card K ^ 5 ∧
      (𝐐 ⊔ 𝐃[i] : Subgroup G) ≤ normalizer (𝐐 : Set G) := by
  have hDQ := h.D_le_normalizer_Q i
  refine ⟨(coe_mul_of_right_le_normalizer_left _ _ hDQ).symm,
    IsPGroup.to_sup_of_normal_left' h.setup.Q_two (CFSG.pCore_isPGroup.map _) hDQ, ?_,
    sup_le le_normalizer hDQ⟩
  have h1 := card_sup_mul_card_inf 𝐐 𝐃[i] hDQ
  rw [h.Q_inf_D i, h.card_B, h.card_Q, h.card_D] at h1
  have hq : 0 < 2 * Nat.card K ^ 3 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card (𝐐 ⊔ 𝐃[i] : Subgroup G) * (2 * Nat.card K ^ 3) =
      2 * Nat.card K ^ 5 * (2 * Nat.card K ^ 3) := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

omit [Finite K] in
theorem Qi_le_M (h : FCHyp L K n φ t) (i : Axis) : (𝐐 ⊔ 𝐃[i] : Subgroup G) ≤ 𝐌[i] :=
  sup_le (h.Q_le_M i) (map_subtype_le _)

theorem Qi_le_Y (h : FCHyp L K n φ t) (i : Axis) : (𝐐 ⊔ 𝐃[i] : Subgroup G) ≤ 𝐘 := by
  intro x hx
  have hxQ := (h.Qi_facts i).2.2.2 hx
  obtain ⟨h1, h2⟩ := h.mem_normalizer_B_of hxQ i (h.twoCore.M_le_normalizer_B φ i (h.Qi_le_M i hx))
  exact ⟨⟨hxQ, h1⟩, h2⟩

theorem Qi_inf_C (h : FCHyp L K n φ t) (i : Axis) : (𝐐 ⊔ 𝐃[i] : Subgroup G) ⊓ 𝐂 = 𝐐 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQi, hxC⟩ := mem_inf.mp hx
    have hx' : x ∈ (𝐐 : Set G) * (𝐃[i] : Set G) := by
      rw [(h.Qi_facts i).1]
      exact hxQi
    obtain ⟨q, hq, d, hd, rfl⟩ := hx'
    have hdC : d ∈ 𝐂 := by
      have := mul_mem (inv_mem (h.setup.Q_le_C hq)) hxC
      rwa [inv_mul_cancel_left] at this
    have hdB : d ∈ 𝐁[i] := by
      rw [← h.D_inf_C i]
      exact mem_inf.mpr ⟨hd, hdC⟩
    exact mul_mem hq (B_le_Q i hdB)
  · exact le_inf le_sup_left h.setup.Q_le_C

theorem Qi_le_normalizer_Qj (h : FCHyp L K n φ t) (i j : Axis) :
    (𝐐 ⊔ 𝐃[i] : Subgroup G) ≤ normalizer (((𝐐 ⊔ 𝐃[j] : Subgroup G) : Subgroup G) : Set G) := by
  intro x hx
  have hY := h.Qi_le_Y i hx
  have hxN : x ∈ 𝐍[j] := by
    cases j
    · exact hY.1.2
    · exact hY.2
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun y hy => conj_mem_sup (fun q hq => ?_)
    (fun d hd => h.conj_mem_D j hxN hd) hy
  exact (mem_normalizer_iff.mp hY.1.1 q).mp hq

theorem Q1_inf_Q2 (h : FCHyp L K n φ t) :
    (𝐐 ⊔ 𝐃[Axis.one] : Subgroup G) ⊓ (𝐐 ⊔ 𝐃[Axis.two] : Subgroup G) = 𝐐 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    have hm1 : x⁻¹ * t * x ∈ {x : G | ∃ m ∈ 𝐌[Axis.one], x = m⁻¹ * t * m} :=
      ⟨x, h.Qi_le_M _ hx1, rfl⟩
    have hm2 : x⁻¹ * t * x ∈ {x : G | ∃ m ∈ 𝐌[Axis.two], x = m⁻¹ * t * m} :=
      ⟨x, h.Qi_le_M _ hx2, rfl⟩
    rw [h.orbit_M] at hm1 hm2
    obtain ⟨u₁, hu₁, h1⟩ := hm1
    obtain ⟨u₂, hu₂, h2⟩ := hm2
    have hu : u₁ = u₂ := mul_left_cancel (h1.symm.trans h2)
    have hinf : 𝐔[Axis.one] ⊓ 𝐔[Axis.two] = ⊥ := by rw [← pull_inf, rootU_inf, pull_bot]
    have hu1 : u₁ = 1 := by
      have : u₁ ∈ 𝐔[Axis.one] ⊓ 𝐔[Axis.two] := mem_inf.mpr ⟨hu₁, hu ▸ hu₂⟩
      rwa [hinf, mem_bot] at this
    rw [hu1, mul_one] at h1
    have hxC : x ∈ 𝐂 := by
      rw [mem_centralizer_singleton_iff]
      calc x * t = x * (x⁻¹ * t * x) := by rw [h1]
        _ = t * x := by group
    rw [← h.Qi_inf_C Axis.one]
    exact mem_inf.mpr ⟨hx1, hxC⟩
  · exact le_inf le_sup_left le_sup_left

omit [Finite K] in
theorem torus_le_normalizer_Qi (h : FCHyp L K n φ t) (i : Axis) :
    𝐉 ≤ normalizer (((𝐐 ⊔ 𝐃[i] : Subgroup G) : Subgroup G) : Set G) := by
  intro δ hδ
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun y hy => conj_mem_sup (fun q hq => ?_)
    (fun d hd => conj_mem_pCore_map (h.torus_le_M i hδ) hd) hy
  exact (mem_normalizer_iff.mp (h.setup.diagTorus_le_normalizer hδ) q).mp hq

omit [Finite G] in
theorem torus_trans (i : Axis) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ δ ∈ 𝐉, δ * coordG φ i x * δ⁻¹ = coordG φ i y := by
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ ∈ diagTorus K, δ⁻¹ * rootCoord K i x * δ = rootCoord K i y := by
    cases i
    · exact exists_diagTorus_conj_axisOne hx hy
    · exact exists_diagTorus_conj (b := 0) (b' := 0) hx hy (Or.inl ⟨rfl, rfl⟩)
  refine ⟨((φ.symm δ : L) : G)⁻¹, inv_mem (symm_mem_pull.mpr hδ), ?_⟩
  rw [inv_inv]
  exact Setup.symm_conj hδc

theorem H_centralizes_U (h : FCHyp L K n φ t) (i : Axis) {x : G}
    (hx : x ∈ (𝐐 ⊔ 𝐃[Axis.one] : Subgroup G) ⊔ (𝐐 ⊔ 𝐃[Axis.two] : Subgroup G)) {u : G}
    (hu : u ∈ 𝐔[i]) : x * u * x⁻¹ = u := by
  set H := (𝐐 ⊔ 𝐃[Axis.one] : Subgroup G) ⊔ (𝐐 ⊔ 𝐃[Axis.two] : Subgroup G) with hH
  have hH2 : IsPGroup 2 H := IsPGroup.to_sup_of_normal_right' (h.Qi_facts _).2.1
    (h.Qi_facts _).2.1 (h.Qi_le_normalizer_Qj _ _)
  have hHY : H ≤ 𝐘 := sup_le (h.Qi_le_Y _) (h.Qi_le_Y _)
  have hHU : H ≤ normalizer (𝐔[i] : Set G) := fun y hy => by
    cases i
    · exact (h.Y_le_normalizer_U (hHY hy)).1
    · exact (h.Y_le_normalizer_U (hHY hy)).2
  have hJH : 𝐉 ≤ normalizer (H : Set G) := fun δ hδ =>
    RootAxisTwoCore.mem_normalizer_of_conj_le fun y hy => conj_mem_sup
      (fun y hy => (mem_normalizer_iff.mp (h.torus_le_normalizer_Qi _ hδ) y).mp hy)
      (fun y hy => (mem_normalizer_iff.mp (h.torus_le_normalizer_Qi _ hδ) y).mp hy) hy
  set H₀ := H ⊔ 𝐉 with hH₀
  have hH₀U : H₀ ≤ normalizer (𝐔[i] : Set G) := sup_le hHU (torus_le_normalizer_U i)
  have hH₀H : H₀ ≤ normalizer (H : Set G) := sup_le le_normalizer hJH
  set ψ : G → K := Function.invFun (coordG φ i) with hψ
  have hψc : ∀ v ∈ 𝐔[i], coordG φ i (ψ v) = v := fun v hv =>
    Function.invFun_eq (exists_coordG_eq φ i hv)
  have hψx : ∀ y : K, ψ (coordG φ i y) = y := fun y =>
    Function.leftInverse_invFun (coordG_injective φ i) y
  have hA : ActHyp ψ 1 𝐔[i] ⊥ H₀ :=
    { U_le := bot_le
      add := fun a ha b hb => coordG_injective φ i (by
        rw [coordG_add, hψc a ha, hψc b hb, hψc _ (mul_mem ha hb)])
      ker := fun a ha => by
        rw [mem_bot]
        constructor
        · intro h0
          rw [← hψc a ha, h0, coordG_zero]
        · rintro rfl
          rw [← coordG_zero φ i, hψx]
      surj := fun v => ⟨coordG φ i v, coordG_mem φ i v, hψx v⟩
      conj_A := fun g hg a ha => (mem_normalizer_iff.mp (hH₀U hg) a).mp ha
      conj_U := fun g _ u hu => by
        rw [mem_bot] at hu ⊢
        rw [hu]
        group
      conj_t := fun _ _ => by
        rw [inv_one, one_mul, mul_one, mul_inv_cancel]
        exact one_mem _ }
  have h2K : 2 ∣ Nat.card K := by
    rw [h.setup.card_K]
    exact dvd_pow_self 2 (by have := h.setup.two_le; omega)
  have htrans : ∀ v w : K, v ≠ 0 → w ≠ 0 → ∃ g ∈ H₀, hA.linFun g v = w := by
    intro v w hv hw
    obtain ⟨δ, hδ, hδc⟩ := torus_trans (φ := φ) i hv hw
    refine ⟨δ, mem_sup_right hδ, ?_⟩
    rw [← hψx v, hA.linFun_psi (mem_sup_right hδ) (coordG_mem φ i v), hδc, hψx]
  have hfix := hA.linFun_eq_of_normal le_rfl (le_sup_left : H ≤ H₀)
    (fun g hg r hr => (mem_normalizer_iff.mp (hH₀H hg) r).mp hr) hH2 h2K htrans hx (ψ u)
  rw [hA.linFun_psi (mem_sup_left hx) hu] at hfix
  rw [← hψc _ ((mem_normalizer_iff.mp (hHU hx) u).mp hu), hfix, hψc u hu]

end Pairs

section Overgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔
  (CFSG.pCore 2 (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) :
    Set G))).map (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) :
    Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => ((pull φ (antiUnipotent K) ⊔ zpowers t ⊔
  (CFSG.pCore 2 (normalizer (((zpowers t ⊔ pull φ (rootU K Axis.one) : Subgroup G) :
    Subgroup G) : Set G))).map (normalizer (((zpowers t ⊔ pull φ (rootU K Axis.one) :
    Subgroup G) : Subgroup G) : Set G)).subtype : Subgroup G) ⊔
  (pull φ (antiUnipotent K) ⊔ zpowers t ⊔
  (CFSG.pCore 2 (normalizer (((zpowers t ⊔ pull φ (rootU K Axis.two) : Subgroup G) :
    Subgroup G) : Set G))).map (normalizer (((zpowers t ⊔ pull φ (rootU K Axis.two) :
    Subgroup G) : Subgroup G) : Set G)).subtype : Subgroup G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem H_facts (h : FCHyp L K n φ t) :
    (𝐐[Axis.one] : Set G) * (𝐐[Axis.two] : Set G) = (𝐇 : Set G) ∧ IsPGroup 2 𝐇 ∧
      Nat.card 𝐇 = 2 * Nat.card K ^ 6 := by
  refine ⟨(coe_mul_of_left_le_normalizer_right _ _ (h.Qi_le_normalizer_Qj _ _)).symm,
    IsPGroup.to_sup_of_normal_right' (h.Qi_facts _).2.1 (h.Qi_facts _).2.1
      (h.Qi_le_normalizer_Qj _ _), ?_⟩
  have h1 := card_sup_mul_card_inf 𝐐[Axis.one] 𝐐[Axis.two] (h.Qi_le_normalizer_Qj _ _)
  rw [h.Q1_inf_Q2, (h.Qi_facts _).2.2.1, (h.Qi_facts _).2.2.1, h.card_Q] at h1
  have hq : 0 < 2 * Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card 𝐇 * (2 * Nat.card K ^ 4) = 2 * Nat.card K ^ 6 * (2 * Nat.card K ^ 4) := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

theorem H_le_normalizer_Q (h : FCHyp L K n φ t) : 𝐇 ≤ normalizer (𝐐 : Set G) :=
  sup_le (h.Qi_facts _).2.2.2 (h.Qi_facts _).2.2.2

theorem H_le_normalizer_Qi (h : FCHyp L K n φ t) (i : Axis) :
    𝐇 ≤ normalizer ((𝐐[i] : Subgroup G) : Set G) :=
  sup_le (h.Qi_le_normalizer_Qj _ _) (h.Qi_le_normalizer_Qj _ _)

omit [Finite G] [Finite K] in
theorem ZP_eq :
    𝐙 = 𝐔[Axis.one] ⊔ 𝐔[Axis.two] ∧ ∀ x ∈ 𝐔[Axis.one], ∀ y ∈ 𝐔[Axis.two], x * y = y * x := by
  refine ⟨by rw [center_eq_rootU_sup, pull_sup], fun x hx y hy => ?_⟩
  exact Setup.comm_P_ZP (Setup.ZP_le_PG (pull_mono φ (rootU_le_center _) hx))
    (pull_mono φ (rootU_le_center _) hy)

omit [Finite G] [Finite K] in
theorem comm_ZP_of {g : G}
    (h1 : ∀ u ∈ 𝐔[Axis.one], g * u * g⁻¹ = u) (h2 : ∀ u ∈ 𝐔[Axis.two], g * u * g⁻¹ = u)
    {z : G} (hz : z ∈ 𝐙) : g * z = z * g := by
  have hc : ∀ x ∈ 𝐔[Axis.one], ∀ y ∈ 𝐔[Axis.two], x * y = y * x := fun x hx y hy =>
    Setup.comm_P_ZP (Setup.ZP_le_PG (pull_mono φ (rootU_le_center _) hx))
      (pull_mono φ (rootU_le_center _) hy)
  rw [center_eq_rootU_sup, pull_sup] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_commute hc).mp hz
  calc g * (x * y) = (g * x * g⁻¹) * (g * y * g⁻¹) * g := by group
    _ = x * y * g := by rw [h1 x hx, h2 y hy]

theorem orbit_H (h : FCHyp L K n φ t) :
    {x : G | ∃ g ∈ 𝐇, x = g⁻¹ * t * g} = {x | ∃ z ∈ 𝐙, x = t * z} := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [← h.full]
    exact ⟨g, h.H_le_normalizer_Q hg, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hZ, hc⟩ := ZP_eq (φ := φ)
    rw [hZ] at hz
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := (mem_sup_of_commute hc).mp hz
    obtain ⟨-, -, -, h41⟩ := h.twoCore.cond φ Axis.one (h.M_not_le_C Axis.one)
    obtain ⟨-, -, -, h42⟩ := h.twoCore.cond φ Axis.two (h.M_not_le_C Axis.two)
    obtain ⟨d₁, hd₁, hd₁t⟩ := h41 u₁ hu₁
    obtain ⟨d₂, hd₂, hd₂t⟩ := h42 u₂ hu₂
    have hd₁H : d₁ ∈ 𝐇 := mem_sup_left (mem_sup_right hd₁ : d₁ ∈ 𝐐[Axis.one])
    have hd₂H : d₂ ∈ 𝐇 := mem_sup_right (mem_sup_right hd₂ : d₂ ∈ 𝐐[Axis.two])
    have hcom := h.H_centralizes_U Axis.one (inv_mem hd₂H) hu₁
    rw [inv_inv] at hcom
    refine ⟨d₁ * d₂, mul_mem hd₁H hd₂H, ?_⟩
    have e1 : d₁⁻¹ * t * d₁ = t * u₁ := by rw [← hd₁t]; group
    have e2 : d₂⁻¹ * t * d₂ = t * u₂ := by rw [← hd₂t]; group
    calc t * (u₁ * u₂) = t * (u₂ * u₁) := by rw [hc u₁ hu₁ u₂ hu₂]
      _ = (d₂⁻¹ * t * d₂) * (d₂⁻¹ * u₁ * d₂) := by rw [e2, hcom]; group
      _ = d₂⁻¹ * (d₁⁻¹ * t * d₁) * d₂ := by rw [e1]; group
      _ = (d₁ * d₂)⁻¹ * t * (d₁ * d₂) := by group

theorem H_inf_C (h : FCHyp L K n φ t) : 𝐇 ⊓ 𝐂 = 𝐐 := by
  have hQH : 𝐐 ≤ 𝐇 := le_sup_left.trans le_sup_left
  have h1 := relIndex_mul_card 𝐂 𝐇
  rw [relIndex_centralizer_eq_card, h.orbit_H, card_mul_set, card_ZP, (h.H_facts).2.2] at h1
  have hq : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card K ^ 2 * Nat.card (𝐂 ⊓ 𝐇 : Subgroup G) =
      Nat.card K ^ 2 * Nat.card 𝐐 := by rw [h1, h.card_Q]; ring
  have h3 := Nat.eq_of_mul_eq_mul_left hq h2
  rw [inf_comm]
  exact (eq_of_le_of_card_ge (le_inf h.setup.Q_le_C hQH) (le_of_eq h3)).symm

theorem center_H (h : FCHyp L K n φ t) : (center 𝐇).map 𝐇.subtype = 𝐙 := by
  have hQH : 𝐐 ≤ 𝐇 := le_sup_left.trans le_sup_left
  have hZc : ∀ z ∈ 𝐙, ∀ y ∈ 𝐇, y * z = z * y := fun z hz y hy =>
    comm_ZP_of (fun u hu => h.H_centralizes_U Axis.one hy hu)
      (fun u hu => h.H_centralizes_U Axis.two hy hu) hz
  have hZH : 𝐙 ≤ 𝐇 := fun z hz => hQH (mem_sup_left (Setup.ZP_le_PG hz))
  apply le_antisymm
  · intro x hx
    rw [mem_center_map_iff] at hx
    obtain ⟨hxH, hxc⟩ := hx
    have htH : t ∈ 𝐇 := hQH (mem_sup_right (mem_zpowers t))
    have hxC : x ∈ 𝐂 := mem_centralizer_singleton_iff.mpr (hxc t htH).symm
    have hxQ : x ∈ 𝐐 := by
      rw [← h.H_inf_C]
      exact mem_inf.mpr ⟨hxH, hxC⟩
    have hxZQ : x ∈ (center 𝐐).map 𝐐.subtype :=
      mem_center_map_iff.mpr ⟨hxQ, fun y hy => hxc y (hQH hy)⟩
    obtain ⟨z, hz, c, hc, rfl⟩ := h.setup.exists_of_mem_ZQ hxZQ
    have hc' : c = 1 ∨ c = t := by
      obtain ⟨j, rfl⟩ := hc
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hc' with hc1 | hc1 <;> rw [hc1] at hxc ⊢
    · rw [mul_one]
      exact hz
    · exfalso
      have htc : ∀ y ∈ 𝐇, y * t = t * y := by
        intro y hy
        have h1 := hxc y hy
        have h2 := hZc z hz y hy
        calc y * t = z⁻¹ * (y * (z * t)) * y⁻¹ * y := by rw [← mul_assoc y z t, h2]; group
          _ = z⁻¹ * (z * t * y) * y⁻¹ * y := by rw [h1]
          _ = t * y := by group
      have hu := coordG_mem φ Axis.one 1
      have hmem : t * coordG φ Axis.one 1 ∈ {x : G | ∃ g ∈ 𝐇, x = g⁻¹ * t * g} := by
        rw [h.orbit_H]
        exact ⟨_, pull_mono φ (rootU_le_center _) hu, rfl⟩
      obtain ⟨g, hg, hgt⟩ := hmem
      rw [mul_assoc, ← htc g hg, inv_mul_cancel_left] at hgt
      have h3 : coordG φ Axis.one 1 = coordG φ Axis.one 0 := by
        rw [coordG_zero]
        exact mul_left_cancel (hgt.trans (mul_one t).symm)
      exact one_ne_zero (coordG_injective φ Axis.one h3)
  · intro z hz
    exact mem_center_map_iff.mpr ⟨hZH hz, fun y hy => hZc z hz y hy⟩

end Overgroup

end FCHyp

theorem psiG_two_uElt {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
    [Finite K] (φ : L ≃* antiSp K) (a b c : K) :
    psiG φ Axis.two ((φ.symm (uElt a b c 0) : L) : G) = ![b, a] := by
  rw [psiG_symm]
  exact vecOf₂_uElt a b c

theorem psiG_one_uElt {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
    [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (φ : L ≃* antiSp K) (b c d : K) :
    psiG φ Axis.one ((φ.symm (uElt 0 b c d) : L) : G) = ![c ^ 2 ^ (n - 1), d ^ 2 ^ (n - 1)] := by
  rw [psiG_symm]
  have hpow : ∀ x : K, (x ^ 2 ^ (n - 1)) ^ 2 = x := by
    intro x
    have := Fintype.ofFinite K
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have h : (minorAut K).symm (uElt 0 b c d) =
      uElt (d ^ 2 ^ (n - 1)) (c ^ 2 ^ (n - 1)) (b + d ^ 2 ^ (n - 1) * c ^ 2 ^ (n - 1)) 0 := by
    rw [MulEquiv.symm_apply_eq, minorAut_uElt_radA2, hpow c, hpow d]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    congr 1
    linear_combination (-(d ^ 2 ^ (n - 1) * c ^ 2 ^ (n - 1))) * h2
  show vecOf₂ ((minorAut K).symm (uElt 0 b c d)) = _
  rw [h, vecOf₂_uElt]

end FullCenter

open Subgroup GomiFusion RootAxisTwoCore FullCenter
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
