module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure
public import CFSG.LocalAnalysis.SteinbergSFSingleCommTorusLayerAut
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores RootStandard TorusLayer
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix Pointwise

namespace TorusLayer

section General

variable {G : Type*} [Group G] {H : Subgroup G}

theorem centralizer_subgroupOf {X : Subgroup G} (hX : X ≤ H) :
    centralizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (centralizer (X : Set G)).subgroupOf H := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, hX hy⟩ (mem_subgroupOf.mpr hy))
  · intro hx y hy
    exact Subtype.ext (hx y (mem_subgroupOf.mp hy))

theorem centralizer_singleton_subgroupOf {t : G} (ht : t ∈ H) :
    centralizer ({(⟨t, ht⟩ : ↥H)} : Set ↥H) = (centralizer ({t} : Set G)).subgroupOf H := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩

theorem zpowers_subgroupOf {t : G} (ht : t ∈ H) :
    zpowers (⟨t, ht⟩ : ↥H) = (zpowers t).subgroupOf H := by
  ext x
  rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by rw [SubgroupClass.coe_zpow]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Subtype.ext (by rw [SubgroupClass.coe_zpow, hm])⟩

theorem sup_subgroupOf {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    (A ⊔ B).subgroupOf H = A.subgroupOf H ⊔ B.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left hA, inf_of_le_left hB, inf_of_le_left (sup_le hA hB)]

end General

section Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}
set_option quotPrecheck false in
local notation "𝐕[" i "," k "]" => (𝐌₀[i] ⊓ centralizer (𝐉[k] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒[" k "]" => (⁅L ⊓ centralizer (𝐉[k] : Set G),
  L ⊓ centralizer (𝐉[k] : Set G)⁆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇𝐭[" k "]" => centralizer (𝐉[k] : Set G)
set_option quotPrecheck false in
local notation "𝐘[" k "]" => closure {x : G | ∃ g ∈ 𝐇𝐭[k], ∃ s ∈ 𝐒[k], x = g⁻¹ * s * g}
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

omit [Finite G] [CharP K 2] [Finite K] in
theorem J_le_center (k : Axis) : 𝐉[k].subgroupOf 𝐇𝐭[k] ≤ center ↥𝐇𝐭[k] := fun _ hx =>
  mem_center_iff.mpr fun g => Subtype.ext
    (mem_centralizer_iff.mp g.2 _ (mem_subgroupOf.mp hx)).symm

omit [Finite G] [CharP K 2] [Finite K] in
theorem J_le_Ht (k : Axis) : 𝐉[k] ≤ 𝐇𝐭[k] := fun _ hx => mem_centralizer_iff.mpr fun _ hb =>
  torus_comm (axisTorus_le_J0 k hb) (axisTorus_le_J0 k hx)

omit [Finite G] [CharP K 2] [Finite K] in
theorem Y_subgroupOf_eq (k : Axis) :
    𝐘[k].subgroupOf 𝐇𝐭[k] = normalClosure ((𝐒[k].subgroupOf 𝐇𝐭[k] : Subgroup ↥𝐇𝐭[k]) :
      Set ↥𝐇𝐭[k]) := by
  apply le_antisymm
  · intro x hx
    have hle : 𝐘[k] ≤ (normalClosure ((𝐒[k].subgroupOf 𝐇𝐭[k] : Subgroup ↥𝐇𝐭[k]) :
        Set ↥𝐇𝐭[k])).map 𝐇𝐭[k].subtype := by
      rw [closure_le]
      rintro _ ⟨g, hg, s, hs, rfl⟩
      refine ⟨(⟨g, hg⟩ : ↥𝐇𝐭[k])⁻¹ * ⟨s, S_le_Ht φ k hs⟩ * ((⟨g, hg⟩ : ↥𝐇𝐭[k])⁻¹)⁻¹, ?_,
        by simp⟩
      exact (normalClosure_normal).conj_mem _ (subset_normalClosure (mem_subgroupOf.mpr hs)) _
    obtain ⟨y, hy, hyx⟩ := hle (mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy
  · have hN : (𝐘[k].subgroupOf 𝐇𝐭[k]).Normal := ⟨fun x hx g => mem_subgroupOf.mpr
      (conj_mem_Y k g.2 (mem_subgroupOf.mp hx))⟩
    exact normalClosure_le_normal fun x hx => mem_subgroupOf.mpr (S_le_Y k (mem_subgroupOf.mp hx))

omit [Finite G] [CharP K 2] [Finite K] in
theorem Ht_ne_top [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hK : 2 < Nat.card K)
    (k : Axis) : 𝐇𝐭[k] ≠ ⊤ := by
  intro htop
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne hK (1 : K)
  have hne : ∀ δ : antiSp K, ((φ.symm δ : L) : G) = 1 → δ = 1 := by
    intro δ e
    have : φ.symm δ = 1 := Subtype.ext e
    rwa [MulEquiv.symm_apply_eq, map_one] at this
  obtain ⟨δ, hδJ, hδ1⟩ : ∃ δ ∈ axisTorus K k, δ ≠ 1 := by
    cases k
    · obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
      refine ⟨δ, ⟨r, hr0, hδm⟩, fun h1 => hr1 ?_⟩
      rw [h1] at hδm
      have h2 := congrFun (congrFun hδm 3) 3
      simp [diagMat] at h2
      exact h2
    · obtain ⟨δ, -, hδm⟩ := exists_diagTorus (K := K) one_ne_zero hr0
      refine ⟨δ, ⟨r, hr0, hδm⟩, fun h1 => hr1 ?_⟩
      rw [h1] at hδm
      have h2 := congrFun (congrFun hδm 2) 2
      simp [diagMat] at h2
      exact h2
  have hc : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
    · exact h1
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (mem_center_iff.mp (h1 ▸ mem_top b) a) hab
  have hj : ((φ.symm δ : L) : G) ∈ center G := mem_center_iff.mpr fun g =>
    (mem_centralizer_iff.mp (htop ▸ mem_top g) _ (symm_mem_pull.mpr hδJ)).symm
  rw [hc, mem_bot] at hj
  exact hδ1 (hne δ hj)

theorem layerHyp [IsSimpleGroup G] (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (k : Axis) :
    ∃ (e : SL₂ K ≃* ↥(𝐒[k].subgroupOf 𝐇𝐭[k])) (u w : ↥𝐇𝐭[k]),
      (∀ X, ((e X : ↥𝐇𝐭[k]) : G) = ((φ.symm (rootSLHom K k X) : L) : G)) ∧
      LayerHyp n e (𝐉[k].subgroupOf 𝐇𝐭[k]) (𝐕[i, k].subgroupOf 𝐇𝐭[k])
        ⟨t, t_mem_Ht φ h.twoCore k⟩ u w := by
  have hS := h.twoCore
  have hK4 : 4 ≤ Nat.card K := h.four_le_card
  have htH := t_mem_Ht φ hS k
  have hSH := S_le_Ht φ k
  obtain ⟨e₀, he₀⟩ := exists_equiv_S φ hK4 k
  have hu1 : coordG φ k 1 ≠ 1 := fun e1 => one_ne_zero (coordG_injective φ k
    (e1.trans (coordG_zero φ k).symm))
  have huS : coordG φ k 1 ∈ 𝐒[k] := U_le_S φ hK4 k (coordG_mem φ k 1)
  obtain ⟨w, hw, -, hwt, -⟩ := exists_W_kappa h k (coordG_mem φ k 1)
  refine ⟨e₀.trans (subgroupOfEquivOfLe hSH).symm, ⟨coordG φ k 1, hSH huS⟩,
    ⟨w, (mem_inf.mp hw).2⟩, fun X => he₀ X, ?_⟩
  have hVH : 𝐕[i, k] ≤ 𝐇𝐭[k] := inf_le_right
  refine
    { two_le := h.setup.two_le
      card_K := h.setup.card_K
      order_t := (Subgroup.orderOf_coe _).symm.trans h.setup.order_t
      S_le := ?_
      S_normal := ?_
      J_le := J_le_center k
      J_odd := ?_
      cent_eq := ?_
      u_mem := mem_subgroupOf.mpr huS
      u_ne := fun h1 => hu1 (congrArg Subtype.val h1)
      u_sq := Subtype.ext (U_comm_mul_self φ (coordG_mem φ k 1) (coordG_mem φ k 1)).2
      w_conj := Subtype.ext hwt
      four := exists_four_S φ h.setup.two_le h.setup.card_K k
      sylow := ?_
      V_pgroup := ((isPGroup_M h i hne hbot).to_le inf_le_left).comap_of_injective
        𝐇𝐭[k].subtype 𝐇𝐭[k].subtype_injective
      V_le := ?_
      V_card := ?_
      kgroup := CFSG.QuasithinUnique.isKGroupCat_of_kProper hKP
        (Ht_ne_top hnab (by omega) k) }
  · rw [centralizer_singleton_subgroupOf htH]
    exact fun x hx => mem_subgroupOf.mpr (hS.L_le (S_le_L φ k (mem_subgroupOf.mp hx)))
  · refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgC : (((g : ↥(centralizer ({(⟨t, htH⟩ : ↥𝐇𝐭[k])} : Set ↥𝐇𝐭[k]))) : ↥𝐇𝐭[k]) : G) ∈
        𝐂 := mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2))
    have := conj_mem_S φ hS k (mem_inf.mpr ⟨((g : _) : ↥𝐇𝐭[k]).2, hgC⟩) hx
    simpa using this
  · rw [Nat.card_congr (subgroupOfEquivOfLe (J_le_Ht k)).toEquiv]
    exact Nat.not_even_iff_odd.mp fun he => not_two_dvd_card_J h k (even_iff_two_dvd.mp he)
  · rw [centralizer_subgroupOf hSH, centralizer_singleton_subgroupOf htH, zpowers_subgroupOf htH,
      ← sup_subgroupOf (J_le_Ht k) (zpowers_le.mpr htH),
      ← centralizer_J_inf_centralizer_S_inf_C φ hS k]
    ext x
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h1 => ⟨⟨x.2, h1.1⟩, h1.2⟩, fun h1 => ⟨h1.1.2, h1.2⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨R₀, hR₀⟩ := exists_sylow_U φ h.setup.two_le h.setup.card_K k
    have hcR : Nat.card R₀ = 2 ^ n := by
      rw [← card_map_of_injective 𝐒[k].subtype_injective, hR₀, card_U, h.setup.card_K]
    have hcS : Nat.card (𝐒[k].subgroupOf 𝐇𝐭[k]) = Nat.card 𝐒[k] :=
      Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv
    refine ⟨Classical.arbitrary _, ?_⟩
    rw [Sylow.card_eq_multiplicity, hcS, ← R₀.card_eq_multiplicity, hcR]
  · rw [← Y_subgroupOf_eq k]
    exact fun x hx => mem_subgroupOf.mpr (V_le_Y h i hne hbot k (mem_subgroupOf.mp hx))
  · rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv, ← h.setup.card_K]
    exact card_V_ge h i hne hbot k

end Data

end TorusLayer

end CFSG.LocalAnalysis.SymplecticFourStandard
