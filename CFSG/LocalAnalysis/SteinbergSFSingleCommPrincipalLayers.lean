module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersExchange
public import CFSG.LocalAnalysis.SteinbergSFSingleCommTorusLayer

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores RootStandard TorusLayer
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix Pointwise

namespace PrincipalLayers

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
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
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

theorem axisData [IsSimpleGroup G] (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (k : Axis) :
    ∃ (htH : t ∈ 𝐇𝐭[k]) (hhH : ∀ X, ((φ.symm (rootSLHom K k X) : L) : G) ∈ 𝐇𝐭[k]),
      AxisData ↥𝐇𝐭[k] K n (𝐒[k].subgroupOf 𝐇𝐭[k]) (𝐉[k].subgroupOf 𝐇𝐭[k])
        (𝐘[k].subgroupOf 𝐇𝐭[k]) (𝐕[i, k].subgroupOf 𝐇𝐭[k]) (𝐔[k].subgroupOf 𝐇𝐭[k]) ⟨t, htH⟩
        (fun X => ⟨((φ.symm (rootSLHom K k X) : L) : G), hhH X⟩) := by
  have hK4 : 4 ≤ Nat.card K := h.four_le_card
  obtain ⟨e, u, w, he, hLk⟩ := layerHyp h i hne hbot hKP hnab k
  have htH := t_mem_Ht φ h.twoCore k
  have hhH : ∀ X, ((φ.symm (rootSLHom K k X) : L) : G) ∈ 𝐇𝐭[k] := fun X =>
    S_le_Ht φ k (by
      rw [S_eq φ hK4 k]
      exact ⟨X, rfl⟩)
  have hconc := torusLayerConclusion hLk (Y_subgroupOf_eq k)
    (hk := fun X => (⟨((φ.symm (rootSLHom K k X) : L) : G), hhH X⟩ : ↥𝐇𝐭[k]))
    (fun X => Subtype.ext (he X).symm)
  have hSH := S_le_Ht φ k
  have hUS := U_le_S φ hK4 k
  have hUV : 𝐔[k] ≤ 𝐕[i, k] := by
    have h1 : 𝐕[i, k] ⊓ 𝐂 = 𝐔[k] := by
      rcases SingleComm.eq_or_eq_swap i k with rfl | rfl
      · exact V_inf_C h k hne hbot
      · rw [V_swap_eq h i hne hbot]
        exact W_inf_C h i.swap
    rw [← h1]
    exact inf_le_left
  have : Group.IsPerfect ↥𝐘[k] := isPerfect_Y hK4 k
  refine ⟨htH, hhH,
    { layer := hconc
      two_le := hLk.two_le
      card_K := hLk.card_K
      equiv := ⟨e, fun X => Subtype.ext (he X)⟩
      order_t := hLk.order_t
      perfect := Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (Y_le_H k)).symm.toMonoidHom) (MulEquiv.surjective _)
      Y_normal := by
        rw [Y_subgroupOf_eq k]
        infer_instance
      S_le_Y := fun x hx => mem_subgroupOf.mpr (S_le_Y k (mem_subgroupOf.mp hx))
      V_le := fun x hx => mem_subgroupOf.mpr (V_le_Y h i hne hbot k (mem_subgroupOf.mp hx))
      V_pgroup := hLk.V_pgroup
      t_mem := ?_
      U_le_S := fun x hx => mem_subgroupOf.mpr (hUS (mem_subgroupOf.mp hx))
      U_le_V := fun x hx => mem_subgroupOf.mpr (hUV (mem_subgroupOf.mp hx))
      U_comm := fun x hx y hy => Subtype.ext
        (U_comm_mul_self φ (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy)).1
      U_sq := fun x hx => Subtype.ext
        (U_comm_mul_self φ (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hx)).2
      U_card := ?_
      U_sylow := (exists_sylow_subgroupOf_iff hSH hUS).mpr
        (exists_sylow_U φ hLk.two_le hLk.card_K k)
      upper_mem := ?_ }⟩
  · have htV := t_mem_normalizer_V h i hne hbot k
    rw [mem_normalizer_iff] at htV ⊢
    intro x
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact htV x
  · rw [Nat.card_congr (subgroupOfEquivOfLe (hUS.trans hSH)).toEquiv, card_U, hLk.card_K]
  · rw [mem_subgroupOf]
    change ((φ.symm (rootSLHom K k (RootStandard.upperSL 1)) : L) : G) ∈ 𝐔[k]
    rw [← rootCoord_eq_rootSLHom]
    exact coordG_mem φ k 1

theorem nontrivial_data (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐖[i].subgroupOf 𝐇𝐭[i] ≤ 𝐕[i, i].subgroupOf 𝐇𝐭[i] ∧
      (∀ x ∈ 𝐖[i].subgroupOf 𝐇𝐭[i], ∀ y ∈ 𝐖[i].subgroupOf 𝐇𝐭[i], x * y = y * x) ∧
      𝐔[i].subgroupOf 𝐇𝐭[i] ≤ 𝐖[i].subgroupOf 𝐇𝐭[i] ∧
      (∀ w ∈ 𝐖[i].subgroupOf 𝐇𝐭[i], w * w ∈ 𝐔[i].subgroupOf 𝐇𝐭[i]) ∧
      (∃ w ∈ 𝐖[i].subgroupOf 𝐇𝐭[i], w * w ≠ 1) ∧
      Nat.card (𝐕[i, i].subgroupOf 𝐇𝐭[i]) = (Nat.card K) ^ 3 := by
  obtain ⟨hWc, lam, -, huniq, -, hlamne⟩ := square_map h i
  have hl : (1 : K) = lam := huniq 1 (W_sq_eq' h i hne hbot)
  obtain ⟨hclW, -, -, -⟩ := hlamne (hl ▸ one_ne_zero)
  have hWH : 𝐖[i] ≤ 𝐇𝐭[i] := inf_le_right
  refine ⟨fun x hx => mem_subgroupOf.mpr (W_le_V h i hne hbot i (mem_subgroupOf.mp hx)),
    fun x hx y hy => Subtype.ext (hWc _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)),
    fun x hx => mem_subgroupOf.mpr (U_le_W h i (mem_subgroupOf.mp hx)),
    fun w hw => mem_subgroupOf.mpr (by
      rw [coe_mul, ← hclW]
      exact subset_closure ⟨w, mem_subgroupOf.mp hw, rfl⟩), ?_, ?_⟩
  · obtain ⟨w, hw, hwt, -, -⟩ := exists_W_kappa h i (coordG_mem φ i 1)
    refine ⟨⟨w, hWH hw⟩, mem_subgroupOf.mpr hw, fun h1 => ?_⟩
    have h2 : w * w = coordG φ i (1 * 1) := W_sq_eq' h i hne hbot w hw 1 hwt
    rw [one_mul] at h2
    have h3 : w * w = 1 := congrArg Subtype.val h1
    exact one_ne_zero (coordG_injective φ i (h2.symm.trans (h3.trans (coordG_zero φ i).symm)))
  · rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : 𝐕[i, i] ≤ 𝐇𝐭[i])).toEquiv]
    exact card_V h i hne hbot

end Data

end PrincipalLayers

open PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
