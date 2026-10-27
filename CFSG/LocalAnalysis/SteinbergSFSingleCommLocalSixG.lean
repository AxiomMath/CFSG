module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGPlus
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGQuot

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

@[expose] def MNNormalIn {G : Type} [Group G] (X Tp J₀ : Subgroup G) : Prop :=
  X ≤ Tp ∧ (X.subgroupOf Tp).Normal ∧ J₀ ≤ normalizer (X : Set G)

@[expose] def MNMaximal {G : Type} [Group G] (A B₁ B₂ T N : Subgroup G) [(N.subgroupOf T).Normal] :
    Prop :=
  ∀ S : Subgroup (↥T ⧸ N.subgroupOf T),
    Maximal (fun S' : Subgroup (↥T ⧸ N.subgroupOf T) =>
      S' ≤ (A.subgroupOf T).map (QuotientGroup.mk' (N.subgroupOf T)) ∧ IsElementaryAbelian 2 S')
      S ↔
    S = (B₁.subgroupOf T).map (QuotientGroup.mk' (N.subgroupOf T)) ∨
      S = (B₂.subgroupOf T).map (QuotientGroup.mk' (N.subgroupOf T))

section Conclusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
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
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐘[" i "," k "]" => (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐑[" k "]" => (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐓₁[" i "]" => (𝐑[i] ⊔ 𝐏₁[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀[" j "]" => (𝐑[j] ⊔ 𝐏₂[j] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₂[" j "]" => (𝐓₀[j] ⊓ normalizer (𝐑[j] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₃[" i "]" => (𝐓₁[i] ⊓ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓̄[" i "]" => (𝐓₁[i] ⊔ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}

set_option quotPrecheck false in
local notation "𝐁⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂⋆[" i "]" => (𝐌₀[i] ⊔ 𝐅ʷ[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐀⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ ⊔ 𝐅ʷ[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓⁺[" i "]" => (𝐓̄[i] ⊔ 𝐓₀[Axis.swap i] : Subgroup G)

theorem closure_sq_M (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    closure {x : G | ∃ y ∈ 𝐌₀[i], x = y * y} = 𝐔[i] := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hM2 y hy
  · exact (closure_sq_F h i hne hbot).ge.trans
      (closure_mono fun _ ⟨y, hy, he⟩ => ⟨y, F_le_M h i hne hbot hy, he⟩)

theorem K_le_T₂ (h : FCHyp L K n φ t) (k : Axis) : 𝐊[k] ≤ 𝐓₂[k] := (K_le_H h k).trans (H_le_T₂ h k)

omit [Finite G] in
theorem normalIn_of {X Tp J : Subgroup G} (hX : X ≤ Tp) (hN : Tp ≤ normalizer (X : Set G))
    (hJ : J ≤ normalizer (X : Set G)) : MNNormalIn X Tp J :=
  ⟨hX, (normal_subgroupOf_iff_le_normalizer hX).mpr hN, hJ⟩

theorem normalIn_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    MNNormalIn 𝐁⋆[i] 𝐓⁺[i] 𝐉 :=
  normalIn_of (((le_sup_left : 𝐁⋆[i] ≤ 𝐀⋆[i]).trans (Astar_le_T₂ h i hne hbot)).trans
      (T₂_le_Tplus i))
    (fun _ hg => (mem_inf.mp (mem_inf.mp (Tplus_le_normalizers h i hne hbot hM2 hg)).1).2)
    (J_le_normalizer_Bstar h i hne hbot)

theorem normalIn_Astar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    MNNormalIn 𝐀⋆[i] 𝐓⁺[i] 𝐉 :=
  normalIn_of ((Astar_le_T₂ h i hne hbot).trans (T₂_le_Tplus i))
    (fun _ hg => mem_normalizer_Astar i
      (mem_inf.mp (mem_inf.mp (Tplus_le_normalizers h i hne hbot hM2 hg)).1).2
      (mem_inf.mp (Tplus_le_normalizers h i hne hbot hM2 hg)).2)
    (J_le_normalizer_Astar h i hne hbot)

theorem normalIn_K (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    MNNormalIn 𝐊[i.swap] 𝐓⁺[i] 𝐉 :=
  normalIn_of ((K_le_T₂ h _).trans (T₂_le_Tplus i))
    (fun _ hg => (mem_inf.mp (mem_inf.mp (Tplus_le_normalizers h i hne hbot hM2 hg)).1).1)
    (J_le_normalizer_K h _)

set_option quotPrecheck false in
local notation "𝛑[" i "]" => QuotientGroup.mk' ((𝐊[Axis.swap i]).subgroupOf 𝐓₂[Axis.swap i])
set_option quotPrecheck false in
local notation "𝐈[" S "," i "]" => ((S).subgroupOf 𝐓₂[Axis.swap i]).map 𝛑[i]

end Conclusion

end SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores SixG
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
