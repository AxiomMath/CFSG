module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGKernel

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Plus

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

theorem Tplus_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    (𝐓̄[i] : Set G) * (𝐓₀[i.swap] : Set G) = (𝐓⁺[i] : Set G) :=
  (coe_mul_of_right_le_normalizer_left _ _ (T₀_le_normalizer_Tbar h i hne hbot hM2)).symm

theorem card_Tplus (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    Nat.card 𝐓⁺[i] = 2 * Nat.card K ^ 10 := by
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐓̄[i]) (B := 𝐓₀[i.swap]) (T₀_le_normalizer_Tbar h i hne hbot hM2)
  have h2 : Nat.card (𝐓̄[i] ⊓ 𝐓₀[i.swap] : Subgroup G) = 2 * Nat.card K ^ 8 :=
    (congrArg (fun S : Subgroup G => Nat.card S) (Tbar_inf_T₀ h i hne hbot)).trans
      (card_T₂ h i hne hbot)
  rw [h2, card_Tbar h i hne hbot, card_T₀ h i hne hbot] at h1
  have hq : 0 < 2 * Nat.card K ^ 8 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  exact Nat.eq_of_mul_eq_mul_right hq (h1.trans (by ring))

theorem isPGroup_Tplus (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    IsPGroup 2 𝐓⁺[i] :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_Tbar h i hne hbot) (isPGroup_T₀ h _)
    (T₀_le_normalizer_Tbar h i hne hbot hM2)

theorem T₀_ne_Tplus (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    ¬ 𝐓⁺[i] ≤ 𝐓₀[i.swap] := fun hle => by
  have h1 := Subgroup.card_le_of_le hle
  rw [card_Tplus h i hne hbot hM2, card_T₀ h i hne hbot] at h1
  have h2 := Nat.pow_lt_pow_right (one_lt_card_K h) (by norm_num : 9 < 10)
  omega

theorem exists_Tbar_normalizer_T₀ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    ∃ τ ∈ 𝐓̄[i], τ ∈ normalizer (𝐓₀[i.swap] : Set G) ∧ τ ∉ 𝐓₂[i.swap] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥𝐓⁺[i] := (isPGroup_Tplus h i hne hbot hM2).isNilpotent
  have hle : 𝐓₀[i.swap] ≤ 𝐓⁺[i] := le_sup_right
  have hlt : (𝐓₀[i.swap]).subgroupOf 𝐓⁺[i] < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => T₀_ne_Tplus h i hne hbot hM2 fun x hx => ?_
    have h1 : (⟨x, hx⟩ : ↥𝐓⁺[i]) ∈ (𝐓₀[i.swap]).subgroupOf 𝐓⁺[i] := by
      rw [htop]
      exact mem_top _
    exact mem_subgroupOf.mp h1
  obtain ⟨x, hxN, hxH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hxNG : (x : G) ∈ normalizer (𝐓₀[i.swap] : Set G) :=
    mem_normalizer_of_conj_le fun y hy => by
      have h1 := (mem_normalizer_iff.mp hxN ⟨y, hle hy⟩).mp (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
  obtain ⟨τ, hτ, g₀, hg₀, hx⟩ := Set.mem_mul.mp ((Tplus_mul h i hne hbot hM2).ge x.2)
  refine ⟨τ, hτ, ?_, fun hτT => hxH (mem_subgroupOf.mpr ?_)⟩
  · have h1 := mul_mem hxNG (inv_mem (le_normalizer hg₀))
    rwa [← hx, mul_inv_cancel_right] at h1
  · rw [← hx]
    exact mul_mem ((inf_le_left : 𝐓₂[i.swap] ≤ 𝐓₀[i.swap]) hτT) hg₀

theorem Tbar_le_normalizer_T₀ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) : 𝐓̄[i] ≤ normalizer (𝐓₀[i.swap] : Set G) := by
  obtain ⟨τ, hτ, hτN, hτT⟩ := exists_Tbar_normalizer_T₀ h i hne hbot hM2
  have hET : 𝐄[i] ≤ normalizer (𝐓₂[i.swap] : Set G) :=
    (E_le_Tbar i).trans (Tbar_le_normalizer_T₂ h i hne hbot)
  obtain ⟨x, hx, e, he, rfl⟩ := Set.mem_mul.mp
    ((coe_mul_of_right_le_normalizer_left _ _ hET).le ((Tbar_eq_sup_E h i hne hbot).le hτ))
  have hT₂N : 𝐓₂[i.swap] ≤ normalizer (𝐓₀[i.swap] : Set G) :=
    (inf_le_left : 𝐓₂[i.swap] ≤ 𝐓₀[i.swap]).trans le_normalizer
  have heN : e ∈ normalizer (𝐓₀[i.swap] : Set G) := by
    have h1 := mul_mem (inv_mem (hT₂N hx)) hτN
    rwa [inv_mul_cancel_left] at h1
  have hψ : psiX φ t i e 1 ≠ 0 := fun h0 =>
    hτT (mul_mem hx (H_le_T₂ h _ ((psiX_one_eq_zero_iff h i he).mp h0)))
  have hE : 𝐄[i] ≤ normalizer (𝐓₀[i.swap] : Set G) := by
    refine E_le_of_psiX h i (fun y hy => hT₂N (H_le_T₂ h _ (mem_inf.mp hy).1))
      fun e' he' => ?_
    by_cases h0 : psiX φ t i e' 1 = 0
    · refine ⟨1, one_mem _, one_mem _, ?_⟩
      rw [h0]
      exact (psiX_one_eq_zero_iff h i (one_mem _)).mpr (one_mem _)
    · obtain ⟨r, s, hr, hs, hrs⟩ := exists_radChar_eq i (div_ne_zero h0 hψ)
      obtain ⟨δ, hδD, hδ⟩ := exists_diagTorus hr hs
      have hgJ : ((φ.symm δ : L) : G)⁻¹ ∈ 𝐉 := inv_mem (symm_mem_pull.mpr hδD)
      have hgN := J_le_normalizer_T₀ h i hne hbot i.swap hgJ
      refine ⟨((φ.symm δ : L) : G)⁻¹ * e * ((φ.symm δ : L) : G), ?_, ?_, ?_⟩
      · have h1 := mul_mem (mul_mem hgN heN) (inv_mem hgN)
        rwa [inv_inv] at h1
      · have h1 := (mem_normalizer_iff.mp (J_le_normalizer_E h i hne hbot i hgJ) e).mp he
        rwa [inv_inv] at h1
      · rw [psiX_conj_torus h i hr hs hδ he, hrs, div_mul_cancel₀ _ hψ]
  exact (Tbar_eq_sup_E h i hne hbot).le.trans (sup_le hT₂N hE)

theorem Tplus_le_normalizer_T₀ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) : 𝐓⁺[i] ≤ normalizer (𝐓₀[i.swap] : Set G) :=
  sup_le (Tbar_le_normalizer_T₀ h i hne hbot hM2) le_normalizer

theorem Tplus_le_normalizers (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐓⁺[i] ≤ normalizer (𝐊[i.swap] : Set G) ⊓ normalizer (𝐁⋆[i] : Set G) ⊓
      normalizer (𝐂⋆[i] : Set G) := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · exact mem_inf.mpr ⟨mem_inf.mpr ⟨Tbar_le_normalizer_K h i hne hbot hg,
      (Tbar_le_normalizer_Bstar h i hne hbot hM2 hg).1⟩,
      (Tbar_le_normalizer_Bstar h i hne hbot hM2 hg).2⟩
  · exact mem_inf.mpr ⟨mem_inf.mpr ⟨T₀_le_normalizer_K h _ hg,
      (T₀_le_normalizer_Bstar h i hne hbot hM2 hg).1⟩,
      (T₀_le_normalizer_Bstar h i hne hbot hM2 hg).2⟩

omit [Finite K] in
theorem mem_normalizer_Astar (i : Axis) {g : G} (hgB : g ∈ normalizer (𝐁⋆[i] : Set G))
    (hgC : g ∈ normalizer (𝐂⋆[i] : Set G)) : g ∈ normalizer (𝐀⋆[i] : Set G) := by
  rw [Astar_eq_sup i]
  exact mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp hgB _).mp hy)
    (fun _ hy => (mem_normalizer_iff.mp hgC _).mp hy) hx

omit [Finite G] [Finite K] in
theorem T₂_le_Tplus (i : Axis) : 𝐓₂[i.swap] ≤ 𝐓⁺[i] := le_sup_right.trans le_sup_left

end Plus

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
