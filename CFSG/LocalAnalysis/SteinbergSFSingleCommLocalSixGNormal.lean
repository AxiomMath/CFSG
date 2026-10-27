module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGElem

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type} [Group G]

theorem elem_map_conj {N E : Subgroup G} {g : G} (hg : g ∈ normalizer (N : Set G))
    (helem : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N) :
    ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, ∀ y ∈ E.map (MulAut.conj g).toMonoidHom,
      x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨h1, h2⟩ := helem x hx y hy
  constructor
  · have e : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp hg _).mp h1
  · have e : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp hg _).mp h2

theorem map_conj_le {E T : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G)) (hET : E ≤ T) :
    E.map (MulAut.conj g).toMonoidHom ≤ T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.mp hg x).mp (hET hx)

theorem card_map_conj (E : Subgroup G) (g : G) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  card_map_of_injective (MulAut.conj g).injective

theorem conj_mem_map {E : Subgroup G} {g x : G} (hx : x ∈ E) :
    g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, rfl⟩

end General

section Normal

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

theorem map_Bstar_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G}
    (hgT : g ∈ normalizer (𝐓₂[i.swap] : Set G)) (hgK : g ∈ normalizer (𝐊[i.swap] : Set G)) :
    𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i] ∨
      𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i] :=
  (card_le_of_elem h i hne hbot hM2 (map_conj_le hgT (Bstar_le_T₃ h i hne hbot |>.trans
    inf_le_right)) (elem_map_conj hgK fun _ hx _ hy => elem_Bstar h i hne hbot hM2 hx hy)).2
    ((card_map_conj _ g).trans (card_Bstar h i hne hbot))

theorem map_Cstar_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G}
    (hgT : g ∈ normalizer (𝐓₂[i.swap] : Set G)) (hgK : g ∈ normalizer (𝐊[i.swap] : Set G)) :
    𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i] ∨
      𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i] :=
  (card_le_of_elem h i hne hbot hM2 (map_conj_le hgT ((Cstar_le_Astar i).trans
    (Astar_le_T₂ h i hne hbot))) (elem_map_conj hgK fun _ hx _ hy =>
      elem_Cstar h i hne hbot hM2 hx hy)).2
    ((card_map_conj _ g).trans (card_Cstar h i hne hbot))

theorem Bstar_ne_Cstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐁⋆[i] ≠ 𝐂⋆[i] := fun he =>
  not_Bstar_le_Cstar h i hne hbot he.le

theorem map_Cstar_of_map_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G}
    (hB : 𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i])
    (hC : 𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i] ∨
      𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i]) :
    𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i] :=
  hC.resolve_left fun hC' => Bstar_ne_Cstar h i hne hbot
    (map_injective (MulAut.conj g).injective (hB.trans hC'.symm))

theorem map_Bstar_of_map_Cstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G}
    (hC : 𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i])
    (hB : 𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i] ∨
      𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i]) :
    𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i] :=
  hB.resolve_right fun hB' => Bstar_ne_Cstar h i hne hbot
    (map_injective (MulAut.conj g).injective (hB'.trans hC.symm))

theorem map_Bstar_of_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G}
    (hgT : g ∈ normalizer (𝐓₂[i.swap] : Set G)) (hgK : g ∈ normalizer (𝐊[i.swap] : Set G))
    (hg3 : g ∈ normalizer (𝐓₃[i] : Set G)) :
    𝐁⋆[i].map (MulAut.conj g).toMonoidHom = 𝐁⋆[i] := by
  refine (map_Bstar_eq h i hne hbot hM2 hgT hgK).resolve_right fun hC => ?_
  have hle : 𝐂⋆[i] ≤ 𝐓₃[i] := hC ▸ map_conj_le hg3 (Bstar_le_T₃ h i hne hbot)
  refine not_Cstar_le_Bstar h i hne hbot fun x hx => ?_
  exact (Astar_inf_T₃ h i hne hbot).le (mem_inf.mpr ⟨Cstar_le_Astar i hx, hle hx⟩)

theorem map_Cstar_of_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G}
    (hgT : g ∈ normalizer (𝐓₂[i.swap] : Set G)) (hgK : g ∈ normalizer (𝐊[i.swap] : Set G))
    (hgP : g ∈ normalizer (𝐏₂[i.swap] : Set G)) :
    𝐂⋆[i].map (MulAut.conj g).toMonoidHom = 𝐂⋆[i] := by
  refine (map_Cstar_eq h i hne hbot hM2 hgT hgK).resolve_left fun hB => ?_
  have hle : 𝐁⋆[i] ≤ 𝐏₂[i.swap] := hB ▸ map_conj_le hgP (Cstar_le_P₂ h i hne hbot)
  refine not_Bstar_le_Cstar h i hne hbot fun x hx => ?_
  exact (Astar_inf_P₂ h i hne hbot).le
    (mem_inf.mpr ⟨(le_sup_left : 𝐁⋆[i] ≤ 𝐀⋆[i]) hx, hle hx⟩)

theorem Tbar_le_normalizer_T₂ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓̄[i] ≤ normalizer (𝐓₂[i.swap] : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_T₂ h i hne hbot (Tbar_le_Nhat h i hne hbot hg) hx

theorem Tbar_le_normalizer_T₃ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓̄[i] ≤ normalizer (𝐓₃[i] : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_T₃ h i hne hbot (Tbar_le_Nhat h i hne hbot hg) hx

theorem Tbar_le_normalizer_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓̄[i] ≤ normalizer (𝐊[i.swap] : Set G) :=
  (Tbar_le_Nhat h i hne hbot).trans (Nhat_le_normalizer_K_swap' h i hne hbot)

theorem T₀_le_normalizer_K (h : FCHyp L K n φ t) (k : Axis) :
    𝐓₀[k] ≤ normalizer (𝐊[k] : Set G) := fun _ hg => (mem_inf.mp (T₀_le_En h k hg)).2

theorem T₀_le_normalizer_P₂ (h : FCHyp L K n φ t) (k : Axis) :
    𝐓₀[k] ≤ normalizer (𝐏₂[k] : Set G) :=
  sup_le (R_le_normalizer_P₂ h k) le_normalizer

theorem T₀_le_normalizer_T₂ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓₀[i.swap] ≤ normalizer (𝐓₂[i.swap] : Set G) := by
  obtain ⟨β, -, hβ⟩ := exists_snd_hom h i hne hbot
  intro g hg
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have hxT := (mem_inf.mp hx).1
  have hgx : g * x * g⁻¹ ∈ 𝐓₀[i.swap] := mul_mem (mul_mem hg hxT) (inv_mem hg)
  refine mem_inf.mpr ⟨hgx, (mem_normalizer_R_iff h i hne hbot hgx).mpr ?_⟩
  have h1 : β ⟨g * x * g⁻¹, hgx⟩ = β ⟨g, hg⟩ * β ⟨x, hxT⟩ * (β ⟨g, hg⟩)⁻¹ := by
    show β (⟨g, hg⟩ * ⟨x, hxT⟩ * ⟨g, hg⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have h2 : β ⟨x, hxT⟩ = 1 := by
    rw [hβ]
    exact ofAdd_eq_one.mpr ((mem_normalizer_R_iff h i hne hbot hxT).mp (mem_inf.mp hx).2)
  rw [h2, mul_one, mul_inv_cancel, hβ] at h1
  exact ofAdd_eq_one.mp h1

theorem Tbar_le_normalizer_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G} (hg : g ∈ 𝐓̄[i]) :
    g ∈ normalizer (𝐁⋆[i] : Set G) ∧ g ∈ normalizer (𝐂⋆[i] : Set G) := by
  have hT := Tbar_le_normalizer_T₂ h i hne hbot hg
  have hK := Tbar_le_normalizer_K h i hne hbot hg
  have hB := map_Bstar_of_T₃ h i hne hbot hM2 hT hK (Tbar_le_normalizer_T₃ h i hne hbot hg)
  exact ⟨mem_normalizer_of_map_eq hB, mem_normalizer_of_map_eq
    (map_Cstar_of_map_Bstar h i hne hbot hB (map_Cstar_eq h i hne hbot hM2 hT hK))⟩

theorem T₀_le_normalizer_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G} (hg : g ∈ 𝐓₀[i.swap]) :
    g ∈ normalizer (𝐁⋆[i] : Set G) ∧ g ∈ normalizer (𝐂⋆[i] : Set G) := by
  have hT := T₀_le_normalizer_T₂ h i hne hbot hg
  have hK := T₀_le_normalizer_K h _ hg
  have hC := map_Cstar_of_P₂ h i hne hbot hM2 hT hK (T₀_le_normalizer_P₂ h _ hg)
  exact ⟨mem_normalizer_of_map_eq
    (map_Bstar_of_map_Cstar h i hne hbot hC (map_Bstar_eq h i hne hbot hM2 hT hK)),
    mem_normalizer_of_map_eq hC⟩

theorem H_inf_Cstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐇 ⊓ 𝐂⋆[i] = 𝐋[i.swap] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (fun _ hl => Ks_le_H h (L_le_Ks h _ hl))
    (fun _ hl => (Cstar_eq h i hne hbot).ge (mem_sup_right (L_le_X h _ hl))))
  obtain ⟨hxH, hxC⟩ := mem_inf.mp hx
  obtain ⟨m, hm, y, hy, rfl⟩ := (mem_Cstar_iff h i hne hbot).mp hxC
  have hmR : m ∈ 𝐑[i.swap] := by
    have := mul_mem (H_le_R h _ hxH) (inv_mem (X_le_R h _ hy))
    rwa [mul_inv_cancel_right] at this
  have hmF := (M_inf_R_swap h i hne hbot).le (mem_inf.mpr ⟨hm, hmR⟩)
  exact SixF.mem_L_of_mem_X_of_mem_H h _ (mul_mem (le_sup_left (a := 𝐅) hmF) hy) hxH

theorem closure_sq_L_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    closure {x : G | ∃ y ∈ 𝐋[i.swap], x = y * y} = 𝐔[i] := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, w', hw', -, -, -, hsq⟩ := sq_L_swap h i hbot hy
    rw [SetLike.mem_coe, hsq, sq_W_swap h i hne hbot hw', mul_one]
    exact W_sq_mem_U h i hw
  · rw [← closure_sq_F h i hne hbot]
    exact closure_mono fun _ ⟨y, hy, he⟩ => ⟨y, F_le_L _ hy, he⟩

theorem mem_Nhat_of_normalizer_T₃ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G} (hgK : g ∈ normalizer (𝐊[i.swap] : Set G))
    (hgB : g ∈ normalizer (𝐁⋆[i] : Set G)) (hgC : g ∈ normalizer (𝐂⋆[i] : Set G))
    (hg3 : g ∈ normalizer (𝐓₃[i] : Set G)) : g ∈ 𝐍ₕ[i] := by
  have hle := le_Bstar_or_le_H h i hne hbot hM2 (map_conj_le hg3 (H_le_T₃ h i))
    (elem_map_conj hgK fun _ hx _ hy => elem_H h _ hx hy)
  have hHH : 𝐇.map (MulAut.conj g).toMonoidHom ≤ 𝐇 := hle.resolve_left fun hB => by
    have h1 := hB (conj_mem_map (g := g) t_mem_H)
    have h2 := conj_inv_mem hgB h1
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h2
    exact t_not_mem_Bstar h i hne hbot h2
  have hgH : g ∈ normalizer ((𝐇 : Subgroup G) : Set G) := mem_normalizer_of_map_eq
    (Subgroup.eq_of_le_of_card_ge hHH (card_map_conj _ g).ge)
  have hgL : g ∈ normalizer (𝐋[i.swap] : Set G) := by
    rw [← H_inf_Cstar h i hne hbot]
    exact mem_normalizer_of_conj_le fun x hx => mem_inf.mpr
      ⟨(mem_normalizer_iff.mp hgH x).mp (mem_inf.mp hx).1,
        (mem_normalizer_iff.mp hgC x).mp (mem_inf.mp hx).2⟩
  have hgU := mem_normalizer_closure_sq hgL
  rw [closure_sq_L_swap h i hne hbot] at hgU
  exact mem_inf.mpr ⟨hgH, hgU⟩

theorem J_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐗[i.swap] : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_X_of_En h i hbot
    (N_le_En h _ (mem_inf.mp (J_le_NRB h i hne hbot i.swap hj)).2) hx

theorem J_le_normalizer_Ks (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐊⋆ : Set G) :=
  (J_le_Nhat h i hne hbot).trans (Nhat_le_normalizer_Ks h i hbot)

theorem J_le_normalizer_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐉 ≤ normalizer (𝐁⋆[i] : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp (J_le_normalizer_M h i hne hbot hj) _).mp hy)
    (fun _ hy => (mem_normalizer_iff.mp (J_le_normalizer_Ks h i hne hbot hj) _).mp hy) hx

theorem J_le_normalizer_Cstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐉 ≤ normalizer (𝐂⋆[i] : Set G) := fun _ hj => by
  rw [Cstar_eq h i hne hbot]
  exact mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp (J_le_normalizer_M h i hne hbot hj) _).mp hy)
    (fun _ hy => (mem_normalizer_iff.mp (J_le_normalizer_X h i hne hbot hj) _).mp hy) hx

omit [Finite G] [Finite K] in
theorem Astar_eq_sup (i : Axis) : 𝐀⋆[i] = 𝐁⋆[i] ⊔ 𝐂⋆[i] :=
  le_antisymm (sup_le le_sup_left ((le_sup_right : 𝐅ʷ[i.swap] ≤ 𝐂⋆[i]).trans le_sup_right))
    (sup_le le_sup_left (Cstar_le_Astar i))

theorem J_le_normalizer_Astar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐉 ≤ normalizer (𝐀⋆[i] : Set G) := fun _ hj => by
  rw [Astar_eq_sup i]
  exact mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp (J_le_normalizer_Bstar h i hne hbot hj) _).mp hy)
    (fun _ hy => (mem_normalizer_iff.mp (J_le_normalizer_Cstar h i hne hbot hj) _).mp hy) hx

theorem J_le_normalizer_K (h : FCHyp L K n φ t) (k : Axis) :
    𝐉 ≤ normalizer (𝐊[k] : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_torus_mem_K h k hj hx

end Normal

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
