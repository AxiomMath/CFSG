module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresNormal

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace NextCores

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

@[expose] def deltaSub (P F : Subgroup G) (a : G) (hPa : ∀ p ∈ P, a⁻¹ * p * a ∈ P)
    (hFP : ∀ p ∈ P, ∀ f ∈ F, p * f * p⁻¹ ∈ F)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ F) : Subgroup G where
  carrier := {x | x ∈ P ∧ ∃ y ∈ P, (y⁻¹ * (a⁻¹ * y * a))⁻¹ * x ∈ F}
  one_mem' := ⟨one_mem P, 1, one_mem P, by
    rw [show ((1 : G)⁻¹ * (a⁻¹ * 1 * a))⁻¹ * 1 = 1 by group]
    exact one_mem F⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨hx₁, y₁, hy₁, hf₁⟩ ⟨hx₂, y₂, hy₂, hf₂⟩
    refine ⟨mul_mem hx₁ hx₂, y₁ * y₂, mul_mem hy₁ hy₂, ?_⟩
    have hδ₁ : y₁⁻¹ * (a⁻¹ * y₁ * a) ∈ P := mul_mem (inv_mem hy₁) (hPa y₁ hy₁)
    have hδ₂ : y₂⁻¹ * (a⁻¹ * y₂ * a) ∈ P := mul_mem (inv_mem hy₂) (hPa y₂ hy₂)
    have hc := hcomm y₂⁻¹ (inv_mem hy₂) _ (inv_mem hδ₁)
    have h3 := hFP _ (inv_mem hδ₂) _ (mul_mem hc hf₁)
    have e : ((y₁ * y₂)⁻¹ * (a⁻¹ * (y₁ * y₂) * a))⁻¹ * (x₁ * x₂) =
        ((y₂⁻¹ * (a⁻¹ * y₂ * a))⁻¹ * ((y₂⁻¹ * (y₁⁻¹ * (a⁻¹ * y₁ * a))⁻¹ * y₂⁻¹⁻¹ *
          (y₁⁻¹ * (a⁻¹ * y₁ * a))⁻¹⁻¹) * ((y₁⁻¹ * (a⁻¹ * y₁ * a))⁻¹ * x₁)) *
            (y₂⁻¹ * (a⁻¹ * y₂ * a))⁻¹⁻¹) * ((y₂⁻¹ * (a⁻¹ * y₂ * a))⁻¹ * x₂) := by group
    rw [e]
    exact mul_mem h3 hf₂
  inv_mem' := by
    rintro x ⟨hx, y, hy, hf⟩
    refine ⟨inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
    have hD : a⁻¹ * y * a ∈ P := hPa y hy
    have h1 := hFP _ (mul_mem hD (inv_mem hy)) _ (inv_mem hf)
    have h2 := hcomm _ hD y⁻¹ (inv_mem hy)
    have e : (y⁻¹⁻¹ * (a⁻¹ * y⁻¹ * a))⁻¹ * x⁻¹ =
        ((a⁻¹ * y * a) * y⁻¹ * ((y⁻¹ * (a⁻¹ * y * a))⁻¹ * x)⁻¹ * ((a⁻¹ * y * a) * y⁻¹)⁻¹) *
          ((a⁻¹ * y * a) * y⁻¹ * (a⁻¹ * y * a)⁻¹ * y⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem h1 h2

variable {P F : Subgroup G} {a : G} {hPa : ∀ p ∈ P, a⁻¹ * p * a ∈ P}
  {hFP : ∀ p ∈ P, ∀ f ∈ F, p * f * p⁻¹ ∈ F} {hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ F}

theorem deltaSub_le : deltaSub P F a hPa hFP hcomm ≤ P := fun _ hx => hx.1

theorem le_deltaSub (hF : F ≤ P) : F ≤ deltaSub P F a hPa hFP hcomm := fun f hf =>
  ⟨hF hf, 1, one_mem P, by
    rw [show ((1 : G)⁻¹ * (a⁻¹ * 1 * a))⁻¹ * f = f by group]
    exact hf⟩

theorem delta_mem_deltaSub {y : G} (hy : y ∈ P) :
    y⁻¹ * (a⁻¹ * y * a) ∈ deltaSub P F a hPa hFP hcomm :=
  ⟨mul_mem (inv_mem hy) (hPa y hy), y, hy, by
    rw [inv_mul_cancel]
    exact one_mem F⟩

theorem conj_mem_deltaSub (hF : F ≤ P) {p : G} (hp : p ∈ P) {x : G}
    (hx : x ∈ deltaSub P F a hPa hFP hcomm) : p * x * p⁻¹ ∈ deltaSub P F a hPa hFP hcomm := by
  rw [show p * x * p⁻¹ = (p * x * p⁻¹ * x⁻¹) * x by group]
  exact mul_mem (le_deltaSub hF (hcomm p hp x hx.1)) hx

theorem conj_comm_mem_deltaSub {b : G} (hab : a * b = b * a)
    (hbP : ∀ p ∈ P, b * p * b⁻¹ ∈ P) (hbF : ∀ f ∈ F, b * f * b⁻¹ ∈ F) {x : G}
    (hx : x ∈ deltaSub P F a hPa hFP hcomm) : b * x * b⁻¹ ∈ deltaSub P F a hPa hFP hcomm := by
  obtain ⟨hxP, y, hy, hf⟩ := hx
  refine ⟨hbP x hxP, b * y * b⁻¹, hbP y hy, ?_⟩
  have hc : Commute a b := hab
  have h1 : a⁻¹ * b = b * a⁻¹ := hc.inv_left.eq
  have h2 : b⁻¹ * a = a * b⁻¹ := hc.inv_right.eq.symm
  have e : ((b * y * b⁻¹)⁻¹ * (a⁻¹ * (b * y * b⁻¹) * a))⁻¹ * (b * x * b⁻¹) =
      b * ((y⁻¹ * (a⁻¹ * y * a))⁻¹ * x) * b⁻¹ := by
    calc ((b * y * b⁻¹)⁻¹ * (a⁻¹ * (b * y * b⁻¹) * a))⁻¹ * (b * x * b⁻¹)
        = (b * y⁻¹ * (b⁻¹ * (a⁻¹ * b)) * y * (b⁻¹ * a))⁻¹ * (b * x * b⁻¹) := by group
      _ = (b * y⁻¹ * (b⁻¹ * (b * a⁻¹)) * y * (a * b⁻¹))⁻¹ * (b * x * b⁻¹) := by rw [h1, h2]
      _ = b * ((y⁻¹ * (a⁻¹ * y * a))⁻¹ * x) * b⁻¹ := by group
  rw [e]
  exact hbF _ hf

theorem t_not_mem_deltaSub {t : G} (htP : t ∈ P) (htF : t ∉ F) (htt : t * t = 1)
    (hat : a * t = t * a) (hFa : ∀ f ∈ F, a⁻¹ * f * a ∈ F) {m : ℕ} (hm : Odd m)
    (ham : a ^ m = 1) : t ∉ deltaSub P F a hPa hFP hcomm := by
  rintro ⟨-, y, hy, hf⟩
  set f := (y⁻¹ * (a⁻¹ * y * a))⁻¹ * t with hfdef
  have hya : a⁻¹ * y * a = y * t * f⁻¹ := by rw [hfdef]; group
  have hc : Commute a t := hat
  have key : ∀ k : ℕ, ∃ c ∈ F, (a ^ k)⁻¹ * y * a ^ k = y * t ^ k * c := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem F, by simp⟩
    | succ k ih =>
      obtain ⟨c, hc', hck⟩ := ih
      have htk : a⁻¹ * t ^ k * a = t ^ k := by
        rw [mul_assoc, ← (hc.pow_right k).eq, inv_mul_cancel_left]
      have h1 : (t ^ k)⁻¹ * f⁻¹ * t ^ k ∈ F := by
        have := hFP _ (inv_mem (pow_mem htP k)) _ (inv_mem hf)
        rwa [inv_inv] at this
      refine ⟨((t ^ k)⁻¹ * f⁻¹ * t ^ k) * (a⁻¹ * c * a), mul_mem h1 (hFa c hc'), ?_⟩
      calc (a ^ (k + 1))⁻¹ * y * a ^ (k + 1) = a⁻¹ * ((a ^ k)⁻¹ * y * a ^ k) * a := by
            rw [pow_succ]; group
        _ = (a⁻¹ * y * a) * (a⁻¹ * t ^ k * a) * (a⁻¹ * c * a) := by rw [hck]; group
        _ = y * t * f⁻¹ * t ^ k * (a⁻¹ * c * a) := by rw [hya, htk]
        _ = y * t ^ (k + 1) * (((t ^ k)⁻¹ * f⁻¹ * t ^ k) * (a⁻¹ * c * a)) := by
            rw [pow_succ']; group
  obtain ⟨c, hc', hcm⟩ := key m
  rw [ham, inv_one, one_mul, mul_one] at hcm
  have htm : t ^ m = c⁻¹ := by
    have := hcm.symm
    rw [mul_assoc, mul_eq_left] at this
    exact eq_inv_of_mul_eq_one_left this
  obtain ⟨k, rfl⟩ := hm
  have e : t ^ (2 * k + 1) = t := by rw [pow_succ, pow_mul, sq, htt, one_pow, one_mul]
  rw [e] at htm
  exact htF (htm ▸ inv_mem hc')

end General

section Complement

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
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}

theorem F_le_P₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐅 ≤ 𝐏₀[i] :=
  (F_le_E0 h).trans (E0_le_P₀ h i hne hbot)

theorem t_mem_P₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : t ∈ 𝐏₀[i] :=
  E0_le_P₀ h i hne hbot (t_mem_E0 h)

theorem P₀_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₀[i] ≤ 𝐍ₕ[i] :=
  (P₀_le_T₃ h i hne hbot).trans (inf_le_left.trans (T₁_le_Nhat h i hne hbot))

theorem conj_P₀_mem_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₀[i]) {f : G} (hf : f ∈ 𝐅) :
    p * f * p⁻¹ ∈ 𝐅 :=
  (mem_normalizer_iff.mp (Nhat_le_normalizer_F h i hbot (P₀_le_Nhat h i hne hbot hp)) f).mp hf

theorem comm_P₀_mem_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐏₀[i]) {y : G} (hy : y ∈ 𝐏₀[i]) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐅 :=
  comm_mem_of_sq_mem (sq_P₀_mem_F h i hne hbot hx) (sq_P₀_mem_F h i hne hbot hy)
    (sq_P₀_mem_F h i hne hbot (mul_mem hx hy))
    (mem_normalizer_of_conj_le fun _ hf => conj_P₀_mem_F h i hne hbot hy hf)

theorem conj_torus_mem_P₀ (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐏₀[i]) : j * x * j⁻¹ ∈ 𝐏₀[i] :=
  mem_inf.mpr ⟨conj_mem_P₁ i (N_le_normalizer_D h i (h.torus_le_N i hj)) (mem_inf.mp hx).1,
    conj_mem_P₂ _ (N_le_En h _ (h.torus_le_N _ hj)) (mem_inf.mp hx).2⟩

theorem conj_inv_torus_mem_P₀ (h : FCHyp L K n φ t) (i : Axis) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐏₀[i]) : j⁻¹ * x * j ∈ 𝐏₀[i] := by
  simpa using conj_torus_mem_P₀ h i (inv_mem hj) hx

theorem sq_kappa_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G} (hx : x ∈ 𝐏₁[i]) (hy : y ∈ 𝐏₁[i]) :
    (t⁻¹ * ((x * y)⁻¹ * t * (x * y))) * (t⁻¹ * ((x * y)⁻¹ * t * (x * y))) =
      ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) *
        ((t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y))) := by
  obtain ⟨_, e, he⟩ := quotient_P₁ h i hne hbot
  have h1 := he (⟨x, hx⟩ * ⟨y, hy⟩)
  rw [QuotientGroup.mk_mul, map_mul, coe_mul, he, he] at h1
  exact h1.symm

theorem sq_kappa_eq_one_iff (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G}
    (hx : x ∈ 𝐏₁[i]) :
    (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) = 1 ↔ x ∈ 𝐄[i] := by
  constructor
  · intro h1
    have h2 := mem_E_of_sq_kappa_eq h i hne hbot hx (one_mem _) (by rw [h1]; group)
    simpa using inv_mem h2
  · intro hxE
    exact A_mul_self h i (kappa_E_mem_A h i hxE)

omit [Finite G] [Finite K] in
theorem sq_kappa_conj_C {c : G} (hc : c ∈ 𝐂) (x : G) :
    (t⁻¹ * ((c * x * c⁻¹)⁻¹ * t * (c * x * c⁻¹))) * (t⁻¹ * ((c * x * c⁻¹)⁻¹ * t * (c * x * c⁻¹))) =
      c * ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) * c⁻¹ := by
  rw [kappa_conj_C hc x]
  group

theorem exists_P₀_sq_kappa_eq (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {u : G}
    (hu : u ∈ 𝐔[i]) : ∃ p ∈ 𝐏₀[i], (t⁻¹ * (p⁻¹ * t * p)) * (t⁻¹ * (p⁻¹ * t * p)) = u := by
  obtain ⟨_, e, he⟩ := quotient_P₁ h i hne hbot
  obtain ⟨q, hq⟩ := e.surjective ⟨u, hu⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hxu := congrArg Subtype.val hq
  rw [he] at hxu
  have hPE : 𝐏₀[i] ≤ normalizer (𝐄[i] : Set G) := fun _ hp =>
    mem_normalizer_of_conj_le fun _ he' =>
      conj_mem_E_of_normalizer_D h i (P₁_le i (mem_inf.mp hp).1) he'
  have hx : (x : G) ∈ ((𝐄[i] ⊔ 𝐏₀[i] : Subgroup G) : Set G) := by
    rw [E_sup_P₀ h i hne hbot]
    exact x.2
  rw [coe_mul_of_right_le_normalizer_left _ _ hPE, Set.mem_mul] at hx
  obtain ⟨e', he', p, hp, hep⟩ := hx
  refine ⟨p, hp, ?_⟩
  have hpP : p ∈ 𝐏₁[i] := (mem_inf.mp hp).1
  have he'P : e' ∈ 𝐏₁[i] := E_le_P₁ h i hne hbot he'
  have hxu' : (t⁻¹ * ((x : G)⁻¹ * t * x)) * (t⁻¹ * ((x : G)⁻¹ * t * x)) = u := hxu
  rw [← hxu', ← hep, sq_kappa_mul h i hne hbot he'P hpP,
    (sq_kappa_eq_one_iff h i hne hbot he'P).mpr he', one_mul]

omit [Finite G] in
theorem exists_torus_scalar (h : FCHyp L K n φ t) (i : Axis) :
    ∃ j₀ ∈ 𝐉, ∃ χ : K, χ ≠ 1 ∧ ∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u) := by
  have hK2 : 2 < Nat.card K := by have := h.four_le_card; omega
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne hK2 (1 : K)
  obtain ⟨δ, hδ, hδc⟩ := FCHyp.torus_trans (φ := φ) i (one_ne_zero (α := K)) hc0
  obtain ⟨r, s, -, -, hrs⟩ := exists_conj_zc (φ := φ) (inv_mem hδ)
  have hδc' : δ⁻¹⁻¹ * coordG φ i 1 * δ⁻¹ = coordG φ i c := by rw [inv_inv]; exact hδc
  refine ⟨δ⁻¹, inv_mem hδ, ?_⟩
  cases i
  · have hu : ∀ u : K, δ⁻¹⁻¹ * coordG φ Axis.one u * δ⁻¹ = coordG φ Axis.one (r * s * u) := by
      intro u
      rw [coordG_one_eq, coordG_one_eq, hrs, mul_zero]
    refine ⟨r * s, fun h1 => hc1 ?_, hu⟩
    have := (hu 1).symm.trans hδc'
    rw [h1, one_mul] at this
    exact coordG_injective φ _ this
  · have hu : ∀ u : K, δ⁻¹⁻¹ * coordG φ Axis.two u * δ⁻¹ = coordG φ Axis.two (r ^ 2 * u) := by
      intro u
      rw [coordG_two_eq, coordG_two_eq, hrs, mul_zero]
    refine ⟨r ^ 2, fun h1 => hc1 ?_, hu⟩
    have := (hu 1).symm.trans hδc'
    rw [h1, one_mul] at this
    exact coordG_injective φ _ this

@[expose] noncomputable def dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) : Subgroup G :=
  deltaSub 𝐏₀[i] 𝐅 j₀ (fun _ hp => conj_inv_torus_mem_P₀ h i hj₀ hp)
    (fun _ hp _ hf => conj_P₀_mem_F h i hne hbot hp hf)
    (fun _ hx _ hy => comm_P₀_mem_F h i hne hbot hx hy)

theorem F_le_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) : 𝐅 ≤ dSub h i hne hbot hj₀ := le_deltaSub (F_le_P₀ h i hne hbot)

theorem dSub_le_P₀ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) : dSub h i hne hbot hj₀ ≤ 𝐏₀[i] := deltaSub_le

theorem conj_P₀_mem_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {p : G} (hp : p ∈ 𝐏₀[i]) {x : G} (hx : x ∈ dSub h i hne hbot hj₀) :
    p * x * p⁻¹ ∈ dSub h i hne hbot hj₀ :=
  conj_mem_deltaSub (F_le_P₀ h i hne hbot) hp hx

theorem conj_torus_mem_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {j : G} (hj : j ∈ 𝐉) {x : G} (hx : x ∈ dSub h i hne hbot hj₀) :
    j * x * j⁻¹ ∈ dSub h i hne hbot hj₀ :=
  conj_comm_mem_deltaSub (torus_comm hj₀ hj) (fun _ hp => conj_torus_mem_P₀ h i hj hp)
    (fun _ hf => by simpa using conj_torus_mem_F h (inv_mem hj) hf) hx

theorem t_not_mem_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) : t ∉ dSub h i hne hbot hj₀ :=
  t_not_mem_deltaSub (t_mem_P₀ h i hne hbot) (t_not_mem_F h) h.setup.t_mul_t
    (torus_comm_t h hj₀) (fun _ hf => conj_torus_mem_F h hj₀ hf) (odd_card_sub_one h)
    (torus_pow_card_sub_one hj₀)

theorem dSub_inf_E0 (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) : dSub h i hne hbot hj₀ ⊓ 𝐄₀ = 𝐅 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (F_le_dSub h i hne hbot hj₀) (F_le_E0 h))
  obtain ⟨hxD, hxE⟩ := mem_inf.mp hx
  have htF : t ∈ normalizer (𝐅 : Set G) := H_le_normalizer_F h t_mem_H
  rcases mem_or_mul_mem h.setup.t_mul_t htF (by rw [(F_sup_t h).2]; exact hxE) with h1 | h1
  · exact h1
  · exfalso
    apply t_not_mem_dSub h i hne hbot hj₀
    have := mul_mem (F_le_dSub h i hne hbot hj₀ h1) (inv_mem hxD)
    rwa [mul_inv_cancel_right] at this

theorem exists_dSub_sq_kappa_eq (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {χ : K} (hχ : χ ≠ 1)
    (hj₀c : ∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u)) {u : G} (hu : u ∈ 𝐔[i]) :
    ∃ x ∈ dSub h i hne hbot hj₀, (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) = u := by
  obtain ⟨v, rfl⟩ := exists_coordG_eq φ i hu
  have hχ1 : χ + 1 ≠ 0 := fun h0 => hχ (CharTwo.add_eq_zero.mp h0)
  obtain ⟨y, hy, hyk⟩ := exists_P₀_sq_kappa_eq h i hne hbot (coordG_mem φ i (v / (χ + 1)))
  refine ⟨y⁻¹ * (j₀⁻¹ * y * j₀), delta_mem_deltaSub hy, ?_⟩
  have hyP : y ∈ 𝐏₁[i] := (mem_inf.mp hy).1
  have hy'P : j₀⁻¹ * y * j₀ ∈ 𝐏₁[i] := (mem_inf.mp (conj_inv_torus_mem_P₀ h i hj₀ hy)).1
  have hinv : (t⁻¹ * (y⁻¹⁻¹ * t * y⁻¹)) * (t⁻¹ * (y⁻¹⁻¹ * t * y⁻¹)) =
      ((t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y)))⁻¹ := by
    have h1 := sq_kappa_mul h i hne hbot hyP (inv_mem hyP)
    rw [(sq_kappa_eq_one_iff h i hne hbot (by rw [mul_inv_cancel]; exact one_mem _)).mpr
      (by rw [mul_inv_cancel]; exact one_mem _)] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have hconj : (t⁻¹ * ((j₀⁻¹ * y * j₀)⁻¹ * t * (j₀⁻¹ * y * j₀))) *
      (t⁻¹ * ((j₀⁻¹ * y * j₀)⁻¹ * t * (j₀⁻¹ * y * j₀))) =
      j₀⁻¹ * ((t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y))) * j₀ := by
    have := sq_kappa_conj_C (inv_mem (h.torus_le_C hj₀)) y
    simpa using this
  have hcinv : ∀ w : K, (coordG φ i w)⁻¹ = coordG φ i w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← coordG_add, CharTwo.add_self_eq_zero, coordG_zero])
  rw [sq_kappa_mul h i hne hbot (inv_mem hyP) hy'P, hinv, hconj, hyk, hj₀c, hcinv,
    ← coordG_add]
  congr 1
  field_simp
  ring

theorem quotient_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {χ : K} (hχ : χ ≠ 1)
    (hj₀c : ∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u)) :
    ∃ _ : (𝐅.subgroupOf (dSub h i hne hbot hj₀)).Normal,
      ∃ e : (↥(dSub h i hne hbot hj₀) ⧸ 𝐅.subgroupOf (dSub h i hne hbot hj₀)) ≃* ↥𝐔[i],
        ∀ x : dSub h i hne hbot hj₀, (e (x : ↥(dSub h i hne hbot hj₀) ⧸
          𝐅.subgroupOf (dSub h i hne hbot hj₀)) : G) =
            (t⁻¹ * ((x : G)⁻¹ * t * x)) * (t⁻¹ * ((x : G)⁻¹ * t * x)) := by
  have hP : ∀ x ∈ dSub h i hne hbot hj₀, x ∈ 𝐏₁[i] := fun x hx =>
    (mem_inf.mp (dSub_le_P₀ h i hne hbot hj₀ hx)).1
  refine exists_quotient_equiv_of_hom (fun x => (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)))
    (fun x hx => sq_kappa_mem_U h i hne hbot (hP x hx))
    (fun x hx y hy => sq_kappa_mul h i hne hbot (hP x hx) (hP y hy)) (fun x hx => ?_)
    (fun u hu => exists_dSub_sq_kappa_eq h i hne hbot hj₀ hχ hj₀c hu)
  rw [sq_kappa_eq_one_iff h i hne hbot (hP x hx)]
  constructor
  · intro hxE
    rw [← dSub_inf_E0 h i hne hbot hj₀, ← P₀_inf_E h i hne hbot]
    exact mem_inf.mpr ⟨hx, dSub_le_P₀ h i hne hbot hj₀ hx, hxE⟩
  · intro hxF
    exact E0_le_E i (F_le_E0 h hxF)

theorem card_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {χ : K} (hχ : χ ≠ 1)
    (hj₀c : ∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u)) :
    Nat.card (dSub h i hne hbot hj₀) = Nat.card K ^ 5 := by
  obtain ⟨_, e, -⟩ := quotient_dSub h i hne hbot hj₀ hχ hj₀c
  have h1 := card_eq_card_quotient_mul_card_subgroup (𝐅.subgroupOf (dSub h i hne hbot hj₀))
  rw [Nat.card_congr e.toEquiv, card_U, Nat.card_congr (subgroupOfEquivOfLe
    (F_le_dSub h i hne hbot hj₀)).toEquiv, card_F h] at h1
  rw [h1]
  ring

theorem dSub_sup_t (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {χ : K} (hχ : χ ≠ 1)
    (hj₀c : ∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u)) :
    dSub h i hne hbot hj₀ ⊔ zpowers t = 𝐏₀[i] := by
  have htN : zpowers t ≤ normalizer (dSub h i hne hbot hj₀ : Set G) := zpowers_le.mpr
    (mem_normalizer_of_conj_le fun _ hx =>
      conj_P₀_mem_dSub h i hne hbot hj₀ (t_mem_P₀ h i hne hbot) hx)
  have hinf : dSub h i hne hbot hj₀ ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxt⟩ := mem_inf.mp hx
    obtain ⟨k, hk⟩ := hxt
    have hk' : t ^ k = x := hk
    rcases zpow_eq_one_or_eq h.setup.t_mul_t k with h1 | h1
    · rw [← hk', h1]
      exact one_mem _
    · rw [← hk', h1] at hxD
      exact absurd hxD (t_not_mem_dSub h i hne hbot hj₀)
  refine eq_of_le_of_card_ge (sup_le (dSub_le_P₀ h i hne hbot hj₀)
    (zpowers_le.mpr (t_mem_P₀ h i hne hbot))) ?_
  have h1 := card_sup_mul_card_inf _ _ htN
  rw [hinf, card_bot, mul_one, card_dSub h i hne hbot hj₀ hχ hj₀c, Nat.card_zpowers,
    h.setup.order_t] at h1
  rw [card_P₀ h i hne hbot, h1]
  ring_nf
  exact le_rfl

theorem F_le_M (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐅 ≤ 𝐌₀[i] := closure_mono fun _ ⟨e, he, j, hj, hx⟩ =>
  ⟨e, E0_le_P₀ h i hne hbot he, j, hj, hx⟩

theorem M_eq_dSub (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : j₀ ∈ 𝐉) {χ : K} (hχ : χ ≠ 1)
    (hj₀c : ∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u)) :
    𝐌₀[i] = dSub h i hne hbot hj₀ := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨p, hp, j, hj, rfl⟩
    have hp' : p ∈ dSub h i hne hbot hj₀ ⊔ zpowers t := by
      rw [dSub_sup_t h i hne hbot hj₀ hχ hj₀c]
      exact hp
    have htD : t ∈ normalizer (dSub h i hne hbot hj₀ : Set G) :=
      mem_normalizer_of_conj_le fun _ hx =>
        conj_P₀_mem_dSub h i hne hbot hj₀ (t_mem_P₀ h i hne hbot) hx
    have hjD : ∀ x ∈ dSub h i hne hbot hj₀, j⁻¹ * x * j ∈ dSub h i hne hbot hj₀ :=
      fun x hx => by simpa using conj_torus_mem_dSub h i hne hbot hj₀ (inv_mem hj) hx
    rcases mem_or_mul_mem h.setup.t_mul_t htD hp' with h1 | h1
    · exact mul_mem (inv_mem h1) (hjD p h1)
    · have hjt : j⁻¹ * t = t * j⁻¹ := (Commute.inv_left (torus_comm_t h hj)).eq
      have e : p⁻¹ * (j⁻¹ * p * j) = (t * p)⁻¹ * (j⁻¹ * (t * p) * j) := by
        calc p⁻¹ * (j⁻¹ * p * j) = p⁻¹ * t⁻¹ * (t * j⁻¹) * p * j := by group
          _ = p⁻¹ * t⁻¹ * (j⁻¹ * t) * p * j := by rw [hjt]
          _ = (t * p)⁻¹ * (j⁻¹ * (t * p) * j) := by group
      rw [e]
      exact mul_mem (inv_mem h1) (hjD _ h1)
  · intro x hx
    obtain ⟨-, y, hy, hf⟩ := hx
    rw [show x = (y⁻¹ * (j₀⁻¹ * y * j₀)) * ((y⁻¹ * (j₀⁻¹ * y * j₀))⁻¹ * x) by group]
    exact mul_mem (subset_closure ⟨y, hy, j₀, hj₀, rfl⟩) (F_le_M h i hne hbot hf)

theorem exists_M_eq_dSub (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ j₀, ∃ hj₀ : j₀ ∈ 𝐉, ∃ χ : K, χ ≠ 1 ∧
      (∀ u : K, j₀⁻¹ * coordG φ i u * j₀ = coordG φ i (χ * u)) ∧
        𝐌₀[i] = dSub h i hne hbot hj₀ := by
  obtain ⟨j₀, hj₀, χ, hχ, hj₀c⟩ := exists_torus_scalar h i
  exact ⟨j₀, hj₀, χ, hχ, hj₀c, M_eq_dSub h i hne hbot hj₀ hχ hj₀c⟩

theorem M_le_P₀ (h : FCHyp L K n φ t) (i : Axis) : 𝐌₀[i] ≤ 𝐏₀[i] := by
  rw [closure_le]
  rintro _ ⟨p, hp, j, hj, rfl⟩
  exact mul_mem (inv_mem hp) (conj_inv_torus_mem_P₀ h i hj hp)

theorem card_M (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐌₀[i] = Nat.card K ^ 5 := by
  obtain ⟨j₀, hj₀, χ, hχ, hj₀c, heq⟩ := exists_M_eq_dSub h i hne hbot
  rw [heq]
  exact card_dSub h i hne hbot hj₀ hχ hj₀c

theorem M_inf_E0 (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐄₀ = 𝐅 := by
  obtain ⟨j₀, hj₀, -, -, -, heq⟩ := exists_M_eq_dSub h i hne hbot
  rw [heq]
  exact dSub_inf_E0 h i hne hbot hj₀

theorem M_sup_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊔ zpowers t = 𝐏₀[i] := by
  obtain ⟨j₀, hj₀, χ, hχ, hj₀c, heq⟩ := exists_M_eq_dSub h i hne hbot
  rw [heq]
  exact dSub_sup_t h i hne hbot hj₀ hχ hj₀c

theorem J_le_normalizer_M (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐌₀[i] : Set G) := by
  obtain ⟨j₀, hj₀, -, -, -, heq⟩ := exists_M_eq_dSub h i hne hbot
  rw [heq]
  exact fun j hj => mem_normalizer_of_conj_le fun _ hx =>
    conj_torus_mem_dSub h i hne hbot hj₀ hj hx

theorem t_mem_normalizer_M (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    t ∈ normalizer (𝐌₀[i] : Set G) := by
  obtain ⟨j₀, hj₀, -, -, -, heq⟩ := exists_M_eq_dSub h i hne hbot
  rw [heq]
  exact mem_normalizer_of_conj_le fun _ hx =>
    conj_P₀_mem_dSub h i hne hbot hj₀ (t_mem_P₀ h i hne hbot) hx

theorem M_inf_C (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐂 = 𝐙 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxC⟩ := mem_inf.mp hx
    have hxP := M_le_P₀ h i hxM
    have hk : t⁻¹ * (x⁻¹ * t * x) = 1 := kappa_eq_one_iff.mpr hxC
    have hxE : x ∈ 𝐄[i] := (sq_kappa_eq_one_iff h i hne hbot (mem_inf.mp hxP).1).mp
      (by rw [hk, mul_one])
    have hxE0 : x ∈ 𝐄₀ := by
      rw [← P₀_inf_E h i hne hbot]
      exact mem_inf.mpr ⟨hxP, hxE⟩
    have hxF : x ∈ 𝐅 := by
      rw [← M_inf_E0 h i hne hbot]
      exact mem_inf.mpr ⟨hxM, hxE0⟩
    rw [← C_inf_F h]
    exact mem_inf.mpr ⟨hxC, hxF⟩
  · exact le_inf ((ZP_le_F h).trans (F_le_M h i hne hbot))
      ((pull_mono φ (center_le_rootA i)).trans (A_le_C h i))

omit [Finite G] [Finite K] in
theorem sq_kappa_conj_torus (h : FCHyp L K n φ t) {j : G} (hj : j ∈ 𝐉) (x : G) :
    (t⁻¹ * ((j * x * j⁻¹)⁻¹ * t * (j * x * j⁻¹))) * (t⁻¹ * ((j * x * j⁻¹)⁻¹ * t * (j * x * j⁻¹))) =
      j * ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) * j⁻¹ :=
  sq_kappa_conj_C (h.torus_le_C hj) x

theorem M_inf_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐄[i] = 𝐅 := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (F_le_M h i hne hbot) ((F_le_E0 h).trans (E0_le_E i)))
  obtain ⟨hxM, hxE⟩ := mem_inf.mp hx
  have hxE0 : x ∈ 𝐄₀ := by
    rw [← P₀_inf_E h i hne hbot]
    exact mem_inf.mpr ⟨M_le_P₀ h i hxM, hxE⟩
  rw [← M_inf_E0 h i hne hbot]
  exact mem_inf.mpr ⟨hxM, hxE0⟩

end Complement

end NextCores

end CFSG.LocalAnalysis.SymplecticFourStandard
