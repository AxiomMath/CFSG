module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresProducts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace NextCores

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped Matrix Pointwise

section Normality

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

omit [Finite G] [Finite K] in
theorem mem_E0_of (k : Axis) {x : G} (h1 : x ∈ 𝐄[k]) (h2 : x ∈ 𝐄[k.swap]) : x ∈ 𝐄₀ := by
  cases k
  · exact mem_inf.mpr ⟨h1, h2⟩
  · exact mem_inf.mpr ⟨h2, h1⟩

theorem Hk_sup_Hk (h : FCHyp L K n φ t) (k : Axis) : (𝐇 ⊓ 𝐄[k]) ⊔ (𝐇 ⊓ 𝐄[k.swap]) = 𝐇 := by
  cases k
  · exact Hi_sup_Hi h
  · exact (sup_comm _ _).trans (Hi_sup_Hi h)

theorem T₁_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₁[i] ≤ 𝐍ₕ[i] :=
  (T₁_le_Y h i hne hbot).trans inf_le_left

theorem T₂_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₂[i.swap] ≤ 𝐍ₕ[i] :=
  (T₂_le_Y h i hne hbot).trans inf_le_left

theorem H_le_T₁ (h : FCHyp L K n φ t) (i : Axis) : 𝐇 ≤ 𝐓₁[i] :=
  (H_le_R h i).trans le_sup_left

theorem H_le_T₂ (h : FCHyp L K n φ t) (k : Axis) : 𝐇 ≤ 𝐓₂[k] :=
  (H_le_R h k).trans (R_le_T₂ k)

theorem isPGroup_T₁ (h : FCHyp L K n φ t) (i : Axis) : IsPGroup 2 𝐓₁[i] :=
  IsPGroup.to_sup_of_normal_right' (R_isPGroup h i) (CFSG.pCore_isPGroup.map _)
    (R_le_normalizer_P₁ h i)

theorem isPGroup_T₀ (h : FCHyp L K n φ t) (k : Axis) : IsPGroup 2 𝐓₀[k] :=
  IsPGroup.to_sup_of_normal_right' (R_isPGroup h k) (CFSG.pCore_isPGroup.map _)
    (R_le_normalizer_P₂ h k)

theorem isPGroup_T₂ (h : FCHyp L K n φ t) (k : Axis) : IsPGroup 2 𝐓₂[k] :=
  (isPGroup_T₀ h k).to_le inf_le_left

theorem mem_L_of_mem_Ks (h : FCHyp L K n φ t) (k : Axis) {x : G} (hxK : x ∈ 𝐊⋆)
    (hxE : x ∈ 𝐄[k]) : x ∈ 𝐋[k] := by
  have htN : t ∈ normalizer (𝐋[k] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h k t_mem_H hl
  have hx : x ∈ 𝐋[k] ⊔ zpowers t := by
    rw [L_sup_t h k]
    exact mem_inf.mpr ⟨Ks_le_H h hxK, hxE⟩
  rcases mem_or_mul_mem h.setup.t_mul_t htN hx with h1 | h1
  · exact h1
  · exfalso
    apply t_not_mem_Ks h
    have := mul_mem (L_le_Ks h k h1) (inv_mem hxK)
    rwa [mul_inv_cancel_right] at this

theorem kappa_Nhat_mem_Ks (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐍ₕ[i]) : t⁻¹ * (x * t * x⁻¹) ∈ 𝐊⋆ := by
  have htKs : t ∈ normalizer (𝐊⋆ : Set G) :=
    mem_normalizer_of_conj_le fun _ hk => conj_H_mem_Ks h t_mem_H hk
  have hxK := Nhat_le_normalizer_Ks h i hbot hx
  have h1 : x * t * x⁻¹ ∈ 𝐇 := (mem_normalizer_iff.mp (mem_inf.mp hx).1 t).mp t_mem_H
  have h2 : x * t * x⁻¹ ∉ 𝐊⋆ := fun h2 =>
    t_not_mem_Ks h ((mem_normalizer_iff.mp hxK t).mpr h2)
  have h3 := (mem_or_mul_mem h.setup.t_mul_t htKs
    (by rw [(Ks_sup_t h).2]; exact h1)).resolve_left h2
  rwa [h.twoCore.t_inv]

theorem comm_Nhat_H_mem_Ks (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐍ₕ[i]) {y : G} (hy : y ∈ 𝐇) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐊⋆ := by
  have htKs : t ∈ normalizer (𝐊⋆ : Set G) :=
    mem_normalizer_of_conj_le fun _ hk => conj_H_mem_Ks h t_mem_H hk
  have hxK := Nhat_le_normalizer_Ks h i hbot hx
  rcases mem_or_mul_mem h.setup.t_mul_t htKs (by rw [(Ks_sup_t h).2]; exact hy) with h1 | h1
  · exact mul_mem ((mem_normalizer_iff.mp hxK y).mp h1) (inv_mem h1)
  · have hy' : y = t⁻¹ * (t * y) := by group
    generalize t * y = k at h1 hy'
    subst hy'
    have h2 := kappa_Nhat_mem_Ks h i hbot hx
    have h3 : t⁻¹ * (x * k * x⁻¹ * k⁻¹) * t⁻¹⁻¹ ∈ 𝐊⋆ :=
      (mem_normalizer_iff.mp (inv_mem htKs) _).mp
        (mul_mem ((mem_normalizer_iff.mp hxK k).mp h1) (inv_mem h1))
    rw [show x * (t⁻¹ * k) * x⁻¹ * (t⁻¹ * k)⁻¹ =
      (t⁻¹ * (x * t * x⁻¹))⁻¹ * (t⁻¹ * (x * k * x⁻¹ * k⁻¹) * t⁻¹⁻¹) by group]
    exact mul_mem (inv_mem h2) h3

theorem comm_H_mem_L (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (k : Axis) {T : Subgroup G} (hTN : T ≤ 𝐍ₕ[i]) (hHT : 𝐇 ≤ T)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ 𝐄[k]) {x : G} (hx : x ∈ T) {y : G}
    (hy : y ∈ 𝐇) : x * y * x⁻¹ * y⁻¹ ∈ 𝐋[k] :=
  mem_L_of_mem_Ks h k (comm_Nhat_H_mem_Ks h i hbot (hTN hx) hy) (hc x hx y (hHT hy))

@[expose] noncomputable def kerL (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    Subgroup G :=
  quotCent 𝐍ₕ[i] 𝐇 𝐋[k] (fun _ hg _ hy => (mem_normalizer_iff.mp (mem_inf.mp hg).1 _).mp hy)
    (fun _ hg _ hl => (mem_normalizer_iff.mp (Nhat_le_normalizer_L h i hne hbot k hg) _).mp hl)

theorem mem_kerL (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {g : G} :
    g ∈ kerL h i hne hbot k ↔ g ∈ 𝐍ₕ[i] ∧ ∀ y ∈ 𝐇, g * y * g⁻¹ * y⁻¹ ∈ 𝐋[k] :=
  mem_quotCent

theorem kerL_le_Y (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : kerL h i hne hbot k ≤ 𝐘[i, k] := by
  intro x hx
  obtain ⟨hxN, hxc⟩ := (mem_kerL h i hne hbot k).mp hx
  have htN : t ∈ normalizer (𝐋[k] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h k t_mem_H hl
  refine mem_inf.mpr ⟨hxN, (mem_normalizer_Hk_iff h i hne hbot k hxN).mpr ?_⟩
  have h2 := (mem_normalizer_iff.mp (inv_mem htN) _).mp (hxc t t_mem_H)
  rwa [show t⁻¹ * (x * t * x⁻¹ * t⁻¹) * t⁻¹⁻¹ = t⁻¹ * (x * t * x⁻¹) by group] at h2

theorem mem_ZP_of_mem_L_A (h : FCHyp L K n φ t) (k : Axis) {y : G} (hy : y ∈ 𝐋[k])
    (hyA : y ∈ 𝐀[k.swap]) : y ∈ 𝐙 := by
  have hZ : 𝐀[Axis.one] ⊓ 𝐀[Axis.two] = 𝐙 := by
    rw [← pull_inf]
    exact congrArg (pull φ) radA1_inf_radA2
  rw [← SetLike.mem_coe, ← L_mul h] at hy
  obtain ⟨f, hf, a, ha, rfl⟩ := hy
  have hP : ∀ m, 𝐀[m] ≤ 𝐏 := fun m => pull_mono φ (rootA_le_antiUnipotent m)
  have hfZ : f ∈ 𝐙 := by
    rw [← F_inf_P h]
    refine mem_inf.mpr ⟨hf, ?_⟩
    have := mul_mem (hP _ hyA) (inv_mem (hP _ ha))
    rwa [mul_inv_cancel_right] at this
  have hyk : f * a ∈ 𝐀[k] := mul_mem (pull_mono φ (center_le_rootA k) hfZ) ha
  rw [← hZ]
  cases k
  · exact mem_inf.mpr ⟨hyk, hyA⟩
  · exact mem_inf.mpr ⟨hyA, hyk⟩

theorem kerL_le_sup_J (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {T : Subgroup G}
    (hY : (𝐘[i, k] : Set G) = (T : Set G) * (𝐍𝐑[k] : Set G)) (hRT : 𝐑[k] ≤ T)
    (hTC : T ≤ kerL h i hne hbot k) {x : G} (hx : x ∈ kerL h i hne hbot k) : x ∈ T ⊔ 𝐉 := by
  have hxY : x ∈ ((𝐘[i, k] : Subgroup G) : Set G) := kerL_le_Y h i hne hbot k hx
  rw [hY, Set.mem_mul] at hxY
  obtain ⟨τ, hτ, m, hm, rfl⟩ := hxY
  have hm' : m ∈ ((𝐍𝐑[k] : Subgroup G) : Set G) := hm
  rw [← NRB_eq' h i hne hbot k, Set.mem_mul] at hm'
  obtain ⟨r, hr, c, hc, rfl⟩ := hm'
  have hτr : τ * r ∈ T := mul_mem hτ (hRT hr)
  have hcC' : c ∈ kerL h i hne hbot k := by
    have := mul_mem (inv_mem (hTC hτr)) hx
    rwa [show (τ * r)⁻¹ * (τ * (r * c)) = c by group] at this
  have hcN : ∀ m, c ∈ 𝐍[m] := fun m => normalizer_Q_le_N h i hne hbot m (mem_inf.mp hc).2
  have hcA : ∀ a ∈ 𝐀[k.swap], c * a * c⁻¹ * a⁻¹ ∈ 𝐙 := fun a ha =>
    mem_ZP_of_mem_L_A h k (((mem_kerL h i hne hbot k).mp hcC').2 a (A_le_H h _ ha))
      (mul_mem ((mem_normalizer_iff.mp (h.N_le_normalizer_A _ (hcN _)) a).mp ha) (inv_mem ha))
  have hcQJ := mem_Q_sup_J h k (mem_inf.mp hc).1 hcN hcA
  rw [show τ * (r * c) = (τ * r) * c by group]
  exact mul_mem (mem_sup_left hτr)
    ((sup_le_sup_right ((le_sup_left : 𝐐 ≤ 𝐑[k]).trans hRT) 𝐉) hcQJ)

theorem conj_mem_of_kerL (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hJT : 𝐉 ≤ normalizer (T : Set G)) (hTC : T ≤ kerL h i hne hbot k)
    (hCT : ∀ x ∈ kerL h i hne hbot k, x ∈ T ⊔ 𝐉) {g : G} (hg : g ∈ 𝐍ₕ[i]) {x : G}
    (hx : x ∈ T) : g * x * g⁻¹ ∈ T := by
  have hs : g * x * g⁻¹ ∈ kerL h i hne hbot k := conj_mem_quotCent hg (hTC hx)
  obtain ⟨e, he⟩ := exists_two_pow_eq_one hT2 hx
  refine mem_of_two_pow hJT (odd_card_sub_one h) (fun j hj => torus_pow_card_sub_one hj)
    (hCT _ hs) (e := e) ?_
  rw [conj_pow, he, mul_one, mul_inv_cancel]

theorem J_le_normalizer_T₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐓₁[i] : Set G) :=
  (J_le_NRB h i hne hbot i).trans
    ((NRB_le h i hne hbot i).trans (Y₁_le_normalizer_T₁ h i hne hbot))

theorem J_le_normalizer_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐓₂[i.swap] : Set G) :=
  (J_le_NRB h i hne hbot i.swap).trans (NR_le_normalizer_T₂ h _)

theorem T₁_le_kerL (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₁[i] ≤ kerL h i hne hbot i := fun _ hx =>
  (mem_kerL h i hne hbot i).mpr ⟨T₁_le_Nhat h i hne hbot hx, fun _ hy =>
    comm_H_mem_L h i hbot i (T₁_le_Nhat h i hne hbot) (H_le_T₁ h i)
      (fun _ ha _ hb => comm_T₁_mem_E h i hne hbot ha hb) hx hy⟩

theorem T₂_le_kerL (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₂[i.swap] ≤ kerL h i hne hbot i.swap := fun _ hx =>
  (mem_kerL h i hne hbot i.swap).mpr ⟨T₂_le_Nhat h i hne hbot hx, fun _ hy =>
    comm_H_mem_L h i hbot i.swap (T₂_le_Nhat h i hne hbot) (H_le_T₂ h _)
      (fun _ ha _ hb => comm_T₂_mem_E h i hne hbot ha hb) hx hy⟩

theorem conj_mem_T₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} (hg : g ∈ 𝐍ₕ[i]) {x : G} (hx : x ∈ 𝐓₁[i]) :
    g * x * g⁻¹ ∈ 𝐓₁[i] :=
  conj_mem_of_kerL h i hne hbot i (isPGroup_T₁ h i) (J_le_normalizer_T₁ h i hne hbot)
    (T₁_le_kerL h i hne hbot) (fun _ hy => kerL_le_sup_J h i hne hbot i (Y₁_eq h i hne hbot)
      le_sup_left (T₁_le_kerL h i hne hbot) hy) hg hx

theorem conj_mem_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} (hg : g ∈ 𝐍ₕ[i]) {x : G}
    (hx : x ∈ 𝐓₂[i.swap]) : g * x * g⁻¹ ∈ 𝐓₂[i.swap] :=
  conj_mem_of_kerL h i hne hbot i.swap (isPGroup_T₂ h _) (J_le_normalizer_T₂ h i hne hbot)
    (T₂_le_kerL h i hne hbot) (fun _ hy => kerL_le_sup_J h i hne hbot i.swap (Y₂_mul h i hne hbot)
      (R_le_T₂ _) (T₂_le_kerL h i hne hbot) hy) hg hx

theorem Tbar_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓̄[i] ≤ 𝐍ₕ[i] :=
  sup_le (T₁_le_Nhat h i hne hbot) (T₂_le_Nhat h i hne hbot)

theorem T₁_le_normalizer_T₂ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓₁[i] ≤ normalizer (𝐓₂[i.swap] : Set G) := fun _ hx =>
  mem_normalizer_of_conj_le fun _ hy => conj_mem_T₂ h i hne hbot (T₁_le_Nhat h i hne hbot hx) hy

theorem T₂_le_normalizer_T₁ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓₂[i.swap] ≤ normalizer (𝐓₁[i] : Set G) := fun _ hx =>
  mem_normalizer_of_conj_le fun _ hy => conj_mem_T₁ h i hne hbot (T₂_le_Nhat h i hne hbot hx) hy

theorem Tbar_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐓₁[i] : Set G) * (𝐓₂[i.swap] : Set G) = (𝐓̄[i] : Set G) :=
  (coe_mul_of_left_le_normalizer_right _ _ (T₁_le_normalizer_T₂ h i hne hbot)).symm

theorem isPGroup_Tbar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : IsPGroup 2 𝐓̄[i] :=
  IsPGroup.to_sup_of_normal_right' (isPGroup_T₁ h i) (isPGroup_T₂ h _)
    (T₁_le_normalizer_T₂ h i hne hbot)

theorem conj_mem_Tbar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} (hg : g ∈ 𝐍ₕ[i]) {x : G} (hx : x ∈ 𝐓̄[i]) :
    g * x * g⁻¹ ∈ 𝐓̄[i] :=
  conj_mem_sup (fun _ hy => conj_mem_T₁ h i hne hbot hg hy)
    (fun _ hy => conj_mem_T₂ h i hne hbot hg hy) hx

theorem conj_mem_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} (hg : g ∈ 𝐍ₕ[i]) {x : G} (hx : x ∈ 𝐓₃[i]) :
    g * x * g⁻¹ ∈ 𝐓₃[i] :=
  mem_inf.mpr ⟨conj_mem_T₁ h i hne hbot hg (mem_inf.mp hx).1,
    conj_mem_T₂ h i hne hbot hg (mem_inf.mp hx).2⟩

theorem J_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ 𝐍ₕ[i] := fun _ hj =>
  (mem_inf.mp (NRB_le h i hne hbot i (J_le_NRB h i hne hbot i hj))).1

theorem Tbar_comm_U (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓̄[i]) {u : G} (hu : u ∈ 𝐔[i]) :
    x * u * x⁻¹ = u :=
  comm_U_of_two_group h i (isPGroup_Tbar h i hne hbot)
    (fun _ hy => (mem_inf.mp (Tbar_le_Nhat h i hne hbot hy)).2)
    (fun _ hj => mem_normalizer_of_conj_le fun _ hy =>
      conj_mem_Tbar h i hne hbot (J_le_Nhat h i hne hbot hj) hy) hx hu

theorem mem_Q_of_Tbar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {c : G} (hc : c ∈ 𝐂 ⊓ normalizer (𝐐 : Set G))
    (hcT : c ∈ 𝐓̄[i]) : c ∈ 𝐐 := by
  have hcQJ := mem_Q_sup_J_of_cent h i (mem_inf.mp hc).1
    (fun m => normalizer_Q_le_N h i hne hbot m (mem_inf.mp hc).2)
    (fun _ hu => Tbar_comm_U h i hne hbot hcT hu)
  obtain ⟨e, he⟩ := exists_two_pow_eq_one (isPGroup_Tbar h i hne hbot) hcT
  exact mem_of_two_pow h.setup.diagTorus_le_normalizer (odd_card_sub_one h)
    (fun j hj => torus_pow_card_sub_one hj) hcQJ he

theorem mem_T₂_of_T₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₁[i])
    (hxH : x ∈ normalizer ((𝐇 ⊓ 𝐄[i.swap] : Subgroup G) : Set G)) : x ∈ 𝐓₂[i.swap] := by
  have hxY : x ∈ ((𝐘[i, i.swap] : Subgroup G) : Set G) :=
    mem_inf.mpr ⟨T₁_le_Nhat h i hne hbot hx, hxH⟩
  rw [Y₂_mul h i hne hbot, Set.mem_mul] at hxY
  obtain ⟨τ, hτ, m, hm, rfl⟩ := hxY
  have hm' : m ∈ ((𝐍𝐑[i.swap] : Subgroup G) : Set G) := hm
  rw [← NRB_eq' h i hne hbot i.swap, Set.mem_mul] at hm'
  obtain ⟨r, hr, c, hc, rfl⟩ := hm'
  have hτr : τ * r ∈ 𝐓₂[i.swap] := mul_mem hτ (R_le_T₂ _ hr)
  have hcT : c ∈ 𝐓̄[i] := by
    have := mul_mem (inv_mem (mem_sup_right (S := 𝐓₁[i]) hτr)) (mem_sup_left (T := 𝐓₂[i.swap]) hx)
    rwa [show (τ * r)⁻¹ * (τ * (r * c)) = c by group] at this
  rw [show τ * (r * c) = (τ * r) * c by group]
  exact mul_mem hτr (((le_sup_left : 𝐐 ≤ 𝐑[i.swap]).trans (R_le_T₂ _))
    (mem_Q_of_Tbar h i hne hbot hc hcT))

theorem T₃_eq_T₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐓₃[i] = 𝐓₁[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i.swap] : Subgroup G) : Set G) :=
  le_antisymm (fun _ hx => mem_inf.mpr ⟨(mem_inf.mp hx).1,
      (mem_inf.mp (T₂_le_Y h i hne hbot (mem_inf.mp hx).2)).2⟩)
    fun _ hx => mem_inf.mpr ⟨(mem_inf.mp hx).1,
      mem_T₂_of_T₁ h i hne hbot (mem_inf.mp hx).1 (mem_inf.mp hx).2⟩

theorem R_inf_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐑[i] ⊓ 𝐓₂[i.swap] = 𝐇 := by
  apply le_antisymm
  · intro x hx
    rw [← R_inf_normalizer_Hj h i hbot]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (T₂_le_Y h i hne hbot (mem_inf.mp hx).2)).2⟩
  · exact le_inf (H_le_R h i) (H_le_T₂ h _)

theorem R_swap_inf_T₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐑[i.swap] ⊓ 𝐓₁[i] = 𝐇 := by
  apply le_antisymm
  · intro x hx
    rw [← R_swap_inf_normalizer_Hi h i hne hbot]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (T₁_le_Y h i hne hbot (mem_inf.mp hx).2)).2⟩
  · exact le_inf (H_le_R h _) (H_le_T₁ h i)

theorem H_le_T₃ (h : FCHyp L K n φ t) (i : Axis) : 𝐇 ≤ 𝐓₃[i] :=
  le_inf (H_le_T₁ h i) (H_le_T₂ h _)

theorem T₃_sup_R (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₃[i] ⊔ 𝐑[i] = 𝐓₁[i] := by
  apply le_antisymm (sup_le inf_le_left le_sup_left)
  intro x hx
  obtain ⟨y, hy, r, hr, rfl⟩ := (first_index h i hne hbot i.swap).2 x (T₁_le_Nhat h i hne hbot hx)
  rw [swap_swap] at hr
  have hyT : y ∈ 𝐓₁[i] := by
    have := mul_mem hx (inv_mem (le_sup_left (b := 𝐏₁[i]) hr))
    rwa [mul_inv_cancel_right] at this
  have hy3 : y ∈ 𝐓₃[i] := by
    rw [T₃_eq_T₁ h i hne hbot]
    exact mem_inf.mpr ⟨hyT, (mem_inf.mp hy).2⟩
  exact mul_mem (mem_sup_left hy3) (mem_sup_right hr)

theorem card_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐓₃[i] = 2 * Nat.card K ^ 7 := by
  have hRN : 𝐑[i] ≤ normalizer (𝐓₃[i] : Set G) := fun _ hr =>
    mem_normalizer_of_conj_le fun _ hx =>
      conj_mem_T₃ h i hne hbot (R_le_Nhat h i hne hbot i hr) hx
  have h1 := card_sup_mul_card_inf 𝐓₃[i] 𝐑[i] hRN
  have hinf : 𝐓₃[i] ⊓ 𝐑[i] = 𝐇 := by
    rw [← R_inf_T₂ h i hne hbot]
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩
      exact ⟨⟨le_sup_left (b := 𝐏₁[i]) h3, h2⟩, h3⟩
  rw [T₃_sup_R h i hne hbot, hinf, card_T₁ h i hne hbot, h.H_facts.2.2, card_R h i] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 7)) ?_
  rw [← h1]
  ring

theorem sq_T₃_mem_E0 (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₃[i]) : x * x ∈ 𝐄₀ :=
  mem_E0_of i (sq_T₁_mem_E h i hne hbot (mem_inf.mp hx).1)
    (sq_T₂_mem_E h i hne hbot (mem_inf.mp hx).2)

theorem sq_T₃_mem_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₃[i]) : x * x ∈ 𝐅 := by
  by_contra hxF
  have htt := h.setup.t_mul_t
  have htF : t ∈ normalizer (𝐅 : Set G) := H_le_normalizer_F h t_mem_H
  have hsplit : ∀ y ∈ 𝐄₀, y ∈ 𝐅 ∨ (x * x)⁻¹ * y ∈ 𝐅 := by
    intro y hy
    rcases mem_or_mul_mem htt htF (by rw [(F_sup_t h).2]; exact hy) with h1 | h1
    · exact Or.inl h1
    · right
      have h2 := (mem_or_mul_mem htt htF
        (by rw [(F_sup_t h).2]; exact sq_T₃_mem_E0 h i hne hbot hx)).resolve_left hxF
      have := mul_mem (inv_mem h2) h1
      rwa [show (t * (x * x))⁻¹ * (t * y) = (x * x)⁻¹ * y by group] at this
  have hEn : ∀ e ∈ 𝐄[i], ∀ y ∈ 𝐄₀, e * y * e⁻¹ ∈ 𝐄₀ := by
    intro e he y hy
    have heN : e ∈ 𝐍ₕ[i] := R_le_Nhat h i hne hbot i (mem_sup_right he)
    have heF := Nhat_le_normalizer_F h i hbot heN
    rcases hsplit y hy with h1 | h1
    · exact F_le_E0 h ((mem_normalizer_iff.mp heF y).mp h1)
    · have h2 : e * (x * x) * e⁻¹ ∈ 𝐄₀ := by
        rw [show e * (x * x) * e⁻¹ = (e * x * e⁻¹) * (e * x * e⁻¹) by group]
        exact sq_T₃_mem_E0 h i hne hbot (conj_mem_T₃ h i hne hbot heN hx)
      rw [show e * y * e⁻¹ = (e * (x * x) * e⁻¹) * (e * ((x * x)⁻¹ * y) * e⁻¹) by group]
      exact mul_mem h2 (F_le_E0 h ((mem_normalizer_iff.mp heF _).mp h1))
  have hAZ : 𝐀[i] ≤ 𝐙 := by
    intro a ha
    have hmem : t * a ∈ {y : G | ∃ e ∈ 𝐄[i], y = e⁻¹ * t * e} := by
      rw [orbit_E h i]
      exact ⟨a, ha, rfl⟩
    obtain ⟨e, he, hea⟩ := hmem
    have h1 : t * a ∈ 𝐄₀ := by
      rw [hea]
      have := hEn e⁻¹ (inv_mem he) t (t_mem_E0 h)
      rwa [inv_inv] at this
    have h2 : a ∈ 𝐄₀ ⊓ 𝐐 := by
      refine mem_inf.mpr ⟨?_, mem_sup_left (pull_mono φ (rootA_le_antiUnipotent i) ha)⟩
      have := mul_mem (inv_mem (t_mem_E0 h)) h1
      rwa [inv_mul_cancel_left] at this
    rw [E0_inf_Q h] at h2
    rcases (mem_zpowers_sup_iff htt (fun w hw => h.twoCore.comm (pull_le φ _ hw))).mp h2 with
      h3 | h3
    · exact h3
    · exfalso
      apply h.twoCore.t_not_mem
      have := mul_mem (pull_le φ _ h3) (inv_mem (pull_le φ _ ha))
      rwa [mul_inv_cancel_right] at this
  have h3 := card_le_of_le hAZ
  rw [card_pull, card_rootA, FCHyp.card_ZP] at h3
  have : Nat.card K ^ 2 < Nat.card K ^ 3 :=
    Nat.pow_lt_pow_right (by have := h.four_le_card; omega) (by norm_num)
  omega

theorem card_Tbar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐓̄[i] = 2 * Nat.card K ^ 9 := by
  have h1 := card_sup_mul_card_inf 𝐓₁[i] 𝐓₂[i.swap] (T₂_le_normalizer_T₁ h i hne hbot)
  rw [card_T₃ h i hne hbot, card_T₁ h i hne hbot, card_T₂ h i hne hbot] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 7)) ?_
  rw [h1]
  ring

theorem R_sup_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₂[i.swap] ⊔ 𝐑[i] = 𝐓̄[i] := by
  refine eq_of_le_of_card_ge (sup_le le_sup_right
    ((le_sup_left : 𝐑[i] ≤ 𝐓₁[i]).trans le_sup_left)) ?_
  have hRN : 𝐑[i] ≤ normalizer (𝐓₂[i.swap] : Set G) := fun _ hr =>
    mem_normalizer_of_conj_le fun _ hx =>
      conj_mem_T₂ h i hne hbot (R_le_Nhat h i hne hbot i hr) hx
  have h1 := card_sup_mul_card_inf 𝐓₂[i.swap] 𝐑[i] hRN
  have e1 : 𝐓₂[i.swap] ⊓ 𝐑[i] = 𝐇 := (inf_comm _ _).trans (R_inf_T₂ h i hne hbot)
  rw [e1, card_T₂ h i hne hbot, card_R h i, h.H_facts.2.2] at h1
  rw [card_Tbar h i hne hbot]
  have hq : 0 < Nat.card K := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 6)) ?_).symm.le
  rw [h1]
  ring

theorem Tbar_inf_T₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓̄[i] ⊓ 𝐓₀[i.swap] = 𝐓₂[i.swap] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hx0⟩ := mem_inf.mp hx
    have hxH : x ∈ normalizer ((𝐇 : Subgroup G) : Set G) :=
      (mem_inf.mp (Tbar_le_Nhat h i hne hbot hxT)).1
    have hxE : x ∈ normalizer (𝐄[i.swap] : Set G) := (mem_inf.mp (T₀_le_En h _ hx0)).1
    refine mem_inf.mpr ⟨hx0, mem_normalizer_of_conj_le fun r hr => ?_⟩
    rw [R_eq_H_sup_E h i.swap] at hr ⊢
    exact conj_mem_sup (fun y hy => (mem_normalizer_iff.mp hxH y).mp hy)
      (fun e he => (mem_normalizer_iff.mp hxE e).mp he) hr
  · exact le_inf le_sup_right inf_le_left

theorem E_inf_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i] ⊓ 𝐏₂[i.swap] = 𝐄₀ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, hxP⟩ := mem_inf.mp hx
    have hxR : x ∈ 𝐑[i] := mem_sup_right hxE
    have hxT : x ∈ 𝐓₂[i.swap] := by
      rw [← Tbar_inf_T₀ h i hne hbot]
      exact mem_inf.mpr ⟨mem_sup_left (mem_sup_left hxR), mem_sup_right hxP⟩
    have hxH : x ∈ 𝐇 := by
      rw [← R_inf_T₂ h i hne hbot]
      exact mem_inf.mpr ⟨hxR, hxT⟩
    have hxEj : x ∈ 𝐄[i.swap] := by
      rw [← R_inf_P₂ h i hne hbot]
      exact mem_inf.mpr ⟨H_le_R h _ hxH, hxP⟩
    exact mem_E0_of i hxE hxEj
  · exact le_inf (E0_le_E i) ((E0_le_E i.swap).trans (E_le_P₂ h i hne hbot))

theorem E_swap_inf_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i.swap] ⊓ 𝐏₁[i] = 𝐄₀ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, hxP⟩ := mem_inf.mp hx
    have hxH : x ∈ 𝐇 := by
      rw [← R_swap_inf_T₁ h i hne hbot]
      exact mem_inf.mpr ⟨mem_sup_right hxE, mem_sup_right hxP⟩
    have hxEi : x ∈ 𝐄[i] := by
      rw [← R_inf_P₁ h i hne hbot]
      exact mem_inf.mpr ⟨H_le_R h _ hxH, hxP⟩
    exact mem_E0_of i hxEi hxE
  · exact le_inf (E0_le_E i.swap) ((E0_le_E i).trans (E_le_P₁ h i hne hbot))

theorem P₀_le_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₀[i] ≤ 𝐓₃[i] := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨mem_sup_right h1, ?_⟩
  rw [← Tbar_inf_T₀ h i hne hbot]
  exact mem_inf.mpr ⟨mem_sup_left (mem_sup_right h1), mem_sup_right h2⟩

theorem T₃_inf_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₃[i] ⊓ 𝐄[i] = 𝐇 ⊓ 𝐄[i] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, h2⟩
    rw [← R_inf_T₂ h i hne hbot]
    exact mem_inf.mpr ⟨mem_sup_right h2, (mem_inf.mp h1).2⟩
  · exact inf_le_inf_right _ (H_le_T₃ h i)

theorem T₃_inf_E_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₃[i] ⊓ 𝐄[i.swap] = 𝐇 ⊓ 𝐄[i.swap] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, h2⟩
    rw [← R_swap_inf_T₁ h i hne hbot]
    exact mem_inf.mpr ⟨mem_sup_right h2, (mem_inf.mp h1).1⟩
  · exact inf_le_inf_right _ (H_le_T₃ h i)

theorem E_sup_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i] ⊔ 𝐓₃[i] = 𝐓₁[i] := by
  refine eq_of_le_of_card_ge (sup_le ((le_sup_right : 𝐄[i] ≤ 𝐑[i]).trans le_sup_left)
    inf_le_left) ?_
  have hTE : 𝐓₃[i] ≤ normalizer (𝐄[i] : Set G) := fun _ hx =>
    mem_normalizer_of_conj_le fun _ he =>
      conj_mem_E_of_normalizer_D h i (T₁_le_Dn h i (mem_inf.mp hx).1) he
  have h1 := card_sup_mul_card_inf 𝐄[i] 𝐓₃[i] hTE
  have e1 : 𝐄[i] ⊓ 𝐓₃[i] = 𝐇 ⊓ 𝐄[i] := (inf_comm _ _).trans (T₃_inf_E h i hne hbot)
  rw [e1, card_Hi h i, card_E h i, card_T₃ h i hne hbot] at h1
  rw [card_T₁ h i hne hbot]
  have hq : 0 < Nat.card K := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 5)) ?_).symm.le
  rw [h1]
  ring

theorem E_swap_sup_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i.swap] ⊔ 𝐓₃[i] = 𝐓₂[i.swap] := by
  refine eq_of_le_of_card_ge (sup_le ((le_sup_right : 𝐄[i.swap] ≤ 𝐑[i.swap]).trans
    (R_le_T₂ _)) inf_le_right) ?_
  have hTE : 𝐓₃[i] ≤ normalizer (𝐄[i.swap] : Set G) := fun _ hx =>
    (mem_inf.mp (T₀_le_En h _ (mem_inf.mp (mem_inf.mp hx).2).1)).1
  have h1 := card_sup_mul_card_inf 𝐄[i.swap] 𝐓₃[i] hTE
  have e1 : 𝐄[i.swap] ⊓ 𝐓₃[i] = 𝐇 ⊓ 𝐄[i.swap] :=
    (inf_comm _ _).trans (T₃_inf_E_swap h i hne hbot)
  rw [e1, card_Hi h _, card_E h _, card_T₃ h i hne hbot] at h1
  rw [card_T₂ h i hne hbot]
  have hq : 0 < Nat.card K := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 5)) ?_).symm.le
  rw [h1]
  ring

theorem P₁_sup_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ⊔ 𝐓₃[i] = 𝐓₁[i] := by
  exact le_antisymm (sup_le le_sup_right inf_le_left)
    ((E_sup_T₃ h i hne hbot).symm.le.trans (sup_le_sup_right (E_le_P₁ h i hne hbot) _))

theorem P₂_sup_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₂[i.swap] ⊔ 𝐓₃[i] = 𝐓₀[i.swap] := by
  apply le_antisymm (sup_le le_sup_right ((inf_le_right : 𝐓₃[i] ≤ 𝐓₂[i.swap]).trans inf_le_left))
  exact sup_le ((R_le_T₂ _).trans ((E_swap_sup_T₃ h i hne hbot).symm.le.trans
    (sup_le_sup_right (E_le_P₂ h i hne hbot) _))) le_sup_left

theorem card_P₁_inf_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card (𝐏₁[i] ⊓ 𝐓₃[i] : Subgroup G) = 2 * Nat.card K ^ 6 := by
  have hTP : 𝐓₃[i] ≤ normalizer (𝐏₁[i] : Set G) := fun _ hx =>
    mem_normalizer_of_conj_le fun _ hp => conj_mem_P₁ i (T₁_le_Dn h i (mem_inf.mp hx).1) hp
  have h1 := card_sup_mul_card_inf 𝐏₁[i] 𝐓₃[i] hTP
  rw [P₁_sup_T₃ h i hne hbot, card_T₁ h i hne hbot, card_P₁ h i hne hbot,
    card_T₃ h i hne hbot] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left (mul_pos two_pos (pow_pos hq 8)) ?_
  rw [h1]
  ring

theorem card_P₂_inf_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    Nat.card (𝐏₂[i.swap] ⊓ 𝐓₃[i] : Subgroup G) = 2 * Nat.card K ^ 6 := by
  have hTP : 𝐓₃[i] ≤ normalizer (𝐏₂[i.swap] : Set G) := fun _ hx =>
    mem_normalizer_of_conj_le fun _ hp =>
      conj_mem_P₂ _ (T₀_le_En h _ (mem_inf.mp (mem_inf.mp hx).2).1) hp
  have h1 := card_sup_mul_card_inf 𝐏₂[i.swap] 𝐓₃[i] hTP
  rw [P₂_sup_T₃ h i hne hbot, card_T₀ h i hne hbot, card_P₂ h i hne hbot,
    card_T₃ h i hne hbot] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left (mul_pos two_pos (pow_pos hq 9)) ?_
  rw [h1]
  ring

theorem P₁_inf_H (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ⊓ 𝐇 = 𝐇 ⊓ 𝐄[i] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨h2, ?_⟩
    rw [← R_inf_P₁ h i hne hbot]
    exact mem_inf.mpr ⟨H_le_R h i h2, h1⟩
  · exact le_inf (inf_le_right.trans (E_le_P₁ h i hne hbot)) inf_le_left

theorem P₁_inf_T₃_sup_H (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐇 ⊔ (𝐏₁[i] ⊓ 𝐓₃[i]) = 𝐓₃[i] := by
  refine eq_of_le_of_card_ge (sup_le (H_le_T₃ h i) inf_le_right) ?_
  have hAH : 𝐏₁[i] ⊓ 𝐓₃[i] ≤ normalizer ((𝐇 : Subgroup G) : Set G) := fun _ hx =>
    (mem_inf.mp (T₁_le_Nhat h i hne hbot (mem_inf.mp (mem_inf.mp hx).2).1)).1
  have h1 := card_sup_mul_card_inf 𝐇 (𝐏₁[i] ⊓ 𝐓₃[i]) hAH
  have e1 : 𝐇 ⊓ (𝐏₁[i] ⊓ 𝐓₃[i]) = 𝐇 ⊓ 𝐄[i] := by
    rw [← P₁_inf_H h i hne hbot]
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨hxH, hxP, -⟩
      exact ⟨hxP, hxH⟩
    · rintro ⟨hxP, hxH⟩
      exact ⟨hxH, hxP, H_le_T₃ h i hxH⟩
  rw [e1, card_Hi h i, h.H_facts.2.2, card_P₁_inf_T₃ h i hne hbot] at h1
  rw [card_T₃ h i hne hbot]
  have hq : 0 < Nat.card K := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 5)) ?_).symm.le
  rw [h1]
  ring

theorem card_P₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐏₀[i] = 2 * Nat.card K ^ 5 := by
  have hBA : 𝐏₂[i.swap] ⊓ 𝐓₃[i] ≤ normalizer ((𝐏₁[i] ⊓ 𝐓₃[i] : Subgroup G) : Set G) := by
    intro b hb
    have hb3 := (mem_inf.mp hb).2
    refine mem_normalizer_of_conj_le fun x hx => mem_inf.mpr ⟨?_, ?_⟩
    · exact conj_mem_P₁ i (T₁_le_Dn h i (mem_inf.mp hb3).1) (mem_inf.mp hx).1
    · exact mul_mem (mul_mem hb3 (mem_inf.mp hx).2) (inv_mem hb3)
  have h1 := card_sup_mul_card_inf (𝐏₁[i] ⊓ 𝐓₃[i]) (𝐏₂[i.swap] ⊓ 𝐓₃[i]) hBA
  have hsup : (𝐏₁[i] ⊓ 𝐓₃[i]) ⊔ (𝐏₂[i.swap] ⊓ 𝐓₃[i]) = 𝐓₃[i] := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    refine (P₁_inf_T₃_sup_H h i hne hbot).symm.le.trans (sup_le ?_ le_sup_left)
    refine (Hk_sup_Hk h i).symm.le.trans (sup_le ?_ ?_)
    · exact le_sup_of_le_left (le_inf (inf_le_right.trans (E_le_P₁ h i hne hbot))
        (inf_le_left.trans (H_le_T₃ h i)))
    · exact le_sup_of_le_right (le_inf (inf_le_right.trans (E_le_P₂ h i hne hbot))
        (inf_le_left.trans (H_le_T₃ h i)))
  have hinf : (𝐏₁[i] ⊓ 𝐓₃[i]) ⊓ (𝐏₂[i.swap] ⊓ 𝐓₃[i]) = 𝐏₀[i] := by
    refine le_antisymm (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (le_inf (le_inf inf_le_left (P₀_le_T₃ h i hne hbot))
        (le_inf inf_le_right (P₀_le_T₃ h i hne hbot)))
  rw [hsup, hinf, card_T₃ h i hne hbot, card_P₁_inf_T₃ h i hne hbot,
    card_P₂_inf_T₃ h i hne hbot] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left (mul_pos two_pos (pow_pos hq 7)) ?_
  rw [h1]
  ring

theorem sq_P₀_mem_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐏₀[i]) : x * x ∈ 𝐅 :=
  sq_T₃_mem_F h i hne hbot (P₀_le_T₃ h i hne hbot hx)

theorem E0_le_P₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄₀ ≤ 𝐏₀[i] :=
  le_inf ((E0_le_E i).trans (E_le_P₁ h i hne hbot))
    ((E0_le_E i.swap).trans (E_le_P₂ h i hne hbot))

theorem P₀_inf_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₀[i] ⊓ 𝐄[i] = 𝐄₀ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (E0_le_P₀ h i hne hbot) (E0_le_E i))
  rw [← E_inf_P₂ h i hne hbot]
  exact mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩

theorem E_sup_P₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i] ⊔ 𝐏₀[i] = 𝐏₁[i] := by
  refine eq_of_le_of_card_ge (sup_le (E_le_P₁ h i hne hbot) inf_le_left) ?_
  have hPE : 𝐏₀[i] ≤ normalizer (𝐄[i] : Set G) := fun _ hx =>
    mem_normalizer_of_conj_le fun _ he =>
      conj_mem_E_of_normalizer_D h i (P₁_le i (mem_inf.mp hx).1) he
  have h1 := card_sup_mul_card_inf 𝐄[i] 𝐏₀[i] hPE
  have e1 : 𝐄[i] ⊓ 𝐏₀[i] = 𝐄₀ := (inf_comm _ _).trans (P₀_inf_E h i hne hbot)
  rw [e1, card_E0 h, card_E h i, card_P₀ h i hne hbot] at h1
  rw [card_P₁ h i hne hbot]
  have hq : 0 < Nat.card K := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 4)) ?_).symm.le
  rw [h1]
  ring

end Normality

end NextCores

end CFSG.LocalAnalysis.SymplecticFourStandard
