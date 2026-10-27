module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace NextCores

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
  CFSG.LocalAnalysis.ComponentInitial.BinaryAffinePlane
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem exists_quotient_equiv_of_hom_mod {P E A U : Subgroup G} (hUA : (U.subgroupOf A).Normal)
    (f : G → G) (hf : ∀ x ∈ P, f x ∈ A)
    (hmul : ∀ x ∈ P, ∀ y ∈ P, (f x * f y)⁻¹ * f (x * y) ∈ U)
    (hker : ∀ x ∈ P, f x ∈ U ↔ x ∈ E) (hsurj : ∀ a ∈ A, ∃ x ∈ P, (f x)⁻¹ * a ∈ U) :
    ∃ _ : (E.subgroupOf P).Normal, ∃ e : (↥P ⧸ E.subgroupOf P) ≃* (↥A ⧸ U.subgroupOf A),
      ∀ x : P, e (x : ↥P ⧸ E.subgroupOf P) =
        ((⟨f x, hf x x.2⟩ : A) : ↥A ⧸ U.subgroupOf A) := by
  let θ : P →* ↥A ⧸ U.subgroupOf A :=
    { toFun := fun x => ((⟨f x, hf x x.2⟩ : A) : ↥A ⧸ U.subgroupOf A)
      map_one' := by
        rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact (hker 1 (one_mem P)).mpr (one_mem E)
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have := inv_mem (hmul x x.2 y y.2)
        rw [mul_inv_rev, inv_inv] at this
        simp only [coe_mul, coe_inv]
        exact this }
  have hkerEq : E.subgroupOf P = θ.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    change (x : G) ∈ E ↔ ((⟨f x, hf x x.2⟩ : A) : ↥A ⧸ U.subgroupOf A) = 1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact (hker x x.2).symm
  have hN : (E.subgroupOf P).Normal := hkerEq ▸ θ.normal_ker
  have hθs : Function.Surjective θ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨x, hx, hxa⟩ := hsurj a a.2
      refine ⟨⟨x, hx⟩, ?_⟩
      change ((⟨f x, hf x hx⟩ : A) : ↥A ⧸ U.subgroupOf A) = (a : ↥A ⧸ U.subgroupOf A)
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact hxa
  refine ⟨hN, (QuotientGroup.quotientMulEquivOfEq hkerEq).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs), fun x => rfl⟩

theorem center_quotient_eq {P K X : Subgroup G} (hn : (K.subgroupOf P).Normal) (hKX : K ≤ X)
    (hPK : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hc : ∀ x ∈ P, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ K) ↔ x ∈ X) :
    center (↥P ⧸ K.subgroupOf P) = (X.subgroupOf P).map (QuotientGroup.mk' (K.subgroupOf P)) := by
  have hKX' : K.subgroupOf P ≤ X.subgroupOf P := fun x hx => mem_subgroupOf.mpr
    (hKX (mem_subgroupOf.mp hx))
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [mem_map_mk'_iff hKX', mem_subgroupOf, Subgroup.mem_center_iff, ← hc x x.2]
  constructor
  · intro hq p hp
    have h1 := hq (QuotientGroup.mk (⟨p, hp⟩ : P))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h1
    simp only [coe_mul, coe_inv] at h1
    have h2 := hPK _ (mul_mem hp x.2) _ h1
    rwa [show p * x * ((p * x)⁻¹ * ((x : G) * p)) * (p * x)⁻¹ =
      (x : G) * p * (x : G)⁻¹ * p⁻¹ by group] at h2
  · intro hx g
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    have h2 := hPK _ (inv_mem (mul_mem p.2 x.2)) _ (hx p p.2)
    rwa [show ((p : G) * x)⁻¹ * ((x : G) * p * (x : G)⁻¹ * (p : G)⁻¹) * ((p : G) * x)⁻¹⁻¹ =
      ((p : G) * x)⁻¹ * ((x : G) * p) by group] at h2

end General

section SecondCore

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
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype

theorem F_comm_K_swap (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {f : G} (hf : f ∈ 𝐅) {k : G} (hk : k ∈ 𝐊[i.swap]) : f * k = k * f :=
  L_swap_comm h i hbot (F_le_L _ hf) (K_le_L _ hk)

theorem Fw_comm_K_swap (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {f : G} (hf : f ∈ 𝐅ʷ[i.swap]) {k : G} (hk : k ∈ 𝐊[i.swap]) : f * k = k * f := by
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  have hwk := conj_w_mem_K h i.swap hk
  have h1 := F_comm_K_swap h i hbot hf₀ hwk
  show (MulAut.conj 𝐰[i.swap]⁻¹) f₀ * k = k * (MulAut.conj 𝐰[i.swap]⁻¹) f₀
  rw [MulAut.conj_apply, inv_inv]
  calc 𝐰[i.swap]⁻¹ * f₀ * 𝐰[i.swap] * k
      = 𝐰[i.swap]⁻¹ * (f₀ * (𝐰[i.swap] * k * 𝐰[i.swap]⁻¹)) * 𝐰[i.swap] := by group
    _ = 𝐰[i.swap]⁻¹ * ((𝐰[i.swap] * k * 𝐰[i.swap]⁻¹) * f₀) * 𝐰[i.swap] := by rw [h1]
    _ = k * (𝐰[i.swap]⁻¹ * f₀ * 𝐰[i.swap]) := by group

theorem X_le_centralizer_K (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐗[i.swap] ≤ centralizer ((𝐊[i.swap] : Subgroup G) : Set G) :=
  sup_le (fun _ hf => mem_centralizer_iff.mpr fun _ hk => (F_comm_K_swap h i hbot hf hk).symm)
    fun _ hf => mem_centralizer_iff.mpr fun _ hk => (Fw_comm_K_swap h i hbot hf hk).symm

theorem exists_K_not_comm_t (h : FCHyp L K n φ t) (k : Axis) :
    ∃ x ∈ 𝐊[k], x * t ≠ t * x := by
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ 𝐔[k], u ≠ 1 := by
    refine ⟨coordG φ k 1, coordG_mem φ k 1, fun h1 => ?_⟩
    rw [← coordG_zero φ k] at h1
    exact one_ne_zero (coordG_injective φ k h1)
  obtain ⟨f, hf, hfu⟩ := exists_kappa_eq_Fi h k hu
  refine ⟨f, mem_sup_right hf, fun hc => hu1 ?_⟩
  rw [← hfu, show f⁻¹ * t * f = t by rw [mul_assoc, ← hc, inv_mul_cancel_left], inv_mul_cancel]

theorem mem_X_iff (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {e : G} (he : e ∈ 𝐄[i.swap]) :
    e ∈ 𝐗[i.swap] ↔ ∀ k ∈ 𝐊[i.swap], e * k = k * e := by
  constructor
  · intro hx k hk
    exact (mem_centralizer_iff.mp (X_le_centralizer_K h i hbot hx) k hk).symm
  · intro hc
    have htX : t ∈ normalizer ((𝐗[i.swap] : Subgroup G) : Set G) :=
      R_le_normalizer_X h i.swap (Qi_le_R h i.swap (mem_sup_left (mem_sup_right (mem_zpowers t))))
    rw [← (X_sup_t h i.swap).2] at he
    rcases mem_or_mul_mem h.setup.t_mul_t htX he with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨x, hx, hxt⟩ := exists_K_not_comm_t h i.swap
      have h2 := (mem_centralizer_iff.mp (X_le_centralizer_K h i hbot h1) x hx)
      have h3 := hc x hx
      apply hxt
      have htt := h.setup.t_mul_t
      calc x * t = x * (t * e) * e⁻¹ := by group
        _ = t * e * x * e⁻¹ := by rw [h2]
        _ = t * (e * x) * e⁻¹ := by group
        _ = t * (x * e) * e⁻¹ := by rw [h3]
        _ = t * x := by group

theorem conj_mem_X_of_En (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {g : G} (hg : g ∈ 𝐄𝐧[i.swap]) {x : G} (hx : x ∈ 𝐗[i.swap]) : g * x * g⁻¹ ∈ 𝐗[i.swap] := by
  obtain ⟨hgE, hgK⟩ := mem_inf.mp hg
  have hxE : x ∈ 𝐄[i.swap] := X_le_E h i.swap hx
  have hgx : g * x * g⁻¹ ∈ 𝐄[i.swap] := (mem_normalizer_iff.mp hgE x).mp hxE
  refine (mem_X_iff h i hbot hgx).mpr fun k hk => ?_
  have hk' : g⁻¹ * k * g ∈ 𝐊[i.swap] := by
    have := (mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
    rwa [inv_inv] at this
  have h1 := (mem_X_iff h i hbot hxE).mp hx _ hk'
  calc g * x * g⁻¹ * k = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by rw [h1]
    _ = k * (g * x * g⁻¹) := by group

variable (φ t) in
@[expose] noncomputable def psiX (k : Axis) (x : G) : Fin 2 → K :=
  psiG φ k (t⁻¹ * (x⁻¹ * t * x))

theorem kappa_E_mem_A (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐄[k]) :
    t⁻¹ * (x⁻¹ * t * x) ∈ 𝐀[k] := by
  have hmem : x⁻¹ * t * x ∈ {y : G | ∃ e ∈ 𝐄[k], y = e⁻¹ * t * e} := ⟨x, hx, rfl⟩
  rw [orbit_E h k] at hmem
  obtain ⟨a, ha, he⟩ := hmem
  rw [he, ← mul_assoc, inv_mul_cancel, one_mul]
  exact ha

theorem psiX_mul (h : FCHyp L K n φ t) (k : Axis) {x y : G} (hx : x ∈ 𝐄[k]) (hy : y ∈ 𝐄[k]) :
    psiX φ t k (x * y) = psiX φ t k x + psiX φ t k y := by
  have hxA := kappa_E_mem_A h k hx
  have hyA := kappa_E_mem_A h k hy
  have hyN : y⁻¹ ∈ normalizer (𝐀[k] : Set G) :=
    h.N_le_normalizer_A k (inv_mem (map_subtype_le _ hy))
  have hconj : y⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * y⁻¹⁻¹ ∈ 𝐀[k] :=
    (mem_normalizer_iff.mp hyN _).mp hxA
  have e : t⁻¹ * ((x * y)⁻¹ * t * (x * y)) =
      (t⁻¹ * (y⁻¹ * t * y)) * (y⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * y⁻¹⁻¹) := by group
  rw [psiX, e, psiG_mul h.twoCore φ k hyA hconj, h.E_lin k (inv_mem hy) hxA, add_comm]
  rfl

theorem psiX_eq_zero_iff_D (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐄[k]) :
    psiX φ t k x = 0 ↔ x ∈ 𝐃[k] := by
  rw [psiX, psiG_eq_zero_iff h.twoCore φ k (kappa_E_mem_A h k hx)]
  exact ⟨fun hu => mem_D_of_kappa h k hx hu, fun hd => kappa_mem_U h k hd⟩

theorem K_le_X (h : FCHyp L K n φ t) (k : Axis) : 𝐊[k] ≤ 𝐗[k] := by
  rw [← X_inf_D h k]
  exact inf_le_left

theorem exists_psiX_eq (h : FCHyp L K n φ t) (k : Axis) (v : Fin 2 → K) :
    ∃ x ∈ 𝐗[k], psiX φ t k x = v := by
  obtain ⟨a, ha, hav⟩ := exists_psiG_eq h.twoCore φ k v
  have hmem : t * a ∈ {y : G | ∃ a ∈ 𝐀[k], y = t * a} := ⟨a, ha, rfl⟩
  rw [← orbit_E h k] at hmem
  obtain ⟨e, he, hea⟩ := hmem
  have heXD : e ∈ ((𝐗[k] : Subgroup G) : Set G) * (𝐃[k] : Set G) := by
    rw [X_mul_D h k]
    exact he
  obtain ⟨x, hx, d, hd, rfl⟩ := heXD
  refine ⟨x, hx, ?_⟩
  have hxE : x ∈ 𝐄[k] := X_le_E h k hx
  have hdE : d ∈ 𝐄[k] := h.D_le_E k hd
  have h1 := psiX_mul h k hxE hdE
  rw [(psiX_eq_zero_iff_D h k hdE).mpr hd, add_zero] at h1
  rw [← h1, psiX, ← hea, ← mul_assoc, inv_mul_cancel, one_mul, hav]

theorem psiX_eq_zero_iff (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐗[k]) :
    psiX φ t k x = 0 ↔ x ∈ 𝐊[k] := by
  rw [psiX_eq_zero_iff_D h k (X_le_E h k hx), ← X_inf_D h k]
  exact ⟨fun hd => ⟨hx, hd⟩, fun hk => hk.2⟩

theorem conj_t_mem_X (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {g : G} (hg : g ∈ 𝐄𝐧[i.swap]) : t⁻¹ * (g * t * g⁻¹) ∈ 𝐗[i.swap] := by
  have hgt : g * t * g⁻¹ ∈ 𝐄[i.swap] :=
    (mem_normalizer_iff.mp (mem_inf.mp hg).1 t).mp (t_mem_E h i.swap)
  rw [← (X_sup_t h i.swap).2] at hgt
  have htX : t ∈ normalizer ((𝐗[i.swap] : Subgroup G) : Set G) :=
    R_le_normalizer_X h i.swap (Qi_le_R h i.swap (mem_sup_left (mem_sup_right (mem_zpowers t))))
  rcases mem_or_mul_mem h.setup.t_mul_t htX hgt with h1 | h1
  · exfalso
    apply t_not_mem_X h i.swap
    have := conj_mem_X_of_En h i hbot (inv_mem hg) h1
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  · rwa [h.twoCore.t_inv]

theorem actHyp₂ (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    FullCenter.ActHyp (psiX φ t i.swap) t 𝐗[i.swap] 𝐊[i.swap] 𝐄𝐧[i.swap] where
  U_le := K_le_X h i.swap
  add := fun _ hx _ hy => psiX_mul h i.swap (X_le_E h i.swap hx) (X_le_E h i.swap hy)
  ker := fun _ hx => psiX_eq_zero_iff h i.swap hx
  surj := exists_psiX_eq h i.swap
  conj_A := fun _ hg _ hx => conj_mem_X_of_En h i hbot hg hx
  conj_U := fun _ hg _ hk => (mem_normalizer_iff.mp (mem_inf.mp hg).2 _).mp hk
  conj_t := fun _ hg => conj_t_mem_X h i hbot hg

omit [Finite G] in
theorem frobAut_pow_rootCoord (k : Axis) (e : ℕ) (x : K) :
    (frobAut K ^ e) (rootCoord K k x) = rootCoord K k (x ^ 2 ^ e) := by
  induction e generalizing x with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, MulAut.mul_apply, frobAut_rootCoord, ih, ← pow_mul, ← pow_succ']

theorem mem_Q_sup_J_of_cent (h : FCHyp L K n φ t) (k : Axis) {c : G} (hcC : c ∈ 𝐂)
    (hcN : ∀ m : Axis, c ∈ 𝐍[m]) (hcU : ∀ u ∈ 𝐔[k], c * u * c⁻¹ = u) : c ∈ 𝐐 ⊔ 𝐉 := by
  obtain ⟨a₀, ha₀, l, M, e, he, hα⟩ := h.exists_aut k hcC (hcN k)
  have hst := h.twoCore.axisStr k
  have hUk : ∀ x : K, c * coordG φ k x * c⁻¹ = coordG φ k ((l : K) ^ 2 * x ^ 2 ^ e) := by
    intro x
    rw [coordG, coordG, ← normAct_symm_apply φ ⟨c, h.setup.cent_le hcC⟩ (rootCoord K k x), hα,
      MulAut.mul_apply, frobAut_pow_rootCoord, MulAut.conj_apply]
    congr 2
    have hs := mem_centralizer_iff.mp (hst.s_mem_C M) _ (rootCoord_mem' k (x ^ 2 ^ e))
    have ha := mem_centralizer_iff.mp (hst.A_le_C ha₀) _ (rootCoord_mem' k ((l : K) ^ 2 *
      x ^ 2 ^ e))
    have hd := hst.d_coord l (x ^ 2 ^ e)
    calc a₀ * (dHom K k l * sHom K k M) * rootCoord K k (x ^ 2 ^ e) *
          (a₀ * (dHom K k l * sHom K k M))⁻¹
        = a₀ * (dHom K k l * (sHom K k M * rootCoord K k (x ^ 2 ^ e) * (sHom K k M)⁻¹) *
          (dHom K k l)⁻¹) * a₀⁻¹ := by group
      _ = a₀ * (dHom K k l * rootCoord K k (x ^ 2 ^ e) * (dHom K k l)⁻¹) * a₀⁻¹ := by
          rw [← hs, mul_inv_cancel_right]
      _ = rootCoord K k ((l : K) ^ 2 * x ^ 2 ^ e) := by rw [hd, ← ha, mul_inv_cancel_right]
  have hfix : ∀ x : K, (l : K) ^ 2 * x ^ 2 ^ e = x := fun x =>
    coordG_injective φ k ((hUk x).symm.trans (hcU _ (coordG_mem φ k x)))
  have hl2 : (l : K) ^ 2 = 1 := by simpa using hfix 1
  have hfix' : ∀ x : K, x ^ 2 ^ e = x := fun x => by
    have := hfix x
    rwa [hl2, one_mul] at this
  have he0 : e = 0 := eq_zero_of_frobRingEquiv_pow_eq_one (by have := h.setup.two_le; omega)
    h.setup.card_K he (RingEquiv.ext fun x => by rw [frobRingEquiv_pow_apply, hfix' x]; rfl)
  subst he0
  rw [pow_zero, mul_one] at hα
  have hact : ∀ a ∈ 𝐀[k], psiG φ k (c * a * c⁻¹) =
      (l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ psiG φ k a) := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull ha
    rw [← normAct_symm_apply φ ⟨c, h.setup.cent_le hcC⟩ z, psiG_symm, psiG_symm, hα]
    have := vecOf_aut k hst ha₀ l M 0 hz
    simp only [pow_zero, pow_one, mul_one] at this
    exact this
  have hA : ∀ m, ∀ a ∈ 𝐀[m], c * a * c⁻¹ ∈ 𝐀[m] := fun m a ha =>
    (mem_normalizer_iff.mp (h.N_le_normalizer_A m (hcN m)) a).mp ha
  have hZ : 𝐀[Axis.one] ⊓ 𝐀[Axis.two] = 𝐙 := by
    rw [← pull_inf]
    exact congrArg (pull φ) radA1_inf_radA2
  have hcZ : ∀ z ∈ 𝐙, c * z * c⁻¹ ∈ 𝐙 := fun z hz => by
    rw [← hZ] at hz ⊢
    exact ⟨hA _ z hz.1, hA _ z hz.2⟩
  obtain ⟨z₁, hz₁, hψz₁⟩ := exists_psiG_ZP h k 1
  have hM10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h1 := psiG_ZP_one h k (hcZ z₁ hz₁)
    rw [hact z₁ (pull_mono φ (center_le_rootA _) hz₁), hψz₁] at h1
    simpa [l.ne_zero] using h1
  have hdet : (M : Matrix (Fin 2) (Fin 2) K) 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact M.2
  have hM00 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h0
    rw [h0, hM10] at hdet
    simp at hdet
  have hMdec : M = diagSL (Units.mk0 _ hM00) * upperSL ((M : Matrix (Fin 2) (Fin 2) K) 0 1 *
      ((M : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL, coe_diagSL]
    rw [hM10, mul_zero, sub_zero] at hdet
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM10]
    · field_simp
    · field_simp
      linear_combination hdet
  have hx : a₀ * (dHom K k l * sHom K k M) ∈ antiUnipotent K ⊔ diagTorus K := by
    rw [hMdec, map_mul]
    exact mul_mem (mem_sup_left (rootA_le_antiUnipotent _ ha₀))
      (mul_mem (mem_sup_right (dHom_mem _ l)) (mul_mem (mem_sup_right (sHom_diagSL_mem _ _))
        (mem_sup_left (sHom_upperSL_mem _ _))))
  set x := a₀ * (dHom K k l * sHom K k M) with hxdef
  have hα' : normAct φ ⟨c, h.setup.cent_le hcC⟩ = MulAut.conj (φ (φ.symm x)) := by
    rw [MulEquiv.apply_symm_apply]
    exact hα
  have h0 := inv_mul_mem_centralizer φ _ _ hα'
  have hτ : ((φ.symm x : L) : G)⁻¹ * c ∈ zpowers t :=
    h.twoCore.mem_zpowers_of_mem h0 (mul_mem (inv_mem (h.setup.L_le (φ.symm x).2)) hcC)
  have hxG : ((φ.symm x : L) : G) ∈ 𝐏 ⊔ 𝐉 := by
    rw [← pull_sup]
    exact symm_mem_pull.mpr hx
  rw [show c = ((φ.symm x : L) : G) * (((φ.symm x : L) : G)⁻¹ * c) by group]
  exact mul_mem ((sup_le_sup_right le_sup_left 𝐉) hxG) (mem_sup_left (mem_sup_right hτ))

theorem D_eq_sup_K (h : FCHyp L K n φ t) (k : Axis) : 𝐃[k] = zpowers t ⊔ 𝐊[k] :=
  (K_sup_t h k).2.symm.trans (sup_comm _ _)

theorem mem_normalizer_D_of (h : FCHyp L K n φ t) (k : Axis) {x : G}
    (hxK : x ∈ normalizer (𝐊[k] : Set G)) (hxt : x * t * x⁻¹ ∈ zpowers t ⊔ 𝐊[k]) :
    x ∈ normalizer (𝐃[k] : Set G) := by
  rw [D_eq_sup_K h k]
  exact mem_normalizer_zpowers_sup hxt fun w hw => (mem_normalizer_iff.mp hxK w).mp hw

theorem Nhat_le_normalizer_K_swap' (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐍ₕ[i] ≤ normalizer (𝐊[i.swap] : Set G) :=
  Nhat_le_normalizer_K_swap h i hne hbot (W_sq_eq' h i hne hbot) one_ne_zero

@[expose] noncomputable def cStar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Subgroup G :=
  quotCent 𝐘[i, i.swap] (𝐇 ⊓ 𝐄[i.swap]) 𝐊[i.swap]
    (fun _ hg _ hy => (mem_normalizer_iff.mp (mem_inf.mp hg).2 _).mp hy)
    (fun _ hg _ hb => (mem_normalizer_iff.mp
      (Nhat_le_normalizer_K_swap' h i hne hbot (mem_inf.mp hg).1) _).mp hb)

theorem mem_cStar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} :
    g ∈ cStar h i hne hbot ↔
      g ∈ 𝐘[i, i.swap] ∧ ∀ y ∈ 𝐇 ⊓ 𝐄[i.swap], g * y * g⁻¹ * y⁻¹ ∈ 𝐊[i.swap] :=
  mem_quotCent

theorem R_le_normalizer_Hk (h : FCHyp L K n φ t) (k : Axis) :
    𝐑[k] ≤ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) := fun _ hr =>
  mem_normalizer_of_conj_le fun _ hx => mem_inf.mpr
    ⟨(mem_normalizer_iff.mp (R_le_normalizer_H h k hr) _).mp (mem_inf.mp hx).1,
      conj_mem_E h k hr (mem_inf.mp hx).2⟩

theorem R_le_cStar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐑[i.swap] ≤ cStar h i hne hbot := by
  intro r hr
  refine (mem_cStar h i hne hbot).mpr ⟨mem_inf.mpr ⟨R_le_Nhat h i hne hbot i.swap hr,
    R_le_normalizer_Hk h i.swap hr⟩, fun y hy => ?_⟩
  have hyR : y ∈ 𝐑[i.swap] := H_le_R h i.swap (mem_inf.mp hy).1
  exact comm_mem_symm ((mem_Hk_iff h i.swap hyR).mp hy r hr)

theorem cStar_le_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : cStar h i hne hbot ≤ 𝐍[i.swap] := by
  intro g hg
  obtain ⟨hgY, hgc⟩ := (mem_cStar h i hne hbot).mp hg
  have hgK := Nhat_le_normalizer_K_swap' h i hne hbot (mem_inf.mp hgY).1
  have htH : t ∈ 𝐇 ⊓ 𝐄[i.swap] := D_le_Hi h i.swap (t_mem_D h i.swap)
  have h1 := hgc t htH
  have hgt : g * t * g⁻¹ ∈ zpowers t ⊔ 𝐊[i.swap] := by
    rw [show g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t by group]
    exact mul_mem (mem_sup_right h1) (mem_sup_left (mem_zpowers t))
  have hgD : g ∈ normalizer (𝐃[i.swap] : Set G) := mem_normalizer_D_of h i.swap hgK hgt
  rw [← normalizer_D_swap_eq h i hne hbot]
  exact hgD

omit [Finite G] in
theorem kappa_conj_C {c : G} (hc : c ∈ 𝐂) (x : G) :
    t⁻¹ * ((c * x * c⁻¹)⁻¹ * t * (c * x * c⁻¹)) = c * (t⁻¹ * (x⁻¹ * t * x)) * c⁻¹ := by
  have hct : Commute c t := mem_centralizer_singleton_iff.mp hc
  have hctc : c⁻¹ * t * c = t := by rw [mul_assoc, ← hct.eq, inv_mul_cancel_left]
  have htc : t⁻¹ * c = c * t⁻¹ := hct.symm.inv_left.eq
  calc t⁻¹ * ((c * x * c⁻¹)⁻¹ * t * (c * x * c⁻¹))
      = t⁻¹ * c * x⁻¹ * (c⁻¹ * t * c) * x * c⁻¹ := by group
    _ = t⁻¹ * c * x⁻¹ * t * x * c⁻¹ := by rw [hctc]
    _ = c * t⁻¹ * x⁻¹ * t * x * c⁻¹ := by rw [htc]
    _ = c * (t⁻¹ * (x⁻¹ * t * x)) * c⁻¹ := by group

theorem cStar_comm_U (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {c : G} (hc : c ∈ cStar h i hne hbot) (hcC : c ∈ 𝐂)
    {u : G} (hu : u ∈ 𝐔[i]) : c * u * c⁻¹ = u := by
  obtain ⟨hcY, hcc⟩ := (mem_cStar h i hne hbot).mp hc
  have huZ : u ∈ 𝐙 := pull_mono φ (rootU_le_center _) hu
  obtain ⟨e, he, heu⟩ := exists_kappa_eq h huZ
  have heH : e ∈ 𝐇 ⊓ 𝐄[i.swap] := mem_inf.mpr ⟨E0_le_H h he, E0_le_E i.swap he⟩
  have hk := hcc e heH
  set k' := c * e * c⁻¹ * e⁻¹ with hk'
  have hk'H : k' ∈ 𝐇 := K_le_H h i.swap hk
  have heH' : e ∈ 𝐇 := E0_le_H h he
  have h1 : c * u * c⁻¹ = (t⁻¹ * (k'⁻¹ * t * k')) * u := by
    rw [← heu, ← kappa_conj_C hcC e, show c * e * c⁻¹ = k' * e by rw [hk']; group,
      kappa_mul h hk'H heH']
  have h2 : c * u * c⁻¹ * u⁻¹ ∈ 𝐔[i.swap] := by
    rw [h1, mul_inv_cancel_right]
    exact kappa_mem_U h i.swap (K_le_D h i.swap hk)
  have h3 : c * u * c⁻¹ * u⁻¹ ∈ 𝐔[i] :=
    mul_mem ((mem_normalizer_iff.mp (mem_inf.mp (mem_inf.mp hcY).1).2 u).mp hu) (inv_mem hu)
  have h4 : c * u * c⁻¹ * u⁻¹ ∈ 𝐔[i] ⊓ 𝐔[i.swap] := mem_inf.mpr ⟨h3, h2⟩
  rw [U_inf_U_swap, mem_bot] at h4
  exact mul_inv_eq_one.mp h4

theorem mem_R_of_cStar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} (hg : g ∈ cStar h i hne hbot) {e : ℕ}
    (hge : g ^ 2 ^ e = 1) : g ∈ 𝐑[i.swap] := by
  have hgNR : g ∈ ((normalizer (𝐑[i.swap] : Set G) ⊓ normalizer (𝐁[i.swap] : Set G) :
      Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, ← Nhat_inf_NB h i hne hbot i.swap]
    exact mem_inf.mpr ⟨(mem_inf.mp ((mem_cStar h i hne hbot).mp hg).1).1,
      cStar_le_N h i hne hbot hg⟩
  rw [← NRB_eq' h i hne hbot i.swap] at hgNR
  obtain ⟨r, hr, c, hc, rfl⟩ := hgNR
  obtain ⟨hcC, hcQ⟩ := mem_inf.mp hc
  have hcS : c ∈ cStar h i hne hbot := by
    have := mul_mem (inv_mem (R_le_cStar h i hne hbot hr)) hg
    rwa [inv_mul_cancel_left] at this
  have hcJ : c ∈ 𝐐 ⊔ 𝐉 := mem_Q_sup_J_of_cent h i hcC
    (fun m => normalizer_Q_le_N h i hne hbot m hcQ) fun u hu => cStar_comm_U h i hne hbot hcS hcC hu
  have hQR : 𝐐 ≤ 𝐑[i.swap] := le_sup_left
  have hs : r * c ∈ 𝐑[i.swap] ⊔ 𝐉 :=
    mul_mem (mem_sup_left hr) ((sup_le_sup_right hQR 𝐉) hcJ)
  exact mem_of_two_pow (fun j hj => (mem_inf.mp (J_le_NRB h i hne hbot i.swap hj)).1)
    (odd_card_sub_one h) (fun j hj => torus_pow_card_sub_one hj) hs hge

theorem Y_le_normalizer_R (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐘[i, i.swap] ≤ normalizer (𝐑[i.swap] : Set G) := by
  intro y hy
  refine mem_normalizer_of_conj_le fun r hr => ?_
  have hS : y * r * y⁻¹ ∈ cStar h i hne hbot :=
    conj_mem_quotCent hy (R_le_cStar h i hne hbot hr)
  obtain ⟨e, he⟩ := exists_two_pow_eq_one (R_isPGroup h i.swap) hr
  refine mem_R_of_cStar h i hne hbot hS (e := e) ?_
  rw [conj_pow, he, mul_one, mul_inv_cancel]

theorem le_E_or_le_H (h : FCHyp L K n φ t) (k : Axis) {S : Subgroup G} (hSR : S ≤ 𝐑[k])
    (hS : ∀ s ∈ S, s * s ∈ 𝐃[k]) : S ≤ 𝐄[k] ∨ S ≤ 𝐇 := by
  set S' := (S.subgroupOf 𝐑[k]).map (parabolicHom h k) with hS'
  have hsq : ∀ p ∈ S', p * p = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    exact parabolicHom_D h k (hS s (mem_subgroupOf.mp hs))
  rcases Heis.le_planeXY_or_le_planeXZ S' hsq with hXY | hXZ
  · left
    intro s hs
    have h1 := hXY ⟨⟨s, hSR hs⟩, mem_subgroupOf.mpr hs, rfl⟩
    exact (parabolicHom_z_eq_zero_iff h k ⟨s, hSR hs⟩).mp h1
  · right
    intro s hs
    have h1 := hXZ ⟨⟨s, hSR hs⟩, mem_subgroupOf.mpr hs, rfl⟩
    exact (mem_H_iff h k ⟨s, hSR hs⟩).mpr h1

theorem Y_le_normalizer_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐘[i, i.swap] ≤ normalizer (𝐄[i.swap] : Set G) := by
  intro y hy
  have hyR := Y_le_normalizer_R h i hne hbot hy
  have hyH : y ∈ normalizer ((𝐇 : Subgroup G) : Set G) := (mem_inf.mp (mem_inf.mp hy).1).1
  have hyK := Nhat_le_normalizer_K_swap' h i hne hbot (mem_inf.mp hy).1
  set S := (𝐄[i.swap]).map (MulAut.conj y).toMonoidHom with hSdef
  have hSR : S ≤ 𝐑[i.swap] := by
    rintro _ ⟨e, he, rfl⟩
    exact (mem_normalizer_iff.mp hyR e).mp (mem_sup_right he)
  have hSsq : ∀ s ∈ S, s * s ∈ 𝐃[i.swap] := by
    rintro _ ⟨e, he, rfl⟩
    have hee : e * e ∈ 𝐀[i.swap] := by
      rw [← closure_sq_E h i.swap]
      exact subset_closure ⟨e, he, rfl⟩
    have h1 : y * (e * e) * y⁻¹ ∈ 𝐊[i.swap] :=
      (mem_normalizer_iff.mp hyK _).mp (mem_sup_left hee)
    have e2 : (MulAut.conj y).toMonoidHom e * (MulAut.conj y).toMonoidHom e =
        y * (e * e) * y⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e2]
    exact K_le_D h i.swap h1
  rcases le_E_or_le_H h i.swap hSR hSsq with hSE | hSH
  · exact mem_normalizer_of_conj_le fun e he => hSE ⟨e, he, rfl⟩
  · exfalso
    have hEH : 𝐄[i.swap] ≤ 𝐇 ⊓ 𝐄[i.swap] := by
      intro e he
      refine mem_inf.mpr ⟨?_, he⟩
      have h1 := hSH ⟨e, he, rfl⟩
      have h2 := (mem_normalizer_iff.mp (inv_mem hyH) _).mp h1
      rwa [show y⁻¹ * (MulAut.conj y).toMonoidHom e * y⁻¹⁻¹ = e by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group] at h2
    have h1 := Subgroup.card_le_of_le hEH
    rw [card_E h i.swap, card_Hi h i.swap] at h1
    have h4 := h.four_le_card
    have h5 : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem Y_le_En (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐘[i, i.swap] ≤ 𝐄𝐧[i.swap] := fun _ hy =>
  mem_inf.mpr ⟨Y_le_normalizer_E h i hne hbot hy,
    Nhat_le_normalizer_K_swap' h i hne hbot (mem_inf.mp hy).1⟩

theorem exists_Y_not_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : ∃ y ∈ 𝐘[i, i.swap], y ∉ 𝐍[i.swap] := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : 𝐘[i, i.swap] ≤ normalizer (𝐑[i.swap] : Set G) ⊓ normalizer (𝐁[i.swap] : Set G) := by
    intro y hy
    rw [← Nhat_inf_NB h i hne hbot i.swap]
    exact mem_inf.mpr ⟨(mem_inf.mp hy).1, hcon y hy⟩
  have h1 := second_index h i hne hbot i.swap
  rw [relIndex_eq_one.mpr hle] at h1
  have := h.four_le_card
  omega

theorem N_le_En (h : FCHyp L K n φ t) (k : Axis) : 𝐍[k] ≤ 𝐄𝐧[k] := fun _ hg =>
  mem_inf.mpr ⟨mem_normalizer_of_conj_le fun _ he => conj_mem_pCore_map hg he,
    mem_normalizer_of_conj_le fun _ hx =>
      conj_mem_K_of_normalizer_D h k (N_le_normalizer_D h k hg) hx⟩

theorem aff₂_zero_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (g : 𝐄𝐧[i.swap]) : (actHyp₂ h i hbot).aff g 0 = 0 ↔ (g : G) ∈ 𝐍[i.swap] := by
  rw [(actHyp₂ h i hbot).aff_zero, psiX_eq_zero_iff h i.swap (conj_t_mem_X h i hbot g.2)]
  constructor
  · intro hk
    have hgt : (g : G) * t * (g : G)⁻¹ ∈ zpowers t ⊔ 𝐊[i.swap] := by
      rw [show (g : G) * t * (g : G)⁻¹ = t * (t⁻¹ * ((g : G) * t * (g : G)⁻¹)) by group]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hk)
    have hgD : (g : G) ∈ normalizer (𝐃[i.swap] : Set G) :=
      mem_normalizer_D_of h i.swap (mem_inf.mp g.2).2 hgt
    exact (normalizer_D_swap_eq h i hne hbot).le hgD
  · intro hgN
    have hmem : (g : G) * t * (g : G)⁻¹ ∈ {x : G | ∃ g ∈ 𝐍[i.swap], x = g⁻¹ * t * g} :=
      ⟨(g : G)⁻¹, inv_mem hgN, by rw [inv_inv]⟩
    rw [h.orbit_N i.swap] at hmem
    obtain ⟨a, ha, he⟩ := hmem
    rw [he, ← mul_assoc, inv_mul_cancel, one_mul]
    exact mem_sup_left ha

theorem aff₂_E (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {e : G}
    (he : e ∈ 𝐄[i.swap]) :
    (actHyp₂ h i hbot).aff ⟨e, N_le_En h i.swap (map_subtype_le _ he)⟩ = 1 := by
  rw [(actHyp₂ h i hbot).aff_eq_one_iff]
  intro a ha
  have haE : a ∈ 𝐄[i.swap] := X_le_E h i.swap ha
  have htaE : t * a ∈ 𝐄[i.swap] := mul_mem (t_mem_E h i.swap) haE
  have hc : (t * a)⁻¹ * (e * (t * a) * e⁻¹) ∈ 𝐊[i.swap] := by
    have := commutator_mem_closure_sq htaE (inv_mem he)
    rw [closure_sq_E h i.swap, inv_inv] at this
    exact mem_sup_left this
  have e1 : t⁻¹ * (e * (t * a) * e⁻¹) = a * ((t * a)⁻¹ * (e * (t * a) * e⁻¹)) := by group
  rw [e1, (actHyp₂ h i hbot).add a ha _ (K_le_X h i.swap hc),
    (psiX_eq_zero_iff h i.swap (K_le_X h i.swap hc)).mpr hc, add_zero]

theorem aff₂_of_C (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {c : G}
    (hcC : c ∈ 𝐂) (hcN : c ∈ 𝐍[i.swap]) {a : G} (ha : a ∈ 𝐀[i.swap]) :
    (actHyp₂ h i hbot).aff ⟨c, N_le_En h i.swap hcN⟩ (psiG φ i.swap a) =
      psiG φ i.swap (c * a * c⁻¹) := by
  set hA := actHyp₂ h i hbot with hAdef
  obtain ⟨x, hx, hxa⟩ := exists_psiX_eq h i.swap (psiG φ i.swap a)
  have hct : c * t * c⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hcC, mul_inv_cancel_right]
  rw [← hxa, hA.aff_eq, hA.lin_psi _ hx]
  have h0 : psiX φ t i.swap (t⁻¹ * (c * t * c⁻¹)) = 0 := by
    rw [hct, inv_mul_cancel]
    exact hA.psi_one
  rw [h0, add_zero, psiX, kappa_conj_C hcC x]
  have hκ : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐀[i.swap] := kappa_E_mem_A h i.swap (X_le_E h i.swap hx)
  have hcN' : c ∈ normalizer (𝐀[i.swap] : Set G) := h.N_le_normalizer_A i.swap hcN
  have hcU : c ∈ normalizer (𝐔[i.swap] : Set G) := h.N_le_normalizer_U i.swap hcN
  rw [psiG_eq_iff h.twoCore φ i.swap ((mem_normalizer_iff.mp hcN' _).mp hκ)
    ((mem_normalizer_iff.mp hcN' _).mp ha)]
  have h1 : (t⁻¹ * (x⁻¹ * t * x))⁻¹ * a ∈ 𝐔[i.swap] :=
    (psiG_eq_iff h.twoCore φ i.swap hκ ha).mp hxa
  have h2 := (mem_normalizer_iff.mp hcU _).mp h1
  rwa [show c * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * a) * c⁻¹ =
    (c * (t⁻¹ * (x⁻¹ * t * x)) * c⁻¹)⁻¹ * (c * a * c⁻¹) by group] at h2

theorem aff₂_eq_one_iff (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (g : 𝐄𝐧[i.swap]) : (actHyp₂ h i hbot).aff g = 1 ↔ (g : G) ∈ 𝐄[i.swap] := by
  constructor
  · intro h1
    have hgN : (g : G) ∈ 𝐍[i.swap] :=
      (aff₂_zero_eq_zero_iff h i hne hbot g).mp (by rw [h1]; rfl)
    have hgN' : (g : G) ∈ (𝐄[i.swap] : Set G) * ((𝐂 ⊓ 𝐍[i.swap] : Subgroup G) : Set G) := by
      rw [E_mul_C0 h i.swap]
      exact hgN
    obtain ⟨e, he, c, hc, hgec⟩ := hgN'
    obtain ⟨hcC, hcN⟩ := mem_inf.mp hc
    have hdec : g = ⟨e, N_le_En h i.swap (map_subtype_le _ he)⟩ * ⟨c, N_le_En h i.swap hcN⟩ :=
      Subtype.ext hgec.symm
    have hc1 : (actHyp₂ h i hbot).aff ⟨c, N_le_En h i.swap hcN⟩ = 1 := by
      rw [hdec, map_mul, aff₂_E h i hbot he, one_mul] at h1
      exact h1
    have hcB : c ∈ 𝐁[i.swap] := h.mem_B_of_lin_eq_one i.swap hcC hcN fun a ha => by
      rw [← aff₂_of_C h i hbot hcC hcN ha, hc1]
      rfl
    rw [← hgec]
    exact mul_mem he (h.D_le_E i.swap (h.B_le_D i.swap hcB))
  · intro he
    have e : g = ⟨g, N_le_En h i.swap (map_subtype_le _ he)⟩ := rfl
    rw [e]
    exact aff₂_E h i hbot he

theorem aff₂_linear (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (M : GL (Fin 2) K) : ∃ g : 𝐄𝐧[i.swap], (g : G) ∈ 𝐍[i.swap] ∧
      ∀ x, (actHyp₂ h i hbot).aff g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x := by
  obtain ⟨c, hc, hcM⟩ := h.exists_linear i.swap M
  obtain ⟨hcC, hcN⟩ := mem_inf.mp hc
  refine ⟨⟨c, N_le_En h i.swap hcN⟩, hcN, fun x => ?_⟩
  obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i.swap x
  rw [aff₂_of_C h i hbot hcC hcN ha, hcM a ha]

theorem aff₂_translations (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (∀ b : Fin 2 → K, ∃ g : 𝐄𝐧[i.swap], ∀ x, (actHyp₂ h i hbot).aff g x = x + b) ∧
    ∀ R : Subgroup G, R ≤ 𝐄𝐧[i.swap] → (∀ g ∈ 𝐄𝐧[i.swap], ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      IsPGroup 2 R → ∀ r : 𝐄𝐧[i.swap], (r : G) ∈ R →
        (actHyp₂ h i hbot).aff r ∈ translations (Fin 2 → K) := by
  set hA := actHyp₂ h i hbot with hAdef
  set ρ := hA.aff with hρ
  set F : Subgroup (Equiv.Perm (Fin 2 → K)) := ρ.range with hF
  have hFA : ∀ g ∈ F, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, g x = b + f x := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hA.linAdd g, fun x => (hA.aff_eq g x).trans (add_comm _ _)⟩
  have hGL : ∀ M : GL (Fin 2) K, ∃ g ∈ F, ∀ x, g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x := by
    intro M
    obtain ⟨g, -, hg⟩ := aff₂_linear h i hbot M
    exact ⟨ρ g, ⟨g, rfl⟩, hg⟩
  have hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => x j ^ 2 ^ k := by
    rintro _ ⟨g, rfl⟩ hg0
    have hgN : (g : G) ∈ 𝐍[i.swap] := (aff₂_zero_eq_zero_iff h i hne hbot g).mp hg0
    have hgN' : (g : G) ∈ (𝐄[i.swap] : Set G) * ((𝐂 ⊓ 𝐍[i.swap] : Subgroup G) : Set G) := by
      rw [E_mul_C0 h i.swap]
      exact hgN
    obtain ⟨e, he, c, hc, hgec⟩ := hgN'
    obtain ⟨hcC, hcN⟩ := mem_inf.mp hc
    have hdec : g = ⟨e, N_le_En h i.swap (map_subtype_le _ he)⟩ * ⟨c, N_le_En h i.swap hcN⟩ :=
      Subtype.ext hgec.symm
    obtain ⟨A₀, k, hk, hA₀⟩ := semilinear h i.swap hcN
    refine ⟨A₀, k, hk, fun x => ?_⟩
    obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i.swap x
    rw [hdec, map_mul, aff₂_E h i hbot he, one_mul, aff₂_of_C h i hbot hcC hcN ha, hA₀ a ha]
  have hfrom0 : ∀ v : Fin 2 → K, ∃ g ∈ F, g 0 = v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨1, one_mem F, by rw [hv]; rfl⟩
    obtain ⟨y, hyY, hyN⟩ := exists_Y_not_N h i hne hbot
    set g : 𝐄𝐧[i.swap] := ⟨y, Y_le_En h i hne hbot hyY⟩
    have hw : ρ g 0 ≠ 0 := fun h0 => hyN ((aff₂_zero_eq_zero_iff h i hne hbot g).mp h0)
    obtain ⟨Mw, hMw⟩ := exists_mulVec_e1 hw
    obtain ⟨Mv, hMv⟩ := exists_mulVec_e1 hv
    have hw1 : ((Mw⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ρ g 0 = e1 := by
      rw [← hMw, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    obtain ⟨c, -, hc⟩ := aff₂_linear h i hbot (Mv * Mw⁻¹)
    refine ⟨ρ (c * g), ⟨c * g, rfl⟩, ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply, hc, Matrix.GeneralLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, hw1, hMv]
  have hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y := by
    intro x y
    obtain ⟨f₁, hf₁, h₁⟩ := hfrom0 x
    obtain ⟨f₂, hf₂, h₂⟩ := hfrom0 y
    refine ⟨f₂ * f₁⁻¹, mul_mem hf₂ (inv_mem hf₁), ?_⟩
    rw [Equiv.Perm.mul_apply, ← h₁, show f₁⁻¹ (f₁ 0) = 0 from Equiv.Perm.inv_eq_iff_eq.mpr rfl,
      h₂]
  obtain ⟨hTF, hcore, -⟩ :=
    ComponentInitial.binary_affine_plane_semilinear_stabilizer_normal_translations
    h.setup.two_le h.setup.card_K F hFA hFtr hGL hΓL
  refine ⟨fun b => ?_, fun R hRE hRn hR2 r hr => ?_⟩
  · obtain ⟨g, hg⟩ := hTF (show Equiv.addRight b ∈ translations (Fin 2 → K) from ⟨b, fun _ => rfl⟩)
    exact ⟨g, fun x => by rw [hg]; rfl⟩
  · set R' : Subgroup (Equiv.Perm (Fin 2 → K)) := (R.subgroupOf 𝐄𝐧[i.swap]).map ρ with hR'
    have hR'F : R' ≤ F := map_le_range _ _
    have hR'n : (R'.subgroupOf F).Normal := by
      refine ⟨fun f hf h' => ?_⟩
      rw [mem_subgroupOf] at hf ⊢
      obtain ⟨r', hr', hrf⟩ := hf
      obtain ⟨g, hg⟩ := h'.2
      refine ⟨g * r' * g⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf] at hr' ⊢
        exact hRn g g.2 r' hr'
      · rw [map_mul, map_mul, map_inv, hg, hrf]
        rfl
    have hR'2 : IsPGroup 2 (R'.subgroupOf F) :=
      ((hR2.of_equiv (subgroupOfEquivOfLe hRE).symm).map ρ).of_equiv
        (subgroupOfEquivOfLe hR'F).symm
    have hle : R'.subgroupOf F ≤ CFSG.Assembly.pCore 2 F :=
      le_sSup ⟨hR'n, hR'2⟩
    have hmem : (⟨ρ r, r, rfl⟩ : F) ∈ R'.subgroupOf F :=
      mem_subgroupOf.mpr ⟨r, mem_subgroupOf.mpr hr, rfl⟩
    rw [← hcore]
    exact ⟨_, hle hmem, rfl⟩

omit [Finite G] [CharP K 2] [Finite K] in
theorem conj_mem_translations' {f τ : Equiv.Perm (Fin 2 → K)}
    (hf : ∃ (b : Fin 2 → K) (g : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, f x = b + g x)
    (hτ : τ ∈ translations (Fin 2 → K)) : f * τ * f⁻¹ ∈ translations (Fin 2 → K) := by
  obtain ⟨b, g, hfg⟩ := hf
  obtain ⟨c, hc⟩ := hτ
  refine ⟨g c, fun x => ?_⟩
  have hy : f (f⁻¹ x) = x := perm_apply_inv f x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc, hfg, map_add, ← add_assoc, ← hfg, hy]

omit [Finite G] [CharP K 2] [Finite K] in
theorem eq_one_of_mem_translations {τ : Equiv.Perm (Fin 2 → K)}
    (hτ : τ ∈ translations (Fin 2 → K)) {x : Fin 2 → K} (hx : τ x = x) : τ = 1 := by
  obtain ⟨c, hc⟩ := hτ
  have hc0 : c = 0 := by
    have := hc x
    rw [hx] at this
    exact (add_eq_left.mp this.symm)
  exact Equiv.ext fun y => by rw [hc, hc0, add_zero]; rfl

@[expose] noncomputable def transX (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Subgroup G :=
  ((translations (Fin 2 → K)).comap (actHyp₂ h i hbot).aff).map 𝐄𝐧[i.swap].subtype

theorem mem_transX_iff (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (g : 𝐄𝐧[i.swap]) :
    (g : G) ∈ transX h i hbot ↔ (actHyp₂ h i hbot).aff g ∈ translations (Fin 2 → K) := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    have e : g' = g := Subtype.ext hgg'
    exact e ▸ hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem transX_le (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    transX h i hbot ≤ 𝐄𝐧[i.swap] :=
  map_subtype_le _

theorem conj_mem_transX (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {g : G} (hg : g ∈ 𝐄𝐧[i.swap]) {x : G} (hx : x ∈ transX h i hbot) :
    g * x * g⁻¹ ∈ transX h i hbot := by
  have hxE := transX_le h i hbot hx
  have hxT := (mem_transX_iff h i hbot ⟨x, hxE⟩).mp hx
  have hgx : g * x * g⁻¹ ∈ 𝐄𝐧[i.swap] := mul_mem (mul_mem hg hxE) (inv_mem hg)
  refine (mem_transX_iff h i hbot ⟨_, hgx⟩).mpr ?_
  have e2 : (actHyp₂ h i hbot).aff ⟨g * x * g⁻¹, hgx⟩ = (actHyp₂ h i hbot).aff ⟨g, hg⟩ *
      (actHyp₂ h i hbot).aff ⟨x, hxE⟩ * ((actHyp₂ h i hbot).aff ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e2]
  exact conj_mem_translations' ⟨_, (actHyp₂ h i hbot).linAdd _,
    fun y => ((actHyp₂ h i hbot).aff_eq _ y).trans (add_comm _ _)⟩ hxT

theorem E_le_transX (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐄[i.swap] ≤ transX h i hbot := fun e he =>
  (mem_transX_iff h i hbot ⟨e, N_le_En h i.swap (map_subtype_le _ he)⟩).mpr
    (by rw [aff₂_E h i hbot he]; exact one_mem _)

theorem mem_E_of_mem_transX (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G}
    (hx : x ∈ transX h i hbot) (hxN : x ∈ 𝐍[i.swap]) : x ∈ 𝐄[i.swap] := by
  have hxE := transX_le h i hbot hx
  have hxT := (mem_transX_iff h i hbot ⟨x, hxE⟩).mp hx
  have h0 := (aff₂_zero_eq_zero_iff h i hne hbot ⟨x, hxE⟩).mpr hxN
  exact (aff₂_eq_one_iff h i hne hbot _).mp (eq_one_of_mem_translations hxT h0)

theorem isPGroup_transX (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    IsPGroup 2 (transX h i hbot) := by
  intro g
  have hgE := transX_le h i hbot g.2
  have hgT := (mem_transX_iff h i hbot ⟨g, hgE⟩).mp g.2
  have hsq : (actHyp₂ h i hbot).aff (⟨g, hgE⟩ ^ 2) = 1 := by
    obtain ⟨b, hb⟩ := hgT
    ext x
    rw [map_pow, pow_two, Equiv.Perm.mul_apply, hb, hb, add_assoc, CharTwo.add_self_eq_zero,
      add_zero]
    rfl
  have hg2E : (g : G) ^ 2 ∈ 𝐄[i.swap] := (aff₂_eq_one_iff h i hne hbot _).mp hsq
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup.map (𝐍[i.swap]).subtype) ⟨_, hg2E⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk' ⊢
  rw [pow_succ', pow_mul]
  exact hk'

theorem pCore_eq_transX (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐏₂[i.swap] = transX h i hbot :=
  pCore_map_eq (transX_le h i hbot) (fun _ hg _ hx => conj_mem_transX h i hbot hg hx)
    (isPGroup_transX h i hne hbot) fun R hRE hRn hR2 r hr =>
      (mem_transX_iff h i hbot ⟨r, hRE hr⟩).mpr
        ((aff₂_translations h i hne hbot).2 R hRE hRn hR2 ⟨r, hRE hr⟩ hr)

theorem E_le_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i.swap] ≤ 𝐏₂[i.swap] := by
  rw [pCore_eq_transX h i hne hbot]
  exact E_le_transX h i hbot

omit [Finite G] [Finite K] in
theorem P₂_le (k : Axis) : 𝐏₂[k] ≤ 𝐄𝐧[k] := map_subtype_le _

omit [Finite G] [Finite K] in
theorem conj_mem_P₂ (k : Axis) {g : G} (hg : g ∈ 𝐄𝐧[k]) {x : G} (hx : x ∈ 𝐏₂[k]) :
    g * x * g⁻¹ ∈ 𝐏₂[k] :=
  conj_mem_pCore_map hg hx

theorem P₂_inf_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₂[i.swap] ⊓ 𝐍[i.swap] = 𝐄[i.swap] := by
  apply le_antisymm
  · intro x hx
    rw [pCore_eq_transX h i hne hbot] at hx
    exact mem_E_of_mem_transX h i hne hbot hx.1 hx.2
  · exact le_inf (E_le_P₂ h i hne hbot) (map_subtype_le _)

theorem P₂_mul_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐏₂[i.swap] : Set G) * (𝐍[i.swap] : Set G) = (𝐄𝐧[i.swap] : Set G) := by
  ext g
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (P₂_le _ hx) (N_le_En h i.swap hy)
  · intro hg
    obtain ⟨z, hz⟩ := (aff₂_translations h i hne hbot).1 ((actHyp₂ h i hbot).aff ⟨g, hg⟩ 0)
    have hzT : (z : G) ∈ transX h i hbot :=
      (mem_transX_iff h i hbot z).mpr ⟨_, hz⟩
    refine ⟨z, (pCore_eq_transX h i hne hbot).symm ▸ hzT, (z : G)⁻¹ * g, ?_, by group⟩
    have e : (⟨(z : G)⁻¹ * g, mul_mem (inv_mem z.2) hg⟩ : 𝐄𝐧[i.swap]) = z⁻¹ * ⟨g, hg⟩ := rfl
    refine (aff₂_zero_eq_zero_iff h i hne hbot ⟨_, mul_mem (inv_mem z.2) hg⟩).mp ?_
    rw [e, map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq, hz, zero_add]

theorem kappa_En_mem_X (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐄𝐧[i.swap]) : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐗[i.swap] := by
  have := conj_t_mem_X h i hbot (inv_mem hx)
  rwa [inv_inv] at this

theorem kappa2_mem_A (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐄𝐧[i.swap]) :
    t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x))) ∈ 𝐀[i.swap] :=
  kappa_E_mem_A h i.swap (X_le_E h i.swap (kappa_En_mem_X h i hbot hx))

theorem psiG_kappa2 (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (x : 𝐄𝐧[i.swap]) :
    psiG φ i.swap (t⁻¹ * (((t⁻¹ * ((x : G)⁻¹ * t * x)))⁻¹ * t * (t⁻¹ * ((x : G)⁻¹ * t * x)))) =
      (actHyp₂ h i hbot).aff x⁻¹ 0 := by
  rw [(actHyp₂ h i hbot).aff_zero]
  simp only [coe_inv, inv_inv]
  rfl

theorem aff₂_inv_mem_translations (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G}
    (hx : x ∈ 𝐏₂[i.swap]) :
    (actHyp₂ h i hbot).aff ⟨x, P₂_le _ hx⟩⁻¹ ∈ translations (Fin 2 → K) := by
  have hxT : x⁻¹ ∈ transX h i hbot := (pCore_eq_transX h i hne hbot) ▸ inv_mem hx
  exact (mem_transX_iff h i hbot ⟨x⁻¹, P₂_le _ (inv_mem hx)⟩).mp hxT

theorem kappa2_mul (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G}
    (hx : x ∈ 𝐏₂[i.swap]) (hy : y ∈ 𝐏₂[i.swap]) :
    ((t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x)))) *
        (t⁻¹ * ((t⁻¹ * (y⁻¹ * t * y))⁻¹ * t * (t⁻¹ * (y⁻¹ * t * y)))))⁻¹ *
      (t⁻¹ * ((t⁻¹ * ((x * y)⁻¹ * t * (x * y)))⁻¹ * t * (t⁻¹ * ((x * y)⁻¹ * t * (x * y))))) ∈
        𝐔[i.swap] := by
  set ρ := (actHyp₂ h i hbot).aff with hρ
  have hxA := kappa2_mem_A h i hbot (P₂_le _ hx)
  have hyA := kappa2_mem_A h i hbot (P₂_le _ hy)
  have hxyA := kappa2_mem_A h i hbot (P₂_le _ (mul_mem hx hy))
  rw [← psiG_eq_iff h.twoCore φ i.swap (mul_mem hxA hyA) hxyA,
    psiG_mul h.twoCore φ i.swap hxA hyA, psiG_kappa2 h i hbot ⟨x, P₂_le _ hx⟩,
    psiG_kappa2 h i hbot ⟨y, P₂_le _ hy⟩, psiG_kappa2 h i hbot ⟨x * y, P₂_le _ (mul_mem hx hy)⟩]
  have e1 : (⟨x * y, P₂_le _ (mul_mem hx hy)⟩ : 𝐄𝐧[i.swap])⁻¹ =
      (⟨y, P₂_le _ hy⟩ : 𝐄𝐧[i.swap])⁻¹ * (⟨x, P₂_le _ hx⟩ : 𝐄𝐧[i.swap])⁻¹ := by
    rw [← mul_inv_rev]
    rfl
  obtain ⟨b, hb⟩ := aff₂_inv_mem_translations h i hne hbot hy
  rw [e1, map_mul, Equiv.Perm.mul_apply, hb ((actHyp₂ h i hbot).aff ⟨x, P₂_le _ hx⟩⁻¹ 0), hb 0,
    zero_add]

theorem kappa2_mem_U_iff (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G}
    (hx : x ∈ 𝐏₂[i.swap]) :
    t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x))) ∈ 𝐔[i.swap] ↔
      x ∈ 𝐄[i.swap] := by
  rw [← psiG_eq_zero_iff h.twoCore φ i.swap (kappa2_mem_A h i hbot (P₂_le _ hx)),
    psiG_kappa2 h i hbot ⟨x, P₂_le _ hx⟩, aff₂_zero_eq_zero_iff h i hne hbot]
  constructor
  · intro hxN
    rw [← P₂_inf_N h i hne hbot]
    have hx' : x⁻¹⁻¹ ∈ 𝐍[i.swap] := inv_mem (show x⁻¹ ∈ 𝐍[i.swap] from hxN)
    rw [inv_inv] at hx'
    exact mem_inf.mpr ⟨hx, hx'⟩
  · intro hxE
    exact inv_mem (map_subtype_le _ hxE)

theorem exists_kappa2_eq (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {a : G}
    (ha : a ∈ 𝐀[i.swap]) : ∃ x ∈ 𝐏₂[i.swap],
      (t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x))))⁻¹ * a ∈ 𝐔[i.swap] := by
  obtain ⟨z, hz⟩ := (aff₂_translations h i hne hbot).1 (psiG φ i.swap a)
  have hzT : (z : G) ∈ transX h i hbot := (mem_transX_iff h i hbot z).mpr ⟨_, hz⟩
  have hzP : (z : G)⁻¹ ∈ 𝐏₂[i.swap] := (pCore_eq_transX h i hne hbot).symm ▸ inv_mem hzT
  refine ⟨(z : G)⁻¹, hzP, ?_⟩
  rw [← psiG_eq_iff h.twoCore φ i.swap (kappa2_mem_A h i hbot (P₂_le _ hzP)) ha,
    psiG_kappa2 h i hbot ⟨_, P₂_le _ hzP⟩]
  have e1 : (⟨(z : G)⁻¹, P₂_le _ hzP⟩ : 𝐄𝐧[i.swap])⁻¹ = z := by
    apply Subtype.ext
    show ((z : G)⁻¹)⁻¹ = z
    rw [inv_inv]
  rw [e1, hz, zero_add]

theorem quotient_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hUA : (𝐔[i.swap].subgroupOf 𝐀[i.swap]).Normal) :
    ∃ _ : ((𝐄[i.swap]).subgroupOf 𝐏₂[i.swap]).Normal,
      ∃ e : (↥𝐏₂[i.swap] ⧸ (𝐄[i.swap]).subgroupOf 𝐏₂[i.swap]) ≃*
        (↥𝐀[i.swap] ⧸ 𝐔[i.swap].subgroupOf 𝐀[i.swap]),
      ∀ x : 𝐏₂[i.swap], ∃ a : 𝐀[i.swap],
        (a : G) = t⁻¹ * ((t⁻¹ * ((x : G)⁻¹ * t * x))⁻¹ * t * (t⁻¹ * ((x : G)⁻¹ * t * x))) ∧
        e x = a := by
  obtain ⟨hN, e, he⟩ := exists_quotient_equiv_of_hom_mod (P := 𝐏₂[i.swap]) (E := 𝐄[i.swap])
    hUA (fun x => t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x))))
    (fun _ hx => kappa2_mem_A h i hbot (P₂_le _ hx))
    (fun _ hx _ hy => kappa2_mul h i hne hbot hx hy)
    (fun _ hx => kappa2_mem_U_iff h i hne hbot hx) (fun _ ha => exists_kappa2_eq h i hne hbot ha)
  exact ⟨hN, e, fun x => ⟨⟨_, kappa2_mem_A h i hbot (P₂_le _ x.2)⟩, rfl, he x⟩⟩

omit [Finite G] [Finite K] in
theorem U_normal_A (h : FCHyp L K n φ t) (k : Axis) : ((𝐔[k]).subgroupOf 𝐀[k]).Normal :=
  ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    rw [coe_mul, coe_mul, coe_inv, A_mul_comm h k g.2 x.2, mul_inv_cancel_right]
    exact hx⟩

omit [Finite G] in
theorem card_A_quot_U (k : Axis) [((𝐔[k]).subgroupOf 𝐀[k]).Normal] :
    Nat.card (↥𝐀[k] ⧸ (𝐔[k]).subgroupOf 𝐀[k]) = Nat.card K ^ 2 := by
  have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐔[k]).subgroupOf 𝐀[k])
  rw [Nat.card_congr (subgroupOfEquivOfLe (pull_mono φ (rootU_le_rootA k))).toEquiv, card_pull,
    card_rootA, card_U] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2 : Nat.card K ^ 3 = Nat.card K ^ 2 * Nat.card K := by ring
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

theorem card_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐏₂[i.swap] = 2 * Nat.card K ^ 8 := by
  have hUA := U_normal_A h i.swap
  obtain ⟨_, e, -⟩ := quotient_P₂ h i hne hbot hUA
  have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐄[i.swap]).subgroupOf 𝐏₂[i.swap])
  rw [Nat.card_congr e.toEquiv, card_A_quot_U i.swap, Nat.card_congr (subgroupOfEquivOfLe
    (E_le_P₂ h i hne hbot)).toEquiv, card_E h i.swap] at h1
  rw [h1]
  ring

theorem X_le_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐗[i.swap] ≤ 𝐏₂[i.swap] :=
  (X_le_E h i.swap).trans (E_le_P₂ h i hne hbot)

theorem comm_P₂_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₂[i.swap]) {x : G}
    (hx : x ∈ 𝐗[i.swap]) : p * x * p⁻¹ * x⁻¹ ∈ 𝐊[i.swap] := by
  set hA := actHyp₂ h i hbot with hAdef
  have hpE := P₂_le _ hp
  have hpT : (p : G) ∈ transX h i hbot := (pCore_eq_transX h i hne hbot) ▸ hp
  obtain ⟨b, hb⟩ := (mem_transX_iff h i hbot ⟨p, hpE⟩).mp hpT
  have hlin : hA.lin ⟨p, hpE⟩ (psiX φ t i.swap x) = psiX φ t i.swap x := by
    have h1 := hA.aff_eq ⟨p, hpE⟩ (psiX φ t i.swap x)
    have h2 := hA.aff_zero ⟨p, hpE⟩
    rw [hb] at h1
    rw [hb, zero_add] at h2
    rw [← h2] at h1
    exact (add_right_cancel h1).symm
  rw [hA.lin_psi _ hx] at hlin
  have hpx : p * x * p⁻¹ ∈ 𝐗[i.swap] := hA.conj_A p hpE x hx
  have h3 := (hA.psi_eq_iff hpx hx).mp hlin
  have h4 := (mem_normalizer_iff.mp (mem_inf.mp (X_le_E h i.swap hx |> fun hxE =>
    N_le_En h i.swap (map_subtype_le _ hxE))).2 _).mp h3
  rwa [show x * ((p * x * p⁻¹)⁻¹ * x) * x⁻¹ = (p * x * p⁻¹ * x⁻¹)⁻¹ by group, inv_mem_iff] at h4

theorem mem_N_of_comm_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐄𝐧[i.swap])
    (hpt : t⁻¹ * (p * t * p⁻¹) ∈ 𝐊[i.swap]) : p ∈ 𝐍[i.swap] := by
  refine (aff₂_zero_eq_zero_iff h i hne hbot ⟨p, hp⟩).mp ?_
  rw [(actHyp₂ h i hbot).aff_zero]
  exact (psiX_eq_zero_iff h i.swap (conj_t_mem_X h i hbot hp)).mpr hpt

theorem t_mem_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : t ∈ 𝐏₂[i.swap] :=
  E_le_P₂ h i hne hbot (t_mem_E h i.swap)

omit [Finite G] [Finite K] in
theorem conj_mem_K_of_P₂ (k : Axis) {p : G} (hp : p ∈ 𝐏₂[k]) {x : G} (hx : x ∈ 𝐊[k]) :
    p * x * p⁻¹ ∈ 𝐊[k] :=
  (mem_normalizer_iff.mp (mem_inf.mp (P₂_le k hp)).2 x).mp hx

theorem exists_P₂_not_comm_t (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ p ∈ 𝐏₂[i.swap], t⁻¹ * (p * t * p⁻¹) ∉ 𝐊[i.swap] := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : 𝐏₂[i.swap] ≤ 𝐄[i.swap] := fun p hp => by
    rw [← P₂_inf_N h i hne hbot]
    exact mem_inf.mpr ⟨hp, mem_N_of_comm_t h i hne hbot (P₂_le _ hp) (hcon p hp)⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [card_P₂ h i hne hbot, card_E h i.swap] at h1
  have h4 := h.four_le_card
  have h5 : Nat.card K ^ 6 < Nat.card K ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem mem_X_of_comm_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐏₂[i.swap])
    (hc : ∀ p ∈ 𝐏₂[i.swap], x * p * x⁻¹ * p⁻¹ ∈ 𝐊[i.swap]) : x ∈ 𝐗[i.swap] := by
  have htP := t_mem_P₂ h i hne hbot
  have hxt : t⁻¹ * (x * t * x⁻¹) ∈ 𝐊[i.swap] := by
    have := conj_mem_K_of_P₂ _ (inv_mem htP) (hc t htP)
    rwa [show t⁻¹ * (x * t * x⁻¹ * t⁻¹) * t⁻¹⁻¹ = t⁻¹ * (x * t * x⁻¹) by group] at this
  have hxE : x ∈ 𝐄[i.swap] := by
    rw [← P₂_inf_N h i hne hbot]
    exact mem_inf.mpr ⟨hx, mem_N_of_comm_t h i hne hbot (P₂_le _ hx) hxt⟩
  have htX : t ∈ normalizer ((𝐗[i.swap] : Subgroup G) : Set G) :=
    R_le_normalizer_X h i.swap (Qi_le_R h i.swap (mem_sup_left (mem_sup_right (mem_zpowers t))))
  rw [← (X_sup_t h i.swap).2] at hxE
  rcases mem_or_mul_mem h.setup.t_mul_t htX hxE with h1 | h1
  · exact h1
  · exfalso
    set y := t * x with hy
    obtain ⟨p, hp, hpt⟩ := exists_P₂_not_comm_t h i hne hbot
    apply hpt
    have hyP := X_le_P₂ h i hne hbot h1
    have hc1 : x⁻¹ * p * x * p⁻¹ ∈ 𝐊[i.swap] := by
      have := conj_mem_K_of_P₂ _ (inv_mem hx) (comm_mem_symm (hc p hp))
      rwa [show x⁻¹ * (p * x * p⁻¹ * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * p * x * p⁻¹ by group] at this
    have hc2 : y * p * y⁻¹ * p⁻¹ ∈ 𝐊[i.swap] := comm_mem_symm (comm_P₂_X h i hne hbot hp h1)
    have hc3 : t * p * t⁻¹ * p⁻¹ ∈ 𝐊[i.swap] := by
      have e : t * p * t⁻¹ * p⁻¹ = (y * (x⁻¹ * p * x * p⁻¹) * y⁻¹) * (y * p * y⁻¹ * p⁻¹) := by
        rw [hy]
        group
      rw [e]
      exact mul_mem (conj_mem_K_of_P₂ _ hyP hc1) hc2
    have := conj_mem_K_of_P₂ _ (inv_mem htP) (comm_mem_symm hc3)
    rwa [show t⁻¹ * (p * t * p⁻¹ * t⁻¹) * t⁻¹⁻¹ = t⁻¹ * (p * t * p⁻¹) by group] at this

theorem center_P₂_quot (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ _ : ((𝐊[i.swap]).subgroupOf 𝐏₂[i.swap]).Normal,
      center (↥𝐏₂[i.swap] ⧸ (𝐊[i.swap]).subgroupOf 𝐏₂[i.swap]) =
        ((𝐗[i.swap]).subgroupOf 𝐏₂[i.swap]).map
          (QuotientGroup.mk' ((𝐊[i.swap]).subgroupOf 𝐏₂[i.swap])) := by
  have hn : ((𝐊[i.swap]).subgroupOf 𝐏₂[i.swap]).Normal :=
    ⟨fun x hx p => mem_subgroupOf.mpr (conj_mem_K_of_P₂ _ p.2 (mem_subgroupOf.mp hx))⟩
  refine ⟨hn, center_quotient_eq hn (K_le_X h i.swap) (fun _ hg _ hk => conj_mem_K_of_P₂ _ hg hk)
    fun x hx => ⟨fun hc =>
    mem_X_of_comm_P₂ h i hne hbot hx hc, fun hxX p hp => ?_⟩⟩
  have h1 := inv_mem (comm_P₂_X h i hne hbot hp hxX)
  rwa [show (p * x * p⁻¹ * x⁻¹)⁻¹ = x * p * x⁻¹ * p⁻¹ by group] at h1

theorem sq_P₂_mem_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₂[i.swap]) :
    p * p ∈ 𝐗[i.swap] := by
  set hA := actHyp₂ h i hbot with hAdef
  have hpE := P₂_le _ hp
  have hpT : p ∈ transX h i hbot := (pCore_eq_transX h i hne hbot) ▸ hp
  have hsq : hA.aff (⟨p, hpE⟩ * ⟨p, hpE⟩) = 1 := by
    obtain ⟨b, hb⟩ := (mem_transX_iff h i hbot ⟨p, hpE⟩).mp hpT
    ext x
    rw [map_mul, Equiv.Perm.mul_apply, hb, hb, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rfl
  have hp2E : p * p ∈ 𝐄[i.swap] := (aff₂_eq_one_iff h i hne hbot _).mp hsq
  have htX : t ∈ normalizer ((𝐗[i.swap] : Subgroup G) : Set G) :=
    R_le_normalizer_X h i.swap (Qi_le_R h i.swap (mem_sup_left (mem_sup_right (mem_zpowers t))))
  have hp2E' := hp2E
  rw [← (X_sup_t h i.swap).2] at hp2E'
  rcases mem_or_mul_mem h.setup.t_mul_t htX hp2E' with h1 | h1
  · exact h1
  · exfalso
    set x₀ := t * (p * p) with hx₀
    have hp2 : p * p = t * x₀ := by
      rw [hx₀, ← mul_assoc, h.setup.t_mul_t, one_mul]
    obtain ⟨z, hz⟩ := (aff₂_translations h i hne hbot).1 (psiX φ t i.swap x₀)
    have hzP : (z : G) ∈ 𝐏₂[i.swap] :=
      (pCore_eq_transX h i hne hbot).symm ▸ (mem_transX_iff h i hbot z).mpr ⟨_, hz⟩
    have hk : t⁻¹ * ((z : G) * (t * x₀) * (z : G)⁻¹) ∈ 𝐊[i.swap] := by
      have h2 := hA.aff_psi z h1
      rw [hz, CharTwo.add_self_eq_zero] at h2
      exact (psiX_eq_zero_iff h i.swap (hA.mem_A_aff z.2 h1)).mp h2.symm
    set p' := (z : G) * p * (z : G)⁻¹ with hp'
    have hp'P : p' ∈ 𝐏₂[i.swap] := mul_mem (mul_mem hzP hp) (inv_mem hzP)
    set k := t⁻¹ * ((z : G) * (t * x₀) * (z : G)⁻¹) with hkdef
    have hp'2 : p' * p' = t * k := by
      rw [hkdef, hp', ← hp2]
      group
    have hcomm : p' * (p' * p') * p'⁻¹ = p' * p' := by group
    have hp't : t⁻¹ * (p' * t * p'⁻¹) ∈ 𝐊[i.swap] := by
      rw [hp'2] at hcomm
      have e : t⁻¹ * (p' * t * p'⁻¹) = k * (p' * k * p'⁻¹)⁻¹ := by
        calc t⁻¹ * (p' * t * p'⁻¹) = t⁻¹ * (p' * (t * k) * p'⁻¹) * (p' * k * p'⁻¹)⁻¹ := by group
          _ = t⁻¹ * (t * k) * (p' * k * p'⁻¹)⁻¹ := by rw [hcomm]
          _ = k * (p' * k * p'⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hk (inv_mem (conj_mem_K_of_P₂ _ hp'P hk))
    have hp'E : p' ∈ 𝐄[i.swap] := by
      rw [← P₂_inf_N h i hne hbot]
      exact mem_inf.mpr ⟨hp'P, mem_N_of_comm_t h i hne hbot (P₂_le _ hp'P) hp't⟩
    have hp'A : p' * p' ∈ 𝐀[i.swap] := by
      rw [← closure_sq_E h i.swap]
      exact subset_closure ⟨p', hp'E, rfl⟩
    rw [hp'2] at hp'A
    apply t_not_mem_K h i.swap
    have := mul_mem (mem_sup_left hp'A : t * k ∈ 𝐊[i.swap]) (inv_mem hk)
    rwa [mul_inv_cancel_right] at this

theorem closure_sq_P₂_le (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    closure {x : G | ∃ y ∈ 𝐏₂[i.swap], x = y * y} ≤ 𝐗[i.swap] :=
  (closure_le _).mpr fun _ ⟨_, hy, he⟩ => he ▸ sq_P₂_mem_X h i hne hbot hy

theorem closure_sq_P₂_sup_K (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    closure {x : G | ∃ y ∈ 𝐏₂[i.swap], x = y * y} ⊔ 𝐊[i.swap] = 𝐗[i.swap] := by
  apply le_antisymm (sup_le (closure_sq_P₂_le h i hne hbot) (K_le_X h i.swap))
  intro x hx
  set hA := actHyp₂ h i hbot with hAdef
  obtain ⟨z, hz⟩ := (aff₂_translations h i hne hbot).1 (psiX φ t i.swap x)
  have hzP : (z : G) ∈ 𝐏₂[i.swap] :=
    (pCore_eq_transX h i hne hbot).symm ▸ (mem_transX_iff h i hbot z).mpr ⟨_, hz⟩
  have hz0 := hA.aff_zero z
  rw [hz, zero_add] at hz0
  have hc : t⁻¹ * ((z : G) * t * (z : G)⁻¹) ∈ 𝐗[i.swap] := hA.conj_t z z.2
  have h1 := (hA.psi_eq_iff hc hx).mp hz0.symm
  have h2 : t⁻¹ * ((z : G) * t * (z : G)⁻¹) ∈ closure {x : G | ∃ y ∈ 𝐏₂[i.swap], x = y * y} := by
    have := commutator_mem_closure_sq (t_mem_P₂ h i hne hbot) (inv_mem hzP)
    rwa [inv_inv] at this
  rw [show x = (t⁻¹ * ((z : G) * t * (z : G)⁻¹)) * ((t⁻¹ * ((z : G) * t * (z : G)⁻¹))⁻¹ * x) by
    group]
  exact mul_mem (mem_sup_left h2) (mem_sup_right h1)

end SecondCore

end NextCores

end CFSG.LocalAnalysis.SymplecticFourStandard
