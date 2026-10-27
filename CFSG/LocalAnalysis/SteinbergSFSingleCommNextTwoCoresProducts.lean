module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresSecond

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace NextCores

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
  CFSG.LocalAnalysis.ComponentInitial.BinaryAffinePlane
open scoped Matrix Pointwise

section Products

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

theorem comm_U_of_two_group (h : FCHyp L K n φ t) (k : Axis) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRU : R ≤ normalizer (𝐔[k] : Set G)) (hJR : 𝐉 ≤ normalizer (R : Set G))
    {x : G} (hx : x ∈ R) {u : G} (hu : u ∈ 𝐔[k]) : x * u * x⁻¹ = u := by
  set H₀ := R ⊔ 𝐉 with hH₀
  have hH₀U : H₀ ≤ normalizer (𝐔[k] : Set G) := sup_le hRU (FCHyp.torus_le_normalizer_U k)
  have hH₀R : H₀ ≤ normalizer (R : Set G) := sup_le le_normalizer hJR
  set ψ : G → K := Function.invFun (coordG φ k) with hψ
  have hψc : ∀ v ∈ 𝐔[k], coordG φ k (ψ v) = v := fun v hv =>
    Function.invFun_eq (exists_coordG_eq φ k hv)
  have hψx : ∀ y : K, ψ (coordG φ k y) = y := fun y =>
    Function.leftInverse_invFun (coordG_injective φ k) y
  have hA : ActHyp ψ 1 𝐔[k] ⊥ H₀ :=
    { U_le := bot_le
      add := fun a ha b hb => coordG_injective φ k (by
        rw [coordG_add, hψc a ha, hψc b hb, hψc _ (mul_mem ha hb)])
      ker := fun a ha => by
        rw [mem_bot]
        constructor
        · intro h0
          rw [← hψc a ha, h0, coordG_zero]
        · rintro rfl
          rw [← coordG_zero φ k, hψx]
      surj := fun v => ⟨coordG φ k v, coordG_mem φ k v, hψx v⟩
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
    obtain ⟨δ, hδ, hδc⟩ := FCHyp.torus_trans (φ := φ) k hv hw
    refine ⟨δ, mem_sup_right hδ, ?_⟩
    rw [← hψx v, hA.linFun_psi (mem_sup_right hδ) (coordG_mem φ k v), hδc, hψx]
  have hfix := hA.linFun_eq_of_normal le_rfl (le_sup_left : R ≤ H₀)
    (fun g hg r hr => (mem_normalizer_iff.mp (hH₀R hg) r).mp hr) hR2 h2K htrans hx (ψ u)
  rw [hA.linFun_psi (mem_sup_left hx) hu] at hfix
  rw [← hψc _ ((mem_normalizer_iff.mp (hRU hx) u).mp hu), hfix, hψc u hu]

theorem Dn_le_normalizer_U (h : FCHyp L K n φ t) (k : Axis) :
    𝐃𝐧[k] ≤ normalizer (𝐔[k] : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun u hu => ?_
  rw [← closure_sq_D h k] at hu ⊢
  have hle : (closure {x : G | ∃ y ∈ 𝐃[k], x = y * y}).map (MulAut.conj g).toMonoidHom ≤
      closure {x : G | ∃ y ∈ 𝐃[k], x = y * y} := by
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle ⟨u, hu, rfl⟩

theorem R_le_Dn (h : FCHyp L K n φ t) (k : Axis) : 𝐑[k] ≤ 𝐃𝐧[k] :=
  (R_le_N h k).trans (N_le_normalizer_D h k)

omit [Finite G] in
theorem comm_mem_of_sq_mem {E : Subgroup G} {x y : G} (hx : x * x ∈ E) (hy : y * y ∈ E)
    (hxy : x * y * (x * y) ∈ E) (hyE : y ∈ normalizer (E : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ E := by
  have h1 : y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹ ∈ E :=
    (mem_normalizer_iff.mp (inv_mem hyE) _).mp (inv_mem hx)
  rw [show x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ by
    group]
  exact mul_mem (mul_mem hxy h1) (inv_mem hy)

theorem mem_E_of_sq_kappa_eq (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G}
    (hx : x ∈ 𝐏₁[i]) (hy : y ∈ 𝐏₁[i])
    (hxy : (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) =
      (t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y))) : x⁻¹ * y ∈ 𝐄[i] := by
  obtain ⟨_, e, he⟩ := quotient_P₁ h i hne hbot
  have h1 : e ((⟨x, hx⟩ : 𝐏₁[i]) : ↥𝐏₁[i] ⧸ (𝐄[i]).subgroupOf 𝐏₁[i]) =
      e ((⟨y, hy⟩ : 𝐏₁[i]) : ↥𝐏₁[i] ⧸ (𝐄[i]).subgroupOf 𝐏₁[i]) :=
    Subtype.ext (by rw [he, he]; exact hxy)
  have h2 := e.injective h1
  rw [QuotientGroup.eq, mem_subgroupOf] at h2
  exact h2

theorem sq_kappa_mem_U (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G}
    (hx : x ∈ 𝐏₁[i]) : (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) ∈ 𝐔[i] := by
  obtain ⟨_, e, he⟩ := quotient_P₁ h i hne hbot
  rw [← he ⟨x, hx⟩]
  exact (e _).2

theorem conj_mem_E_of_cent_U (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {c : G}
    (hcC : c ∈ 𝐂) (hcD : c ∈ 𝐃𝐧[i]) (hcU : ∀ u ∈ 𝐔[i], c * u * c⁻¹ = u) {x : G}
    (hx : x ∈ 𝐏₁[i]) : x⁻¹ * (c * x * c⁻¹) ∈ 𝐄[i] := by
  refine mem_E_of_sq_kappa_eq h i hne hbot hx (conj_mem_P₁ i hcD hx) ?_
  rw [kappa_conj_C hcC x, show c * (t⁻¹ * (x⁻¹ * t * x)) * c⁻¹ *
      (c * (t⁻¹ * (x⁻¹ * t * x)) * c⁻¹) =
      c * ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) * c⁻¹ by group,
    hcU _ (sq_kappa_mem_U h i hne hbot hx)]

theorem E_le_Dn (h : FCHyp L K n φ t) (k : Axis) : 𝐄[k] ≤ 𝐃𝐧[k] :=
  (map_subtype_le _).trans (N_le_normalizer_D h k)

theorem comm_R_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {r : G} (hr : r ∈ 𝐑[i]) {x : G} (hx : x ∈ 𝐏₁[i]) :
    x⁻¹ * (r * x * r⁻¹) ∈ 𝐄[i] := by
  rw [← SetLike.mem_coe, ← R_mul h i] at hr
  obtain ⟨q, hq, e, he, rfl⟩ := hr
  have hqC : q ∈ 𝐂 := h.setup.Q_le_C hq
  have hqD : q ∈ 𝐃𝐧[i] := R_le_Dn h i (le_sup_left (a := 𝐐) hq)
  have hqU : ∀ u ∈ 𝐔[i], q * u * q⁻¹ = u := fun u hu => by
    rw [h.Q_comm_ZP hq (pull_mono φ (rootU_le_center i) hu), mul_inv_cancel_right]
  have heD : e ∈ 𝐃𝐧[i] := E_le_Dn h i he
  have hx' : e * x * e⁻¹ ∈ 𝐏₁[i] := conj_mem_P₁ i heD hx
  have h1 : x⁻¹ * (e * x * e⁻¹) ∈ 𝐄[i] := by
    rw [show x⁻¹ * (e * x * e⁻¹) = (x⁻¹ * e * x⁻¹⁻¹) * e⁻¹ by group]
    exact mul_mem (conj_mem_E_of_normalizer_D h i (inv_mem (P₁_le i hx)) he) (inv_mem he)
  have h2 := conj_mem_E_of_cent_U h i hne hbot hqC hqD hqU hx'
  rw [show x⁻¹ * (q * e * x * (q * e)⁻¹) = (x⁻¹ * (e * x * e⁻¹)) *
    ((e * x * e⁻¹)⁻¹ * (q * (e * x * e⁻¹) * q⁻¹)) by group]
  exact mul_mem h1 h2

theorem P₁_le_normalizer_R (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ≤ normalizer (𝐑[i] : Set G) := by
  intro p hp
  refine mem_normalizer_of_conj_le fun r hr => ?_
  have h1 := comm_R_P₁ h i hne hbot hr (inv_mem hp)
  rw [show p⁻¹⁻¹ * (r * p⁻¹ * r⁻¹) = p * r * p⁻¹ * r⁻¹ by group] at h1
  rw [show p * r * p⁻¹ = (p * r * p⁻¹ * r⁻¹) * r by group]
  exact mul_mem (mem_sup_right h1) hr

theorem R_le_normalizer_P₁ (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ≤ normalizer (𝐏₁[i] : Set G) := fun _ hr =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_P₁ i (R_le_Dn h i hr) hx

theorem T₁_mul (h : FCHyp L K n φ t) (i : Axis) :
    (𝐑[i] : Set G) * (𝐏₁[i] : Set G) = (𝐓₁[i] : Set G) :=
  (coe_mul_of_left_le_normalizer_right _ _ (R_le_normalizer_P₁ h i)).symm

theorem R_inf_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐑[i] ⊓ 𝐏₁[i] = 𝐄[i] := by
  apply le_antisymm
  · intro x hx
    rw [← P₁_inf_N h i hne hbot]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, R_le_N h i (mem_inf.mp hx).1⟩
  · exact le_inf le_sup_right (E_le_P₁ h i hne hbot)

theorem card_T₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐓₁[i] = 2 * Nat.card K ^ 8 := by
  have h1 := card_sup_mul_card_inf 𝐏₁[i] 𝐑[i] (R_le_normalizer_P₁ h i)
  rw [sup_comm, inf_comm, R_inf_P₁ h i hne hbot, card_E h i, card_P₁ h i hne hbot,
    card_R h i] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2 : 2 * Nat.card K ^ 7 * (2 * Nat.card K ^ 7) =
      2 * Nat.card K ^ 8 * (2 * Nat.card K ^ 6) := by ring
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 6)) h1

theorem T₁_le_Dn (h : FCHyp L K n φ t) (i : Axis) : 𝐓₁[i] ≤ 𝐃𝐧[i] :=
  sup_le (R_le_Dn h i) (P₁_le i)

theorem P₁_le_normalizer_H (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ≤ normalizer ((𝐇 : Subgroup G) : Set G) := by
  intro p hp
  have hpR := P₁_le_normalizer_R h i hne hbot hp
  have hpD : p ∈ 𝐃𝐧[i] := P₁_le i hp
  set S := (𝐇 : Subgroup G).map (MulAut.conj p).toMonoidHom with hSdef
  have hSR : S ≤ 𝐑[i] := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hpR x).mp (H_le_R h i hx)
  have hSsq : ∀ s ∈ S, s * s ∈ 𝐃[i] := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x * x ∈ 𝐃[i] := h.B_le_D i (ZP_le_B i (mul_self_mem_ZP h hx))
    have h2 := (mem_normalizer_iff.mp hpD _).mp h1
    have e2 : (MulAut.conj p).toMonoidHom x * (MulAut.conj p).toMonoidHom x =
        p * (x * x) * p⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e2]
    exact h2
  rcases le_E_or_le_H h i hSR hSsq with hSE | hSH
  · exfalso
    have hHE : (𝐇 : Subgroup G) ≤ 𝐇 ⊓ 𝐄[i] := by
      intro x hx
      refine mem_inf.mpr ⟨hx, ?_⟩
      have h1 := hSE ⟨x, hx, rfl⟩
      have h2 := conj_mem_E_of_normalizer_D h i (inv_mem hpD) h1
      rwa [show p⁻¹ * (MulAut.conj p).toMonoidHom x * p⁻¹⁻¹ = x by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group] at h2
    have h1 := Subgroup.card_le_of_le hHE
    rw [h.H_facts.2.2, card_Hi h i] at h1
    have h4 := h.four_le_card
    have h5 : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  · exact mem_normalizer_of_conj_le fun x hx => hSH ⟨x, hx, rfl⟩

theorem T₁_le_Y (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₁[i] ≤ 𝐘[i, i] := by
  refine sup_le (fun r hr => mem_inf.mpr ⟨R_le_Nhat h i hne hbot i hr,
    R_le_normalizer_Hk h i hr⟩) fun p hp => ?_
  have hpH := P₁_le_normalizer_H h i hne hbot hp
  have hpD : p ∈ 𝐃𝐧[i] := P₁_le i hp
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨hpH, Dn_le_normalizer_U h i hpD⟩, ?_⟩
  exact mem_normalizer_of_conj_le fun x hx => mem_inf.mpr
    ⟨(mem_normalizer_iff.mp hpH x).mp (mem_inf.mp hx).1,
      conj_mem_E_of_normalizer_D h i hpD (mem_inf.mp hx).2⟩

theorem T₁_inf_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₁[i] ⊓ 𝐍[i] = 𝐑[i] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxN⟩ := mem_inf.mp hx
    rw [← SetLike.mem_coe, ← T₁_mul h i] at hxT
    obtain ⟨r, hr, p, hp, rfl⟩ := hxT
    have hpN : p ∈ 𝐍[i] := by
      have := mul_mem (inv_mem (R_le_N h i hr)) hxN
      rwa [inv_mul_cancel_left] at this
    have hpE : p ∈ 𝐄[i] := by
      rw [← P₁_inf_N h i hne hbot]
      exact mem_inf.mpr ⟨hp, hpN⟩
    exact mul_mem hr (mem_sup_right hpE)
  · exact le_inf le_sup_left (R_le_N h i)

theorem R_le_NR (h : FCHyp L K n φ t) (k : Axis) : 𝐑[k] ≤ 𝐍𝐑[k] :=
  le_inf le_normalizer (R_le_N h k)

theorem T₁_inf_NR (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₁[i] ⊓ 𝐍𝐑[i] = 𝐑[i] := by
  apply le_antisymm
  · intro x hx
    exact (T₁_inf_N h i hne hbot).le
      (mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).2⟩)
  · exact le_inf le_sup_left (R_le_NR h i)

theorem R_eq_H_sup_E (h : FCHyp L K n φ t) (k : Axis) : 𝐑[k] = 𝐇 ⊔ 𝐄[k] :=
  le_antisymm (sup_le (Q_le_H.trans le_sup_left) le_sup_right)
    (sup_le (H_le_R h k) le_sup_right)

theorem Y₁_le_normalizer_T₁ (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐘[i, i] ≤ normalizer (𝐓₁[i] : Set G) := by
  intro y hy
  have hyD : y ∈ 𝐃𝐧[i] := Nhat_inf_normalizer_Hi_le h i hne hbot hy
  have hyH : y ∈ normalizer ((𝐇 : Subgroup G) : Set G) := (mem_inf.mp (mem_inf.mp hy).1).1
  have hyR : ∀ r ∈ 𝐑[i], y * r * y⁻¹ ∈ 𝐑[i] := by
    intro r hr
    rw [R_eq_H_sup_E h i] at hr ⊢
    exact conj_mem_sup (fun x hx => (mem_normalizer_iff.mp hyH x).mp hx)
      (fun e he => conj_mem_E_of_normalizer_D h i hyD he) hr
  exact mem_normalizer_of_conj_le fun x hx =>
    conj_mem_sup hyR (fun p hp => conj_mem_P₁ i hyD hp) hx

theorem card_Y (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    Nat.card 𝐘[i, k] = Nat.card K * Nat.card 𝐍𝐑[k] := by
  have h1 : 𝐍𝐑[k].relIndex 𝐘[i, k] * Nat.card (𝐍𝐑[k] ⊓ 𝐘[i, k] : Subgroup G) =
      Nat.card 𝐘[i, k] := relIndex_mul_card _ _
  rw [second_index h i hne hbot k, inf_eq_left.mpr (NRB_le h i hne hbot k)] at h1
  exact h1.symm

theorem Y₁_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐘[i, i] : Set G) = (𝐓₁[i] : Set G) * (𝐍𝐑[i] : Set G) := by
  have hNT : 𝐍𝐑[i] ≤ normalizer (𝐓₁[i] : Set G) :=
    (NRB_le h i hne hbot i).trans (Y₁_le_normalizer_T₁ h i hne hbot)
  rw [← coe_mul_of_right_le_normalizer_left _ _ hNT]
  congr 1
  symm
  refine Subgroup.eq_of_le_of_card_ge (sup_le (T₁_le_Y h i hne hbot) (NRB_le h i hne hbot i))
    ?_
  have h1 := card_sup_mul_card_inf 𝐓₁[i] 𝐍𝐑[i] hNT
  rw [T₁_inf_NR h i hne hbot, card_T₁ h i hne hbot, card_R h i] at h1
  rw [card_Y h i hne hbot i]
  have h2 : 2 * Nat.card K ^ 8 * Nat.card 𝐍𝐑[i] =
      Nat.card K * Nat.card 𝐍𝐑[i] * (2 * Nat.card K ^ 7) := by ring
  rw [h2] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 7)) h1).symm.le

theorem sq_T₁_mem_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₁[i]) : x * x ∈ 𝐄[i] := by
  rw [← SetLike.mem_coe, ← T₁_mul h i] at hx
  obtain ⟨r, hr, p, hp, rfl⟩ := hx
  have hr2 : r * r ∈ 𝐄[i] := by
    have h1 := (parabolicHom_z_eq_zero_iff h i (⟨r, hr⟩ * ⟨r, hr⟩)).mp
    apply h1
    rw [map_mul, Heis.mul_z, CharTwo.add_self_eq_zero]
  have hp2 : p * p ∈ 𝐄[i] := by
    obtain ⟨_, e, he⟩ := quotient_P₁ h i hne hbot
    have h2 : e ((⟨p⁻¹, inv_mem hp⟩ : 𝐏₁[i]) : ↥𝐏₁[i] ⧸ (𝐄[i]).subgroupOf 𝐏₁[i]) =
        (e ((⟨p, hp⟩ : 𝐏₁[i]) : ↥𝐏₁[i] ⧸ (𝐄[i]).subgroupOf 𝐏₁[i]))⁻¹ := by
      rw [← map_inv]
      rfl
    have h3 : (t⁻¹ * (p⁻¹⁻¹ * t * p⁻¹)) * (t⁻¹ * (p⁻¹⁻¹ * t * p⁻¹)) =
        ((t⁻¹ * (p⁻¹ * t * p)) * (t⁻¹ * (p⁻¹ * t * p)))⁻¹ := by
      have := congrArg Subtype.val h2
      rw [he, coe_inv, he] at this
      exact this
    have hu := sq_kappa_mem_U h i hne hbot hp
    have h4 := mem_E_of_sq_kappa_eq h i hne hbot (inv_mem hp) hp (by
      rw [h3, inv_eq_of_mul_eq_one_right (A_mul_self h i (pull_mono φ (rootU_le_rootA i) hu))])
    rwa [inv_inv] at h4
  have hc : r⁻¹ * p * r * p⁻¹ ∈ 𝐄[i] := by
    have h1 := comm_R_P₁ h i hne hbot (inv_mem hr) hp
    have h2 := conj_mem_E_of_normalizer_D h i (P₁_le i hp) h1
    rwa [show p * (p⁻¹ * (r⁻¹ * p * r⁻¹⁻¹)) * p⁻¹ = r⁻¹ * p * r * p⁻¹ by group] at h2
  rw [show r * p * (r * p) = (r * r) * (r⁻¹ * p * r * p⁻¹) * (p * p) by group]
  exact mul_mem (mul_mem hr2 hc) hp2

theorem comm_T₁_mem_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G} (hx : x ∈ 𝐓₁[i]) (hy : y ∈ 𝐓₁[i]) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐄[i] :=
  comm_mem_of_sq_mem (sq_T₁_mem_E h i hne hbot hx) (sq_T₁_mem_E h i hne hbot hy)
    (sq_T₁_mem_E h i hne hbot (mul_mem hx hy))
    (mem_normalizer_of_conj_le fun _ he => conj_mem_E_of_normalizer_D h i (T₁_le_Dn h i hy) he)

theorem R_le_En (h : FCHyp L K n φ t) (k : Axis) : 𝐑[k] ≤ 𝐄𝐧[k] :=
  (R_le_N h k).trans (N_le_En h k)

theorem R_le_normalizer_P₂ (h : FCHyp L K n φ t) (k : Axis) :
    𝐑[k] ≤ normalizer (𝐏₂[k] : Set G) := fun _ hr =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_P₂ k (R_le_En h k hr) hx

theorem T₀_mul (h : FCHyp L K n φ t) (k : Axis) :
    (𝐑[k] : Set G) * (𝐏₂[k] : Set G) = (𝐓₀[k] : Set G) :=
  (coe_mul_of_left_le_normalizer_right _ _ (R_le_normalizer_P₂ h k)).symm

theorem T₀_le_En (h : FCHyp L K n φ t) (k : Axis) : 𝐓₀[k] ≤ 𝐄𝐧[k] :=
  sup_le (R_le_En h k) (P₂_le k)

theorem R_inf_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐑[i.swap] ⊓ 𝐏₂[i.swap] = 𝐄[i.swap] := by
  apply le_antisymm
  · intro x hx
    rw [← P₂_inf_N h i hne hbot]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, R_le_N h _ (mem_inf.mp hx).1⟩
  · exact le_inf le_sup_right (E_le_P₂ h i hne hbot)

theorem card_T₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐓₀[i.swap] = 2 * Nat.card K ^ 9 := by
  have h1 := card_sup_mul_card_inf 𝐏₂[i.swap] 𝐑[i.swap] (R_le_normalizer_P₂ h _)
  rw [show 𝐏₂[i.swap] ⊔ 𝐑[i.swap] = 𝐓₀[i.swap] from sup_comm _ _,
    show 𝐏₂[i.swap] ⊓ 𝐑[i.swap] = 𝐄[i.swap] from (inf_comm _ _).trans (R_inf_P₂ h i hne hbot),
    card_E h _, card_P₂ h i hne hbot, card_R h _] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2 : 2 * Nat.card K ^ 8 * (2 * Nat.card K ^ 7) =
      2 * Nat.card K ^ 9 * (2 * Nat.card K ^ 6) := by ring
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 6)) h1

theorem T₀_inf_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₀[i.swap] ⊓ 𝐍[i.swap] = 𝐑[i.swap] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxN⟩ := mem_inf.mp hx
    rw [← SetLike.mem_coe, ← T₀_mul h _] at hxT
    obtain ⟨r, hr, p, hp, rfl⟩ := hxT
    have hpN : p ∈ 𝐍[i.swap] := by
      have := mul_mem (inv_mem (R_le_N h _ hr)) hxN
      rwa [inv_mul_cancel_left] at this
    have hpE : p ∈ 𝐄[i.swap] := by
      rw [← P₂_inf_N h i hne hbot]
      exact mem_inf.mpr ⟨hp, hpN⟩
    exact mul_mem hr (mem_sup_right hpE)
  · exact le_inf le_sup_left (R_le_N h _)

theorem aff₂_P₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {p : G} (hp : p ∈ 𝐏₂[i.swap]) (v : Fin 2 → K) :
    (actHyp₂ h i hbot).aff ⟨p, P₂_le _ hp⟩ v = v + (actHyp₂ h i hbot).aff ⟨p, P₂_le _ hp⟩ 0 := by
  have hpT : p ∈ transX h i hbot := (pCore_eq_transX h i hne hbot) ▸ hp
  obtain ⟨b, hb⟩ := (mem_transX_iff h i hbot ⟨p, P₂_le _ hp⟩).mp hpT
  rw [hb, hb, zero_add]

theorem aff₂_rootAct (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {q : G} (hqC : q ∈ 𝐂) (hqN : q ∈ 𝐍[i.swap]) {c : K} (hc : RootAct φ i.swap q c)
    (v : Fin 2 → K) :
    (actHyp₂ h i hbot).aff ⟨q, N_le_En h _ hqN⟩ v = ![v 0 + c * v 1, v 1] := by
  obtain ⟨a, ha, rfl⟩ := exists_psiG_eq h.twoCore φ i.swap v
  rw [aff₂_of_C h i hbot hqC hqN ha, hc a ha]

theorem aff₂_R (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {r : G}
    (hr : r ∈ 𝐑[i.swap]) :
    ∃ c : K, ∀ v, (actHyp₂ h i hbot).aff ⟨r, R_le_En h _ hr⟩ v = ![v 0 + c * v 1, v 1] := by
  have hr' := hr
  rw [← SetLike.mem_coe, ← R_mul h _] at hr'
  obtain ⟨q, hq, e, he, hqe⟩ := hr'
  have hqR : q ∈ 𝐑[i.swap] := le_sup_left (a := 𝐐) hq
  have hqN : q ∈ 𝐍[i.swap] := R_le_N h _ hqR
  obtain ⟨c, hc⟩ := rootAct_of_mem_R h i.swap hqR
  refine ⟨c, fun v => ?_⟩
  have hdec : (⟨r, R_le_En h _ hr⟩ : 𝐄𝐧[i.swap]) =
      ⟨q, N_le_En h _ hqN⟩ * ⟨e, N_le_En h _ (map_subtype_le _ he)⟩ := Subtype.ext hqe.symm
  rw [hdec, map_mul, aff₂_E h i hbot he, mul_one]
  exact aff₂_rootAct h i hbot (h.setup.Q_le_C hq) hqN hc v

theorem aff₂_T₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₀[i.swap]) :
    ∃ (c : K) (b : Fin 2 → K), ∀ v,
      (actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩ v = ![v 0 + c * v 1, v 1] + b := by
  have hx' := hx
  rw [← SetLike.mem_coe, ← T₀_mul h _] at hx'
  obtain ⟨r, hr, p, hp, hrp⟩ := hx'
  obtain ⟨c, hc⟩ := aff₂_R h i hbot hr
  set b := (actHyp₂ h i hbot).aff ⟨p, P₂_le _ hp⟩ 0 with hb
  refine ⟨c, ![b 0 + c * b 1, b 1], fun v => ?_⟩
  have hdec : (⟨x, T₀_le_En h _ hx⟩ : 𝐄𝐧[i.swap]) =
      ⟨r, R_le_En h _ hr⟩ * ⟨p, P₂_le _ hp⟩ := Subtype.ext hrp.symm
  rw [hdec, map_mul, Equiv.Perm.mul_apply, aff₂_P₂ h i hne hbot hp, hc, ← hb]
  refine vec_ext ?_ ?_
  · simp
    ring
  · simp

theorem aff₂_T₀_snd (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₀[i.swap]) (v : Fin 2 → K) :
    ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩ v) 1 =
      v 1 + ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩ 0) 1 := by
  obtain ⟨c, b, hcb⟩ := aff₂_T₀ h i hne hbot hx
  rw [hcb, hcb]
  simp

theorem exists_root_one (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ r₀, ∃ hr₀ : r₀ ∈ 𝐑[i.swap],
      ∀ v, (actHyp₂ h i hbot).aff ⟨r₀, R_le_En h _ hr₀⟩ v = ![v 0 + v 1, v 1] := by
  obtain ⟨q, hqP, hq⟩ := exists_rootAct_P h i.swap 1
  have hqQ : q ∈ 𝐐 := mem_sup_left hqP
  have hqR : q ∈ 𝐑[i.swap] := le_sup_left (a := 𝐐) hqQ
  refine ⟨q, hqR, fun v => ?_⟩
  rw [aff₂_rootAct h i hbot (h.setup.Q_le_C hqQ) (R_le_N h _ hqR) hq v, one_mul]

theorem aff₂_inv_zero_snd (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₀[i.swap]) :
    ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩⁻¹ 0) 1 =
      ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩ 0) 1 := by
  have h1 : (actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩
      ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩⁻¹ 0) = 0 := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have h2 := aff₂_T₀_snd h i hne hbot hx ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩⁻¹ 0)
  rw [h1] at h2
  have h3 : (0 : Fin 2 → K) 1 = 0 := rfl
  rw [h3] at h2
  rw [eq_neg_of_add_eq_zero_left h2.symm, CharTwo.neg_eq]

theorem conj_mem_R_iff (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₀[i.swap]) {r : G}
    (hr : r ∈ 𝐑[i.swap]) :
    x * r * x⁻¹ ∈ 𝐑[i.swap] ↔
      (actHyp₂ h i hbot).aff ⟨r, R_le_En h _ hr⟩ ((actHyp₂ h i hbot).aff
        ⟨x, T₀_le_En h _ hx⟩⁻¹ 0) = (actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩⁻¹ 0 := by
  set ρ := (actHyp₂ h i hbot).aff with hρ
  set X : 𝐄𝐧[i.swap] := ⟨x, T₀_le_En h _ hx⟩
  set Rr : 𝐄𝐧[i.swap] := ⟨r, R_le_En h _ hr⟩
  have hxr : x * r * x⁻¹ ∈ 𝐓₀[i.swap] :=
    mul_mem (mul_mem hx (le_sup_left (a := 𝐑[i.swap]) hr)) (inv_mem hx)
  have hmemR : x * r * x⁻¹ ∈ 𝐑[i.swap] ↔ x * r * x⁻¹ ∈ 𝐍[i.swap] := by
    rw [← T₀_inf_N h i hne hbot]
    exact ⟨fun h1 => (mem_inf.mp h1).2, fun h1 => mem_inf.mpr ⟨hxr, h1⟩⟩
  rw [hmemR, ← aff₂_zero_eq_zero_iff h i hne hbot ⟨_, T₀_le_En h _ hxr⟩]
  have e : (⟨x * r * x⁻¹, T₀_le_En h _ hxr⟩ : 𝐄𝐧[i.swap]) = X * Rr * X⁻¹ := rfl
  rw [e, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro h1
    have h2 := congrArg (ρ X⁻¹) h1
    rwa [← Equiv.Perm.mul_apply (ρ X⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply] at h2
  · intro h1
    rw [h1, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem mem_normalizer_R_iff (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G}
    (hx : x ∈ 𝐓₀[i.swap]) :
    x ∈ normalizer (𝐑[i.swap] : Set G) ↔
      ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ hx⟩ 0) 1 = 0 := by
  rw [← aff₂_inv_zero_snd h i hne hbot hx]
  constructor
  · intro hxR
    obtain ⟨r₀, hr₀, hr₀v⟩ := exists_root_one h i hbot
    have h1 := (conj_mem_R_iff h i hne hbot hx hr₀).mp ((mem_normalizer_iff.mp hxR r₀).mp hr₀)
    rw [hr₀v] at h1
    have h2 := congrFun h1 0
    simpa using h2
  · intro hw
    refine mem_normalizer_of_conj_le fun r hr => ?_
    refine (conj_mem_R_iff h i hne hbot hx hr).mpr ?_
    obtain ⟨c, hc⟩ := aff₂_R h i hbot hr
    rw [hc]
    refine vec_ext ?_ ?_
    · simp only [Matrix.cons_val_zero]
      rw [hw, mul_zero, add_zero]
    · simp

omit [Finite G] [Finite K] in
theorem R_le_T₂ (k : Axis) : 𝐑[k] ≤ 𝐓₂[k] := le_inf le_sup_left le_normalizer

theorem T₂_inf_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₂[i.swap] ⊓ 𝐍[i.swap] = 𝐑[i.swap] := by
  apply le_antisymm
  · intro x hx
    exact (T₀_inf_N h i hne hbot).le
      (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1, (mem_inf.mp hx).2⟩)
  · exact le_inf (R_le_T₂ _) (R_le_N h _)

theorem T₂_inf_NR (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₂[i.swap] ⊓ 𝐍𝐑[i.swap] = 𝐑[i.swap] := by
  apply le_antisymm
  · intro x hx
    exact (T₂_inf_N h i hne hbot).le
      (mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).2⟩)
  · exact le_inf (R_le_T₂ _) (R_le_NR h _)

theorem snd_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (x y : 𝐓₀[i.swap]) :
    ((actHyp₂ h i hbot).aff ⟨((x * y : 𝐓₀[i.swap]) : G), T₀_le_En h _ (x * y).2⟩ 0) 1 =
      ((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ x.2⟩ 0) 1 +
        ((actHyp₂ h i hbot).aff ⟨y, T₀_le_En h _ y.2⟩ 0) 1 := by
  have e : (⟨((x * y : 𝐓₀[i.swap]) : G), T₀_le_En h _ (x * y).2⟩ : 𝐄𝐧[i.swap]) =
      ⟨x, T₀_le_En h _ x.2⟩ * ⟨y, T₀_le_En h _ y.2⟩ := rfl
  rw [e, map_mul, Equiv.Perm.mul_apply, aff₂_T₀_snd h i hne hbot x.2, add_comm]

theorem exists_snd_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (b : K) :
    ∃ z : 𝐄𝐧[i.swap], (z : G) ∈ 𝐏₂[i.swap] ∧ (actHyp₂ h i hbot).aff z 0 = ![0, b] := by
  obtain ⟨z, hz⟩ := (aff₂_translations h i hne hbot).1 ![0, b]
  refine ⟨z, (pCore_eq_transX h i hne hbot).symm ▸ (mem_transX_iff h i hbot z).mpr ⟨_, hz⟩, ?_⟩
  rw [hz, zero_add]

theorem exists_snd_hom (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ β : 𝐓₀[i.swap] →* Multiplicative K, Function.Surjective β ∧
      ∀ x : 𝐓₀[i.swap], β x = Multiplicative.ofAdd
        (((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ x.2⟩ 0) 1) := by
  refine ⟨MonoidHom.mk' (fun x : 𝐓₀[i.swap] => Multiplicative.ofAdd
      (((actHyp₂ h i hbot).aff ⟨x, T₀_le_En h _ x.2⟩ 0) 1)) fun x y => ?_, fun b => ?_,
    fun x => rfl⟩
  · rw [snd_mul h i hne hbot x y, ofAdd_add]
  · obtain ⟨z, hzP, hz⟩ := exists_snd_eq h i hne hbot (Multiplicative.toAdd b)
    refine ⟨⟨z, le_sup_right (a := 𝐑[i.swap]) hzP⟩, ?_⟩
    rw [MonoidHom.mk'_apply]
    have e : (⟨((⟨z, le_sup_right (a := 𝐑[i.swap]) hzP⟩ : 𝐓₀[i.swap]) : G),
        T₀_le_En h _ (le_sup_right (a := 𝐑[i.swap]) hzP)⟩ : 𝐄𝐧[i.swap]) = z := rfl
    rw [e, hz]
    simp

theorem card_T₂ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐓₂[i.swap] = 2 * Nat.card K ^ 8 := by
  obtain ⟨β, hβs, hβ⟩ := exists_snd_hom h i hne hbot
  have hker : β.ker = 𝐓₂[i.swap].subgroupOf 𝐓₀[i.swap] := by
    ext x
    rw [MonoidHom.mem_ker, hβ, mem_subgroupOf, ofAdd_eq_one]
    constructor
    · intro h0
      exact mem_inf.mpr ⟨x.2, (mem_normalizer_R_iff h i hne hbot x.2).mpr h0⟩
    · intro hx
      exact (mem_normalizer_R_iff h i hne hbot x.2).mp (mem_inf.mp hx).2
  have h1 := card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : 𝐓₂[i.swap] ≤ 𝐓₀[i.swap])).toEquiv,
    card_T₀ h i hne hbot] at h1
  have h2 : Nat.card (Multiplicative K) = Nat.card K := rfl
  rw [h2] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  have h3 : 2 * Nat.card K ^ 9 = Nat.card K * (2 * Nat.card K ^ 8) := by ring
  rw [h3] at h1
  exact (Nat.eq_of_mul_eq_mul_left hq h1).symm

theorem sq_T₂_mem_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₂[i.swap]) :
    x * x ∈ 𝐄[i.swap] := by
  have hx0 := (mem_inf.mp hx).1
  have hb := (mem_normalizer_R_iff h i hne hbot hx0).mp (mem_inf.mp hx).2
  obtain ⟨c, b, hcb⟩ := aff₂_T₀ h i hne hbot hx0
  have hb1 : b 1 = 0 := by
    have := hcb 0
    rw [this] at hb
    simpa using hb
  refine (aff₂_eq_one_iff h i hne hbot ⟨_, T₀_le_En h _ (mul_mem hx0 hx0)⟩).mp ?_
  have e : (⟨x * x, T₀_le_En h _ (mul_mem hx0 hx0)⟩ : 𝐄𝐧[i.swap]) =
      ⟨x, T₀_le_En h _ hx0⟩ * ⟨x, T₀_le_En h _ hx0⟩ := rfl
  rw [e, map_mul]
  ext v j
  rw [Equiv.Perm.mul_apply, hcb, hcb]
  fin_cases j
  · simp [hb1]
    linear_combination (c * v 1 + b 0) * CharTwo.two_eq_zero (R := K)
  · simp [hb1]

theorem comm_T₂_mem_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x y : G} (hx : x ∈ 𝐓₂[i.swap]) (hy : y ∈ 𝐓₂[i.swap]) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐄[i.swap] :=
  comm_mem_of_sq_mem (sq_T₂_mem_E h i hne hbot hx) (sq_T₂_mem_E h i hne hbot hy)
    (sq_T₂_mem_E h i hne hbot (mul_mem hx hy))
    (mem_normalizer_iff.mpr fun e => (mem_normalizer_iff.mp
      (mem_inf.mp (T₀_le_En h _ (mem_inf.mp hy).1)).1 e))

theorem aff₂_inv_zero_snd_eq_zero (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (g : 𝐄𝐧[i.swap])
    (hgR : (g : G) ∈ normalizer (𝐑[i.swap] : Set G)) :
    ((actHyp₂ h i hbot).aff g⁻¹ 0) 1 = 0 := by
  set ρ := (actHyp₂ h i hbot).aff with hρ
  obtain ⟨r₀, hr₀, hr₀v⟩ := exists_root_one h i hbot
  have hgr : (g : G) * r₀ * (g : G)⁻¹ ∈ 𝐑[i.swap] := (mem_normalizer_iff.mp hgR r₀).mp hr₀
  have h0 := (aff₂_zero_eq_zero_iff h i hne hbot ⟨_, R_le_En h _ hgr⟩).mpr (R_le_N h _ hgr)
  have e : (⟨(g : G) * r₀ * (g : G)⁻¹, R_le_En h _ hgr⟩ : 𝐄𝐧[i.swap]) =
      g * ⟨r₀, R_le_En h _ hr₀⟩ * g⁻¹ := rfl
  rw [e, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h0
  have h1 := congrArg (ρ g⁻¹) h0
  rw [← Equiv.Perm.mul_apply (ρ g⁻¹) (ρ g), ← map_mul, inv_mul_cancel, map_one,
    Equiv.Perm.one_apply, hr₀v] at h1
  have h2 := congrFun h1 0
  simp only [Matrix.cons_val_zero] at h2
  exact add_eq_left.mp h2

theorem exists_T₂_mul_NR (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {g : G} (hg : g ∈ 𝐄𝐧[i.swap])
    (hgR : g ∈ normalizer (𝐑[i.swap] : Set G)) :
    ∃ p ∈ 𝐓₂[i.swap], ∃ m ∈ 𝐍𝐑[i.swap], g = p * m := by
  set ρ := (actHyp₂ h i hbot).aff with hρ
  set b := ρ ⟨g, hg⟩ 0 with hb
  have hb1 : b 1 = 0 := by
    have := aff₂_inv_zero_snd_eq_zero h i hne hbot ⟨g, hg⟩⁻¹ (inv_mem hgR)
    rwa [inv_inv] at this
  obtain ⟨z, hz⟩ := (aff₂_translations h i hne hbot).1 b
  have hzP : (z : G) ∈ 𝐏₂[i.swap] :=
    (pCore_eq_transX h i hne hbot).symm ▸ (mem_transX_iff h i hbot z).mpr ⟨_, hz⟩
  have hzT₀ : (z : G) ∈ 𝐓₀[i.swap] := le_sup_right (a := 𝐑[i.swap]) hzP
  have hzR : (z : G) ∈ normalizer (𝐑[i.swap] : Set G) := by
    refine (mem_normalizer_R_iff h i hne hbot hzT₀).mpr ?_
    have e : (⟨(z : G), T₀_le_En h _ hzT₀⟩ : 𝐄𝐧[i.swap]) = z := rfl
    rw [e, hz, zero_add, hb1]
  refine ⟨z, mem_inf.mpr ⟨hzT₀, hzR⟩, (z : G)⁻¹ * g,
    mem_inf.mpr ⟨mul_mem (inv_mem hzR) hgR, ?_⟩, by group⟩
  refine (aff₂_zero_eq_zero_iff h i hne hbot ⟨_, mul_mem (inv_mem z.2) hg⟩).mp ?_
  have e : (⟨(z : G)⁻¹ * g, mul_mem (inv_mem z.2) hg⟩ : 𝐄𝐧[i.swap]) = z⁻¹ * ⟨g, hg⟩ := rfl
  rw [e, map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq, hz, zero_add]

theorem NR_le_normalizer_T₂ (h : FCHyp L K n φ t) (k : Axis) :
    𝐍𝐑[k] ≤ normalizer (𝐓₂[k] : Set G) := by
  intro m hm
  obtain ⟨hmR, hmB⟩ := mem_inf.mp hm
  have hmE := N_le_En h k hmB
  refine mem_normalizer_of_conj_le fun x hx => mem_inf.mpr ⟨?_, ?_⟩
  · exact conj_mem_sup (fun r hr => (mem_normalizer_iff.mp hmR r).mp hr)
      (fun p hp => conj_mem_P₂ k hmE hp) (mem_inf.mp hx).1
  · exact mul_mem (mul_mem hmR (mem_inf.mp hx).2) (inv_mem hmR)

theorem Y₂_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐘[i, i.swap] = 𝐓₂[i.swap] ⊔ 𝐍𝐑[i.swap] := by
  have hle : 𝐘[i, i.swap] ≤ 𝐓₂[i.swap] ⊔ 𝐍𝐑[i.swap] := by
    intro y hy
    obtain ⟨p, hp, m, hm, rfl⟩ := exists_T₂_mul_NR h i hne hbot (Y_le_En h i hne hbot hy)
      (Y_le_normalizer_R h i hne hbot hy)
    exact mul_mem (mem_sup_left hp) (mem_sup_right hm)
  refine eq_of_le_of_card_ge hle ?_
  have h1 := card_sup_mul_card_inf 𝐓₂[i.swap] 𝐍𝐑[i.swap] (NR_le_normalizer_T₂ h _)
  rw [T₂_inf_NR h i hne hbot, card_T₂ h i hne hbot, card_R h _] at h1
  rw [card_Y h i hne hbot i.swap]
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2 : 2 * Nat.card K ^ 8 * Nat.card 𝐍𝐑[i.swap] =
      Nat.card K * Nat.card 𝐍𝐑[i.swap] * (2 * Nat.card K ^ 7) := by ring
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right (mul_pos two_pos (pow_pos hq 7)) h1).le

theorem Y₂_mul (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐘[i, i.swap] : Set G) = (𝐓₂[i.swap] : Set G) * (𝐍𝐑[i.swap] : Set G) := by
  rw [Y₂_eq h i hne hbot, coe_mul_of_right_le_normalizer_left _ _ (NR_le_normalizer_T₂ h _)]

theorem T₂_le_Y (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₂[i.swap] ≤ 𝐘[i, i.swap] := by
  rw [Y₂_eq h i hne hbot]
  exact le_sup_left

theorem Y₁_eq' (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐘[i, i] = 𝐓₁[i] ⊔ 𝐍𝐑[i] := by
  have hNT : 𝐍𝐑[i] ≤ normalizer (𝐓₁[i] : Set G) :=
    (NRB_le h i hne hbot i).trans (Y₁_le_normalizer_T₁ h i hne hbot)
  refine SetLike.coe_injective ?_
  rw [Y₁_eq h i hne hbot, coe_mul_of_right_le_normalizer_left _ _ hNT]

end Products

end NextCores

end CFSG.LocalAnalysis.SymplecticFourStandard
