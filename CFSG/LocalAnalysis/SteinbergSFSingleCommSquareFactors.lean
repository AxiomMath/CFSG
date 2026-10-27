module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommSquareFactorsBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleComm

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Indices

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐮[" a "," b "," c "," d "]" => ((φ.symm (uElt a b c d) : L) : G)

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
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
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)

theorem normalizer_D_le_normalizer_A (h : FCHyp L K n φ t) (k : Axis) :
    normalizer (𝐃[k] : Set G) ≤ normalizer (𝐀[k] : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun a ha => ?_
  rw [← center_D h k] at ha ⊢
  obtain ⟨haD, hac⟩ := mem_center_map_iff.mp ha
  refine mem_center_map_iff.mpr ⟨(mem_normalizer_iff.mp hg a).mp haD, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ 𝐃[k] := by
    have := (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
    rwa [inv_inv] at this
  have h1 := hac _ hy'
  calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = g * a * g⁻¹ * y := by group

theorem N_le_normalizer_D (h : FCHyp L K n φ t) (k : Axis) : 𝐍[k] ≤ normalizer (𝐃[k] : Set G) :=
  fun _ hg => mem_normalizer_of_conj_le fun _ hd => h.conj_mem_D k hg hd

theorem conj_mem_K_of_normalizer_D (h : FCHyp L K n φ t) (k : Axis) {g : G}
    (hg : g ∈ normalizer (𝐃[k] : Set G)) {x : G} (hx : x ∈ 𝐊[k]) : g * x * g⁻¹ ∈ 𝐊[k] := by
  set S := 𝐊[k].map (MulAut.conj g).toMonoidHom with hS
  have hSD : S ≤ 𝐃[k] := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp (K_le_D h k hy)
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, K_comm h k hx hy]
    group
  have hcard : Nat.card S = Nat.card 𝐊[k] := card_map_of_injective (MulAut.conj _).injective
  have hSK := (K_unique h k hSD hSc).2 hcard
  rw [← hSK]
  exact ⟨x, hx, rfl⟩

theorem normalizer_D_le_normalizer_B (h : FCHyp L K n φ t) (k : Axis)
    (hK : ∀ x ∈ 𝐊[k], x * x = 1) : normalizer (𝐃[k] : Set G) ≤ normalizer (𝐁[k] : Set G) := by
  intro g hg
  have htt := h.setup.t_mul_t
  have htN : t ∈ normalizer (𝐊[k] : Set G) := H_le_normalizer_K h k t_mem_H
  have hy : g * t * g⁻¹ ∈ 𝐃[k] := (mem_normalizer_iff.mp hg t).mp (t_mem_D h k)
  have hyK : g * t * g⁻¹ ∉ 𝐊[k] := fun h1 => by
    have := conj_mem_K_of_normalizer_D h k (inv_mem hg) h1
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact t_not_mem_K h k this
  have hty : t * (g * t * g⁻¹) ∈ 𝐊[k] :=
    (mem_or_mul_mem htt htN (by rw [(K_sup_t h k).2]; exact hy)).resolve_left hyK
  have e : g * t * g⁻¹ = t * (t * (g * t * g⁻¹)) := by rw [← mul_assoc, htt, one_mul]
  have hxA : t * (g * t * g⁻¹) ∈ 𝐀[k] := by
    rw [← K_inf_C h k]
    refine ⟨hty, mem_centralizer_singleton_iff.mpr ?_⟩
    have hyy : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
        mul_inv_cancel]
    set x := t * (g * t * g⁻¹) with hx
    rw [e] at hyy
    have h1 : t * x = (t * x)⁻¹ := eq_inv_of_mul_eq_one_left hyy
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right (hK x hty), h.twoCore.t_inv]
  have htg : g * t * g⁻¹ ∈ 𝐁[k] := by
    rw [e]
    exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hxA)
  exact mem_normalizer_zpowers_sup htg fun a ha =>
    (mem_normalizer_iff.mp (normalizer_D_le_normalizer_A h k hg) a).mp ha

theorem conj_R_mem_K (h : FCHyp L K n φ t) (k : Axis) {r : G} (hr : r ∈ 𝐑[k]) {x : G}
    (hx : x ∈ 𝐊[k]) : r * x * r⁻¹ ∈ 𝐊[k] := by
  rw [← X_inf_D h k] at hx ⊢
  exact ⟨(mem_normalizer_iff.mp (R_le_normalizer_X h k hr) x).mp hx.1,
    h.conj_mem_D k (R_le_N h k hr) hx.2⟩

theorem comm_mem_D_of_mem_Hk (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐇 ⊓ 𝐄[k])
    {r : G} (hr : r ∈ 𝐑[k]) : x * r * x⁻¹ * r⁻¹ ∈ 𝐃[k] := by
  have hxR : x ∈ 𝐑[k] := H_le_R h k (mem_inf.mp hx).1
  have hy : (parabolicHom h k ⟨x, hxR⟩).y = 0 := (mem_H_iff h k ⟨x, hxR⟩).mp (mem_inf.mp hx).1
  have hz : (parabolicHom h k ⟨x, hxR⟩).z = 0 :=
    (parabolicHom_z_eq_zero_iff h k ⟨x, hxR⟩).mpr (mem_inf.mp hx).2
  have h1 : (⟨x, hxR⟩ : 𝐑[k]) * ⟨r, hr⟩ * (⟨x, hxR⟩ : 𝐑[k])⁻¹ * (⟨r, hr⟩ : 𝐑[k])⁻¹ ∈
      (parabolicHom h k).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    ext <;> simp [hy, hz]
  rw [ker_parabolicHom] at h1
  exact h1

theorem mem_Hk_iff (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐑[k]) :
    x ∈ 𝐇 ⊓ 𝐄[k] ↔ ∀ r ∈ 𝐑[k], x * r * x⁻¹ * r⁻¹ ∈ 𝐊[k] := by
  constructor
  · intro hxH
    let Z : Subgroup G :=
      { carrier := {x | x ∈ 𝐑[k] ∧ ∀ r ∈ 𝐑[k], x * r * x⁻¹ * r⁻¹ ∈ 𝐊[k]}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨mul_mem ha hb, fun r hr => ?_⟩
          rw [show a * b * r * (a * b)⁻¹ * r⁻¹ =
            a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ * (a * r * a⁻¹ * r⁻¹) by group]
          exact mul_mem (conj_R_mem_K h k ha (hb' r hr)) (ha' r hr)
        one_mem' := ⟨one_mem _, fun r _ => by
          rw [one_mul, inv_one, mul_one, mul_inv_cancel]
          exact one_mem _⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨inv_mem ha, fun r hr => ?_⟩
          rw [show a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ = a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * a⁻¹⁻¹ by group]
          exact conj_R_mem_K h k (inv_mem ha) (inv_mem (ha' r hr)) }
    have hFZ : 𝐅 ≤ Z := fun f hf => ⟨mem_sup_right (F_le_E h k hf), fun r hr => by
      rw [← X_inf_D h k]
      refine ⟨?_, comm_mem_D_of_mem_Hk h k ⟨F_le_H h hf, F_le_E h k hf⟩ hr⟩
      have hfX : f ∈ 𝐅 ⊔ 𝐅ʷ[k] := mem_sup_left hf
      rw [show f * r * f⁻¹ * r⁻¹ = f * (r * f⁻¹ * r⁻¹) by group]
      exact mul_mem hfX ((mem_normalizer_iff.mp (R_le_normalizer_X h k hr) _).mp (inv_mem hfX))⟩
    have hAZ : 𝐀[k] ≤ Z := fun a ha => ⟨D_le_R h k (A_le_D h k ha), fun r hr => by
      have h1 := (mem_normalizer_iff.mp (h.N_le_normalizer_A k (R_le_N h k hr)) _).mp
        (inv_mem ha)
      rw [show a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) by group]
      exact mem_sup_left (mul_mem ha h1)⟩
    have htZ : t ∈ Z := ⟨D_le_R h k (t_mem_D h k), fun r hr => by
      have ha := conj_t_mem_A h k hr
      have hc : t * (t⁻¹ * (r * t * r⁻¹))⁻¹ = (t⁻¹ * (r * t * r⁻¹))⁻¹ * t :=
        h.twoCore.comm (pull_le φ _ (inv_mem ha))
      rw [show t * r * t⁻¹ * r⁻¹ = t * (t⁻¹ * (r * t * r⁻¹))⁻¹ * t⁻¹ by group, hc,
        mul_inv_cancel_right]
      exact mem_sup_left (inv_mem ha)⟩
    have hHZ : 𝐇 ⊓ 𝐄[k] ≤ Z := by
      rw [← L_sup_t h k]
      exact sup_le (sup_le hFZ hAZ) (zpowers_le.mpr htZ)
    exact (hHZ hxH).2
  · intro hc
    have hcent : ∀ r : 𝐑[k], parabolicHom h k ⟨x, hx⟩ * parabolicHom h k r =
        parabolicHom h k r * parabolicHom h k ⟨x, hx⟩ := by
      intro r
      have h1 : (⟨x, hx⟩ : 𝐑[k]) * r * (⟨x, hx⟩ : 𝐑[k])⁻¹ * r⁻¹ ∈ (parabolicHom h k).ker := by
        rw [ker_parabolicHom, mem_subgroupOf]
        exact K_le_D h k (hc r r.2)
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc parabolicHom h k ⟨x, hx⟩ * parabolicHom h k r =
          (parabolicHom h k ⟨x, hx⟩ * parabolicHom h k r * (parabolicHom h k ⟨x, hx⟩)⁻¹ *
            (parabolicHom h k r)⁻¹) * (parabolicHom h k r * parabolicHom h k ⟨x, hx⟩) := by
            group
        _ = parabolicHom h k r * parabolicHom h k ⟨x, hx⟩ := by rw [h1, one_mul]
    obtain ⟨r₁, hr₁⟩ := parabolicHom_surjective h k ⟨0, 0, 1⟩
    obtain ⟨r₂, hr₂⟩ := parabolicHom_surjective h k ⟨0, 1, 0⟩
    have h1 := congrArg Heis.x (hcent r₁)
    have h2 := congrArg Heis.x (hcent r₂)
    rw [hr₁] at h1
    rw [hr₂] at h2
    simp only [Heis.mul_x] at h1 h2
    have hy : (parabolicHom h k ⟨x, hx⟩).y = 0 := by linear_combination (-1 : K) * h1
    have hz : (parabolicHom h k ⟨x, hx⟩).z = 0 := by linear_combination h2
    exact ⟨(mem_H_iff h k ⟨x, hx⟩).mpr hy, (parabolicHom_z_eq_zero_iff h k ⟨x, hx⟩).mp hz⟩

theorem exists_H_mul_C (h : FCHyp L K n φ t) {g : G} (hg : g ∈ normalizer (𝐐 : Set G)) :
    ∃ x ∈ 𝐇, ∃ c ∈ 𝐂 ⊓ normalizer (𝐐 : Set G), g = x * c := by
  have hmem : g * t * g⁻¹ ∈ {x : G | ∃ m ∈ normalizer (𝐐 : Set G), x = m⁻¹ * t * m} :=
    ⟨g⁻¹, inv_mem hg, by rw [inv_inv]⟩
  rw [h.full, ← h.orbit_H] at hmem
  obtain ⟨x, hx, hxg⟩ := hmem
  refine ⟨x⁻¹, inv_mem hx, x * g, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
    mul_mem (h.H_le_normalizer_Q hx) hg⟩, by group⟩
  exact (calc t * (x * g) = x * (x⁻¹ * t * x) * g := by group
    _ = x * (g * t * g⁻¹) * g := by rw [hxg]
    _ = x * g * t := by group).symm

theorem NRB_eq (h : FCHyp L K n φ t) (k : Axis)
    (hQB : normalizer (𝐐 : Set G) ≤ normalizer (𝐁[k] : Set G))
    (hQR : normalizer (𝐐 : Set G) ≤ normalizer (𝐑[k] : Set G)) :
    (𝐑[k] : Set G) * ((𝐂 ⊓ normalizer (𝐐 : Set G) : Subgroup G) : Set G) =
      ((normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) : Subgroup G) : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨r, hr, c, hc, rfl⟩
    exact ⟨mul_mem (le_normalizer hr) (hQR hc.2), mul_mem (R_le_N h k hr) (hQB hc.2)⟩
  · intro g hg
    obtain ⟨hgR, hgB⟩ := hg
    have hg' : g ∈ (𝐄[k] : Set G) * ((𝐂 ⊓ 𝐍[k] : Subgroup G) : Set G) := by
      rw [E_mul_C0 h k]
      exact hgB
    obtain ⟨e, he, c, hc, rfl⟩ := hg'
    have heR : e ∈ 𝐑[k] := mem_sup_right he
    have hcR : c ∈ normalizer (𝐑[k] : Set G) := by
      have := mul_mem (inv_mem (le_normalizer heR)) hgR
      rwa [inv_mul_cancel_left] at this
    have hcQ : c ∈ normalizer (𝐐 : Set G) := mem_normalizer_of_conj_le fun q hq => by
      rw [← R_inf_C h k] at hq ⊢
      have hcC := (mem_inf.mp hc).1
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcR q).mp (mem_inf.mp hq).1,
        mul_mem (mul_mem hcC (mem_inf.mp hq).2) (inv_mem hcC)⟩
    exact ⟨e, heR, c, mem_inf.mpr ⟨(mem_inf.mp hc).1, hcQ⟩, rfl⟩

theorem card_NRB (h : FCHyp L K n φ t) (k : Axis)
    (hQB : normalizer (𝐐 : Set G) ≤ normalizer (𝐁[k] : Set G))
    (hQR : normalizer (𝐐 : Set G) ≤ normalizer (𝐑[k] : Set G))
    (hQH : normalizer (𝐐 : Set G) ≤ normalizer ((𝐇 : Subgroup G) : Set G)) :
    Nat.card (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) : Subgroup G) =
      Nat.card K * Nat.card (normalizer (𝐐 : Set G)) := by
  set NC := 𝐂 ⊓ normalizer (𝐐 : Set G) with hNC
  have hNCR : NC ≤ normalizer (𝐑[k] : Set G) := fun c hc => hQR hc.2
  have e1 : 𝐑[k] ⊔ NC = normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) :=
    SetLike.coe_injective (by
      rw [coe_mul_of_right_le_normalizer_left 𝐑[k] NC hNCR]
      exact NRB_eq h k hQB hQR)
  have h1 := card_sup_mul_card_inf 𝐑[k] NC hNCR
  have hRNC : 𝐑[k] ⊓ NC = 𝐐 := le_antisymm
    (fun x hx => R_inf_C h k ▸ mem_inf.mpr ⟨hx.1, hx.2.1⟩)
    (le_inf le_sup_left (le_inf h.setup.Q_le_C le_normalizer))
  have hNQ : 𝐇 ⊔ NC = normalizer (𝐐 : Set G) := le_antisymm
    (sup_le h.H_le_normalizer_Q inf_le_right) fun g hg => by
      obtain ⟨x, hx, c, hc, rfl⟩ := exists_H_mul_C h hg
      exact mul_mem (mem_sup_left hx) (mem_sup_right hc)
  have h2 := card_sup_mul_card_inf 𝐇 NC fun c hc => hQH hc.2
  have hHNC : 𝐇 ⊓ NC = 𝐐 := le_antisymm
    (fun x hx => h.H_inf_C ▸ mem_inf.mpr ⟨hx.1, hx.2.1⟩)
    (le_inf Q_le_H (le_inf h.setup.Q_le_C le_normalizer))
  rw [e1, hRNC] at h1
  rw [hNQ, hHNC] at h2
  have hR : Nat.card 𝐑[k] = Nat.card K * Nat.card 𝐇 := by
    rw [card_R h k, h.H_facts.2.2]
    ring
  have hQ : 0 < Nat.card 𝐐 := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hQ ?_
  rw [h1, hR, mul_assoc, ← h2]
  ring

theorem mem_Q_sup_J (h : FCHyp L K n φ t) (k : Axis) {c : G} (hcC : c ∈ 𝐂)
    (hcN : ∀ m : Axis, c ∈ 𝐍[m]) (hcA : ∀ a ∈ 𝐀[k.swap], c * a * c⁻¹ * a⁻¹ ∈ 𝐙) :
    c ∈ 𝐐 ⊔ 𝐉 := by
  obtain ⟨a₀, ha₀, l, M, e, he, hα⟩ := h.exists_aut k.swap hcC (hcN k.swap)
  have hst := h.twoCore.axisStr k.swap
  have hact : ∀ a ∈ 𝐀[k.swap], psiG φ k.swap (c * a * c⁻¹) =
      (l : K) • ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => psiG φ k.swap a j ^ 2 ^ e) := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull ha
    rw [← normAct_symm_apply φ ⟨c, h.setup.cent_le hcC⟩ z, psiG_symm, psiG_symm, hα]
    exact vecOf_aut k.swap hst ha₀ l M e hz
  have hpow0 : (0 : K) ^ 2 ^ e = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hA : ∀ m, ∀ a ∈ 𝐀[m], c * a * c⁻¹ ∈ 𝐀[m] := fun m a ha =>
    (mem_normalizer_iff.mp (h.N_le_normalizer_A m (hcN m)) a).mp ha
  have hZ : 𝐀[Axis.one] ⊓ 𝐀[Axis.two] = 𝐙 := by
    rw [← pull_inf]
    exact congrArg (pull φ) radA1_inf_radA2
  have hcZ : ∀ z ∈ 𝐙, c * z * c⁻¹ ∈ 𝐙 := fun z hz => by
    rw [← hZ] at hz ⊢
    exact ⟨hA _ z hz.1, hA _ z hz.2⟩
  obtain ⟨z₁, hz₁, hψz₁⟩ := exists_psiG_ZP h k.swap 1
  have hM10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h1 := psiG_ZP_one h k.swap (hcZ z₁ hz₁)
    rw [hact z₁ (pull_mono φ (center_le_rootA _) hz₁), hψz₁] at h1
    simp [hpow0] at h1
    exact h1
  have hfix : ∀ x : K, (l : K) * (M : Matrix (Fin 2) (Fin 2) K) 1 1 * x ^ 2 ^ e = x := by
    intro x
    obtain ⟨a, ha, hψa⟩ := exists_psiG_eq h.twoCore φ k.swap ![0, x]
    have h1 := psiG_ZP_one h k.swap (hcA a ha)
    rw [psiG_mul h.twoCore φ k.swap (hA _ a ha) (inv_mem ha), psiG_inv h.twoCore φ k.swap ha,
      hact a ha, hψa] at h1
    simp [hpow0, hM10] at h1
    linear_combination h1
  have h11 : (l : K) * (M : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simpa using hfix 1
  have hfix' : ∀ x : K, x ^ 2 ^ e = x := fun x => by
    have := hfix x
    rwa [h11, one_mul] at this
  have he0 : e = 0 := eq_zero_of_frobRingEquiv_pow_eq_one (by have := h.setup.two_le; omega)
    h.setup.card_K he (RingEquiv.ext fun x => by rw [frobRingEquiv_pow_apply, hfix' x]; rfl)
  subst he0
  rw [pow_zero, mul_one] at hα
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
  have hx : a₀ * (dHom K k.swap l * sHom K k.swap M) ∈ antiUnipotent K ⊔ diagTorus K := by
    rw [hMdec, map_mul]
    exact mul_mem (mem_sup_left (rootA_le_antiUnipotent _ ha₀))
      (mul_mem (mem_sup_right (dHom_mem _ l)) (mul_mem (mem_sup_right (sHom_diagSL_mem _ _))
        (mem_sup_left (sHom_upperSL_mem _ _))))
  set x := a₀ * (dHom K k.swap l * sHom K k.swap M) with hxdef
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

theorem card_center_E_le (h : FCHyp L K n φ t) {k m : Axis} {g : G}
    (hg : ∀ x ∈ 𝐁[k], g * x * g⁻¹ ∈ 𝐁[m]) :
    Nat.card ((center 𝐄[k]).map 𝐄[k].subtype) ≤ Nat.card ((center 𝐄[m]).map 𝐄[m].subtype) := by
  have hBm : ∀ b ∈ 𝐁[m], g⁻¹ * b * g ∈ 𝐁[k] := by
    have hle : 𝐁[k].map (MulAut.conj g).toMonoidHom ≤ 𝐁[m] := by
      rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    have heq := eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj g).injective, h.card_B, h.card_B])
    intro b hb
    rw [← heq] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    show g⁻¹ * (g * x * g⁻¹) * g ∈ _
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  have hE1 : ∀ e ∈ 𝐄[k], g * e * g⁻¹ ∈ 𝐄[m] := fun e he =>
    conj_mem_pCore_normalizer hg hBm he
  have hE2 : ∀ e ∈ 𝐄[m], g⁻¹ * e * g ∈ 𝐄[k] := fun e he => by
    have := conj_mem_pCore_normalizer (g := g⁻¹) (fun b hb => by simpa using hBm b hb)
      (fun b hb => by simpa using hg b hb) he
    simpa using this
  have hle : ((center 𝐄[k]).map 𝐄[k].subtype).map (MulAut.conj g).toMonoidHom ≤
      (center 𝐄[m]).map 𝐄[m].subtype := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzE, hzc⟩ := mem_center_map_iff.mp hz
    refine mem_center_map_iff.mpr ⟨hE1 z hzE, fun y hy => ?_⟩
    have h1 := hzc _ (hE2 y hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * y := by group
  calc Nat.card ((center 𝐄[k]).map 𝐄[k].subtype)
      = Nat.card (((center 𝐄[k]).map 𝐄[k].subtype).map (MulAut.conj g).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj g).injective).symm
    _ ≤ _ := card_le_of_le hle

theorem normalizer_Q_le_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : normalizer (𝐐 : Set G) ≤ 𝐍[k] := by
  intro g hg
  rcases h.conj_B hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · cases k
    · exact h1
    · exact h2
  · exfalso
    have c1 := card_center_E_le h h1
    have c2 := card_center_E_le h h2
    obtain ⟨hZi, -, -⟩ := centers_of_ne_bot h i hne
    have hbot' : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i.swap.swap]⁆ = ⊥ := by rw [swap_swap]; exact hbot
    obtain ⟨hZj, -⟩ := centers_of_bot h i.swap hbot'
    have heq : Nat.card ((center 𝐄[i]).map 𝐄[i].subtype) =
        Nat.card ((center 𝐄[i.swap]).map 𝐄[i.swap].subtype) := by
      cases i
      · exact le_antisymm c1 c2
      · exact le_antisymm c2 c1
    rw [hZi, hZj, card_pull, card_pull, card_rootU, card_rootA] at heq
    have : Nat.card K < Nat.card K ^ 3 := by
      have h4 := h.four_le_card
      calc Nat.card K = Nat.card K ^ 1 := (pow_one _).symm
        _ < Nat.card K ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem conj_normalizer_Q_mem_E (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {g : G}
    (hg : g ∈ normalizer (𝐐 : Set G)) {e : G} (he : e ∈ 𝐄[k]) : g * e * g⁻¹ ∈ 𝐄[k] :=
  conj_mem_pCore_map (normalizer_Q_le_N h i hne hbot k hg) he

theorem normalizer_Q_le_normalizer_R (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    normalizer (𝐐 : Set G) ≤ normalizer (𝐑[k] : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ hx =>
    conj_mem_sup (fun q hq => (mem_normalizer_iff.mp hg q).mp hq)
      (fun _ he => conj_normalizer_Q_mem_E h i hne hbot k hg he) hx

theorem normalizer_Q_le_normalizer_H (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    normalizer (𝐐 : Set G) ≤ normalizer ((𝐇 : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_of_conj_le fun x hx => by
    rw [← R_inf_R h] at hx ⊢
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (normalizer_Q_le_normalizer_R h i hne hbot _ hg)
      x).mp (mem_inf.mp hx).1, (mem_normalizer_iff.mp
        (normalizer_Q_le_normalizer_R h i hne hbot _ hg) x).mp (mem_inf.mp hx).2⟩

theorem normalizer_Q_le_normalizer_U (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    normalizer (𝐐 : Set G) ≤ normalizer (𝐔[k] : Set G) := fun _ hg =>
  h.N_le_normalizer_U k (normalizer_Q_le_N h i hne hbot k hg)

theorem normalizer_Q_le_Nhat (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    normalizer (𝐐 : Set G) ≤ 𝐍ₕ[i] := fun _ hg =>
  mem_inf.mpr ⟨normalizer_Q_le_normalizer_H h i hne hbot hg,
    normalizer_Q_le_normalizer_U h i hne hbot i hg⟩

theorem R_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐑[k] ≤ 𝐍ₕ[i] := by
  intro r hr
  refine mem_inf.mpr ⟨R_le_normalizer_H h k hr, mem_normalizer_of_conj_le fun u hu => ?_⟩
  have hc : r * u = u * r := by
    rcases eq_or_eq_swap i k with rfl | rfl
    · obtain ⟨-, hZR, -⟩ := centers_of_ne_bot h _ hne
      have huZ : u ∈ (center 𝐑[k]).map 𝐑[k].subtype := by rw [hZR]; exact hu
      exact (mem_center_map_iff.mp huZ).2 r hr
    · have hbot' : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i.swap.swap]⁆ = ⊥ := by rw [swap_swap]; exact hbot
      obtain ⟨-, hZR⟩ := centers_of_bot h i.swap hbot'
      have huZ : u ∈ (center 𝐑[i.swap]).map 𝐑[i.swap].subtype := by
        rw [hZR]
        exact pull_mono φ (rootU_le_center i) hu
      exact (mem_center_map_iff.mp huZ).2 r hr
  rw [hc, mul_inv_cancel_right]
  exact hu

theorem mem_D_of_sq (h : FCHyp L K n φ t) (i : Axis) (hj : ∀ w ∈ 𝐖[i.swap], w * w = 1) {s : G}
    (hs : s ∈ 𝐇 ⊓ 𝐄[i]) (hsL : s ∉ 𝐋[i]) (hss : s * s ∈ 𝐔[i]) : s ∈ 𝐃[i] := by
  have htt := h.setup.t_mul_t
  have htN : t ∈ normalizer (𝐋[i] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i t_mem_H hl
  have hts : t * s ∈ 𝐋[i] :=
    (mem_or_mul_mem htt htN (by rw [L_sup_t h i]; exact hs)).resolve_left hsL
  rw [← SetLike.mem_coe, ← L_mul h i] at hts
  obtain ⟨f, hf, a, ha, hfa⟩ := hts
  have hfa : f * a = t * s := hfa
  have hs' : s = t * f * a := by rw [mul_assoc, hfa, ← mul_assoc, htt, one_mul]
  have hc : a * f * a⁻¹ * f⁻¹ ∈ 𝐔[i] := by
    have := commutator_le.mp (commutator_A_F h i) a ha f hf
    rwa [commutatorElement_def] at this
  have hat : a * t = t * a := (h.twoCore.comm (pull_le φ _ ha)).symm
  have hfH := F_le_H h hf
  have htft : t * f * t ∈ 𝐇 := mul_mem (mul_mem t_mem_H hfH) t_mem_H
  have hcc := comm_U h i htft hc
  have e1 : s * s = (a * f * a⁻¹ * f⁻¹) * ((t⁻¹ * (f⁻¹⁻¹ * t * f⁻¹)) * (f * f)) := by
    calc s * s = t * f * (a * t) * f * a := by rw [hs']; group
      _ = t * f * (t * a) * f * a := by rw [hat]
      _ = (t * f * t) * ((a * f * a⁻¹ * f⁻¹) * f * (a * a)) := by group
      _ = (t * f * t) * ((a * f * a⁻¹ * f⁻¹) * f) := by rw [A_mul_self h i ha, mul_one]
      _ = ((t * f * t) * (a * f * a⁻¹ * f⁻¹)) * f := by group
      _ = ((a * f * a⁻¹ * f⁻¹) * (t * f * t)) * f := by rw [hcc]
      _ = (a * f * a⁻¹ * f⁻¹) * ((t⁻¹ * (f⁻¹⁻¹ * t * f⁻¹)) * (f * f)) := by
        rw [inv_inv, h.twoCore.t_inv]
        group
  have hκ : t⁻¹ * (f⁻¹⁻¹ * t * f⁻¹) ∈ 𝐔[i] := by
    have h1 := mul_mem (inv_mem hc) (e1 ▸ hss)
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
    have h2 := mul_mem h1 (inv_mem (F_sq_mem_U h i hj hf))
    rwa [mul_inv_cancel_right] at h2
  have hfD : f ∈ 𝐃[i] := by
    have := mem_D_of_kappa h i (F_le_E h i (inv_mem hf)) hκ
    simpa using inv_mem this
  rw [hs']
  exact mul_mem (mul_mem (t_mem_D h i) hfD) (A_le_D h i ha)

theorem Nhat_inf_normalizer_Hi_le (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) ≤ normalizer (𝐃[i] : Set G) := by
  have hj := fun w hw => sq_W_swap h i hne hbot (w := w) hw
  intro g hg
  obtain ⟨hgN, hgHi⟩ := mem_inf.mp hg
  have hgU := (mem_inf.mp hgN).2
  have hgK := Nhat_le_normalizer_Ks h i hbot hgN
  have hDsq : ∀ d ∈ 𝐃[i], d * d ∈ 𝐔[i] := fun d hd =>
    closure_sq_D h i ▸ subset_closure ⟨d, hd, rfl⟩
  have key : ∀ d ∈ 𝐃[i], g * d * g⁻¹ ∉ 𝐋[i] → g * d * g⁻¹ ∈ 𝐃[i] := fun d hd hdL =>
    mem_D_of_sq h i hj ((mem_normalizer_iff.mp hgHi d).mp (D_le_Hi h i hd)) hdL (by
      rw [show g * d * g⁻¹ * (g * d * g⁻¹) = g * (d * d) * g⁻¹ by group]
      exact (mem_normalizer_iff.mp hgU _).mp (hDsq d hd))
  have htL : g * t * g⁻¹ ∉ 𝐋[i] := fun h1 =>
    t_not_mem_Ks h ((mem_normalizer_iff.mp hgK t).mpr (L_le_Ks h i h1))
  refine mem_normalizer_of_conj_le fun d hd => ?_
  by_cases hdL : g * d * g⁻¹ ∈ 𝐋[i]
  · have htd : g * (t * d) * g⁻¹ ∉ 𝐋[i] := fun h1 => htL (by
      rw [show g * t * g⁻¹ = g * (t * d) * g⁻¹ * (g * d * g⁻¹)⁻¹ by group]
      exact mul_mem h1 (inv_mem hdL))
    have h1 := key _ (mul_mem (t_mem_D h i) hd) htd
    have h2 := key t (t_mem_D h i) htL
    rw [show g * d * g⁻¹ = (g * t * g⁻¹)⁻¹ * (g * (t * d) * g⁻¹) by group]
    exact mul_mem (inv_mem h2) h1
  · exact key d hd hdL

theorem R_swap_inf_normalizer_Hi (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐑[i.swap] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) = 𝐇 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨hrR, hrN⟩ := mem_inf.mp hr
    have hrA := normalizer_D_le_normalizer_A h i (Nhat_inf_normalizer_Hi_le h i hne hbot
      (mem_inf.mpr ⟨R_le_Nhat h i hne hbot i.swap hrR, hrN⟩))
    have h1 := R_inf_normalizer_A h i.swap
    rw [swap_swap] at h1
    rw [← h1]
    exact mem_inf.mpr ⟨hrR, hrA⟩
  · exact le_inf (H_le_R h _) (H_le_normalizer_Hi h i)

theorem center_Hj_le (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {z : G} (hz : z ∈ 𝐇 ⊓ 𝐄[i.swap]) (hzc : ∀ y ∈ 𝐇 ⊓ 𝐄[i.swap], z * y = y * z) :
    z ∈ 𝐀[i.swap] := by
  have htt := h.setup.t_mul_t
  have htN : t ∈ normalizer (𝐋[i.swap] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h _ t_mem_H hl
  have hFH : 𝐅 ≤ 𝐇 ⊓ 𝐄[i.swap] := le_inf (F_le_H h) (F_le_E h _)
  rcases mem_or_mul_mem htt htN (by rw [L_sup_t h]; exact hz) with hzL | hzL
  · have hzt : z * t = t * z := hzc t (mem_inf.mpr ⟨t_mem_H, t_mem_E h _⟩)
    rw [← SetLike.mem_coe, ← L_mul h] at hzL
    obtain ⟨f, hf, a, ha, rfl⟩ := hzL
    have hat : a * t = t * a := (h.twoCore.comm (pull_le φ _ ha)).symm
    have hfC : f ∈ 𝐂 := by
      rw [mem_centralizer_singleton_iff]
      have e1 : f * a * t = t * (f * a) := hzt
      calc f * t = f * a * t * a⁻¹ := by rw [mul_assoc f a t, hat]; group
        _ = t * (f * a) * a⁻¹ := by rw [e1]
        _ = t * f := by group
    exact mul_mem (pull_mono φ (center_le_rootA _) (mem_ZP_of_mem_F h hf hfC)) ha
  · exfalso
    have hFC : 𝐅 ≤ 𝐂 := fun f hf => by
      rw [mem_centralizer_singleton_iff]
      have h1 := hzc f (hFH hf)
      have h2 := L_swap_comm h i hbot hzL (F_le_L _ hf)
      have e : z = t * (t * z) := by rw [← mul_assoc, htt, one_mul]
      rw [e] at h1
      have h3 : t * f * (t * z) = f * t * (t * z) := by
        calc t * f * (t * z) = t * (f * (t * z)) := by group
          _ = t * ((t * z) * f) := by rw [h2]
          _ = f * (t * (t * z)) := by rw [← mul_assoc]; exact h1
          _ = f * t * (t * z) := by group
      exact (mul_right_cancel h3).symm
    have h3 : 𝐅 ≤ 𝐙 := fun f hf => mem_ZP_of_mem_F h hf (hFC hf)
    have h4 := card_le_of_le h3
    rw [card_F h, FCHyp.card_ZP] at h4
    have : Nat.card K ^ 2 < Nat.card K ^ 4 :=
      Nat.pow_lt_pow_right (by have := h.four_le_card; omega) (by norm_num)
    omega

theorem R_inf_normalizer_Hj (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐑[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i.swap] : Subgroup G) : Set G) = 𝐇 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨hrR, hrN⟩ := mem_inf.mp hr
    rw [← R_inf_normalizer_A h i]
    refine mem_inf.mpr ⟨hrR, mem_normalizer_of_conj_le fun a ha => ?_⟩
    have haH : a ∈ 𝐇 ⊓ 𝐄[i.swap] :=
      (A_le_D h _).trans (D_le_Hi h _) ha
    have hHC : 𝐇 ⊓ 𝐄[i.swap] ≤ centralizer ({a} : Set G) := by
      rw [← L_sup_t h]
      refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr
        (L_swap_comm h i hbot hy (A_le_L _ ha))) (zpowers_le.mpr
          (mem_centralizer_singleton_iff.mpr (h.twoCore.comm (pull_le φ _ ha))))
    refine center_Hj_le h i hbot ((mem_normalizer_iff.mp hrN a).mp haH) fun y hy => ?_
    have hy' : r⁻¹ * y * r ∈ 𝐇 ⊓ 𝐄[i.swap] := by
      have := (mem_normalizer_iff.mp (inv_mem hrN) y).mp hy
      rwa [inv_inv] at this
    have h1 := mem_centralizer_singleton_iff.mp (hHC hy')
    calc r * a * r⁻¹ * y = r * (a * (r⁻¹ * y * r)) * r⁻¹ := by group
      _ = r * ((r⁻¹ * y * r) * a) * r⁻¹ := by rw [h1]
      _ = y * (r * a * r⁻¹) := by group
  · exact le_inf (H_le_R h i) (H_le_normalizer_Hi h _)

theorem mem_normalizer_Hk_iff (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {x : G}
    (hx : x ∈ 𝐍ₕ[i]) :
    x ∈ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) ↔ t⁻¹ * (x * t * x⁻¹) ∈ 𝐋[k] := by
  have htt := h.setup.t_mul_t
  have hxK := Nhat_le_normalizer_Ks h i hbot hx
  have hxL := Nhat_le_normalizer_L h i hne hbot k hx
  have hxtL : x * t * x⁻¹ ∉ 𝐋[k] := fun h1 =>
    t_not_mem_Ks h ((mem_normalizer_iff.mp hxK t).mpr (L_le_Ks h k h1))
  have htN : t ∈ normalizer (𝐋[k] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h k t_mem_H hl
  constructor
  · intro hxN
    have h1 : x * t * x⁻¹ ∈ 𝐋[k] ⊔ zpowers t := by
      rw [L_sup_t h k]
      exact (mem_normalizer_iff.mp hxN t).mp (mem_inf.mpr ⟨t_mem_H, t_mem_E h k⟩)
    have h2 := (mem_or_mul_mem htt htN h1).resolve_left hxtL
    rwa [h.twoCore.t_inv]
  · intro h1
    rw [← L_sup_t h k, sup_comm 𝐋[k] (zpowers t)]
    refine mem_normalizer_zpowers_sup ?_ fun l hl => (mem_normalizer_iff.mp hxL l).mp hl
    rw [show x * t * x⁻¹ = t * (t⁻¹ * (x * t * x⁻¹)) by group]
    exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right h1)

theorem first_index (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G)).relIndex 𝐍ₕ[i] = Nat.card K ∧
      ∀ x ∈ 𝐍ₕ[i], ∃ y ∈ 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G),
        ∃ r ∈ 𝐑[k.swap], x = y * r := by
  have htt := h.setup.t_mul_t
  have htKs : t ∈ normalizer (𝐊⋆ : Set G) :=
    mem_normalizer_of_conj_le fun _ hk => conj_H_mem_Ks h t_mem_H hk
  have hL : 𝐋[k].relIndex 𝐊⋆ = Nat.card K := by
    have h1 := relIndex_mul_card 𝐋[k] 𝐊⋆
    rw [inf_of_le_left (L_le_Ks h k), card_L h, card_Ks h] at h1
    have hq : 0 < Nat.card K ^ 5 := by have : 0 < Nat.card K := Nat.card_pos; positivity
    exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  have e : 𝐑[k.swap] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) = 𝐇 := by
    rcases eq_or_eq_swap i k with rfl | rfl
    · exact R_swap_inf_normalizer_Hi h _ hne hbot
    · rw [swap_swap]
      exact R_inf_normalizer_Hj h i hbot
  have hRH : (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G)) ⊓ 𝐑[k.swap] = 𝐇 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, h2⟩ := mem_inf.mp hx
      have : x ∈ 𝐑[k.swap] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) :=
        mem_inf.mpr ⟨h2, (mem_inf.mp hx1).2⟩
      rwa [e] at this
    · intro x hx
      have hx' : x ∈ 𝐑[k.swap] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) := by
        rw [e]
        exact hx
      obtain ⟨h2, h1⟩ := mem_inf.mp hx'
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨R_le_Nhat h i hne hbot k.swap h2, h1⟩, h2⟩
  have hXM : ∀ x ∈ 𝐍ₕ[i], t⁻¹ * (x * t * x⁻¹) ∈ 𝐊⋆ := by
    intro x hx
    have hxK := Nhat_le_normalizer_Ks h i hbot hx
    have h1 : x * t * x⁻¹ ∈ 𝐇 := (mem_normalizer_iff.mp (mem_inf.mp hx).1 t).mp t_mem_H
    have h2 : x * t * x⁻¹ ∉ 𝐊⋆ := fun h2 => t_not_mem_Ks h ((mem_normalizer_iff.mp hxK t).mpr h2)
    have h3 := (mem_or_mul_mem htt htKs (by rw [(Ks_sup_t h).2]; exact h1)).resolve_left h2
    rwa [h.twoCore.t_inv]
  obtain ⟨hidx, hdec⟩ := coset_of_sub (X := 𝐍ₕ[i])
    (Y := 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G)) (M := 𝐊⋆) (L := 𝐋[k])
    (R := 𝐑[k.swap]) (t := t)
    (fun x hx l hl => (mem_normalizer_iff.mp (Nhat_le_normalizer_L h i hne hbot k hx) l).mp hl)
    hXM (fun x hx => by
      rw [mem_inf]
      exact ⟨fun h1 => (mem_normalizer_Hk_iff h i hne hbot k hx).mp h1.2,
        fun h1 => ⟨hx, (mem_normalizer_Hk_iff h i hne hbot k hx).mpr h1⟩⟩)
    (R_le_Nhat h i hne hbot k.swap) (by rw [hRH, relIndex_H h k.swap, hL])
  exact ⟨hidx.trans hL, hdec⟩

theorem NRB_eq' (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    (𝐑[k] : Set G) * ((𝐂 ⊓ normalizer (𝐐 : Set G) : Subgroup G) : Set G) =
      ((normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) : Subgroup G) : Set G) :=
  NRB_eq h k (normalizer_Q_le_N h i hne hbot k) (normalizer_Q_le_normalizer_R h i hne hbot k)

theorem card_NRB' (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    Nat.card (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) : Subgroup G) =
      Nat.card K * Nat.card (normalizer (𝐐 : Set G)) :=
  card_NRB h k (normalizer_Q_le_N h i hne hbot k) (normalizer_Q_le_normalizer_R h i hne hbot k)
    (normalizer_Q_le_normalizer_H h i hne hbot)

theorem NRB_le (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) ≤
      𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) := by
  intro g hg
  rw [← SetLike.mem_coe, ← NRB_eq' h i hne hbot k] at hg
  obtain ⟨r, hr, c, hc, rfl⟩ := hg
  have hcQ := (mem_inf.mp hc).2
  refine mul_mem (mem_inf.mpr ⟨R_le_Nhat h i hne hbot k hr, mem_normalizer_of_conj_le
    fun x hx => mem_inf.mpr ⟨conj_mem_H h k hr (mem_inf.mp hx).1,
      conj_mem_E h k hr (mem_inf.mp hx).2⟩⟩)
    (mem_inf.mpr ⟨normalizer_Q_le_Nhat h i hne hbot hcQ, mem_normalizer_of_conj_le
      fun x hx => mem_inf.mpr ⟨(mem_normalizer_iff.mp
        (normalizer_Q_le_normalizer_H h i hne hbot hcQ) x).mp (mem_inf.mp hx).1,
          conj_normalizer_Q_mem_E h i hne hbot k hcQ (mem_inf.mp hx).2⟩⟩)

theorem Nhat_inf_NB (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    𝐍ₕ[i] ⊓ normalizer (𝐁[k] : Set G) =
      normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgB⟩ := mem_inf.mp hg
    refine mem_inf.mpr ⟨mem_normalizer_of_conj_le fun x hx => ?_, hgB⟩
    have hRHE : 𝐑[k] = 𝐇 ⊔ 𝐄[k] := le_antisymm (sup_le (Q_le_H.trans le_sup_left) le_sup_right)
      (sup_le (H_le_R h k) le_sup_right)
    rw [hRHE] at hx ⊢
    exact conj_mem_sup (fun y hy => (mem_normalizer_iff.mp (mem_inf.mp hgN).1 y).mp hy)
      (fun e he => conj_mem_pCore_map hgB he) hx
  · intro g hg
    exact mem_inf.mpr ⟨(mem_inf.mp (NRB_le h i hne hbot k hg)).1, (mem_inf.mp hg).2⟩

theorem J_le_NRB (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    𝐉 ≤ normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) := fun _ hj =>
  mem_inf.mpr ⟨normalizer_Q_le_normalizer_R h i hne hbot k (h.setup.diagTorus_le_normalizer hj),
    normalizer_Q_le_N h i hne hbot k (h.setup.diagTorus_le_normalizer hj)⟩

theorem conj_torus_mem_K (h : FCHyp L K n φ t) (k : Axis) {j : G} (hj : j ∈ 𝐉) {x : G}
    (hx : x ∈ 𝐊[k]) : j * x * j⁻¹ ∈ 𝐊[k] :=
  conj_mem_sup (fun a ha => (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A k hj) a).mp ha)
    (fun f hf => by
      have h1 := conj_torus_mem_F h (inv_mem hj) (mem_inf.mp hf).1
      have h2 := conj_torus_mem_D h k (inv_mem hj) (mem_inf.mp hf).2
      rw [inv_inv] at h1 h2
      exact mem_inf.mpr ⟨h1, h2⟩) hx

theorem exists_torus_K (h : FCHyp L K n φ t) (k : Axis) {k₀ m : G} (hk₀ : k₀ ∈ 𝐊[k])
    (hk₀A : k₀ ∉ 𝐀[k]) (hm : m ∈ 𝐊[k]) (hmA : m ∉ 𝐀[k]) :
    ∃ j ∈ 𝐉, (j * k₀ * j⁻¹)⁻¹ * m ∈ 𝐀[k] := by
  have hK : ∀ x ∈ 𝐊[k], t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[k] := fun x hx =>
    kappa_mem_U h k (K_le_D h k hx)
  have hKC : ∀ x ∈ 𝐊[k], t⁻¹ * (x⁻¹ * t * x) = 1 → x ∈ 𝐀[k] := fun x hx h1 => by
    rw [← K_inf_C h k]
    exact mem_inf.mpr ⟨hx, kappa_eq_one_iff.mp h1⟩
  obtain ⟨c₀, hc₀⟩ := exists_coordG_eq φ k (hK k₀ hk₀)
  obtain ⟨c, hc⟩ := exists_coordG_eq φ k (hK m hm)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [coordG_zero] at hc₀
    exact hk₀A (hKC k₀ hk₀ hc₀.symm)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [coordG_zero] at hc
    exact hmA (hKC m hm hc.symm)
  obtain ⟨δ, hδ, hδc⟩ := FCHyp.torus_trans (φ := φ) k hc₀0 hc0
  refine ⟨δ, hδ, ?_⟩
  have hδk₀ : δ * k₀ * δ⁻¹ ∈ 𝐊[k] := conj_torus_mem_K h k hδ hk₀
  refine hKC _ (mul_mem (inv_mem hδk₀) hm) ?_
  have hκδ : t⁻¹ * ((δ * k₀ * δ⁻¹)⁻¹ * t * (δ * k₀ * δ⁻¹)) = coordG φ k c := by
    have := kappa_conj_torus h (inv_mem hδ) k₀
    rw [inv_inv] at this
    rw [this, ← hc₀, hδc]
  have hH : ∀ x ∈ 𝐊[k], x ∈ 𝐇 := fun x hx => K_le_H h k hx
  rw [kappa_mul h (inv_mem (hH _ hδk₀)) (hH _ hm), kappa_inv h (hH _ hδk₀), hκδ, ← hc,
    inv_mul_cancel]

theorem K_le_Ks (h : FCHyp L K n φ t) (k : Axis) : 𝐊[k] ≤ 𝐊⋆ := (K_le_L k).trans (L_le_Ks h k)

theorem second_index_i (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (normalizer (𝐑[i] : Set G) ⊓ normalizer (𝐁[i] : Set G)).relIndex
        (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G)) = 1 ∨
      (normalizer (𝐑[i] : Set G) ⊓ normalizer (𝐁[i] : Set G)).relIndex
        (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G)) = Nat.card K := by
  set X1 := 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) with hX1
  set Y1 := normalizer (𝐑[i] : Set G) ⊓ normalizer (𝐁[i] : Set G) with hY1
  have htt := h.setup.t_mul_t
  have hX1D : X1 ≤ normalizer (𝐃[i] : Set G) := Nhat_inf_normalizer_Hi_le h i hne hbot
  have hXA : ∀ x ∈ X1, ∀ a ∈ 𝐀[i], x * a * x⁻¹ ∈ 𝐀[i] := fun x hx a ha =>
    (mem_normalizer_iff.mp (normalizer_D_le_normalizer_A h i (hX1D hx)) a).mp ha
  have hY : ∀ x ∈ X1, x ∈ Y1 ↔ t⁻¹ * (x * t * x⁻¹) ∈ 𝐀[i] := by
    intro x hx
    rw [hY1, ← Nhat_inf_NB h i hne hbot i, mem_inf]
    constructor
    · rintro ⟨-, hxB⟩
      have h1 : x * t * x⁻¹ ∈ 𝐁[i] :=
        (mem_normalizer_iff.mp hxB t).mp (mem_sup_left (mem_zpowers t))
      rcases (mem_zpowers_sup_iff htt (TwoCoreSetup.comm_pull φ h.twoCore)).mp h1 with h2 | h2
      · exact absurd (pull_le φ _ h2) (by simpa using h.not_conj x⁻¹)
      · rwa [h.twoCore.t_inv]
    · intro h1
      refine ⟨(mem_inf.mp hx).1, mem_normalizer_zpowers_sup ?_ (hXA x hx)⟩
      rw [show x * t * x⁻¹ = t * (t⁻¹ * (x * t * x⁻¹)) by group]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right h1)
  have hXM : ∀ x ∈ X1, t⁻¹ * (x * t * x⁻¹) ∈ 𝐊[i] := by
    intro x hx
    have hxK := Nhat_le_normalizer_Ks h i hbot (mem_inf.mp hx).1
    have h1 : x * t * x⁻¹ ∈ 𝐃[i] := (mem_normalizer_iff.mp (hX1D hx) t).mp (t_mem_D h i)
    have h2 : x * t * x⁻¹ ∉ 𝐊[i] := fun h2 =>
      t_not_mem_Ks h ((mem_normalizer_iff.mp hxK t).mpr (K_le_Ks h i h2))
    have htN : t ∈ normalizer (𝐊[i] : Set G) := H_le_normalizer_K h i t_mem_H
    have h3 := (mem_or_mul_mem htt htN (by rw [(K_sup_t h i).2]; exact h1)).resolve_left h2
    rwa [h.twoCore.t_inv]
  have hKA : 𝐀[i].relIndex 𝐊[i] = Nat.card K := by
    have h1 := relIndex_mul_card 𝐀[i] 𝐊[i]
    rw [inf_of_le_left (le_sup_left : 𝐀[i] ≤ 𝐊[i]), card_K h i, card_pull, card_rootA] at h1
    have hq : 0 < Nat.card K ^ 3 := by have : 0 < Nat.card K := Nat.card_pos; positivity
    exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  by_cases hsub : X1 ≤ Y1
  · exact Or.inl (relIndex_eq_one.mpr hsub)
  · right
    obtain ⟨x₀, hx₀X, hx₀Y⟩ := IsConcreteLE.not_le_iff_exists.mp hsub
    rw [← hKA]
    refine relIndex_eq_of_coset hXA hXM hY fun m hm => ?_
    by_cases hmA : m ∈ 𝐀[i]
    · exact ⟨1, one_mem _, by simpa using hmA⟩
    · have hk₀A : t⁻¹ * (x₀ * t * x₀⁻¹) ∉ 𝐀[i] := fun h1 => hx₀Y ((hY x₀ hx₀X).mpr h1)
      obtain ⟨j, hj, hjk⟩ := exists_torus_K h i (hXM x₀ hx₀X) hk₀A hm hmA
      refine ⟨j * x₀, mul_mem (NRB_le h i hne hbot i (J_le_NRB h i hne hbot i hj)) hx₀X, ?_⟩
      have hjt : j * t = t * j := torus_comm_t h hj
      have htj : t⁻¹ * j = j * t⁻¹ := by
        calc t⁻¹ * j = t⁻¹ * (j * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * j) * t⁻¹ := by rw [hjt]
          _ = j * t⁻¹ := by group
      rw [show t⁻¹ * (j * x₀ * t * (j * x₀)⁻¹) = (t⁻¹ * j) * (x₀ * t * x₀⁻¹) * j⁻¹ by group,
        htj, show j * t⁻¹ * (x₀ * t * x₀⁻¹) * j⁻¹ = j * (t⁻¹ * (x₀ * t * x₀⁻¹)) * j⁻¹ by group]
      exact hjk

theorem Nhat_le_normalizer_R (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis)
    (h1 : 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) ≤
      normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G)) :
    𝐍ₕ[i] ≤ normalizer (𝐑[k] : Set G) := by
  let C' : Subgroup G :=
    { carrier := {x | x ∈ 𝐍ₕ[i] ∧ ∀ y ∈ 𝐇, x * y * x⁻¹ * y⁻¹ ∈ 𝐋[k]}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun y hy => ?_⟩
        rw [show a * b * y * (a * b)⁻¹ * y⁻¹ =
          a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) by group]
        exact mul_mem ((mem_normalizer_iff.mp (Nhat_le_normalizer_L h i hne hbot k ha) _).mp
          (hb' y hy)) (ha' y hy)
      one_mem' := ⟨one_mem _, fun y _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun y hy => ?_⟩
        have hy' : a⁻¹ * y * a ∈ 𝐇 := by
          have := (mem_normalizer_iff.mp (inv_mem (mem_inf.mp ha).1) y).mp hy
          rwa [inv_inv] at this
        have h2 := inv_mem (ha' _ hy')
        rwa [show (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ = a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ by
          group] at h2 }
  have hC'n : ∀ g ∈ 𝐍ₕ[i], ∀ x ∈ C', g * x * g⁻¹ ∈ C' := by
    rintro g hg x ⟨hx, hx'⟩
    refine ⟨mul_mem (mul_mem hg hx) (inv_mem hg), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ 𝐇 := by
      have := (mem_normalizer_iff.mp (inv_mem (mem_inf.mp hg).1) y).mp hy
      rwa [inv_inv] at this
    have h2 := (mem_normalizer_iff.mp (Nhat_le_normalizer_L h i hne hbot k hg) _).mp (hx' _ hy')
    rwa [show g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ by group] at h2
  have hRC' : 𝐑[k] ≤ C' := fun r hr => ⟨R_le_Nhat h i hne hbot k hr, fun y hy => by
    have h2 := commutator_mem_closure_sq (inv_mem hr) (inv_mem (H_le_R h k hy))
    rw [inv_inv, inv_inv] at h2
    have h3 := sq_R_le_L h k h2
    rwa [show r * (y * r⁻¹ * y⁻¹) = r * y * r⁻¹ * y⁻¹ by group] at h3⟩
  have htN : t ∈ normalizer (𝐋[k] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h k t_mem_H hl
  have hC'X : ∀ x ∈ C', x ∈ 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) := by
    rintro x ⟨hx, hx'⟩
    refine mem_inf.mpr ⟨hx, (mem_normalizer_Hk_iff h i hne hbot k hx).mpr ?_⟩
    have h2 := (mem_normalizer_iff.mp (inv_mem htN) _).mp (hx' t t_mem_H)
    rwa [show t⁻¹ * (x * t * x⁻¹ * t⁻¹) * t⁻¹⁻¹ = t⁻¹ * (x * t * x⁻¹) by group] at h2
  have hZ : 𝐀[Axis.one] ⊓ 𝐀[Axis.two] = 𝐙 := by
    rw [← pull_inf]
    exact congrArg (pull φ) radA1_inf_radA2
  have hLA : ∀ y ∈ 𝐋[k], y ∈ 𝐀[k.swap] → y ∈ 𝐙 := by
    intro y hy hyA
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
  have hC'RJ : ∀ x ∈ C', x ∈ 𝐑[k] ⊔ 𝐉 := by
    intro x hx
    have hxY := h1 (hC'X x hx)
    rw [← SetLike.mem_coe, ← NRB_eq' h i hne hbot k] at hxY
    obtain ⟨r, hr, c, hc, rfl⟩ := hxY
    have hcC' : c ∈ C' := by
      have := mul_mem (inv_mem (hRC' hr)) hx
      rwa [inv_mul_cancel_left] at this
    have hcN : ∀ m, c ∈ 𝐍[m] := fun m => normalizer_Q_le_N h i hne hbot m (mem_inf.mp hc).2
    have hcA : ∀ a ∈ 𝐀[k.swap], c * a * c⁻¹ * a⁻¹ ∈ 𝐙 := fun a ha =>
      hLA _ (hcC'.2 a (A_le_H h _ ha)) (mul_mem ((mem_normalizer_iff.mp
        (h.N_le_normalizer_A _ (hcN _)) a).mp ha) (inv_mem ha))
    have hcQJ := mem_Q_sup_J h k (mem_inf.mp hc).1 hcN hcA
    exact mul_mem (mem_sup_left hr) ((sup_le_sup_right (le_sup_left : 𝐐 ≤ 𝐑[k]) 𝐉) hcQJ)
  have hJR : 𝐉 ≤ normalizer (𝐑[k] : Set G) := fun j hj =>
    normalizer_Q_le_normalizer_R h i hne hbot k (h.setup.diagTorus_le_normalizer hj)
  intro g hg
  refine mem_normalizer_of_conj_le fun r hr => ?_
  have hs : g * r * g⁻¹ ∈ C' := hC'n g hg r (hRC' hr)
  obtain ⟨e, he⟩ := exists_two_pow_eq_one (R_isPGroup h k) hr
  refine mem_of_two_pow hJR (odd_card_sub_one h) (fun j hj => torus_pow_card_sub_one hj)
    (hC'RJ _ hs) (e := e) ?_
  rw [conj_pow, he, mul_one, mul_inv_cancel]

theorem K_sq (h : FCHyp L K n φ t) (k : Axis) (hk : ∀ w ∈ 𝐖[k], w * w = 1) {x : G}
    (hx : x ∈ 𝐊[k]) : x * x = 1 := by
  rw [← SetLike.mem_coe, ← K_mul h k] at hx
  obtain ⟨a, ha, f, hf, rfl⟩ := hx
  rw [← W_mul_U h k] at hf
  obtain ⟨w, hw, u, hu, rfl⟩ := hf
  show a * (w * u) * (a * (w * u)) = 1
  have huZ : u ∈ 𝐙 := pull_mono φ (rootU_le_center _) hu
  have hKa : a ∈ 𝐊[k] := mem_sup_left ha
  have hKw : w ∈ 𝐊[k] := mem_sup_right (W_le_Fi h k hw)
  have hKu : u ∈ 𝐊[k] := mem_sup_right (ZP_le_Fi h k huZ)
  rw [show a * (w * u) * (a * (w * u)) = a * w * u * (a * w * u) by group,
    sq_of_comm (K_comm h k hKa hKw) (K_comm h k hKa hKu) (K_comm h k hKw hKu),
    A_mul_self h k ha, hk w hw, Setup.ZP_mul_self huZ]
  group

theorem mem_F_or_K (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hi : ∀ w ∈ 𝐖[i], w * w = 1) {x : G}
    (hx : x ∈ 𝐋[i]) (hxx : x * x = 1) : x ∈ 𝐅 ∨ x ∈ 𝐊[i] := by
  have hj := fun w hw => sq_W_swap h i hne hbot (w := w) hw
  rw [← SetLike.mem_coe, ← L_mul h] at hx
  obtain ⟨f, hf, a, ha, rfl⟩ := hx
  have hc : a * f * a⁻¹ * f⁻¹ ∈ 𝐔[i] := by
    have := commutator_le.mp (commutator_A_F h i) a ha f hf
    rwa [commutatorElement_def] at this
  have hcc := comm_U h i (F_le_H h hf) hc
  have hff : f * f = 1 := by
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_mul h i hf
    have hc' : w * w' = w' * w := F_comm h (W_le_F _ hw) (W_le_F _ hw')
    rw [show w * w' * (w * w') = w * (w' * w) * w' by group, ← hc',
      show w * (w * w') * w' = w * w * (w' * w') by group, hi w hw, hj w' hw', mul_one]
  have e : f * a * (f * a) = (a * f * a⁻¹ * f⁻¹) * (f * f) := by
    calc f * a * (f * a) = f * (a * f * a⁻¹ * f⁻¹) * f * (a * a) := by group
      _ = f * (a * f * a⁻¹ * f⁻¹) * f := by rw [A_mul_self h i ha, mul_one]
      _ = (a * f * a⁻¹ * f⁻¹) * f * f := by rw [hcc]
      _ = (a * f * a⁻¹ * f⁻¹) * (f * f) := by group
  rw [e, hff, mul_one] at hxx
  have haf : a * f = f * a := by
    have h1 : a * f * a⁻¹ = f := mul_inv_eq_one.mp hxx
    calc a * f = a * f * a⁻¹ * a := by group
      _ = f * a := by rw [h1]
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_mul h i hf
  have haw : a * w = w * a := A_comm_D h i ha (mem_inf.mp (W_le_Fi h i hw)).2
  have haw' : a * w' = w' * a := by
    have h1 : w * (a * w') = w * (w' * a) := by
      calc w * (a * w') = (w * a) * w' := by group
        _ = (a * w) * w' := by rw [haw]
        _ = a * (w * w') := by group
        _ = w * w' * a := haf
        _ = w * (w' * a) := by group
    exact mul_left_cancel h1
  by_cases hw'Z : w' ∈ 𝐙
  · right
    have hfD : w * w' ∈ 𝐅 ⊓ 𝐃[i] :=
      mul_mem (W_le_Fi h i hw) (ZP_le_Fi h i hw'Z)
    exact mul_mem (mem_sup_right hfD) (mem_sup_left ha)
  · left
    have hcent := (centers_of_ne_bot h i hne).2.2 w' (W_le_Fi h i.swap hw') hw'Z
    have haZ : a ∈ 𝐙 := by
      rw [← hcent]
      exact mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr haw'⟩
    exact mul_mem hf (ZP_le_F h haZ)

theorem Nhat_le_normalizer_K_i (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hi : ∀ w ∈ 𝐖[i], w * w = 1) : 𝐍ₕ[i] ≤ normalizer (𝐊[i] : Set G) := by
  intro g hg
  have hgL := Nhat_le_normalizer_L h i hne hbot i hg
  have hgF := Nhat_le_normalizer_F h i hbot hg
  set Y := 𝐊[i].map (MulAut.conj g).toMonoidHom with hY
  have hYsub : (Y : Set G) ⊆ (𝐅 : Set G) ∪ (𝐊[i] : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_F_or_K h i hne hbot hi ((mem_normalizer_iff.mp hgL x).mp (K_le_L i hx)) ?_
    show g * x * g⁻¹ * (g * x * g⁻¹) = 1
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, K_sq h i hi hx,
      mul_one, mul_inv_cancel]
  rcases SubgroupClass.subset_union.mp hYsub with hYF | hYK
  · exfalso
    have hAF : 𝐀[i] ≤ 𝐅 := fun a ha =>
      (mem_normalizer_iff.mp hgF a).mpr (hYF ⟨a, mem_sup_left ha, rfl⟩)
    have h2 : 𝐀[i] ≤ 𝐙 := fun a ha => by
      rw [← A_inf_F h i]
      exact mem_inf.mpr ⟨ha, hAF ha⟩
    have h3 := card_le_of_le h2
    rw [card_pull, card_rootA, FCHyp.card_ZP] at h3
    have : Nat.card K ^ 2 < Nat.card K ^ 3 :=
      Nat.pow_lt_pow_right (by have := h.four_le_card; omega) (by norm_num)
    omega
  · exact mem_normalizer_of_conj_le fun x hx => hYK ⟨x, hx, rfl⟩

theorem mem_K_swap_of_sq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {lam : K}
    (hlam : ∀ w ∈ 𝐖[i], ∀ a : K, t⁻¹ * (w⁻¹ * t * w) = coordG φ i a →
      w * w = coordG φ i (lam * a)) (hlam0 : lam ≠ 0) {x : G} (hx : x ∈ 𝐋[i.swap])
    (hxx : x * x = 1) : x ∈ 𝐊[i.swap] := by
  obtain ⟨w, hw, w', hw', a, ha, rfl, hsq⟩ := sq_L_swap h i hbot hx
  rw [hsq, sq_W_swap h i hne hbot hw', mul_one] at hxx
  have hwU := mem_U_of_sq_eq_one h i hlam hlam0 hw hxx
  have hUA : 𝐔[i] ≤ 𝐀[i.swap] := pull_mono φ ((rootU_le_center i).trans (center_le_rootA _))
  exact mul_mem (mul_mem (mem_sup_left (hUA hwU)) (mem_sup_right (W_le_Fi h _ hw')))
    (mem_sup_left ha)

theorem Nhat_le_normalizer_K_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {lam : K}
    (hlam : ∀ w ∈ 𝐖[i], ∀ a : K, t⁻¹ * (w⁻¹ * t * w) = coordG φ i a →
      w * w = coordG φ i (lam * a)) (hlam0 : lam ≠ 0) :
    𝐍ₕ[i] ≤ normalizer (𝐊[i.swap] : Set G) := by
  intro g hg
  have hgL := Nhat_le_normalizer_L h i hne hbot i.swap hg
  refine mem_normalizer_of_conj_le fun x hx => mem_K_swap_of_sq h i hne hbot hlam hlam0
    ((mem_normalizer_iff.mp hgL x).mp (K_le_L _ hx)) ?_
  rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group,
    K_sq h i.swap (fun w hw => sq_W_swap h i hne hbot hw) hx, mul_one, mul_inv_cancel]

theorem Nhat_le_normalizer_Hk (h : FCHyp L K n φ t) (i k : Axis)
    (hR : 𝐍ₕ[i] ≤ normalizer (𝐑[k] : Set G)) (hK : 𝐍ₕ[i] ≤ normalizer (𝐊[k] : Set G)) :
    𝐍ₕ[i] ≤ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have hxR : x ∈ 𝐑[k] := H_le_R h k (mem_inf.mp hx).1
  have hgxR : g * x * g⁻¹ ∈ 𝐑[k] := (mem_normalizer_iff.mp (hR hg) x).mp hxR
  refine (mem_Hk_iff h k hgxR).mpr fun r hr => ?_
  have hr' : g⁻¹ * r * g ∈ 𝐑[k] := by
    have := (mem_normalizer_iff.mp (inv_mem (hR hg)) r).mp hr
    rwa [inv_inv] at this
  have h1 := (mem_Hk_iff h k hxR).mp hx _ hr'
  have h2 := (mem_normalizer_iff.mp (hK hg) _).mp h1
  rwa [show g * (x * (g⁻¹ * r * g) * x⁻¹ * (g⁻¹ * r * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * r * (g * x * g⁻¹)⁻¹ * r⁻¹ by group] at h2

theorem second_index (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G)).relIndex
      (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G)) = Nat.card K := by
  have hcard : ∀ m : Axis, (normalizer (𝐑[m] : Set G) ⊓ normalizer (𝐁[m] : Set G)).relIndex
      (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[m] : Subgroup G) : Set G)) *
        (Nat.card K * Nat.card (normalizer (𝐐 : Set G)) * Nat.card K) = Nat.card 𝐍ₕ[i] := by
    intro m
    have h1 := relIndex_mul_card (normalizer (𝐑[m] : Set G) ⊓ normalizer (𝐁[m] : Set G))
      (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[m] : Subgroup G) : Set G))
    rw [inf_of_le_left (NRB_le h i hne hbot m), card_NRB' h i hne hbot m] at h1
    have h2 := relIndex_mul_card (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[m] : Subgroup G) : Set G)) 𝐍ₕ[i]
    rw [inf_of_le_left inf_le_left, (first_index h i hne hbot m).1] at h2
    rw [← h2, ← h1]
    ring
  have hpos : 0 < Nat.card K * Nat.card (normalizer (𝐐 : Set G)) * Nat.card K := by
    have : 0 < Nat.card K := Nat.card_pos
    have : 0 < Nat.card (normalizer (𝐐 : Set G)) := Nat.card_pos
    positivity
  have heq : ∀ m : Axis, (normalizer (𝐑[m] : Set G) ⊓ normalizer (𝐁[m] : Set G)).relIndex
      (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[m] : Subgroup G) : Set G)) =
      (normalizer (𝐑[i] : Set G) ⊓ normalizer (𝐁[i] : Set G)).relIndex
        (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G)) := fun m =>
    Nat.eq_of_mul_eq_mul_right hpos ((hcard m).trans (hcard i).symm)
  rw [heq k]
  rcases second_index_i h i hne hbot with h1 | h1
  · exfalso
    have hX : ∀ m : Axis, 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[m] : Subgroup G) : Set G) ≤
        normalizer (𝐑[m] : Set G) ⊓ normalizer (𝐁[m] : Set G) := fun m =>
      relIndex_eq_one.mp ((heq m).trans h1)
    have hRi := Nhat_le_normalizer_R h i hne hbot i (hX i)
    have hRj := Nhat_le_normalizer_R h i hne hbot i.swap (hX i.swap)
    have hno : ∀ m : Axis, ¬ 𝐍ₕ[i] ≤ normalizer ((𝐇 ⊓ 𝐄[m] : Subgroup G) : Set G) := by
      intro m hm
      have h2 := (first_index h i hne hbot m).1
      rw [relIndex_eq_one.mpr (le_inf le_rfl hm)] at h2
      have := h.four_le_card
      omega
    by_cases hi : ∀ w ∈ 𝐖[i], w * w = 1
    · exact hno i (Nhat_le_normalizer_Hk h i i hRi (Nhat_le_normalizer_K_i h i hne hbot hi))
    · obtain ⟨-, lam, hlam, -⟩ := square_map h i
      have hlam0 : lam ≠ 0 := by
        rintro rfl
        apply hi
        intro w hw
        obtain ⟨a, ha⟩ := exists_coordG_eq φ i (kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hw)).2)
        rw [hlam w hw a ha.symm, zero_mul, coordG_zero]
      exact hno i.swap (Nhat_le_normalizer_Hk h i i.swap hRj
        (Nhat_le_normalizer_K_swap h i hne hbot hlam hlam0))
  · exact h1

theorem exists_mem_normalizer_D_not_B (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ g ∈ normalizer (𝐃[i] : Set G), g ∉ normalizer (𝐁[i] : Set G) := by
  by_contra hcon
  have hsub : 𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) ≤
      normalizer (𝐑[i] : Set G) ⊓ normalizer (𝐁[i] : Set G) := by
    intro g hg
    rw [← Nhat_inf_NB h i hne hbot i]
    refine mem_inf.mpr ⟨(mem_inf.mp hg).1, ?_⟩
    by_contra hgB
    exact hcon ⟨g, Nhat_inf_normalizer_Hi_le h i hne hbot hg, hgB⟩
  have h1 := second_index h i hne hbot i
  rw [relIndex_eq_one.mpr hsub] at h1
  have := h.four_le_card
  omega

theorem W_sq_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {w : G} (hw : w ∈ 𝐖[i]) {a : K}
    (ha : t⁻¹ * (w⁻¹ * t * w) = coordG φ i a) : w * w = coordG φ i a := by
  obtain ⟨-, lam, hlam, -⟩ := square_map h i
  suffices hl : lam = 1 by rw [hlam w hw a ha, hl, one_mul]
  obtain ⟨g, hgD, hgB⟩ := exists_mem_normalizer_D_not_B h i hne hbot
  have htt := h.setup.t_mul_t
  have htN : t ∈ normalizer (𝐊[i] : Set G) := H_le_normalizer_K h i t_mem_H
  have hy : g * t * g⁻¹ ∈ 𝐃[i] := (mem_normalizer_iff.mp hgD t).mp (t_mem_D h i)
  have hyK : g * t * g⁻¹ ∉ 𝐊[i] := fun h1 => by
    have := conj_mem_K_of_normalizer_D h i (inv_mem hgD) h1
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact t_not_mem_K h i this
  have hk : t * (g * t * g⁻¹) ∈ 𝐊[i] :=
    (mem_or_mul_mem htt htN (by rw [(K_sup_t h i).2]; exact hy)).resolve_left hyK
  have e : g * t * g⁻¹ = t * (t * (g * t * g⁻¹)) := by rw [← mul_assoc, htt, one_mul]
  have hyy : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have hkA : t * (g * t * g⁻¹) ∉ 𝐀[i] := fun hkA => hgB (mem_normalizer_zpowers_sup
    (by rw [e]; exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hkA))
    fun a ha => (mem_normalizer_iff.mp (normalizer_D_le_normalizer_A h i hgD) a).mp ha)
  generalize hkdef : t * (g * t * g⁻¹) = k at hk hkA e
  rw [e] at hyy
  rw [← SetLike.mem_coe, ← K_mul h i] at hk
  obtain ⟨a', ha', f, hf, hkf⟩ := hk
  rw [← W_mul_U h i] at hf
  obtain ⟨v, hv, u, hu, rfl⟩ := hf
  have hkf : a' * (v * u) = k := hkf
  have huZ : u ∈ 𝐙 := pull_mono φ (rootU_le_center _) hu
  have huA : u ∈ 𝐀[i] := pull_mono φ (center_le_rootA i) huZ
  have hvH : v ∈ 𝐇 := F_le_H h (W_le_F i hv)
  have hvu : v * u = u * v := comm_ZP h hvH huZ
  have hk' : k = (a' * u) * v := by rw [← hkf, hvu]; group
  have hvU : v ∉ 𝐔[i] := fun hvU => hkA (by
    rw [hk']
    exact mul_mem (mul_mem ha' huA) (pull_mono φ (rootU_le_rootA i) hvU))
  rw [hk'] at hyy
  have ha'' : a' * u ∈ 𝐀[i] := mul_mem ha' huA
  have hat : (a' * u) * t = t * (a' * u) := (h.twoCore.comm (pull_le φ _ ha'')).symm
  have hav : (a' * u) * v = v * (a' * u) := A_comm_D h i ha'' (mem_inf.mp (W_le_Fi h i hv)).2
  have haa : (a' * u) * (a' * u) = 1 := A_mul_self h i ha''
  have e2 : t * ((a' * u) * v) * (t * ((a' * u) * v)) = (t * v) * (t * v) := by
    calc t * ((a' * u) * v) * (t * ((a' * u) * v)) =
        t * ((a' * u) * v) * t * (a' * u) * v := by group
      _ = t * (v * (a' * u)) * t * (a' * u) * v := by rw [hav]
      _ = t * v * ((a' * u) * t) * (a' * u) * v := by group
      _ = t * v * (t * (a' * u)) * (a' * u) * v := by rw [hat]
      _ = t * v * t * ((a' * u) * (a' * u)) * v := by group
      _ = (t * v) * (t * v) := by rw [haa]; group
  rw [e2] at hyy
  obtain ⟨b, hb⟩ := exists_coordG_eq φ i (kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hv)).2)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [coordG_zero] at hb
    exact hvU (by rw [← W_inf_C h i]; exact mem_inf.mpr ⟨hv, kappa_eq_one_iff.mp hb.symm⟩)
  have hκZ : t⁻¹ * (v⁻¹ * t * v) ∈ 𝐙 := kappa_mem h hvH
  have c1 := comm_ZP h t_mem_H hκZ
  have c2 := comm_ZP h hvH hκZ
  have e3 : (t * v) * (t * v) = v * v * (t⁻¹ * (v⁻¹ * t * v)) := by
    calc (t * v) * (t * v) = v * (t * (t⁻¹ * (v⁻¹ * t * v))) * t * v := by group
      _ = v * ((t⁻¹ * (v⁻¹ * t * v)) * t) * t * v := by rw [c1]
      _ = v * (t⁻¹ * (v⁻¹ * t * v)) * (t * t) * v := by group
      _ = v * ((t⁻¹ * (v⁻¹ * t * v)) * v) := by rw [htt]; group
      _ = v * (v * (t⁻¹ * (v⁻¹ * t * v))) := by rw [← c2]
      _ = v * v * (t⁻¹ * (v⁻¹ * t * v)) := by group
  rw [e3, hlam v hv b hb.symm, ← hb, ← coordG_add, ← coordG_zero φ i] at hyy
  have h5 := coordG_injective φ i hyy
  have h6 : (lam + 1) * b = 0 := by linear_combination h5
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h6).resolve_right hb0)

theorem normalizer_D_swap_eq (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    normalizer (𝐃[i.swap] : Set G) = normalizer (𝐁[i.swap] : Set G) :=
  le_antisymm (normalizer_D_le_normalizer_B h i.swap
    (fun _ hx => K_sq h i.swap (fun _ hw => sq_W_swap h i hne hbot hw) hx))
    (N_le_normalizer_D h i.swap)

theorem W_sq_eq' (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∀ w ∈ 𝐖[i], ∀ a : K, t⁻¹ * (w⁻¹ * t * w) = coordG φ i a →
      w * w = coordG φ i (1 * a) := fun _ hw _ ha => by
  rw [one_mul]
  exact W_sq_eq h i hne hbot hw ha

theorem closure_sq_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : closure {x : G | ∃ y ∈ 𝐅, x = y * y} = 𝐔[i] := by
  obtain ⟨-, lam, -, huniq, -, hlamne⟩ := square_map h i
  have hl : (1 : K) = lam := huniq 1 (W_sq_eq' h i hne hbot)
  obtain ⟨hcl, -⟩ := hlamne (hl ▸ one_ne_zero)
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact F_sq_mem_U h i (fun w hw => sq_W_swap h i hne hbot hw) hy
  · rw [← hcl]
    exact closure_mono fun x ⟨y, hy, hxy⟩ => ⟨y, W_le_F i hy, hxy⟩

end Indices

end SingleComm

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
