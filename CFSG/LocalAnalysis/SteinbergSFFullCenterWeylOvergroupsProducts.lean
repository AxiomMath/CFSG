module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterWeyl

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Conj

variable {G : Type*} [Group G]

theorem mem_map_conj_inv {S : Subgroup G} {g x : G} :
    x ∈ S.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

end Conj

section Weyl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

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
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅ᵢʷ[" i "]" => ((𝐅 ⊓ 𝐃[i]).map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇ʷ[" i "]" => ((𝐇 ⊓ 𝐄[i]).map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋ʷ[" i "]" => (𝐋[i].map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)

omit [Finite G] [CharP K 2] [Finite K] in
theorem w_conj_conj (i : Axis) (x : G) : 𝐰[i] * (𝐰[i] * x * 𝐰[i]⁻¹) * 𝐰[i]⁻¹ = x := by
  rw [w_inv]
  calc 𝐰[i] * (𝐰[i] * x * 𝐰[i]) * 𝐰[i] = (𝐰[i] * 𝐰[i]) * x * (𝐰[i] * 𝐰[i]) := by group
    _ = x := by rw [w_mul_self, one_mul, mul_one]

omit [Finite G] [CharP K 2] [Finite K] in
theorem map_conj_w_eq {Y : Subgroup G} (i : Axis) (hY : ∀ y ∈ Y, 𝐰[i] * y * 𝐰[i]⁻¹ ∈ Y) :
    Y.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom = Y := by
  ext x
  rw [mem_map_conj_inv]
  exact ⟨fun hx => by simpa only [w_conj_conj] using hY _ hx, hY x⟩

theorem conj_w_mem_K (h : FCHyp L K n φ t) (i : Axis) {k : G} (hk : k ∈ 𝐊[i]) :
    𝐰[i] * k * 𝐰[i]⁻¹ ∈ 𝐊[i] := by
  set S := 𝐊[i].map (MulAut.conj 𝐰[i]).toMonoidHom with hS
  have hSD : S ≤ 𝐃[i] := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_w_mem_D h i (K_le_D h i hy)
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show 𝐰[i] * x * 𝐰[i]⁻¹ * (𝐰[i] * y * 𝐰[i]⁻¹) = 𝐰[i] * (x * y) * 𝐰[i]⁻¹ by group,
      K_comm h i hx hy]
    group
  have hcard : Nat.card S = Nat.card 𝐊[i] := card_map_of_injective (MulAut.conj _).injective
  have hSK := (K_unique h i hSD hSc).2 hcard
  rw [← hSK]
  exact ⟨k, hk, rfl⟩

theorem K_inf_cent_J (h : FCHyp L K n φ t) (i : Axis) :
    𝐊[i] ⊓ centralizer (𝐉[i] : Set G) = 𝐖[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf ((W_le_Fi h i).trans le_sup_right) inf_le_right)
  obtain ⟨hxK, hxJ⟩ := mem_inf.mp hx
  obtain ⟨g, hgJ, hfix⟩ := exists_good_Ji h i
  have hgJ0 : g ∈ 𝐉 := axisTorus_le_J0 i hgJ
  rw [← SetLike.mem_coe, ← K_mul h i] at hxK
  obtain ⟨a, ha, f, hf, rfl⟩ := hxK
  have hxg : g⁻¹ * (a * f) * g = a * f := by
    rw [mul_assoc, ← mem_centralizer_iff.mp hxJ g hgJ, inv_mul_cancel_left]
  have hga : g⁻¹ * a * g ∈ 𝐀[i] := by
    have := (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A i (inv_mem hgJ0)) a).mp ha
    rwa [inv_inv] at this
  have hgf : g⁻¹ * f * g ∈ 𝐅 ⊓ 𝐃[i] :=
    ⟨conj_torus_mem_F h hgJ0 hf.1, conj_torus_mem_D h i hgJ0 hf.2⟩
  have e1 : a⁻¹ * (g⁻¹ * a * g) = f * (g⁻¹ * f * g)⁻¹ := by
    have e2 : (g⁻¹ * a * g) * (g⁻¹ * f * g) = a * f := by rw [← hxg]; group
    calc a⁻¹ * (g⁻¹ * a * g) = a⁻¹ * ((g⁻¹ * a * g) * (g⁻¹ * f * g)) * (g⁻¹ * f * g)⁻¹ := by
          group
      _ = f * (g⁻¹ * f * g)⁻¹ := by rw [e2]; group
  have hmem : a⁻¹ * (g⁻¹ * a * g) ∈ 𝐀[i] ⊓ (𝐅 ⊓ 𝐃[i]) :=
    mem_inf.mpr ⟨mul_mem (inv_mem ha) hga, by rw [e1]; exact mul_mem hf (inv_mem hgf)⟩
  rw [A_inf_Fi h i] at hmem
  have haZ := hfix a ha hmem
  exact mem_inf.mpr ⟨mul_mem (ZP_le_F h haZ) hf.1, hxJ⟩

theorem conj_w_mem_W (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐖[i]) :
    𝐰[i] * x * 𝐰[i]⁻¹ ∈ 𝐖[i] := by
  rw [← K_inf_cent_J h i]
  refine ⟨conj_w_mem_K h i ((W_le_Fi h i).trans le_sup_right hx), mem_centralizer_iff.mpr
    fun j hj => ?_⟩
  have hj' : 𝐰[i] * j * 𝐰[i]⁻¹ ∈ 𝐉[i] := conj_w_mem_Ji i hj
  rw [w_inv] at hj' ⊢
  have hc := mem_centralizer_iff.mp (mem_inf.mp hx).2 _ hj'
  calc j * (𝐰[i] * x * 𝐰[i]) = 𝐰[i] * ((𝐰[i] * j * 𝐰[i]) * x) * 𝐰[i] := by
        rw [show 𝐰[i] * ((𝐰[i] * j * 𝐰[i]) * x) * 𝐰[i] =
          (𝐰[i] * 𝐰[i]) * j * (𝐰[i] * x * 𝐰[i]) by group, w_mul_self, one_mul]
    _ = 𝐰[i] * (x * (𝐰[i] * j * 𝐰[i])) * 𝐰[i] := by rw [hc]
    _ = 𝐰[i] * x * 𝐰[i] * j := by
        rw [show 𝐰[i] * (x * (𝐰[i] * j * 𝐰[i])) * 𝐰[i] =
          𝐰[i] * x * 𝐰[i] * j * (𝐰[i] * 𝐰[i]) by group, w_mul_self, mul_one]

theorem Fiw_le_K (h : FCHyp L K n φ t) (i : Axis) : 𝐅ᵢʷ[i] ≤ 𝐊[i] := fun x hx => by
  rw [mem_map_conj_inv] at hx
  simpa only [w_conj_conj] using conj_w_mem_K h i (mem_sup_right hx : _ ∈ 𝐊[i])

theorem W_le_Fiw (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ≤ 𝐅ᵢʷ[i] := fun _ hx =>
  mem_map_conj_inv.mpr (W_le_Fi h i (conj_w_mem_W h i hx))

theorem Fi_mul_Fiw (h : FCHyp L K n φ t) (i : Axis) :
    ((𝐅 ⊓ 𝐃[i] : Subgroup G) : Set G) * (𝐅ᵢʷ[i] : Set G) = 𝐊[i] := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (mem_sup_right hx) (Fiw_le_K h i hy)
  · intro k hk
    rw [← K_mul h i] at hk
    obtain ⟨a, ha, f, hf, rfl⟩ := hk
    have hc : a * f = f * a := A_comm_D h i ha hf.2
    obtain ⟨z, hz, u, hu, rfl⟩ := exists_A_eq h i ha
    refine ⟨f * z, mul_mem hf (ZP_le_Fi h i hz), 𝐰[i] * u * 𝐰[i]⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_map_conj_inv, w_conj_conj]
      exact ZP_le_Fi h i (pull_mono φ (rootU_le_center _) hu)
    · simp only
      rw [hc]
      group

theorem Fi_sup_Fiw (h : FCHyp L K n φ t) (i : Axis) : (𝐅 ⊓ 𝐃[i]) ⊔ 𝐅ᵢʷ[i] = 𝐊[i] := by
  refine le_antisymm (sup_le le_sup_right (Fiw_le_K h i)) fun k hk => ?_
  rw [← SetLike.mem_coe, ← Fi_mul_Fiw h i] at hk
  obtain ⟨x, hx, y, hy, rfl⟩ := hk
  exact mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem Fi_inf_Fiw (h : FCHyp L K n φ t) (i : Axis) : (𝐅 ⊓ 𝐃[i]) ⊓ 𝐅ᵢʷ[i] = 𝐖[i] := by
  have hle : 𝐖[i] ≤ (𝐅 ⊓ 𝐃[i]) ⊓ 𝐅ᵢʷ[i] := le_inf (W_le_Fi h i) (W_le_Fiw h i)
  have hN : 𝐅ᵢʷ[i] ≤ normalizer ((𝐅 ⊓ 𝐃[i] : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun x hx y hy =>
      K_comm h i (Fiw_le_K h i hx) (mem_sup_right hy : y ∈ 𝐊[i])
  have h1 := card_sup_mul_card_inf (𝐅 ⊓ 𝐃[i]) 𝐅ᵢʷ[i] hN
  rw [Fi_sup_Fiw h i, card_K h i, card_map_of_injective (MulAut.conj _).injective,
    card_Fi h] at h1
  have hq : 0 < Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card ((𝐅 ⊓ 𝐃[i]) ⊓ 𝐅ᵢʷ[i] : Subgroup G) = Nat.card K ^ 2 :=
    Nat.eq_of_mul_eq_mul_left hq (by rw [h1]; ring)
  exact (eq_of_le_of_card_ge hle (by rw [h2, card_W h i])).symm

omit [Finite G] [Finite K] in
theorem kappa_conj_w (h : FCHyp L K n φ t) (i : Axis) (x : G) :
    t⁻¹ * ((𝐰[i] * x * 𝐰[i]⁻¹)⁻¹ * t * (𝐰[i] * x * 𝐰[i]⁻¹)) =
      𝐰[i] * (t⁻¹ * (x⁻¹ * t * x)) * 𝐰[i]⁻¹ := by
  have hwt : 𝐰[i] * t * 𝐰[i]⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp (h.setup.L_le (w_mem_L i)), mul_inv_cancel_right]
  calc t⁻¹ * ((𝐰[i] * x * 𝐰[i]⁻¹)⁻¹ * t * (𝐰[i] * x * 𝐰[i]⁻¹))
      = (𝐰[i] * t * 𝐰[i]⁻¹)⁻¹ * ((𝐰[i] * x * 𝐰[i]⁻¹)⁻¹ * (𝐰[i] * t * 𝐰[i]⁻¹) *
          (𝐰[i] * x * 𝐰[i]⁻¹)) := by rw [hwt]
    _ = 𝐰[i] * (t⁻¹ * (x⁻¹ * t * x)) * 𝐰[i]⁻¹ := by group

theorem mem_D_of_kappa (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐄[i])
    (hu : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[i]) : x ∈ 𝐃[i] := by
  have hxM : x ∈ 𝐌[i] := FCHyp.mem_M_of (h.N_le_normalizer_U i (map_subtype_le _ hx)) hu
    (by rw [mul_inv_cancel_left])
  rw [← (coreFacts h i).E_inf_M]
  exact mem_inf.mpr ⟨hx, hxM⟩

theorem Hi_inf_Hiw (h : FCHyp L K n φ t) (i : Axis) : (𝐇 ⊓ 𝐄[i]) ⊓ 𝐇ʷ[i] = 𝐃[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (D_le_Hi h i) fun d hd =>
    mem_map_conj_inv.mpr (D_le_Hi h i (conj_w_mem_D h i hd)))
  obtain ⟨hxHi, hxw⟩ := mem_inf.mp hx
  obtain ⟨hxH, hxE⟩ := mem_inf.mp hxHi
  obtain ⟨hyH, hyE⟩ := mem_inf.mp (mem_map_conj_inv.mp hxw)
  have h1 : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐙 := (mem_H_iff_E h i hxE).mp hxH
  have h2 := (mem_H_iff_E h i hyE).mp hyH
  rw [kappa_conj_w h i] at h2
  exact mem_D_of_kappa h i hxE (mem_U_of_conj_w h i h1 h2)

theorem F_inf_Fw (h : FCHyp L K n φ t) (i : Axis) : 𝐅 ⊓ 𝐅ʷ[i] = 𝐖[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (W_le_F i) fun x hx =>
    mem_map_conj_inv.mpr (W_le_F i (conj_w_mem_W h i hx)))
  obtain ⟨hxF, hxw⟩ := mem_inf.mp hx
  rw [mem_map_conj_inv] at hxw
  have hFHi : 𝐅 ≤ 𝐇 ⊓ 𝐄[i] := le_inf (F_le_H h) (F_le_E h i)
  have hxD : x ∈ 𝐃[i] := by
    rw [← Hi_inf_Hiw h i]
    exact mem_inf.mpr ⟨hFHi hxF, mem_map_conj_inv.mpr (hFHi hxw)⟩
  rw [← Fi_inf_Fiw h i]
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxF, hxD⟩,
    mem_map_conj_inv.mpr (mem_inf.mpr ⟨hxw, conj_w_mem_D h i hxD⟩)⟩

theorem conj_E_mem_of (h : FCHyp L K n φ t) (i : Axis) {S : Subgroup G} (hAS : 𝐀[i] ≤ S)
    (hSE : S ≤ 𝐄[i]) {e : G} (he : e ∈ 𝐄[i]) {s : G} (hs : s ∈ S) : e * s * e⁻¹ ∈ S := by
  have h1 := commutator_mem_closure_sq (hSE hs) (inv_mem he)
  rw [inv_inv, closure_sq_E h i] at h1
  rw [show e * s * e⁻¹ = s * (s⁻¹ * (e * s * e⁻¹)) by group]
  exact mul_mem hs (hAS h1)

theorem E_le_normalizer_of (h : FCHyp L K n φ t) (i : Axis) {S : Subgroup G} (hAS : 𝐀[i] ≤ S)
    (hSE : S ≤ 𝐄[i]) : 𝐄[i] ≤ normalizer (S : Set G) := fun _ he =>
  mem_normalizer_of_conj_le fun _ hs => conj_E_mem_of h i hAS hSE he hs

theorem L_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ≤ 𝐄[i] := (L_le_Hi h i).trans inf_le_right

omit [Finite G] [Finite K] in
theorem K_le_L (i : Axis) : 𝐊[i] ≤ 𝐋[i] := sup_le (A_le_L i) (inf_le_left.trans (F_le_L i))

theorem Lw_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐋ʷ[i] ≤ 𝐄[i] := fun x hx => by
  rw [mem_map_conj_inv] at hx
  simpa only [w_conj_conj] using conj_w_mem_E h i (L_le_E h i hx)

omit [Finite G] [Finite K] in
theorem Fw_le_Lw (i : Axis) : 𝐅ʷ[i] ≤ 𝐋ʷ[i] := map_mono (F_le_L i)

omit [Finite G] [Finite K] in
theorem Fiw_le_Fw (i : Axis) : 𝐅ᵢʷ[i] ≤ 𝐅ʷ[i] := map_mono inf_le_left

theorem L_inf_D (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ⊓ 𝐃[i] = 𝐊[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (K_le_L i) (K_le_D h i))
  obtain ⟨hxL, hxD⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← L_mul h i] at hxL
  obtain ⟨f, hf, a, ha, rfl⟩ := hxL
  have hfD : f ∈ 𝐃[i] := by simpa using mul_mem hxD (inv_mem (A_le_D h i ha))
  exact mul_mem (mem_sup_right (mem_inf.mpr ⟨hf, hfD⟩)) (mem_sup_left ha)

theorem L_inf_Lw (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ⊓ 𝐋ʷ[i] = 𝐊[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (K_le_L i) fun k hk =>
    mem_map_conj_inv.mpr (K_le_L i (conj_w_mem_K h i hk)))
  obtain ⟨hxL, hxw⟩ := mem_inf.mp hx
  rw [mem_map_conj_inv] at hxw
  have hxD : x ∈ 𝐃[i] := by
    rw [← Hi_inf_Hiw h i]
    exact mem_inf.mpr ⟨L_le_Hi h i hxL, mem_map_conj_inv.mpr (L_le_Hi h i hxw)⟩
  rw [← L_inf_D h i]
  exact mem_inf.mpr ⟨hxL, hxD⟩

theorem conj_D_mem_Fw (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {f : G}
    (hf : f ∈ 𝐅ʷ[i]) : d⁻¹ * f * d ∈ 𝐅ʷ[i] := by
  rw [mem_map_conj_inv] at hf ⊢
  have hdH : (𝐰[i] * d * 𝐰[i]⁻¹)⁻¹ ∈ 𝐇 := inv_mem (D_le_H i (conj_w_mem_D h i hd))
  have := conj_H_mem_F h hdH hf
  rwa [inv_inv, show (𝐰[i] * d * 𝐰[i]⁻¹)⁻¹ * (𝐰[i] * f * 𝐰[i]⁻¹) * (𝐰[i] * d * 𝐰[i]⁻¹) =
    𝐰[i] * (d⁻¹ * f * d) * 𝐰[i]⁻¹ by group] at this

theorem Lw_le_normalizer_L (h : FCHyp L K n φ t) (i : Axis) :
    𝐋ʷ[i] ≤ normalizer (𝐋[i] : Set G) :=
  (Lw_le_E h i).trans (E_le_normalizer_of h i (A_le_L i) (L_le_E h i))

theorem F_mul_Fw (h : FCHyp L K n φ t) (i : Axis) :
    (𝐅 : Set G) * (𝐅ʷ[i] : Set G) = ((𝐋[i] ⊔ 𝐋ʷ[i] : Subgroup G) : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, f', hf', rfl⟩
    exact mul_mem (mem_sup_left (F_le_L i hf)) (mem_sup_right (Fw_le_Lw i hf'))
  · intro x hx
    rw [coe_mul_of_right_le_normalizer_left _ _ (Lw_le_normalizer_L h i)] at hx
    obtain ⟨l, hl, l', hl', rfl⟩ := hx
    rw [SetLike.mem_coe, ← SetLike.mem_coe, ← L_mul h i] at hl
    obtain ⟨f, hf, a, ha, rfl⟩ := hl
    have hl'' : 𝐰[i] * l' * 𝐰[i]⁻¹ ∈ 𝐋[i] := mem_map_conj_inv.mp hl'
    rw [← SetLike.mem_coe, ← L_mul h i] at hl''
    obtain ⟨f₀, hf₀, a₀, ha₀, hfa⟩ := hl''
    have hl'eq : l' = (𝐰[i]⁻¹ * f₀ * 𝐰[i]) * (𝐰[i]⁻¹ * a₀ * 𝐰[i]) := by
      change f₀ * a₀ = _ at hfa
      rw [show l' = 𝐰[i]⁻¹ * (𝐰[i] * l' * 𝐰[i]⁻¹) * 𝐰[i] by group, ← hfa]
      group
    have hf' : 𝐰[i]⁻¹ * f₀ * 𝐰[i] ∈ 𝐅ʷ[i] := by
      rw [mem_map_conj_inv]
      rw [show 𝐰[i] * (𝐰[i]⁻¹ * f₀ * 𝐰[i]) * 𝐰[i]⁻¹ = f₀ by group]
      exact hf₀
    have ha' : 𝐰[i]⁻¹ * a₀ * 𝐰[i] ∈ 𝐀[i] := by
      simpa only [w_inv] using conj_w_mem_A h i ha₀
    set f' := 𝐰[i]⁻¹ * f₀ * 𝐰[i]
    set a' := 𝐰[i]⁻¹ * a₀ * 𝐰[i]
    have hf'E : f' ∈ 𝐄[i] := Lw_le_E h i (Fw_le_Lw i hf')
    have ha'' : f'⁻¹ * a * f'⁻¹⁻¹ * a' ∈ 𝐀[i] :=
      mul_mem ((h.actHyp i).conj_A _ (inv_mem (map_subtype_le _ hf'E)) a ha) ha'
    have hK : f'⁻¹ * a * f'⁻¹⁻¹ * a' ∈ ((𝐅 ⊓ 𝐃[i] : Subgroup G) : Set G) * (𝐅ᵢʷ[i] : Set G) := by
      rw [Fi_mul_Fiw h i]
      exact mem_sup_left ha''
    obtain ⟨y, hy, z, hz, hyz⟩ := hK
    refine ⟨f * y, mul_mem hf hy.1, (y⁻¹ * f' * y) * z,
      mul_mem (conj_D_mem_Fw h i hy.2 hf') (Fiw_le_Fw i hz), ?_⟩
    rw [hl'eq]
    change f * y * (y⁻¹ * f' * y * z) = f * a * (f' * a')
    rw [show f * a * (f' * a') = f * f' * (f'⁻¹ * a * f'⁻¹⁻¹ * a') by group, ← hyz]
    group

theorem X_eq (h : FCHyp L K n φ t) (i : Axis) : 𝐅 ⊔ 𝐅ʷ[i] = 𝐋[i] ⊔ 𝐋ʷ[i] := by
  refine le_antisymm (sup_le ((F_le_L i).trans le_sup_left) ((Fw_le_Lw i).trans le_sup_right))
    fun x hx => ?_
  rw [← SetLike.mem_coe, ← F_mul_Fw h i] at hx
  obtain ⟨f, hf, f', hf', rfl⟩ := hx
  exact mul_mem (mem_sup_left hf) (mem_sup_right hf')

theorem F_mul_Fw' (h : FCHyp L K n φ t) (i : Axis) :
    (𝐅 : Set G) * (𝐅ʷ[i] : Set G) = ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) := by
  rw [X_eq h i, F_mul_Fw h i]

theorem card_X (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) = Nat.card K ^ 6 := by
  rw [X_eq h i]
  have h1 := card_sup_mul_card_inf 𝐋[i] 𝐋ʷ[i] (Lw_le_normalizer_L h i)
  rw [L_inf_Lw h i, card_K h i, card_map_of_injective (MulAut.conj _).injective, card_L h i] at h1
  have hq : 0 < Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem X_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐅 ⊔ 𝐅ʷ[i] ≤ 𝐄[i] := by
  rw [X_eq h i]
  exact sup_le (L_le_E h i) (Lw_le_E h i)

theorem L_le_X (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ≤ 𝐅 ⊔ 𝐅ʷ[i] := by
  rw [X_eq h i]
  exact le_sup_left

theorem L_sup_D (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ⊔ 𝐃[i] = 𝐇 ⊓ 𝐄[i] := by
  have hN : 𝐃[i] ≤ normalizer (𝐋[i] : Set G) := fun _ hd =>
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i (D_le_H i hd) hl
  have h1 := card_sup_mul_card_inf 𝐋[i] 𝐃[i] hN
  rw [L_inf_D h i, card_K h i, card_L h i, h.card_D i] at h1
  refine eq_of_le_of_card_ge (sup_le (L_le_Hi h i) (D_le_Hi h i)) ?_
  have hq : 0 < Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card (𝐋[i] ⊔ 𝐃[i] : Subgroup G) = 2 * Nat.card K ^ 5 :=
    Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  rw [h2, card_Hi h i]

theorem D_map_w (h : FCHyp L K n φ t) (i : Axis) :
    𝐃[i].map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom = 𝐃[i] :=
  map_conj_w_eq i fun _ hd => conj_w_mem_D h i hd

theorem Lw_sup_D (h : FCHyp L K n φ t) (i : Axis) : 𝐋ʷ[i] ⊔ 𝐃[i] = 𝐇ʷ[i] := by
  conv_rhs => rw [← L_sup_D h i, Subgroup.map_sup, D_map_w h i]

theorem Hiw_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐇ʷ[i] ≤ 𝐄[i] := fun x hx => by
  rw [mem_map_conj_inv] at hx
  simpa only [w_conj_conj] using conj_w_mem_E h i (mem_inf.mp hx).2

theorem Hi_sup_Hiw (h : FCHyp L K n φ t) (i : Axis) : (𝐇 ⊓ 𝐄[i]) ⊔ 𝐇ʷ[i] = 𝐄[i] := by
  have hAH : 𝐀[i] ≤ 𝐇 ⊓ 𝐄[i] := (A_le_D h i).trans (D_le_Hi h i)
  have hN : 𝐇ʷ[i] ≤ normalizer ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) :=
    (Hiw_le_E h i).trans (E_le_normalizer_of h i hAH inf_le_right)
  have h1 := card_sup_mul_card_inf (𝐇 ⊓ 𝐄[i]) 𝐇ʷ[i] hN
  rw [Hi_inf_Hiw h i, h.card_D i, card_map_of_injective (MulAut.conj _).injective,
    card_Hi h i] at h1
  refine eq_of_le_of_card_ge (sup_le inf_le_right (Hiw_le_E h i)) ?_
  have hq : 0 < 2 * Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card ((𝐇 ⊓ 𝐄[i]) ⊔ 𝐇ʷ[i] : Subgroup G) = 2 * Nat.card K ^ 6 :=
    Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
  rw [h2, card_E h i]

theorem X_sup_D (h : FCHyp L K n φ t) (i : Axis) : (𝐅 ⊔ 𝐅ʷ[i]) ⊔ 𝐃[i] = 𝐄[i] := by
  refine le_antisymm (sup_le (X_le_E h i) (h.D_le_E i)) ?_
  have hLw : 𝐋ʷ[i] ≤ 𝐅 ⊔ 𝐅ʷ[i] := by
    rw [X_eq h i]
    exact le_sup_right
  calc 𝐄[i] = (𝐇 ⊓ 𝐄[i]) ⊔ 𝐇ʷ[i] := (Hi_sup_Hiw h i).symm
    _ ≤ (𝐅 ⊔ 𝐅ʷ[i]) ⊔ 𝐃[i] := by
      refine sup_le ?_ ?_
      · rw [← L_sup_D h i]
        exact sup_le ((L_le_X h i).trans le_sup_left) le_sup_right
      · rw [← Lw_sup_D h i]
        exact sup_le (hLw.trans le_sup_left) le_sup_right

theorem D_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) :
    𝐃[i] ≤ normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) :=
  (h.D_le_E i).trans (E_le_normalizer_of h i ((A_le_L i).trans (L_le_X h i)) (X_le_E h i))

theorem X_mul_D (h : FCHyp L K n φ t) (i : Axis) :
    ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) * (𝐃[i] : Set G) = 𝐄[i] := by
  rw [← coe_mul_of_right_le_normalizer_left _ _ (D_le_normalizer_X h i), X_sup_D h i]

theorem X_inf_D (h : FCHyp L K n φ t) (i : Axis) : (𝐅 ⊔ 𝐅ʷ[i]) ⊓ 𝐃[i] = 𝐊[i] := by
  have h1 := card_sup_mul_card_inf (𝐅 ⊔ 𝐅ʷ[i]) 𝐃[i] (D_le_normalizer_X h i)
  rw [X_sup_D h i, card_E h i, card_X h i, h.card_D i] at h1
  have hle : 𝐊[i] ≤ (𝐅 ⊔ 𝐅ʷ[i]) ⊓ 𝐃[i] := le_inf ((K_le_L i).trans (L_le_X h i)) (K_le_D h i)
  have hq : 0 < 2 * Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card ((𝐅 ⊔ 𝐅ʷ[i]) ⊓ 𝐃[i] : Subgroup G) = Nat.card K ^ 4 :=
    Nat.eq_of_mul_eq_mul_left hq (by rw [h1]; ring)
  exact (eq_of_le_of_card_ge hle (by rw [h2, card_K h i])).symm

theorem t_not_mem_X (h : FCHyp L K n φ t) (i : Axis) : t ∉ 𝐅 ⊔ 𝐅ʷ[i] := fun ht => by
  have h1 : t ∈ (𝐅 ⊔ 𝐅ʷ[i]) ⊓ 𝐃[i] := mem_inf.mpr ⟨ht, t_mem_D h i⟩
  rw [X_inf_D h i] at h1
  exact t_not_mem_K h i h1

theorem X_sup_t (h : FCHyp L K n φ t) (i : Axis) :
    (𝐅 ⊔ 𝐅ʷ[i]) ⊓ zpowers t = ⊥ ∧ (𝐅 ⊔ 𝐅ʷ[i]) ⊔ zpowers t = 𝐄[i] := by
  have hinf : (𝐅 ⊔ 𝐅ʷ[i]) ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxt⟩ := mem_inf.mp hx
    have hx' : x = 1 ∨ x = t := by
      obtain ⟨j, rfl⟩ := hxt
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact absurd hxX (t_not_mem_X h i)
  refine ⟨hinf, ?_⟩
  have hnorm : zpowers t ≤ normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) :=
    zpowers_le.mpr (D_le_normalizer_X h i (t_mem_D h i))
  have h1 := card_sup_mul_card_inf (𝐅 ⊔ 𝐅ʷ[i]) (zpowers t) hnorm
  rw [hinf, card_bot, mul_one, card_X h i, Nat.card_zpowers, h.setup.order_t] at h1
  refine eq_of_le_of_card_ge (sup_le (X_le_E h i) (zpowers_le.mpr (t_mem_E h i))) ?_
  rw [card_E h i, h1, mul_comm]

theorem X_normal_R (h : FCHyp L K n φ t) (i : Axis) :
    𝐅 ⊔ 𝐅ʷ[i] ≤ 𝐑[i] ∧ ((𝐅 ⊔ 𝐅ʷ[i]).subgroupOf 𝐑[i]).Normal := by
  have hXR : 𝐅 ⊔ 𝐅ʷ[i] ≤ 𝐑[i] := (X_le_E h i).trans le_sup_right
  refine ⟨hXR, ⟨fun k hk r => mem_subgroupOf.mpr ?_⟩⟩
  have hk' : (k : G) ∈ 𝐅 ⊔ 𝐅ʷ[i] := mem_subgroupOf.mp hk
  have h1 := commutator_mem_closure_sq (hXR hk') (inv_mem r.2)
  rw [inv_inv] at h1
  have h2 := L_le_X h i (sq_R_le_L h i h1)
  rw [coe_mul, coe_mul, coe_inv, show (r : G) * k * (r : G)⁻¹ =
    k * ((k : G)⁻¹ * ((r : G) * k * (r : G)⁻¹)) by group]
  exact mul_mem hk' h2

theorem R_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ≤ normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) := fun r hr =>
  mem_normalizer_of_conj_le fun x hx => mem_subgroupOf.mp
    ((X_normal_R h i).2.conj_mem ⟨x, (X_normal_R h i).1 hx⟩ (mem_subgroupOf.mpr hx) ⟨r, hr⟩)

theorem J_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) :
    𝐉 ≤ normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) := fun j hj =>
  mem_normalizer_of_conj_le fun x hx => conj_mem_sup
    (fun f hf => by simpa using conj_torus_mem_F h (inv_mem hj) hf)
    (fun f hf => by
      rw [mem_map_conj_inv] at hf ⊢
      have hj' : 𝐰[i] * j * 𝐰[i]⁻¹ ∈ 𝐉 := conj_w_mem_J i hj
      have := conj_torus_mem_F h (inv_mem hj') hf
      rwa [inv_inv, show 𝐰[i] * j * 𝐰[i]⁻¹ * (𝐰[i] * f * 𝐰[i]⁻¹) * (𝐰[i] * j * 𝐰[i]⁻¹)⁻¹ =
        𝐰[i] * (j * f * j⁻¹) * 𝐰[i]⁻¹ by group] at this) hx

omit [Finite K] in
theorem w_mem_normalizer_X (i : Axis) :
    𝐰[i] ∈ normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have hle : 𝐅 ⊔ 𝐅ʷ[i] ≤ (𝐅 ⊔ 𝐅ʷ[i]).comap (MulAut.conj 𝐰[i]).toMonoidHom :=
    sup_le (fun f hf => mem_sup_right (by
      change 𝐰[i] * f * 𝐰[i]⁻¹ ∈ 𝐅ʷ[i]
      rw [mem_map_conj_inv, w_conj_conj]
      exact hf)) fun f hf => mem_sup_left (mem_map_conj_inv.mp hf)
  exact hle hx

theorem normalizer_A_le (h : FCHyp L K n φ t) (i : Axis) :
    L ⊓ normalizer (𝐀[i] : Set G) ≤ normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) := by
  set NX := normalizer ((𝐅 ⊔ 𝐅ʷ[i] : Subgroup G) : Set G) with hNX
  have hP : ∀ p ∈ 𝐏, p ∈ NX := fun p hp =>
    R_le_normalizer_X h i (mem_sup_left (mem_sup_left hp))
  let σ : SL₂ K →* G := (L.subtype.comp φ.symm.toMonoidHom).comp (sHom K i)
  have hS : ∀ M : SL₂ K, σ M ∈ NX := fun M => sl2_mem (NX.comap σ)
    (fun x => hP _ (symm_mem_pull.mpr (sHom_upperSL_mem i x)))
    (fun c => J_le_normalizer_X h i (symm_mem_pull.mpr (sHom_diagSL_mem i c)))
    (by
      change ((φ.symm (sHom K i swapSL) : L) : G) ∈ NX
      rw [sHom_swapSL]
      exact w_mem_normalizer_X i) M
  intro g hg
  obtain ⟨hgL, hgA⟩ := mem_inf.mp hg
  have hgX : φ ⟨g, hgL⟩ ∈ normalizer (rootU K i : Set (antiSp K)) := by
    rw [(h.twoCore.axisStr i).N_eq, mem_normalizer_iff]
    intro z
    have e : ((φ.symm (φ ⟨g, hgL⟩ * z * (φ ⟨g, hgL⟩)⁻¹) : L) : G) =
        g * ((φ.symm z : L) : G) * g⁻¹ := by simp
    calc z ∈ rootA K i ↔ ((φ.symm z : L) : G) ∈ 𝐀[i] := symm_mem_pull.symm
      _ ↔ g * ((φ.symm z : L) : G) * g⁻¹ ∈ 𝐀[i] := mem_normalizer_iff.mp hgA _
      _ ↔ ((φ.symm (φ ⟨g, hgL⟩ * z * (φ ⟨g, hgL⟩)⁻¹) : L) : G) ∈ 𝐀[i] := by rw [e]
      _ ↔ φ ⟨g, hgL⟩ * z * (φ ⟨g, hgL⟩)⁻¹ ∈ rootA K i := symm_mem_pull
  obtain ⟨a, ha, l, M, hgdec⟩ := (h.twoCore.axisStr i).N_decomp _ hgX
  have hg' : g = ((φ.symm a : L) : G) * (((φ.symm (dHom K i l) : L) : G) * σ M) := by
    have := congrArg (fun x => ((φ.symm x : L) : G)) hgdec
    simp only [MulEquiv.symm_apply_apply, map_mul, coe_mul] at this
    exact this
  rw [hg']
  exact mul_mem (hP _ (pull_mono φ (rootA_le_antiUnipotent i) (symm_mem_pull.mpr ha)))
    (mul_mem (J_le_normalizer_X h i (symm_mem_pull.mpr (dHom_mem i l))) (hS M))

end Weyl

end FullCenterWeyl

end CFSG.LocalAnalysis.SymplecticFourStandard
