module

public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourRankThompson
public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourCenterFusion
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.Adapters.Involutions
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace GomiFusion

open Subgroup
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem le_normalizer_of_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    H ≤ normalizer (K : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rwa [hc x hx y hy, mul_inv_cancel_right]
  · intro hy
    have h1 := hc x hx _ hy
    have h2 : x * y * x⁻¹ = y := mul_left_cancel (a := x) (by rw [h1]; group)
    rwa [h2] at hy

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {g : G} :
    g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, x * y = g := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H K (le_normalizer_of_commute hc),
    Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem card_sup_of_commute [Finite G] {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (hHK : H ⊓ K = ⊥) : Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let f : H × K →* G := H.subtype.noncommCoprod K.subtype (fun x y => hc x x.2 y y.2)
  have hf : ∀ (x : H) (y : K), f (x, y) = (x : G) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    rw [hf] at h
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hxK : (x : G) ∈ H ⊓ K := ⟨x.2, by rw [hx]; exact K.inv_mem y.2⟩
    rw [hHK, mem_bot] at hxK
    have hy : (y : G) = 1 := by rw [hxK, one_mul] at h; exact h
    exact Prod.ext (Subtype.ext hxK) (Subtype.ext hy)
  have hrange : f.range = H ⊔ K := by
    ext g
    rw [mem_sup_of_commute hc]
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨x, x.2, y, y.2, (hf x y).symm⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hf _ _⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem rank_le_rank_ker_add_rank_range {A B : Type*} [Group A] [Finite A] [Group B]
    [Finite B] (f : A →* B) : Group.rank A ≤ Group.rank f.ker + Group.rank f.range := by
  have h := CFSG.PreuniquenessRankFour.Helpers.subgroup_rank_le_rank_add_quotient_rank f.ker
  rwa [Group.rank_congr (QuotientGroup.quotientKerEquivRange f)] at h

theorem two_pow_rank_eq_card_of_sq {X : Type*} [Group X] [Finite X] (hX : ∀ x : X, x * x = 1) :
    2 ^ Group.rank X = Nat.card X := by
  have hinv : ∀ x : X, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hX x)
  have hc : ∀ x y : X, x * y = y * x := fun x y => by
    rw [← hinv (x * y), mul_inv_rev, hinv, hinv]
  have : IsMulCommutative (⊤ : Subgroup X) :=
    isMulCommutative_iff_of_setLike.mpr fun x _ y _ => hc x y
  have h := CFSG.LocalAnalysis.SymplecticFourRankThompson.two_pow_rank_eq_card_of_elementary
    (⊤ : Subgroup X) fun x _ => hX x
  rwa [Group.rank_congr Subgroup.topEquiv, Subgroup.card_top] at h

theorem two_mul_card_le_two_pow_rank_sup [Finite G] {E : Subgroup G} {y : G}
    (hE : ∀ x ∈ E, x * x = 1) (hEc : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x)
    (hc : ∀ x ∈ E, x * y = y * x) (hy : 2 ∣ orderOf y) (hEY : E ⊓ zpowers y = ⊥) :
    2 * Nat.card E ≤ 2 ^ Group.rank (E ⊔ zpowers y : Subgroup G) := by
  set B := E ⊔ zpowers y with hB
  have hcY' : ∀ x ∈ E, ∀ k : ℤ, Commute x (y ^ k) := fun x hx k =>
    Commute.zpow_right (hc x hx) k
  have hcY : ∀ x ∈ E, ∀ z ∈ zpowers y, x * z = z * x := by
    rintro x hx _ ⟨k, rfl⟩
    exact (hcY' x hx k).eq
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, z, hz, rfl⟩ := (mem_sup_of_commute hcY).mp ha
    obtain ⟨x', hx', z', hz', rfl⟩ := (mem_sup_of_commute hcY).mp hb
    obtain ⟨k, rfl⟩ := hz
    obtain ⟨k', rfl⟩ := hz'
    have h1 : Commute x x' := hEc x hx x' hx'
    exact (Commute.mul_left (Commute.mul_right h1 (hcY' x hx k'))
      (Commute.mul_right (hcY' x' hx' k).symm (Commute.zpow_zpow_self y k k'))).eq
  set N : Subgroup B := (zpowers (y ^ 2)).subgroupOf B with hN
  have hNn : N.Normal := ⟨fun a _ b => by
    rwa [show b * a * b⁻¹ = a from Subtype.ext (by
      simp only [coe_mul, coe_inv]
      rw [hBc b b.2 a a.2, mul_inv_cancel_right])]⟩
  have hsq : ∀ b : B ⧸ N, b * b = 1 := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
    obtain ⟨x, hx, z, hz, hxz⟩ := (mem_sup_of_commute hcY).mp b.2
    obtain ⟨k, rfl⟩ := hz
    refine ⟨k, ?_⟩
    simp only [coe_mul, ← hxz]
    rw [Commute.mul_mul_mul_comm (hcY' x hx k).symm, hE x hx, one_mul, ← zpow_add,
      ← zpow_natCast, ← zpow_mul]
    ring_nf
  have hrk : Group.rank (B ⧸ N) ≤ Group.rank B :=
    Group.rank_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hcardQ := two_pow_rank_eq_card_of_sq hsq
  have hBcard : Nat.card B = Nat.card E * orderOf y := by
    rw [hB, card_sup_of_commute hcY hEY, Nat.card_zpowers]
  have hNcard : Nat.card N * 2 = orderOf y := by
    have hle : zpowers (y ^ 2) ≤ B := zpowers_le.mpr (mem_sup_right (pow_mem (mem_zpowers y) 2))
    rw [hN, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
      orderOf_pow_of_dvd two_ne_zero hy, Nat.div_mul_cancel hy]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hQ : Nat.card (B ⧸ N) = 2 * Nat.card E := by
    have h3 : Nat.card (B ⧸ N) * Nat.card N = (2 * Nat.card E) * Nat.card N := by
      rw [← h1, hBcard, ← hNcard]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  calc 2 * Nat.card E = 2 ^ Group.rank (B ⧸ N) := by rw [hcardQ, hQ]
    _ ≤ 2 ^ Group.rank B := Nat.pow_le_pow_right (by norm_num) hrk

end General
section Action

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

@[expose] noncomputable def normAct (φ : L ≃* X) : normalizer (L : Set G) →* MulAut X :=
  (MulAut.congr φ).toMonoidHom.comp L.normalizerMonoidHom

theorem normAct_symm_apply (φ : L ≃* X) (x : normalizer (L : Set G)) (a : X) :
    ((φ.symm (normAct φ x a) : L) : G) = x * φ.symm a * (x : G)⁻¹ := by
  simp [normAct, MulAut.congr_apply]

theorem normAct_eq_one_iff (φ : L ≃* X) (x : normalizer (L : Set G)) :
    normAct φ x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h l hl
    have h1 := congrArg (fun a : X => ((φ.symm a : L) : G))
      (congrArg (fun α : MulAut X => α (φ ⟨l, hl⟩)) h)
    simp only [normAct_symm_apply, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    calc l * x = x * l * (x : G)⁻¹ * x := by rw [h1]
      _ = x * l := by group
  · intro h
    refine MulEquiv.ext fun a => φ.symm.injective (Subtype.ext ?_)
    rw [normAct_symm_apply, MulAut.one_apply, ← h _ (φ.symm a).2, mul_inv_cancel_right]

theorem normAct_of_mem (φ : L ≃* X) {l : L} (hl : (l : G) ∈ normalizer (L : Set G)) :
    normAct φ ⟨l, hl⟩ = MulAut.conj (φ l) := by
  refine MulEquiv.ext fun a => φ.symm.injective (Subtype.ext ?_)
  rw [normAct_symm_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  simp

theorem inv_mul_mem_centralizer (φ : L ≃* X) (x : normalizer (L : Set G)) (l : L)
    (h : normAct φ x = MulAut.conj (φ l)) : (l : G)⁻¹ * x ∈ centralizer (L : Set G) := by
  have hl : (l : G) ∈ normalizer (L : Set G) := le_normalizer l.2
  have hx : (⟨(l : G)⁻¹ * x, mul_mem (inv_mem hl) x.2⟩ : normalizer (L : Set G)) =
      (⟨l, hl⟩ : normalizer (L : Set G))⁻¹ * x := rfl
  have h1 := (normAct_eq_one_iff φ ⟨(l : G)⁻¹ * x, mul_mem (inv_mem hl) x.2⟩).mp
  apply h1
  rw [hx, map_mul, map_inv, normAct_of_mem, h, inv_mul_cancel]

end Action

section Pull

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

@[expose] def pull (φ : L ≃* X) (S : Subgroup X) : Subgroup G :=
  (S.comap φ.toMonoidHom).map L.subtype

theorem mem_pull {φ : L ≃* X} {S : Subgroup X} {x : G} :
    x ∈ pull φ S ↔ ∃ h : x ∈ L, φ ⟨x, h⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hS⟩
    exact ⟨⟨x, h⟩, hS, rfl⟩

theorem symm_mem_pull {φ : L ≃* X} {S : Subgroup X} {a : X} :
    ((φ.symm a : L) : G) ∈ pull φ S ↔ a ∈ S := by
  rw [mem_pull]
  constructor
  · rintro ⟨hx, h⟩
    rwa [Subtype.coe_eta, MulEquiv.apply_symm_apply] at h
  · intro h
    exact ⟨(φ.symm a).2, by rwa [Subtype.coe_eta, MulEquiv.apply_symm_apply]⟩

theorem pull_le (φ : L ≃* X) (S : Subgroup X) : pull φ S ≤ L := map_subtype_le _

theorem pull_mono (φ : L ≃* X) {S S' : Subgroup X} (h : S ≤ S') : pull φ S ≤ pull φ S' :=
  map_mono (comap_mono h)

theorem pull_sup (φ : L ≃* X) (S S' : Subgroup X) : pull φ (S ⊔ S') = pull φ S ⊔ pull φ S' := by
  rw [pull, pull, pull, ← Subgroup.map_sup, comap_equiv_eq_map_symm', comap_equiv_eq_map_symm',
    comap_equiv_eq_map_symm', Subgroup.map_sup]

theorem pull_inf (φ : L ≃* X) (S S' : Subgroup X) : pull φ (S ⊓ S') = pull φ S ⊓ pull φ S' := by
  rw [pull, pull, pull, comap_inf, Subgroup.map_inf _ _ _ L.subtype_injective]

theorem card_pull (φ : L ≃* X) (S : Subgroup X) : Nat.card (pull φ S) = Nat.card S := by
  rw [pull, card_map_of_injective L.subtype_injective, comap_equiv_eq_map_symm',
    card_map_of_injective φ.symm.injective]

theorem pull_bot (φ : L ≃* X) : pull φ (⊥ : Subgroup X) = ⊥ := by
  rw [pull, comap_equiv_eq_map_symm', Subgroup.map_bot, Subgroup.map_bot]

theorem mem_center_map_iff {H : Subgroup G} {x : G} :
    x ∈ (center H).map H.subtype ↔ x ∈ H ∧ ∀ y ∈ H, y * x = x * y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun y => Subtype.ext (h y y.2), rfl⟩

end Pull

section Model

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K] [CharP K 2]

theorem eq_one_of_forall_commute {x : antiSp K} (hx : ∀ y, x * y = y * x) : x = 1 := by
  apply conj_injective (K := K)
  rw [map_one]
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.conj_apply, MulAut.one_apply, hx y, mul_inv_cancel_right]

theorem center_pull_antiUnipotent {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* antiSp K) :
    (center (pull φ (antiUnipotent K))).map (pull φ (antiUnipotent K)).subtype =
      pull φ (antiUnipotentCenter K) := by
  ext x
  rw [mem_center_map_iff, mem_pull, mem_pull]
  constructor
  · rintro ⟨⟨hxL, hxU⟩, h⟩
    refine ⟨hxL, (mem_antiUnipotentCenter_iff_central _).mpr ⟨hxU, fun u hu => ?_⟩⟩
    have hmem : ((φ.symm u : L) : G) ∈ pull φ (antiUnipotent K) := symm_mem_pull.mpr hu
    have h1 := h _ hmem
    have h2 := congrArg φ (Subtype.ext h1 : (φ.symm u : L) * ⟨x, hxL⟩ = ⟨x, hxL⟩ * φ.symm u)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, eq_comm] at h2
  · rintro ⟨hxL, hxZ⟩
    obtain ⟨hxU, hc⟩ := (mem_antiUnipotentCenter_iff_central _).mp hxZ
    refine ⟨⟨hxL, hxU⟩, fun y hy => ?_⟩
    obtain ⟨hyL, hyU⟩ := mem_pull.mp hy
    have h1 := hc _ hyU
    rw [← map_mul, ← map_mul] at h1
    exact (congrArg Subtype.val (φ.injective h1)).symm

end Model

section SubAct

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

@[expose] noncomputable def subAct (φ : L ≃* X) {H : Subgroup G}
    (h : H ≤ normalizer (L : Set G)) : H →* MulAut X :=
  (normAct φ).comp (inclusion h)

theorem subAct_symm_apply (φ : L ≃* X) {H : Subgroup G} (h : H ≤ normalizer (L : Set G))
    (x : H) (a : X) : ((φ.symm (subAct φ h x a) : L) : G) = x * φ.symm a * (x : G)⁻¹ :=
  normAct_symm_apply φ _ a

theorem subAct_eq_one_iff (φ : L ≃* X) {H : Subgroup G} (h : H ≤ normalizer (L : Set G))
    (x : H) : subAct φ h x = 1 ↔ (x : G) ∈ centralizer (L : Set G) :=
  normAct_eq_one_iff φ _

theorem subAct_of_eq (φ : L ≃* X) {H : Subgroup G} (h : H ≤ normalizer (L : Set G))
    {x : H} {l : L} (hxl : (x : G) = l) : subAct φ h x = MulAut.conj (φ l) := by
  have : inclusion h x = ⟨l, le_normalizer l.2⟩ := Subtype.ext hxl
  rw [subAct, MonoidHom.comp_apply, this, normAct_of_mem]

theorem subAct_inv_mul (φ : L ≃* X) {H : Subgroup G} (h : H ≤ normalizer (L : Set G))
    {x : H} {l : L} (hxl : subAct φ h x = MulAut.conj (φ l)) :
    (l : G)⁻¹ * x ∈ centralizer (L : Set G) :=
  inv_mul_mem_centralizer φ (inclusion h x) l hxl

end SubAct

theorem eq_of_orderOf_eq_two_of_isCyclic {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y]
    {x y : Y} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have := Fintype.ofFinite Y
  have hd : 2 ∣ Fintype.card Y := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset Y) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset Y) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

theorem eq_one_of_mem_centralizer {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [CharP K 2] (φ : L ≃* antiSp K) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ centralizer (L : Set G)) : x = 1 := by
  have h : φ ⟨x, hxL⟩ = 1 := by
    refine eq_one_of_forall_commute fun a => ?_
    rw [← MulEquiv.apply_symm_apply φ a, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hxC _ (φ.symm a).2).symm
  have := congrArg Subtype.val (φ.map_eq_one_iff.mp h)
  exact this

theorem conj_mem_centralizer_of_mem_normalizer {G : Type*} [Group G] {L : Subgroup G} {h x : G}
    (hh : h ∈ normalizer (L : Set G)) (hx : x ∈ centralizer (L : Set G)) :
    h * x * h⁻¹ ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro l hl
  have hl' : h⁻¹ * l * h ∈ L := by
    have := (mem_normalizer_iff.mp (inv_mem hh) l).mp hl
    simpa using this
  have hc := hx _ hl'
  calc l * (h * x * h⁻¹) = h * ((h⁻¹ * l * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * l * h)) * h⁻¹ := by rw [hc]
    _ = h * x * h⁻¹ * l := by group

structure Setup {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] (n : ℕ)
    (φ : L ≃* antiSp K) (TG : Subgroup G) (t : G) : Prop where
  two_le : 2 ≤ n
  card_K : Nat.card K = 2 ^ n
  T_le : TG ≤ centralizer (L : Set G)
  t_mem : t ∈ TG
  order_t : orderOf t = 2
  T_cyclic : IsCyclic TG
  T_two : IsPGroup 2 TG
  cent_inf : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = TG
  L_le : L ≤ centralizer ({t} : Set G)
  cent_le : centralizer ({t} : Set G) ≤ normalizer (L : Set G)

namespace Setup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {φ : L ≃* antiSp K}
  {TG : Subgroup G} {t : G}

theorem comm_L_T (hS : Setup L K n φ TG t) {x y : G} (hx : x ∈ L) (hy : y ∈ TG) :
    x * y = y * x :=
  mem_centralizer_iff.mp (hS.T_le hy) x hx

theorem comm_T [Finite G] (hS : Setup L K n φ TG t) {x y : G} (hx : x ∈ TG) (hy : y ∈ TG) :
    x * y = y * x := by
  have := hS.T_cyclic
  let _ : CommGroup TG := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : TG) ⟨y, hy⟩)

theorem L_inf_T [CharP K 2] (hS : Setup L K n φ TG t) : L ⊓ TG = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxT⟩
  exact (mem_bot).mpr (eq_one_of_mem_centralizer φ hxL (hS.T_le hxT))

theorem t_ne_one (hS : Setup L K n φ TG t) : t ≠ 1 := fun h => by
  have := hS.order_t
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem t_not_mem_L [CharP K 2] (hS : Setup L K n φ TG t) : t ∉ L := fun h =>
  hS.t_ne_one (eq_one_of_mem_centralizer φ h (hS.T_le hS.t_mem))

theorem t_mul_t (hS : Setup L K n φ TG t) : t * t = 1 := by
  rw [← sq, ← hS.order_t, pow_orderOf_eq_one]

theorem T_le_C (hS : Setup L K n φ TG t) : TG ≤ centralizer ({t} : Set G) :=
  hS.cent_inf ▸ inf_le_right

theorem mem_T (hS : Setup L K n φ TG t) {x : G} (h0 : x ∈ centralizer (L : Set G))
    (h1 : x ∈ centralizer ({t} : Set G)) : x ∈ TG :=
  hS.cent_inf ▸ ⟨h0, h1⟩

theorem conj_mem_T (hS : Setup L K n φ TG t) {c x : G} (hc : c ∈ centralizer ({t} : Set G))
    (hx : x ∈ TG) : c * x * c⁻¹ ∈ TG :=
  hS.mem_T (conj_mem_centralizer_of_mem_normalizer (hS.cent_le hc)
    (hS.T_le hx)) (mul_mem (mul_mem hc (hS.T_le_C hx)) (inv_mem hc))

theorem eq_t_of_mem_T [Finite G] (hS : Setup L K n φ TG t) {x : G} (hx : x ∈ TG)
    (h2 : orderOf x = 2) :
    x = t := by
  have := hS.T_cyclic
  exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic (x := (⟨x, hx⟩ : TG))
    (y := ⟨t, hS.t_mem⟩) (by rwa [orderOf_mk]) (by rw [orderOf_mk]; exact hS.order_t))

theorem comm_P_T [CharP K 2] (hS : Setup L K n φ TG t) {x y : G} (hx : x ∈ pull φ (antiUnipotent K))
    (hy : y ∈ TG) : x * y = y * x :=
  hS.comm_L_T (pull_le φ _ hx) hy

theorem mem_Q [CharP K 2] (hS : Setup L K n φ TG t) {x : G} :
    x ∈ pull φ (antiUnipotent K) ⊔ TG ↔
      ∃ p ∈ pull φ (antiUnipotent K), ∃ c ∈ TG, p * c = x :=
  mem_sup_of_commute fun _ hp _ hc => hS.comm_P_T hp hc

theorem Q_le_C [CharP K 2] (hS : Setup L K n φ TG t) :
    pull φ (antiUnipotent K) ⊔ TG ≤ centralizer ({t} : Set G) :=
  sup_le ((pull_le φ _).trans hS.L_le) hS.T_le_C

theorem PG_two [Finite K] [CharP K 2] (hS : Setup L K n φ TG t) :
    IsPGroup 2 (pull φ (antiUnipotent K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := n * 4) ?_
  rw [card_pull, (card_and_isSylowTwoOf_antiUnipotent (K := K)).1, hS.card_K, ← pow_mul]

theorem Q_two [Finite K] [CharP K 2] (hS : Setup L K n φ TG t) :
    IsPGroup 2 (pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :=
  hS.PG_two.to_sup_of_normal_right' hS.T_two
    (le_normalizer_of_commute fun _ hp _ hc => hS.comm_P_T hp hc)

theorem image_two (hS : Setup L K n φ TG t) {R : Subgroup G}
    (hRC : R ≤ centralizer ({t} : Set G)) (hR : IsPGroup 2 R) :
    IsPGroup 2 ((R.subgroupOf (centralizer ({t} : Set G))).map (subAct φ hS.cent_le)) :=
  (hR.of_equiv (subgroupOfEquivOfLe hRC).symm).map _

theorem inner_le_image [CharP K 2] (hS : Setup L K n φ TG t) {R : Subgroup G}
    (hRC : R ≤ centralizer ({t} : Set G)) (hQR : pull φ (antiUnipotent K) ⊔ TG ≤ R) :
    (antiUnipotent K).map MulAut.conj ≤
      (R.subgroupOf (centralizer ({t} : Set G))).map (subAct φ hS.cent_le) := by
  rintro _ ⟨u, hu, rfl⟩
  have hl : ((φ.symm u : L) : G) ∈ pull φ (antiUnipotent K) := symm_mem_pull.mpr hu
  refine ⟨⟨_, hRC (hQR (mem_sup_left hl))⟩, mem_subgroupOf.mpr (hQR (mem_sup_left hl)), ?_⟩
  rw [subAct_of_eq φ hS.cent_le (l := φ.symm u) rfl, MulEquiv.apply_symm_apply]

theorem mem_Q_of_act [CharP K 2] (hS : Setup L K n φ TG t) (x : centralizer ({t} : Set G))
    {u : antiSp K} (hu : u ∈ antiUnipotent K)
    (hx : subAct φ hS.cent_le x = MulAut.conj u) : (x : G) ∈ pull φ (antiUnipotent K) ⊔ TG := by
  have hx' : subAct φ hS.cent_le x = MulAut.conj (φ (φ.symm u)) := by
    rw [MulEquiv.apply_symm_apply]; exact hx
  have h0 := subAct_inv_mul φ hS.cent_le hx'
  have h1 : ((φ.symm u : L) : G)⁻¹ * x ∈ TG :=
    hS.mem_T h0 (mul_mem (inv_mem (hS.L_le (φ.symm u).2)) x.2)
  have h2 : (x : G) = ((φ.symm u : L) : G) * (((φ.symm u : L) : G)⁻¹ * x) := by group
  rw [h2]
  exact mul_mem (mem_sup_left (symm_mem_pull.mpr hu)) (mem_sup_right h1)

theorem rank_bound [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) {R : Subgroup G} (hRC : R ≤ centralizer ({t} : Set G))
    (hR : IsPGroup 2 R) (hQR : pull φ (antiUnipotent K) ⊔ TG ≤ R) {A : Subgroup G}
    (hAR : A ≤ R) [IsMulCommutative A] :
    Group.rank A ≤ 3 * n + 1 ∧
      (Group.rank A = 3 * n + 1 → A ≤ pull φ (antiUnipotent K) ⊔ TG) := by
  set f : A →* MulAut (antiSp K) := (subAct φ hS.cent_le).comp (inclusion (hAR.trans hRC))
    with hf
  have hrk := rank_le_rank_ker_add_rank_range f
  have hker : (f.ker).map A.subtype ≤ TG := by
    rintro _ ⟨a, ha, rfl⟩
    have h0 := (subAct_eq_one_iff φ hS.cent_le _).mp ha
    exact hS.mem_T h0 (hRC (hAR a.2))
  have := hS.T_cyclic
  have : IsCyclic ((f.ker).map A.subtype) := Subgroup.isCyclic_of_le hker
  have : IsCyclic f.ker := (f.ker.equivMapOfInjective A.subtype A.subtype_injective).isCyclic.mpr
    inferInstance
  have hk1 := CFSG.PreuniquenessRankFour.Helpers.cyclic_group_rank_at_most_one (source := f.ker)
  have hrange : f.range ≤ (R.subgroupOf (centralizer ({t} : Set G))).map (subAct φ hS.cent_le) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨inclusion (hAR.trans hRC) a, mem_subgroupOf.mpr (hAR a.2), rfl⟩
  have hcomm : IsMulCommutative f.range := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (setLike_mul_comm a.2 b.2)]
  obtain ⟨-, -, -, hall, -⟩ :=
    CFSG.LocalAnalysis.even_symplectic_four_rank_Thompson_subgroup.{0, 0} hS.two_le hS.card_K
  obtain ⟨hbd, -⟩ := hall _ (hS.image_two hRC hR) (hS.inner_le_image hRC hQR)
  obtain ⟨hr1, hr2⟩ := hbd f.range hrange hcomm
  refine ⟨by omega, fun hA => ?_⟩
  have h3 : Group.rank f.range = 3 * n := by omega
  have hU : f.range ≤ (antiUnipotent K).map MulAut.conj := by
    rcases hr2.mp h3 with h | h
    · rw [h]; exact map_mono radA1_le_antiUnipotent
    · rw [h]; exact map_mono radA2_le_antiUnipotent
  intro a ha
  obtain ⟨u, hu, hfu⟩ := hU ⟨⟨a, ha⟩, rfl⟩
  exact hS.mem_Q_of_act (inclusion (hAR.trans hRC) ⟨a, ha⟩) hu hfu.symm

theorem rank_radical_mul [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) {A : Subgroup (antiSp K)} (hAU : A ≤ antiUnipotent K)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x * x = 1)
    (hAcard : Nat.card A = 2 ^ (3 * n)) :
    IsMulCommutative (pull φ A ⊔ TG : Subgroup G) ∧
      pull φ A ⊔ TG ≤ pull φ (antiUnipotent K) ⊔ TG ∧
      Group.rank (pull φ A ⊔ TG : Subgroup G) = 3 * n + 1 := by
  have hc : ∀ x ∈ pull φ A, ∀ y ∈ TG, x * y = y * x := fun x hx y hy =>
    hS.comm_L_T (pull_le φ A hx) hy
  have hAc' : ∀ x ∈ pull φ A, ∀ y ∈ pull φ A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxL, hxA⟩ := mem_pull.mp hx
    obtain ⟨hyL, hyA⟩ := mem_pull.mp hy
    have h := hAc _ hxA _ hyA
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (φ.injective h)
  have hA2' : ∀ x ∈ pull φ A, x * x = 1 := by
    intro x hx
    obtain ⟨hxL, hxA⟩ := mem_pull.mp hx
    have h := hA2 _ hxA
    rw [← map_mul, φ.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  have hcomm : IsMulCommutative (pull φ A ⊔ TG : Subgroup G) := by
    refine isMulCommutative_iff_of_setLike.mpr fun a ha b hb => ?_
    obtain ⟨x, hx, z, hz, rfl⟩ := (mem_sup_of_commute hc).mp ha
    obtain ⟨x', hx', z', hz', rfl⟩ := (mem_sup_of_commute hc).mp hb
    exact (Commute.mul_left (Commute.mul_right (hAc' x hx x' hx') (hc x hx z' hz'))
      (Commute.mul_right (hc x' hx' z hz).symm (hS.comm_T hz hz'))).eq
  have hle : pull φ A ⊔ TG ≤ pull φ (antiUnipotent K) ⊔ TG := sup_le_sup_right (pull_mono φ hAU) _
  refine ⟨hcomm, hle, le_antisymm ?_ ?_⟩
  · exact (hS.rank_bound hS.Q_le_C hS.Q_two le_rfl hle).1
  · have := hS.T_cyclic
    obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := TG)
    have hTy : TG = zpowers (y : G) := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := hy ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      · rintro ⟨k, rfl⟩
        exact zpow_mem y.2 k
    have hy2 : 2 ∣ orderOf (y : G) := by
      rw [← Nat.card_zpowers, ← hTy, ← hS.order_t]
      exact Subgroup.orderOf_dvd_natCard _ hS.t_mem
    have hinf : pull φ A ⊓ zpowers (y : G) = ⊥ := by
      rw [← hTy, eq_bot_iff, ← hS.L_inf_T]
      exact inf_le_inf_right _ (pull_le φ A)
    have h := two_mul_card_le_two_pow_rank_sup hA2' hAc'
      (fun x hx => hc x hx _ y.2) hy2 hinf
    rw [← hTy, card_pull, hAcard, ← pow_succ'] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem rankThompson_eq [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) {R : Subgroup G} (hRC : R ≤ centralizer ({t} : Set G))
    (hR : IsPGroup 2 R) (hQR : pull φ (antiUnipotent K) ⊔ TG ≤ R) :
    (CFSG.LocalAnalysis.rankThompson R).map R.subtype = pull φ (antiUnipotent K) ⊔ TG := by
  obtain ⟨-, ⟨-, -, hA1card⟩, ⟨-, -, hA2card⟩, -⟩ :=
    even_symplectic_four_Sylow_involution_radicals hS.card_K
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hS.card_K, ← pow_mul, mul_comm]
  obtain ⟨hB1c, hB1Q, hB1r⟩ := hS.rank_radical_mul radA1_le_antiUnipotent
    (fun x hx y hy => radA1_comm hx hy) (fun x hx => mul_self_of_mem_radA1 hx) (hA1card.trans hq3)
  obtain ⟨hB2c, hB2Q, hB2r⟩ := hS.rank_radical_mul radA2_le_antiUnipotent
    (fun x hx y hy => radA2_comm hx hy) (fun x hx => mul_self_of_mem_radA2 hx) (hA2card.trans hq3)
  have hsubOf : ∀ A : Subgroup G, A ≤ R → Group.rank (A.subgroupOf R) = Group.rank A :=
    fun A hAR => Group.rank_congr (subgroupOfEquivOfLe hAR)
  have hrankSub : ∀ B : Subgroup R, Group.rank (B.map R.subtype) = Group.rank B := fun B =>
    (Group.rank_congr (B.equivMapOfInjective R.subtype R.subtype_injective)).symm
  have hcommOf : ∀ A : Subgroup G, IsMulCommutative A → IsMulCommutative (A.subgroupOf R) := by
    intro A hA
    exact isMulCommutative_iff_of_setLike.mpr fun x hx y hy =>
      Subtype.ext (setLike_mul_comm (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy))
  have hmax : CFSG.LocalAnalysis.maxAbelianRank R = 3 * n + 1 := by
    unfold CFSG.LocalAnalysis.maxAbelianRank
    refine IsGreatest.csSup_eq ⟨⟨(pull φ (radA1 K) ⊔ TG).subgroupOf R, hcommOf _ hB1c, by
      rw [hsubOf _ (hB1Q.trans hQR), hB1r]⟩, ?_⟩
    rintro r ⟨B, hB, rfl⟩
    rw [← hrankSub B]
    exact (hS.rank_bound hRC hR hQR (map_subtype_le B)).1
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun B hB => ?_
    obtain ⟨hBc, hBr⟩ := hB
    rw [← map_le_iff_le_comap]
    exact (hS.rank_bound hRC hR hQR (map_subtype_le B)).2 (by rw [hrankSub, hBr, hmax])
  · have hmem : ∀ A : Subgroup G, A ≤ R → IsMulCommutative A → Group.rank A = 3 * n + 1 →
        A ≤ (CFSG.LocalAnalysis.rankThompson R).map R.subtype := by
      intro A hAR hA hAr
      have hfam : A.subgroupOf R ∈ CFSG.LocalAnalysis.maxRankAbelianFamily R :=
        ⟨hcommOf A hA, by rw [hsubOf A hAR, hAr, hmax]⟩
      calc A = (A.subgroupOf R).map R.subtype := by
            rw [subgroupOf_map_subtype, inf_of_le_left hAR]
        _ ≤ _ := map_mono (le_sSup hfam)
    calc pull φ (antiUnipotent K) ⊔ TG = (pull φ (radA1 K) ⊔ TG) ⊔ (pull φ (radA2 K) ⊔ TG) := by
          rw [← sup_sup_distrib_right, ← pull_sup, ← antiUnipotent_eq_radA1_sup_radA2]
      _ ≤ _ := sup_le (hmem _ (hB1Q.trans hQR) hB1c hB1r) (hmem _ (hB2Q.trans hQR) hB2c hB2r)

theorem exists_conj_mem_C [Finite G] [Finite K] [CharP K 2] (hS : Setup L K n φ TG t)
    (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) :
    ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧ g⁻¹ * t * g ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  by_contra hcon
  push Not at hcon
  have hQ2 : IsPGroup 2 ((pull φ (antiUnipotent K) ⊔ TG).subgroupOf C) :=
    hS.Q_two.of_equiv (subgroupOfEquivOfLe hS.Q_le_C).symm
  obtain ⟨R, hQR⟩ := hQ2.exists_le_sylow
  set RG := (R : Subgroup C).map C.subtype with hRG
  have hRGC : RG ≤ C := map_subtype_le _
  have htRG : t ∈ RG :=
    ⟨⟨t, hS.T_le_C hS.t_mem⟩, hQR (mem_subgroupOf.mpr (mem_sup_right hS.t_mem)), rfl⟩
  obtain ⟨S, hRS⟩ := (R.isPGroup'.map C.subtype).exists_le_sylow
  have hSC : (S : Subgroup G).subgroupOf C = R := R.is_maximal' S.isPGroup'.comap_subtype
    (fun x hx => mem_subgroupOf.mpr (hRS ⟨x, hx, rfl⟩))
  have hRS' : RG = S := by
    by_contra hne
    have hlt : RG.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm hRS fun x hx => ?_
      have : (⟨x, hx⟩ : (S : Subgroup G)) ∈ RG.subgroupOf S := htop ▸ mem_top _
      exact this
    have := S.isPGroup'.isNilpotent
    obtain ⟨m, hm, hmR⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    have h1 : (m : G)⁻¹ * t * m ∈ RG := by
      have := (mem_normalizer_iff.mp (inv_mem hm) ⟨t, hRS htRG⟩).mp (mem_subgroupOf.mpr htRG)
      rw [mem_subgroupOf] at this
      simpa using this
    have h2 := hcon m (hRGC h1)
    have hmC : (m : G) ∈ C := by
      rw [hC, mem_centralizer_singleton_iff]
      calc (m : G) * t = m * ((m : G)⁻¹ * t * m) := by rw [h2]
        _ = t * m := by group
    apply hmR
    rw [mem_subgroupOf]
    exact ⟨⟨m, hmC⟩, hSC ▸ mem_subgroupOf.mpr m.2, rfl⟩
  have htS : t ∈ (S : Subgroup G) := hRS htRG
  have hcen : (⟨t, htS⟩ : (S : Subgroup G)) ∈ center (S : Subgroup G) := by
    refine mem_center_iff.mpr fun s => Subtype.ext ?_
    have hs : (s : G) ∈ C := hRGC (by rw [hRS']; exact s.2)
    exact (mem_centralizer_singleton_iff.mp hs)
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar S ⟨t, htS⟩ hcen
    (by rw [orderOf_mk]; exact hS.order_t)
    (fun g hg => hcon g (hRGC (by rw [hRS']; exact hg)))
  apply hLn
  refine normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => ?_)
  obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
  rw [hO, mem_bot] at hk
  rw [hk, mul_one]
  exact hS.cent_le hc

theorem commutator_mem_L [Finite G] (hS : Setup L K n φ TG t) {x y : G} (hx : x ∈ L ⊔ TG)
    (hy : y ∈ L ⊔ TG) : ⁅x, y⁆ ∈ L := by
  have hc : ∀ a ∈ L, ∀ b ∈ TG, a * b = b * a := fun a ha b hb => hS.comm_L_T ha hb
  obtain ⟨l, hl, a, ha, rfl⟩ := (mem_sup_of_commute hc).mp hx
  obtain ⟨l', hl', a', ha', rfl⟩ := (mem_sup_of_commute hc).mp hy
  have hal' : Commute a l' := (hc l' hl' a ha).symm
  have haa' : Commute a a' := hS.comm_T ha ha'
  have ha'l : a' * l⁻¹ = l⁻¹ * a' := (hc _ (inv_mem hl) a' ha').symm
  have e1 : a * (l' * a') * a⁻¹ = l' * a' := by
    rw [(Commute.mul_right hal' haa').eq, mul_inv_cancel_right]
  have e2 : ⁅l * a, l' * a'⁆ = ⁅l, l'⁆ := by
    calc ⁅l * a, l' * a'⁆ = l * (a * (l' * a') * a⁻¹) * l⁻¹ * (l' * a')⁻¹ := by
          rw [commutatorElement_def]; group
      _ = l * l' * (a' * l⁻¹) * a'⁻¹ * l'⁻¹ := by rw [e1]; group
      _ = ⁅l, l'⁆ := by rw [ha'l, commutatorElement_def]; group
  rw [e2, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hl hl') (inv_mem hl)) (inv_mem hl')

theorem derivedSeries_two_le [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) {x : centralizer ({t} : Set G)}
    (hx : x ∈ derivedSeries (centralizer ({t} : Set G)) 2) : (x : G) ∈ L := by
  set C := centralizer ({t} : Set G) with hC
  obtain ⟨-, hcyc, -, -⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hS.two_le hS.card_K
  set ρ := subAct φ hS.cent_le with hρ
  have h1 : derivedSeries C 1 ≤ (L ⊔ TG).subgroupOf C := by
    rw [derivedSeries_succ, derivedSeries_zero, commutator_le]
    intro a _ b _
    rw [mem_subgroupOf]
    have hinn : ρ ⁅a, b⁆ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' _) (ρ ⁅a, b⁆) = 1
      rw [map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      let _ : CommGroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer (antiSp K)) :=
        IsCyclic.commGroup
      exact mul_comm _ _
    obtain ⟨c, hc⟩ := hinn
    have hc' : ρ ⁅a, b⁆ = MulAut.conj (φ (φ.symm c)) := by
      rw [MulEquiv.apply_symm_apply]; exact hc.symm
    have h0 := subAct_inv_mul φ hS.cent_le hc'
    have hT : ((φ.symm c : L) : G)⁻¹ * ((⁅a, b⁆ : C) : G) ∈ TG :=
      hS.mem_T h0 (mul_mem (inv_mem (hS.L_le (φ.symm c).2)) (⁅a, b⁆ : C).2)
    have e : ((⁅a, b⁆ : C) : G) =
        ((φ.symm c : L) : G) * (((φ.symm c : L) : G)⁻¹ * ((⁅a, b⁆ : C) : G)) := by group
    rw [e]
    exact mul_mem (mem_sup_left (φ.symm c).2) (mem_sup_right hT)
  have h2 : derivedSeries C 2 ≤ L.subgroupOf C := by
    rw [derivedSeries_succ, commutator_le]
    intro a ha b hb
    rw [mem_subgroupOf]
    exact hS.commutator_mem_L (mem_subgroupOf.mp (h1 ha)) (mem_subgroupOf.mp (h1 hb))
  exact mem_subgroupOf.mp (h2 hx)

theorem exists_conj_mem_tL [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) :
    ∃ v : G, (∃ g : G, v = g⁻¹ * t * g) ∧ v ≠ t ∧ (v ∈ L ∨ t * v ∈ L) := by
  obtain ⟨g, hgC, hgt⟩ := hS.exists_conj_mem_C hO hLn
  set u := g⁻¹ * t * g with hu
  set C := centralizer ({t} : Set G) with hC
  set ρ := subAct φ hS.cent_le with hρ
  set x : C := ⟨u, hgC⟩ with hx
  have huu : u * u = 1 := by
    calc u * u = g⁻¹ * (t * t) * g := by rw [hu]; group
      _ = 1 := by rw [hS.t_mul_t]; group
  have hθθ : ρ x * ρ x = 1 := by rw [← map_mul, show x * x = 1 from Subtype.ext huu, map_one]
  obtain ⟨-, -, -, hout⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hS.two_le hS.card_K
  by_cases hinn : ρ x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K)
  ·
    obtain ⟨a, ha⟩ := hinn
    have ha' : ρ x = MulAut.conj (φ (φ.symm a)) := by
      rw [MulEquiv.apply_symm_apply]; exact ha.symm
    set l : G := ((φ.symm a : L) : G) with hl
    have hlL : l ∈ L := (φ.symm a).2
    have h0 := subAct_inv_mul φ hS.cent_le ha'
    have hcT : l⁻¹ * u ∈ TG := hS.mem_T h0 (mul_mem (inv_mem (hS.L_le hlL)) hgC)
    set c := l⁻¹ * u with hc
    have hulc : u = l * c := by rw [hc]; group
    have hlc : l * c = c * l := hS.comm_L_T hlL hcT
    have hsq : l * l * (c * c) = 1 := by
      rw [← huu, hulc]
      calc l * l * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [hlc]
        _ = l * c * (l * c) := by group
    have hll : l * l = 1 := by
      have hmem : l * l ∈ L ⊓ TG := ⟨mul_mem hlL hlL, by
        rw [eq_inv_of_mul_eq_one_left hsq]; exact TG.inv_mem (TG.mul_mem hcT hcT)⟩
      rw [hS.L_inf_T, mem_bot] at hmem
      exact hmem
    have hcc : c * c = 1 := by rw [hll, one_mul] at hsq; exact hsq
    refine ⟨u, ⟨g, rfl⟩, hgt, ?_⟩
    by_cases hc1 : c = 1
    · left
      rw [hulc, hc1, mul_one]
      exact hlL
    · right
      have hct : c = t := hS.eq_t_of_mem_T hcT (orderOf_eq_prime (by rw [sq]; exact hcc) hc1)
      have e : t * u = l := by
        rw [hulc, hct, hS.comm_L_T hlL hS.t_mem, ← mul_assoc, hS.t_mul_t, one_mul]
      rw [e]
      exact hlL
  ·
    obtain ⟨hconj, -, hres⟩ := hout (ρ x) hθθ hinn
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hres)
    set kX : antiSp K := ((k₀ : fixedSubgroup (ρ x)) : antiSp K) with hkX
    have hkX2 : orderOf kX = 2 := by rw [hkX, orderOf_coe, orderOf_coe, hk₀]
    have hkfix : ρ x kX = kX := (k₀ : fixedSubgroup (ρ x)).2
    have hkDS : (k₀ : fixedSubgroup (ρ x)) ∈ derivedSeries (fixedSubgroup (ρ x)) 2 :=
      (mem_iInf.mp k₀.2) 2
    set k : G := ((φ.symm kX : L) : G) with hk
    have hkL : k ∈ L := (φ.symm kX).2
    have hfixc : ∀ y : antiSp K, ρ x y = y →
        u * ((φ.symm y : L) : G) * u⁻¹ = ((φ.symm y : L) : G) := by
      intro y hy
      have h := subAct_symm_apply φ hS.cent_le x y
      rw [hy] at h
      exact h.symm
    have hku : u * k * u⁻¹ = k := hfixc kX hkfix
    have hψmem : ∀ y : fixedSubgroup (ρ x),
        ((MulAut.conj g).toMonoidHom.comp (L.subtype.comp
          (φ.symm.toMonoidHom.comp (fixedSubgroup (ρ x)).subtype))) y ∈ C := by
      intro y
      have h1 := hfixc y y.2
      change g * ((φ.symm y : L) : G) * g⁻¹ ∈ C
      rw [hC, mem_centralizer_singleton_iff]
      calc g * ((φ.symm y : L) : G) * g⁻¹ * t
          = g * (u * ((φ.symm y : L) : G) * u⁻¹) * u * g⁻¹ := by rw [h1, hu]; group
        _ = t * (g * ((φ.symm y : L) : G) * g⁻¹) := by rw [hu]; group
    set ψ := ((MulAut.conj g).toMonoidHom.comp (L.subtype.comp
      (φ.symm.toMonoidHom.comp (fixedSubgroup (ρ x)).subtype))).codRestrict C hψmem with hψ
    have hψk : ψ (k₀ : fixedSubgroup (ρ x)) ∈ derivedSeries C 2 :=
      map_derivedSeries_le_derivedSeries ψ 2 ⟨_, hkDS, rfl⟩
    have hgk : g * k * g⁻¹ ∈ L := hS.derivedSeries_two_le hψk
    set y : C := ⟨k, hS.L_le hkL⟩ with hy
    have hkk : k * k = 1 := by
      have h := pow_orderOf_eq_one kX
      rw [hkX2, sq, ← φ.symm.map_eq_one_iff, map_mul] at h
      exact congrArg Subtype.val h
    have huk : u * k = k * u := by
      calc u * k = u * k * u⁻¹ * u := by group
        _ = k * u := by rw [hku]
    have hθk : ρ (x * y) * ρ (x * y) = 1 := by
      rw [← map_mul]
      have : (x * y) * (x * y) = 1 := Subtype.ext (by
        change u * k * (u * k) = 1
        calc u * k * (u * k) = u * (k * u) * k := by group
          _ = u * u * (k * k) := by rw [← huk]; group
          _ = 1 := by rw [huu, hkk, one_mul])
      rw [this, map_one]
    have hθk' : ρ (x * y) * (ρ x)⁻¹ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
      rw [← map_inv, ← map_mul]
      have hxy : ((x * y * x⁻¹ : C) : G) = ((⟨k, hkL⟩ : L) : G) := by
        change u * k * u⁻¹ = k
        exact hku
      rw [subAct_of_eq φ hS.cent_le hxy]
      exact ⟨_, rfl⟩
    obtain ⟨cX, hcX⟩ := hconj (ρ (x * y)) hθk hθk'
    set l : G := ((φ.symm cX : L) : G) with hl
    have hlL : l ∈ L := (φ.symm cX).2
    set lC : C := ⟨l, hS.L_le hlL⟩ with hlC
    have hρl : ρ lC = MulAut.conj cX := by
      rw [subAct_of_eq φ hS.cent_le (l := φ.symm cX) rfl, MulEquiv.apply_symm_apply]
    have hone : ρ ((lC * x * lC⁻¹)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hρl, hcX]
      group
    have h0 := (subAct_eq_one_iff φ hS.cent_le _).mp hone
    have hmemL : ((lC * x * lC⁻¹)⁻¹ * (x * y) : C) ∈ L.subgroupOf C := by
      rw [mem_subgroupOf]
      change (l * u * l⁻¹)⁻¹ * (u * k) ∈ L
      have hu' : u⁻¹ * l⁻¹ * u ∈ L := by
        have := (mem_normalizer_iff.mp (inv_mem (hS.cent_le hgC)) l⁻¹).mp (inv_mem hlL)
        simpa using this
      have e : (l * u * l⁻¹)⁻¹ * (u * k) = l * (u⁻¹ * l⁻¹ * u) * k := by group
      rw [e]
      exact mul_mem (mul_mem hlL hu') hkL
    have h1 := eq_one_of_mem_centralizer φ (mem_subgroupOf.mp hmemL) h0
    have hukl : u * k = l * u * l⁻¹ := by
      change (l * u * l⁻¹)⁻¹ * (u * k) = 1 at h1
      calc u * k = (l * u * l⁻¹) * ((l * u * l⁻¹)⁻¹ * (u * k)) := by group
        _ = l * u * l⁻¹ := by rw [h1, mul_one]
    refine ⟨g * (u * k) * g⁻¹, ⟨g * l⁻¹ * g⁻¹, ?_⟩, ?_, Or.inr ?_⟩
    · rw [hukl, hu]; group
    · intro h
      have h2 : g * k * g⁻¹ = 1 := by
        calc g * k * g⁻¹ = t * (g * (u * k) * g⁻¹) := by
              rw [hu]; group; rw [hS.t_mul_t]; group
          _ = 1 := by rw [h, hS.t_mul_t]
      have hk1 : k = 1 := by
        calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      have hkX1 : kX = 1 := by
        have : φ.symm kX = 1 := Subtype.ext hk1
        exact φ.symm.map_eq_one_iff.mp this
      rw [hkX1, orderOf_one] at hkX2
      exact absurd hkX2 (by decide)
    · have e : t * (g * (u * k) * g⁻¹) = g * k * g⁻¹ := by
        rw [hu]
        calc t * (g * (g⁻¹ * t * g * k) * g⁻¹) = (t * t) * (g * k * g⁻¹) := by group
          _ = g * k * g⁻¹ := by rw [hS.t_mul_t, one_mul]
      rw [e]
      exact hgk

theorem ZP_le_PG [CharP K 2] :
    pull φ (antiUnipotentCenter K) ≤ pull φ (antiUnipotent K) :=
  pull_mono φ antiUnipotentCenter_le

theorem comm_P_ZP [CharP K 2] {p z : G} (hp : p ∈ pull φ (antiUnipotent K))
    (hz : z ∈ pull φ (antiUnipotentCenter K)) : p * z = z * p := by
  rw [← center_pull_antiUnipotent φ, mem_center_map_iff] at hz
  exact hz.2 p hp

theorem ZP_mul_self [CharP K 2] {z : G} (hz : z ∈ pull φ (antiUnipotentCenter K)) :
    z * z = 1 := by
  obtain ⟨hzL, hzZ⟩ := mem_pull.mp hz
  have h := mul_self_of_mem_radA1 (antiUnipotentCenter_le_radA1 hzZ)
  rw [← map_mul, φ.map_eq_one_iff] at h
  exact congrArg Subtype.val h

theorem mul_mem_ZQ [CharP K 2] (hS : Setup L K n φ TG t) [Finite G] {z c : G}
    (hz : z ∈ pull φ (antiUnipotentCenter K)) (hc : c ∈ TG) :
    z * c ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype := by
  rw [mem_center_map_iff]
  refine ⟨mul_mem (mem_sup_left (ZP_le_PG hz)) (mem_sup_right hc), fun y hy => ?_⟩
  obtain ⟨p, hp, d, hd, rfl⟩ := hS.mem_Q.mp hy
  have h1 : Commute p z := comm_P_ZP hp hz
  have h2 : Commute p c := hS.comm_P_T hp hc
  have h3 : Commute d z := (hS.comm_P_T (ZP_le_PG hz) hd).symm
  have h4 : Commute d c := hS.comm_T hd hc
  exact (Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4)).eq

theorem exists_of_mem_ZQ [CharP K 2] (hS : Setup L K n φ TG t) {x : G}
    (hx : x ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype) :
    ∃ z ∈ pull φ (antiUnipotentCenter K), ∃ c ∈ TG, z * c = x := by
  rw [mem_center_map_iff] at hx
  obtain ⟨hxQ, hxc⟩ := hx
  obtain ⟨p, hp, c, hc, rfl⟩ := hS.mem_Q.mp hxQ
  refine ⟨p, ?_, c, hc, rfl⟩
  rw [← center_pull_antiUnipotent φ, mem_center_map_iff]
  refine ⟨hp, fun y hy => ?_⟩
  have h1 := hxc y (mem_sup_left hy)
  have h2 : y * c = c * y := hS.comm_P_T hy hc
  have h3 : y * p * c = p * y * c := by
    calc y * p * c = y * (p * c) := mul_assoc _ _ _
      _ = p * c * y := h1
      _ = p * (c * y) := mul_assoc _ _ _
      _ = p * y * c := by rw [← h2, mul_assoc]
  exact mul_right_cancel h3

theorem conj_mem_center {Q : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G)) {x : G}
    (hx : x ∈ (center Q).map Q.subtype) : g * x * g⁻¹ ∈ (center Q).map Q.subtype := by
  rw [mem_center_map_iff] at hx ⊢
  refine ⟨(mem_normalizer_iff.mp hg x).mp hx.1, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ Q :=
    (mem_normalizer_iff.mp hg _).mpr (by simpa [mul_assoc] using hy)
  have h := hx.2 _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * y := by group

theorem exists_conj_mem_ZQ [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) :
    ∃ s : G, (∃ g : G, s = g⁻¹ * t * g) ∧ s ≠ t ∧
      s ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
        (pull φ (antiUnipotent K) ⊔ TG).subtype := by
  obtain ⟨v, ⟨g, rfl⟩, hvt, hvL⟩ := hS.exists_conj_mem_tL hO hLn
  have hvv : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hS.t_mul_t]; group
  obtain ⟨w, hwL, e, he, hvw⟩ : ∃ w ∈ L, ∃ e : G, (e = 1 ∨ e = t) ∧ g⁻¹ * t * g = e * w := by
    rcases hvL with h | h
    · exact ⟨_, h, 1, Or.inl rfl, (one_mul _).symm⟩
    · refine ⟨_, h, t, Or.inr rfl, ?_⟩
      rw [← mul_assoc, hS.t_mul_t, one_mul]
  have hew : e * w = w * e := by
    rcases he with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hS.comm_L_T hwL hS.t_mem).symm
  have hee : e * e = 1 := by
    rcases he with rfl | rfl
    · rw [one_mul]
    · exact hS.t_mul_t
  have hww : w * w = 1 := by
    rw [hvw] at hvv
    calc w * w = e * e * (w * w) := by rw [hee, one_mul]
      _ = e * w * (e * w) := by
          rw [mul_assoc e w (e * w), ← mul_assoc w e w, ← hew]; group
      _ = 1 := hvv
  have hφw : φ ⟨w, hwL⟩ * φ ⟨w, hwL⟩ = 1 := by
    rw [← map_mul, φ.map_eq_one_iff]
    exact Subtype.ext hww
  obtain ⟨h, hh⟩ := SymplecticFourFusion.exists_conj_mem_center hφw
  set y : G := ((φ.symm h : L) : G) with hy
  have hyL : y ∈ L := (φ.symm h).2
  have hywZ : y * w * y⁻¹ ∈ pull φ (antiUnipotentCenter K) := by
    have : ((φ.symm (h * φ ⟨w, hwL⟩ * h⁻¹) : L) : G) = y * w * y⁻¹ := by
      simp [hy, map_mul, map_inv]
    rw [← this]
    exact symm_mem_pull.mpr hh
  have hye : y * e * y⁻¹ = e := by
    rcases he with rfl | rfl
    · group
    · rw [hS.comm_L_T hyL hS.t_mem, mul_inv_cancel_right]
  refine ⟨y * (g⁻¹ * t * g) * y⁻¹, ⟨g * y⁻¹, by group⟩, ?_, ?_⟩
  · intro hcon
    apply hvt
    calc g⁻¹ * t * g = y⁻¹ * (y * (g⁻¹ * t * g) * y⁻¹) * y := by group
      _ = y⁻¹ * t * y := by rw [hcon]
      _ = t := by rw [hS.comm_L_T (inv_mem hyL) hS.t_mem, inv_mul_cancel_right]
  · have e1 : y * (g⁻¹ * t * g) * y⁻¹ = (y * w * y⁻¹) * e := by
      rw [hvw]
      calc y * (e * w) * y⁻¹ = (y * e * y⁻¹) * (y * w * y⁻¹) := by group
        _ = e * (y * w * y⁻¹) := by rw [hye]
        _ = (y * w * y⁻¹) * e := by
            rcases he with rfl | rfl
            · rw [one_mul, mul_one]
            · exact (hS.comm_L_T (pull_le φ _ hywZ) hS.t_mem).symm
    rw [e1]
    refine hS.mul_mem_ZQ hywZ ?_
    rcases he with rfl | rfl
    · exact one_mem _
    · exact hS.t_mem

theorem exists_abelian_generators [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) :
    ∃ B₁ B₂ : Subgroup G, IsMulCommutative B₁ ∧ IsMulCommutative B₂ ∧
      Group.rank B₁ = 3 * n + 1 ∧ Group.rank B₂ = 3 * n + 1 ∧
      B₁ ⊔ B₂ = pull φ (antiUnipotent K) ⊔ TG := by
  obtain ⟨-, ⟨-, -, hA1card⟩, ⟨-, -, hA2card⟩, -⟩ :=
    even_symplectic_four_Sylow_involution_radicals hS.card_K
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hS.card_K, ← pow_mul, mul_comm]
  obtain ⟨hB1c, -, hB1r⟩ := hS.rank_radical_mul radA1_le_antiUnipotent
    (fun x hx y hy => radA1_comm hx hy) (fun x hx => mul_self_of_mem_radA1 hx) (hA1card.trans hq3)
  obtain ⟨hB2c, -, hB2r⟩ := hS.rank_radical_mul radA2_le_antiUnipotent
    (fun x hx y hy => radA2_comm hx hy) (fun x hx => mul_self_of_mem_radA2 hx) (hA2card.trans hq3)
  refine ⟨_, _, hB1c, hB2c, hB1r, hB2r, ?_⟩
  rw [← sup_sup_distrib_right, ← pull_sup, ← antiUnipotent_eq_radA1_sup_radA2]

theorem exists_conj_le_sylow [Finite G] {H : Subgroup G} (R : Sylow 2 H) {X : Subgroup G}
    (hXH : X ≤ H) (hX : IsPGroup 2 X) :
    ∃ c ∈ H, ∀ y ∈ X, c⁻¹ * y * c ∈ (R : Subgroup H).map H.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R', hR'⟩ := (hX.of_equiv (subgroupOfEquivOfLe hXH).symm).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H R' R
  refine ⟨((c⁻¹ : H) : G), (c⁻¹ : H).2, fun y hy => ?_⟩
  have hmem : MulAut.conj c • (⟨y, hXH hy⟩ : H) ∈ ((c • R' : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR' (mem_subgroupOf.mpr hy))
  rw [hc] at hmem
  refine ⟨_, hmem, ?_⟩
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem mem_normalizer_of_conj_le [Finite G] {Q : Subgroup G} {g : G}
    (h : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : g ∈ normalizer (Q : Set G) := by
  have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have heq : Q.map (MulAut.conj g).toMonoidHom = Q := eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro q
  refine ⟨h q, fun hq => ?_⟩
  rw [← heq] at hq
  obtain ⟨q', hq', hqq⟩ := hq
  have : q' = q := by
    have h1 : g * q' * g⁻¹ = g * q * g⁻¹ := hqq
    simpa using h1
  rwa [← this]

theorem mem_conj_normalizer [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) {h₀ : G}
    (hsZ : h₀⁻¹ * t * h₀ ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype) :
    ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
      h₀⁻¹ * t * h₀ = m⁻¹ * t * m := by
  set Q := pull φ (antiUnipotent K) ⊔ TG with hQ
  set C := centralizer ({t} : Set G) with hC
  set s := h₀⁻¹ * t * h₀ with hs
  obtain ⟨R, hQR⟩ := (hS.Q_two.of_equiv (subgroupOfEquivOfLe hS.Q_le_C).symm).exists_le_sylow
  set RG := (R : Subgroup C).map C.subtype with hRG
  have hRGC : RG ≤ C := map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map _
  have hQRG : Q ≤ RG := fun q hq => ⟨⟨q, hS.Q_le_C hq⟩, hQR (mem_subgroupOf.mpr hq), rfl⟩
  set X := (RG ⊓ centralizer ({s} : Set G)).map (MulAut.conj h₀).toMonoidHom with hX
  have hXC : X ≤ C := by
    rintro _ ⟨r, ⟨-, hr⟩, rfl⟩
    rw [hC, mem_centralizer_singleton_iff]
    have hr' := mem_centralizer_singleton_iff.mp hr
    change h₀ * r * h₀⁻¹ * t = t * (h₀ * r * h₀⁻¹)
    calc h₀ * r * h₀⁻¹ * t = h₀ * (r * s) * h₀⁻¹ := by rw [hs]; group
      _ = h₀ * (s * r) * h₀⁻¹ := by rw [hr']
      _ = t * (h₀ * r * h₀⁻¹) := by rw [hs]; group
  have hX2 : IsPGroup 2 X := (hRG2.to_le inf_le_left).map _
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_sylow R hXC hX2
  set g₁ := h₀⁻¹ * c with hg₁
  have hQ1 : ∀ q ∈ Q, g₁⁻¹ * q * g₁ ∈ RG := by
    intro q hq
    have hqs : q ∈ centralizer ({s} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact ((mem_center_map_iff.mp hsZ).2 q hq)
    have h1 := hc (h₀ * q * h₀⁻¹) ⟨q, ⟨hQRG hq, hqs⟩, rfl⟩
    have e : g₁⁻¹ * q * g₁ = c⁻¹ * (h₀ * q * h₀⁻¹) * c := by rw [hg₁]; group
    rw [e]
    exact h1
  obtain ⟨B₁, B₂, hB1c, hB2c, hB1r, hB2r, hB⟩ := hS.exists_abelian_generators
  rw [← hQ] at hB
  have key : ∀ B : Subgroup G, B ≤ Q → IsMulCommutative B → Group.rank B = 3 * n + 1 →
      B ≤ Q.comap (MulAut.conj g₁⁻¹).toMonoidHom := by
    intro B hBQ hBc hBr
    set B' := B.map (MulAut.conj g₁⁻¹).toMonoidHom with hB'
    have hB'R : B' ≤ RG := by
      rintro _ ⟨b, hb, rfl⟩
      have := hQ1 b (hBQ hb)
      simpa using this
    have hB'r : Group.rank B' = 3 * n + 1 := by
      rw [← hBr]
      exact (Group.rank_congr (B.equivMapOfInjective _ (MulAut.conj g₁⁻¹).injective)).symm
    have h1 := (hS.rank_bound hRGC hRG2 hQRG hB'R).2 hB'r
    intro b hb
    exact h1 ⟨b, hb, rfl⟩
  have hBQ1 : B₁ ≤ Q := hB ▸ le_sup_left
  have hBQ2 : B₂ ≤ Q := hB ▸ le_sup_right
  have hQQ : Q ≤ Q.comap (MulAut.conj g₁⁻¹).toMonoidHom := by
    have h := sup_le (key _ hBQ1 hB1c hB1r) (key _ hBQ2 hB2c hB2r)
    rwa [hB] at h
  have hm : g₁⁻¹ ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_le fun q hq => by
    have := hQQ hq
    simpa using this
  refine ⟨g₁⁻¹, hm, ?_⟩
  have hct : c⁻¹ * t * c = t := by
    have := mem_centralizer_singleton_iff.mp hcC
    calc c⁻¹ * t * c = c⁻¹ * (c * t) := by rw [mul_assoc, this]
      _ = t := by group
  calc s = g₁ * (g₁⁻¹ * s * g₁) * g₁⁻¹ := by group
    _ = g₁ * (c⁻¹ * t * c) * g₁⁻¹ := by rw [hg₁, hs]; group
    _ = g₁⁻¹⁻¹ * t * g₁⁻¹ := by rw [hct, inv_inv]

theorem exists_conj_mem_ZP [Finite K] [CharP K 2] {w : G} (hwL : w ∈ L) (hww : w * w = 1) :
    ∃ y ∈ L, y * w * y⁻¹ ∈ pull φ (antiUnipotentCenter K) := by
  have hφw : φ ⟨w, hwL⟩ * φ ⟨w, hwL⟩ = 1 := by
    rw [← map_mul, φ.map_eq_one_iff]
    exact Subtype.ext hww
  obtain ⟨h, hh⟩ := SymplecticFourFusion.exists_conj_mem_center hφw
  refine ⟨((φ.symm h : L) : G), (φ.symm h).2, ?_⟩
  have : ((φ.symm (h * φ ⟨w, hwL⟩ * h⁻¹) : L) : G) =
      ((φ.symm h : L) : G) * w * ((φ.symm h : L) : G)⁻¹ := by
    simp [map_mul, map_inv]
  rw [← this]
  exact symm_mem_pull.mpr hh

theorem T_eq_zpowers [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) :
    TG = zpowers t := by
  have hsq : ∀ y ∈ TG, y * y = t → False := by
    intro y hyT hyy
    obtain ⟨s, ⟨g, rfl⟩, hst, hsZ⟩ := hS.exists_conj_mem_ZQ hO hLn
    obtain ⟨m, hm, hgm⟩ := hS.mem_conj_normalizer hsZ
    have hyZ := hS.mul_mem_ZQ (one_mem _) hyT
    rw [one_mul] at hyZ
    have hy' := conj_mem_center (inv_mem hm) hyZ
    rw [inv_inv] at hy'
    obtain ⟨z, hz, c, hc, hzc⟩ := hS.exists_of_mem_ZQ hy'
    have hzc' : z * c = c * z := (hS.comm_P_T (ZP_le_PG hz) hc)
    have hs : g⁻¹ * t * g = c * c := by
      rw [hgm, ← hyy]
      calc m⁻¹ * (y * y) * m = (m⁻¹ * y * m) * (m⁻¹ * y * m) := by group
        _ = (z * c) * (z * c) := by rw [hzc]
        _ = (z * z) * (c * c) := by rw [mul_assoc z c, ← mul_assoc c, ← hzc']; group
        _ = c * c := by rw [ZP_mul_self hz, one_mul]
    have hord : orderOf (c * c) = 2 := by
      have : g⁻¹ * t * g = MulAut.conj g⁻¹ t := by simp
      rw [← hs, this, MulEquiv.orderOf_eq, hS.order_t]
    exact hst (hs.trans (hS.eq_t_of_mem_T (mul_mem hc hc) hord))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.T_cyclic
  obtain ⟨y₀, hy₀⟩ := IsCyclic.exists_generator (α := TG)
  have hord₀ : orderOf (y₀ : G) = Nat.card TG := by
    rw [orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hy₀
  obtain ⟨k, hk⟩ := hS.T_two.exists_card_eq
  have h2 : 2 ∣ Nat.card TG := by
    rw [← hS.order_t]
    exact Subgroup.orderOf_dvd_natCard _ hS.t_mem
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · rw [hk, pow_zero] at h2; exact absurd h2 (by decide)
    · omega
  have hcard : Nat.card TG = 2 := by
    by_contra hne
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exact absurd (by rw [hk, show k = 1 by omega, pow_one]) hne
      · exact h
    apply hsq ((y₀ : G) ^ 2 ^ (k - 2)) (pow_mem y₀.2 _)
    have hdvd : 2 ^ (k - 1) ∣ orderOf (y₀ : G) := by
      rw [hord₀, hk]; exact pow_dvd_pow 2 (by omega)
    have hpow : (y₀ : G) ^ 2 ^ (k - 2) * (y₀ : G) ^ 2 ^ (k - 2) = (y₀ : G) ^ 2 ^ (k - 1) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      congr 2
      omega
    rw [hpow]
    refine hS.eq_t_of_mem_T (pow_mem y₀.2 _) ?_
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hord₀, hk,
      Nat.pow_div (by omega) (by norm_num), show k - (k - 1) = 1 by omega, pow_one]
  refine (eq_of_le_of_card_ge (zpowers_le.mpr hS.t_mem) ?_).symm
  rw [hcard, Nat.card_zpowers, hS.order_t]

theorem pull_eq_map (φ' : L ≃* antiSp K) (S : Subgroup (antiSp K)) :
    pull φ' S = S.map (L.subtype.comp φ'.symm.toMonoidHom) := by
  rw [pull, comap_equiv_eq_map_symm', map_map]

theorem sq_set_eq [Finite G] [CharP K 2] (hS : Setup L K n φ TG t) (hT : TG = zpowers t) :
    {x : G | ∃ y ∈ pull φ (antiUnipotent K) ⊔ TG, x = y * y} =
      (L.subtype.comp φ.symm.toMonoidHom) '' {g | ∃ h ∈ antiUnipotent K, g = h * h} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp, c, hc, rfl⟩ := hS.mem_Q.mp hy
    obtain ⟨hpL, hpU⟩ := mem_pull.mp hp
    rw [hT] at hc
    obtain ⟨j, rfl⟩ := hc
    have hcc : t ^ j * t ^ j = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, show t ^ (2 : ℤ) = 1 by
        rw [zpow_two, hS.t_mul_t], one_zpow]
    refine ⟨φ ⟨p, hpL⟩ * φ ⟨p, hpL⟩, ⟨_, hpU, rfl⟩, ?_⟩
    have hpt : p * t ^ j = t ^ j * p := hS.comm_L_T hpL (hT ▸ zpow_mem_zpowers t j)
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
      MulEquiv.symm_apply_apply, coe_subtype]
    calc p * p = p * p * (t ^ j * t ^ j) := by rw [hcc, mul_one]
      _ = p * t ^ j * (p * t ^ j) := (Commute.mul_mul_mul_comm hpt.symm p (t ^ j)).symm
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨((φ.symm h : L) : G), mem_sup_left (symm_mem_pull.mpr hh), ?_⟩
    simp

theorem closure_sq_eq [Finite G] [Finite K] [CharP K 2] (hS : Setup L K n φ TG t)
    (hT : TG = zpowers t) :
    closure {x : G | ∃ y ∈ pull φ (antiUnipotent K) ⊔ TG, x = y * y} =
      pull φ (antiUnipotentCenter K) := by
  have hK2 : 2 < Nat.card K := by
    rw [hS.card_K]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  rw [hS.sq_set_eq hT, ← MonoidHom.map_closure, ← pull_eq_map, closure_squares_eq hK2]

theorem conj_mem_closure_sq {Q : Subgroup G} {m : G} (hm : m ∈ normalizer (Q : Set G)) {x : G}
    (hx : x ∈ closure {x : G | ∃ y ∈ Q, x = y * y}) :
    m * x * m⁻¹ ∈ closure {x : G | ∃ y ∈ Q, x = y * y} := by
  have h1 : m * x * m⁻¹ ∈ (closure {x : G | ∃ y ∈ Q, x = y * y}).map
      (MulAut.conj m).toMonoidHom := ⟨x, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨m * y * m⁻¹, (mem_normalizer_iff.mp hm y).mp hy, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conj_not_mem_L [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) (g : G) :
    g⁻¹ * t * g ∉ L := by
  intro hgL
  have hww : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hS.t_mul_t]; group
  obtain ⟨y, hyL, hyZ⟩ := exists_conj_mem_ZP (φ := φ) hgL hww
  have e : y * (g⁻¹ * t * g) * y⁻¹ = (g * y⁻¹)⁻¹ * t * (g * y⁻¹) := by group
  rw [e] at hyZ
  have hZQ := hS.mul_mem_ZQ hyZ (one_mem TG)
  rw [mul_one] at hZQ
  obtain ⟨m, hm, hgm⟩ := hS.mem_conj_normalizer hZQ
  have hT := hS.T_eq_zpowers hO hLn
  rw [← hS.closure_sq_eq hT] at hyZ
  have h1 := conj_mem_closure_sq hm hyZ
  rw [hgm, show m * (m⁻¹ * t * m) * m⁻¹ = t by group, hS.closure_sq_eq hT] at h1
  exact hS.t_not_mem_L (pull_le φ _ h1)

theorem mem_PG_of_commute [CharP K 2] {l : G} (hlL : l ∈ L)
    (hc : ∀ z ∈ pull φ (antiUnipotentCenter K), l * z = z * l) :
    l ∈ pull φ (antiUnipotent K) := by
  refine mem_pull.mpr ⟨hlL, ?_⟩
  rw [← SymplecticFourFusion.centralizer_center_eq, mem_centralizer_iff]
  intro a ha
  have h := hc _ (symm_mem_pull.mpr ha)
  have h2 : (φ.symm a) * ⟨l, hlL⟩ = ⟨l, hlL⟩ * φ.symm a := Subtype.ext h.symm
  have h3 := congrArg φ h2
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3

theorem normalizer_center_eq [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) :
    normalizer (((center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype : Subgroup G) : Set G) =
      normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) := by
  set Q := pull φ (antiUnipotent K) ⊔ TG with hQ
  set ZQ := (center ↥Q).map Q.subtype with hZQ
  have hNle : ∀ g ∈ normalizer (Q : Set G), g ∈ normalizer (ZQ : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_center hg, fun hx => ?_⟩
    have := conj_mem_center (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  apply le_antisymm
  · intro g₂ hg₂
    have hCN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (ZQ : Set G) →
        ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
      intro c hcC hcN q hq
      obtain ⟨p, hp, a, ha, rfl⟩ := hS.mem_Q.mp hq
      have hpL : p ∈ L := pull_le φ _ hp
      have hl : c * p * c⁻¹ ∈ L := (mem_normalizer_iff.mp (hS.cent_le hcC) p).mp hpL
      have ha' : c * a * c⁻¹ ∈ TG := hS.conj_mem_T hcC ha
      have hcomm : ∀ z ∈ pull φ (antiUnipotentCenter K),
          c * p * c⁻¹ * z = z * (c * p * c⁻¹) := by
        intro z hz
        have hzZ := hS.mul_mem_ZQ hz (one_mem TG)
        rw [mul_one] at hzZ
        have hz' : c⁻¹ * z * c ∈ ZQ := by
          have := (mem_normalizer_iff.mp (inv_mem hcN) z).mp hzZ
          simpa using this
        have h1 := (mem_center_map_iff.mp hz').2 (p * a) hq
        have h2 : c * (p * a) * c⁻¹ * z = z * (c * (p * a) * c⁻¹) := by
          calc c * (p * a) * c⁻¹ * z = c * ((p * a) * (c⁻¹ * z * c)) * c⁻¹ := by group
            _ = c * ((c⁻¹ * z * c) * (p * a)) * c⁻¹ := by rw [h1]
            _ = z * (c * (p * a) * c⁻¹) := by group
        have h3 : c * a * c⁻¹ * z = z * (c * a * c⁻¹) :=
          (hS.comm_L_T (pull_le φ _ hz) ha').symm
        have e : c * (p * a) * c⁻¹ = (c * p * c⁻¹) * (c * a * c⁻¹) := by group
        rw [e] at h2
        calc c * p * c⁻¹ * z
            = (c * p * c⁻¹) * (c * a * c⁻¹) * z * (c * a * c⁻¹)⁻¹ := by
              rw [mul_assoc (c * p * c⁻¹) (c * a * c⁻¹) z, h3]; group
          _ = z * ((c * p * c⁻¹) * (c * a * c⁻¹)) * (c * a * c⁻¹)⁻¹ := by rw [h2]
          _ = z * (c * p * c⁻¹) := by group
      have hpP := mem_PG_of_commute (φ := φ) hl hcomm
      have e : c * (p * a) * c⁻¹ = (c * p * c⁻¹) * (c * a * c⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_left hpP) (mem_sup_right ha')
    have htZ : t ∈ ZQ := by
      have := hS.mul_mem_ZQ (one_mem _) hS.t_mem
      rwa [one_mul] at this
    have h1 : g₂⁻¹ * t * g₂ ∈ ZQ := by
      have := (mem_normalizer_iff.mp (inv_mem hg₂) t).mp htZ
      simpa using this
    obtain ⟨m, hm, hgm⟩ := hS.mem_conj_normalizer h1
    have hcC : g₂ * m⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g₂ * m⁻¹ * t = g₂ * (m⁻¹ * t * m) * m⁻¹ := by group
        _ = g₂ * (g₂⁻¹ * t * g₂) * m⁻¹ := by rw [hgm]
        _ = t * (g₂ * m⁻¹) := by group
    have hcN : g₂ * m⁻¹ ∈ normalizer (ZQ : Set G) := mul_mem hg₂ (hNle _ (inv_mem hm))
    have hcQ : g₂ * m⁻¹ ∈ normalizer (Q : Set G) :=
      mem_normalizer_of_conj_le (hCN _ hcC hcN)
    have e : g₂ = g₂ * m⁻¹ * m := by group
    rw [e]
    exact mul_mem hcQ hm
  · exact hNle

end Setup
theorem charP_two_of_card {K : Type} [Field K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := Fintype.ofFinite K
  obtain ⟨q, hq⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hq.2] at hK
  have hdvd : ringChar K ∣ 2 ^ n := hK ▸ dvd_pow_self _ q.ne_zero
  have h2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hq.1 Nat.prime_two).1 (hq.1.dvd_of_dvd_pow hdvd)
  rw [← h2]
  exact ringChar.charP K

theorem exists_equiv_pull_eq {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] (φ : L ≃* antiSp K) (P : Sylow 2 L) :
    ∃ φ' : L ≃* antiSp K, (P : Subgroup L).map L.subtype = pull φ' (antiUnipotent K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hU2, hUodd⟩ := card_and_isSylowTwoOf_antiUnipotent (K := K)
  rw [show ((antiUnipotent K).subgroupOf ⊤).index = (antiUnipotent K).index from
    relIndex_top_right _] at hUodd
  set P₀ : Subgroup L := (antiUnipotent K).comap φ.toMonoidHom with hP₀
  have hP₀2 : IsPGroup 2 P₀ := hU2.comap_of_injective _ φ.injective
  have hP₀i : ¬ 2 ∣ P₀.index := by
    rwa [hP₀, index_comap_of_surjective _ φ.surjective]
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L (hP₀2.toSylow hP₀i) P
  have hmem : ∀ y : L, y ∈ (P : Subgroup L) ↔ φ (MulAut.conj l⁻¹ y) ∈ antiUnipotent K := by
    intro y
    rw [← hl, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv]
    rfl
  refine ⟨(MulAut.conj l⁻¹).trans φ, ?_⟩
  ext x
  rw [mem_pull]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (hmem y).mp hy⟩
  · rintro ⟨hx, hU⟩
    exact ⟨⟨x, hx⟩, (hmem _).mpr hU, rfl⟩

namespace Setup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {φ : L ≃* antiSp K}
  {TG : Subgroup G} {t : G}

theorem fusion [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) :
    (∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → IsPGroup 2 R →
        pull φ (antiUnipotent K) ⊔ TG ≤ R →
        (CFSG.LocalAnalysis.rankThompson R).map R.subtype = pull φ (antiUnipotent K) ⊔ TG) ∧
      {x : G | ∃ g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
          x = g⁻¹ * t * g} =
        {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
          (pull φ (antiUnipotent K) ⊔ TG).subtype} ∧
      {x : G | ∃ g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
          x = g⁻¹ * t * g} ≠ {t} ∧
      TG = zpowers t ∧
      (∀ g : G, g⁻¹ * t * g ∉ L) ∧
      normalizer (((center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
        (pull φ (antiUnipotent K) ⊔ TG).subtype : Subgroup G) : Set G) =
        normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) ∧
      (pull φ (antiUnipotent K) ⊔ TG = zpowers t ⊔ pull φ (antiUnipotent K) ∧
        zpowers t ⊓ pull φ (antiUnipotent K) = ⊥ ∧
        ∀ p ∈ pull φ (antiUnipotent K), t * p = p * t) ∧
      closure {x : G | ∃ y ∈ pull φ (antiUnipotent K) ⊔ TG, x = y * y} =
        (center ↥(pull φ (antiUnipotent K))).map (pull φ (antiUnipotent K)).subtype := by
  have hT := hS.T_eq_zpowers hO hLn
  have htZ : t ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype := by
    have := hS.mul_mem_ZQ (one_mem _) hS.t_mem
    rwa [one_mul] at this
  have horbit : {x : G | ∃ g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
      x = g⁻¹ * t * g} =
      {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
        (pull φ (antiUnipotent K) ⊔ TG).subtype} := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, rfl⟩, ?_⟩
      have := conj_mem_center (inv_mem hg) htZ
      rwa [inv_inv] at this
    · rintro ⟨⟨g, rfl⟩, hx⟩
      obtain ⟨m, hm, hgm⟩ := hS.mem_conj_normalizer hx
      exact ⟨m, hm, hgm⟩
  refine ⟨fun R hRC hR hQR => hS.rankThompson_eq hRC hR hQR, horbit, ?_, hT,
    hS.conj_not_mem_L hO hLn, hS.normalizer_center_eq, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [horbit]
    intro h
    obtain ⟨s, hsg, hst, hsZ⟩ := hS.exists_conj_mem_ZQ hO hLn
    have : s ∈ ({t} : Set G) := h ▸ ⟨hsg, hsZ⟩
    exact hst this
  · rw [hT, sup_comm]
  · rw [eq_bot_iff, ← hS.L_inf_T, hT]
    exact inf_le_inf (le_refl _) (pull_le φ _) |>.trans (by rw [inf_comm])
  · intro p hp
    exact (hS.comm_P_T hp hS.t_mem).symm
  · rw [hS.closure_sq_eq hT, center_pull_antiUnipotent]

end Setup
theorem setup_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ n) (φ : L ≃* antiSp K)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥) :
    Setup L K n φ ((T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
      t := by
  have hL' : CFSG.Assembly.ComponentType.IsStandardSubgroup L := hL
  obtain ⟨-, -, hLC, -, -, -, hCT, -, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hL' T hT htT ht hcore
  have ht2 : orderOf (t : G) = 2 := by rw [orderOf_coe]; exact ht
  exact {
    two_le := hn
    card_K := hK
    T_le := map_subtype_le _
    t_mem := ⟨t, htT, rfl⟩
    order_t := ht2
    T_cyclic := isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
    T_two := T.isPGroup'.map _
    cent_inf := hCT
    L_le := hLC
    cent_le :=
      (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL' t.2
        ht2).1 }

section Torus

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K]

variable (K) in
@[expose] def axisOne [CharP K 2] : Subgroup (antiSp K) where
  carrier := {g | ∃ b : K, g = uElt 0 b 0 0}
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', by rw [uElt_mul]; congr 1 <;> ring⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, by rw [uElt_inv]; congr 1; ring⟩

variable (K) in
@[expose] def axisTwo [CharP K 2] : Subgroup (antiSp K) where
  carrier := {g | ∃ c : K, g = uElt 0 0 c 0}
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', by rw [uElt_mul]; congr 1 <;> ring⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, by rw [uElt_inv]; congr 1; ring⟩

@[expose] def diagMat (r s : K) : Matrix (Fin 4) (Fin 4) K := diagonal ![r⁻¹, s⁻¹, s, r]

theorem diagMat_mul_diagMat (r s r' s' : K) :
    diagMat r s * diagMat r' s' = diagMat (r * r') (s * s') := by
  rw [diagMat, diagMat, diagMat, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem diagMat_one : diagMat (1 : K) 1 = 1 := by
  rw [diagMat, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

variable (K) in
@[expose] def diagTorus : Subgroup (antiSp K) where
  carrier := {g | ∃ r s : K, r ≠ 0 ∧ s ≠ 0 ∧ glMat (g : GL (Fin 4) K) = diagMat r s}
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, diagMat_one.symm⟩
  mul_mem' := by
    rintro g h ⟨r, s, hr, hs, hg⟩ ⟨r', s', hr', hs', hh⟩
    refine ⟨r * r', s * s', mul_ne_zero hr hr', mul_ne_zero hs hs', ?_⟩
    change glMat (g : GL (Fin 4) K) * glMat (h : GL (Fin 4) K) = _
    rw [hg, hh, diagMat_mul_diagMat]
  inv_mem' := by
    rintro g ⟨r, s, hr, hs, hg⟩
    refine ⟨r⁻¹, s⁻¹, inv_ne_zero hr, inv_ne_zero hs, ?_⟩
    have h1 : glMat ((g⁻¹ : antiSp K) : GL (Fin 4) K) * glMat (g : GL (Fin 4) K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    have h2 : diagMat r s * diagMat r⁻¹ s⁻¹ = 1 := by
      rw [diagMat_mul_diagMat, mul_inv_cancel₀ hr, mul_inv_cancel₀ hs, diagMat_one]
    calc glMat ((g⁻¹ : antiSp K) : GL (Fin 4) K)
        = glMat ((g⁻¹ : antiSp K) : GL (Fin 4) K) * (diagMat r s * diagMat r⁻¹ s⁻¹) := by
          rw [h2, Matrix.mul_one]
      _ = diagMat r⁻¹ s⁻¹ := by rw [← Matrix.mul_assoc, ← hg, h1, Matrix.one_mul]

theorem diagTorus_conj [CharP K 2] {δ : antiSp K} {r s : K} (hr : r ≠ 0) (hs : s ≠ 0)
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) (a b c d : K) :
    δ⁻¹ * uElt a b c d * δ = uElt (r * s⁻¹ * a) (r * s * b) (r ^ 2 * c) (s ^ 2 * d) := by
  have h : δ * uElt (r * s⁻¹ * a) (r * s * b) (r ^ 2 * c) (s ^ 2 * d) = uElt a b c d * δ := by
    have hδ' : ((δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagMat r s := hδ
    apply antiSp_ext
    simp only [Subgroup.coe_mul, Units.val_mul, glMat_uElt]
    rw [hδ']
    ext i j
    rw [diagMat, diagonal_mul, mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [uMat] <;> field_simp
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem diagTorus_conj_mem [CharP K 2] {δ : antiSp K} (hδ : δ ∈ diagTorus K) {u : antiSp K}
    (hu : u ∈ antiUnipotent K) : δ⁻¹ * u * δ ∈ antiUnipotent K := by
  obtain ⟨r, s, hr, hs, hδ⟩ := hδ
  obtain ⟨a, b, c, d, rfl⟩ := hu
  rw [diagTorus_conj hr hs hδ]
  exact ⟨_, _, _, _, rfl⟩

theorem exists_diagTorus {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ δ ∈ diagTorus K, glMat (δ : GL (Fin 4) K) = diagMat r s := by
  have hdet : (diagMat r s).det ≠ 0 := by
    rw [diagMat, det_diagonal, Fin.prod_univ_four]
    simp [hr, hs]
  have hmem : (diagMat r s)ᵀ * minorJ K * diagMat r s = minorJ K := by
    ext k l
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
    fin_cases k <;> fin_cases l <;> simp [diagMat, hr, hs]
  let g : GL (Fin 4) K := Matrix.GeneralLinearGroup.mk'' (diagMat r s) (isUnit_iff_ne_zero.mpr hdet)
  have hg : glMat g = diagMat r s := rfl
  exact ⟨⟨g, by rw [mem_antiSp, hg]; exact hmem⟩, ⟨r, s, hr, hs, hg⟩, hg⟩

theorem exists_diagTorus_conj [CharP K 2] [Finite K] {b c b' c' : K} (hc : c ≠ 0)
    (hc' : c' ≠ 0) (hbb : (b = 0 ∧ b' = 0) ∨ (b ≠ 0 ∧ b' ≠ 0)) :
    ∃ δ ∈ diagTorus K, δ⁻¹ * uElt 0 b c 0 * δ = uElt 0 b' c' 0 := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (c' / c)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    exact hr.elim hc' hc
  by_cases hb0 : b = 0
  · obtain ⟨δ, hδ, hδm⟩ := exists_diagTorus (K := K) hr0 one_ne_zero
    refine ⟨δ, hδ, ?_⟩
    rw [diagTorus_conj hr0 one_ne_zero hδm, hb0, (hbb.resolve_right fun h => h.1 hb0).2]
    congr 1 <;> [ring; ring; (rw [sq, ← hr]; field_simp); ring]
  · have hb'0 : b' ≠ 0 := (hbb.resolve_left fun h => hb0 h.1).2
    have hs0 : b' / (r * b) ≠ 0 := div_ne_zero hb'0 (mul_ne_zero hr0 hb0)
    obtain ⟨δ, hδ, hδm⟩ := exists_diagTorus (K := K) hr0 hs0
    refine ⟨δ, hδ, ?_⟩
    rw [diagTorus_conj hr0 hs0 hδm]
    congr 1 <;> [ring; (field_simp); (rw [sq, ← hr]; field_simp); ring]

theorem exists_diagTorus_conj_axisOne [CharP K 2] {b b' : K} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ δ ∈ diagTorus K, δ⁻¹ * uElt 0 b 0 0 * δ = uElt 0 b' 0 0 := by
  have hs0 : b' / b ≠ 0 := div_ne_zero hb' hb
  obtain ⟨δ, hδ, hδm⟩ := exists_diagTorus (K := K) one_ne_zero hs0
  refine ⟨δ, hδ, ?_⟩
  rw [diagTorus_conj one_ne_zero hs0 hδm]
  congr 1 <;> [ring; (field_simp); ring; ring]

theorem antiUnipotentCenter_eq_axis [CharP K 2] :
    antiUnipotentCenter K = axisOne K ⊔ axisTwo K ∧ axisOne K ⊓ axisTwo K = ⊥ := by
  refine ⟨le_antisymm ?_ (sup_le ?_ ?_), ?_⟩
  · rintro _ ⟨b, c, rfl⟩
    have e : uElt (0 : K) b c 0 = uElt 0 b 0 0 * uElt 0 0 c 0 := by
      rw [uElt_mul]; congr 1 <;> ring
    rw [e]
    exact mul_mem (mem_sup_left ⟨b, rfl⟩) (mem_sup_right ⟨c, rfl⟩)
  · rintro _ ⟨b, rfl⟩
    exact ⟨b, 0, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨0, c, rfl⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨b, rfl⟩, ⟨c, h⟩⟩
    obtain ⟨-, hb, -, -⟩ := uElt_inj h
    rw [hb, uElt_zero_eq_one]
    exact one_mem _

theorem card_axis [CharP K 2] : Nat.card (axisOne K) = Nat.card K ∧
    Nat.card (axisTwo K) = Nat.card K := by
  constructor
  · refine (Nat.card_congr (Equiv.ofBijective (fun b : K => (⟨uElt 0 b 0 0, b, rfl⟩ : axisOne K))
      ⟨fun b b' h => (uElt_inj (congrArg Subtype.val h)).2.1, fun ⟨g, b, hg⟩ =>
        ⟨b, Subtype.ext hg.symm⟩⟩)).symm
  · refine (Nat.card_congr (Equiv.ofBijective (fun c : K => (⟨uElt 0 0 c 0, c, rfl⟩ : axisTwo K))
      ⟨fun c c' h => (uElt_inj (congrArg Subtype.val h)).2.2.1, fun ⟨g, c, hg⟩ =>
        ⟨c, Subtype.ext hg.symm⟩⟩)).symm

theorem mem_axis_iff [CharP K 2] {z : antiSp K} (hz : z ∈ antiUnipotentCenter K) :
    (z ∈ axisOne K ∨ z ∈ axisTwo K) ↔ (z = 1 ∨ ¬ ∃ h ∈ antiUnipotent K, h * h = z) := by
  obtain ⟨b, c, rfl⟩ := hz
  by_cases h1 : uElt (0 : K) b c 0 = 1
  · simp only [h1, true_or, iff_true]
    exact Or.inl (one_mem _)
  rw [isSquare_iff _ h1]
  simp only [h1, false_or]
  constructor
  · rintro (⟨b', h⟩ | ⟨c', h⟩) ⟨b'', c'', hb'', hc'', h'⟩
    · exact hc'' ((uElt_inj (h'.symm.trans h)).2.2.1)
    · exact hb'' ((uElt_inj (h'.symm.trans h)).2.1)
  · intro h
    by_cases hb : b = 0
    · exact Or.inr ⟨c, by rw [hb]⟩
    · by_cases hc : c = 0
      · exact Or.inl ⟨b, by rw [hc]⟩
      · exact absurd ⟨b, c, hb, hc, rfl⟩ h

end Torus

section Orbit

variable {G : Type*} [Group G]

structure OrbitHyp (t : G) (U₁ U₂ W D M : Subgroup G) : Prop where
  W_eq : W = U₁ ⊔ U₂
  inf_eq : U₁ ⊓ U₂ = ⊥
  comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  sq : ∀ x ∈ W, x * x = 1
  D_le : D ≤ M
  D_fix : ∀ d ∈ D, d⁻¹ * t * d = t
  M_t : ∀ m ∈ M, t⁻¹ * (m⁻¹ * t * m) ∈ W
  M_U : ∀ m ∈ M, ((∀ x ∈ U₁, m⁻¹ * x * m ∈ U₁) ∧ ∀ x ∈ U₂, m⁻¹ * x * m ∈ U₂) ∨
    ((∀ x ∈ U₁, m⁻¹ * x * m ∈ U₂) ∧ ∀ x ∈ U₂, m⁻¹ * x * m ∈ U₁)
  trans₁ : ∀ x ∈ U₁, ∀ y ∈ U₁, x ≠ 1 → y ≠ 1 → ∃ d ∈ D, d⁻¹ * x * d = y
  trans₂ : ∀ x ∈ U₂, ∀ y ∈ U₂, x ≠ 1 → y ≠ 1 → ∃ d ∈ D, d⁻¹ * x * d = y
  trans₃ : ∀ x ∈ U₁, ∀ y ∈ U₂, ∀ x' ∈ U₁, ∀ y' ∈ U₂, x ≠ 1 → y ≠ 1 → x' ≠ 1 → y' ≠ 1 →
    ∃ d ∈ D, d⁻¹ * (x * y) * d = x' * y'
  big₁ : ∀ x ∈ U₁, ∃ x' ∈ U₁, x' ≠ 1 ∧ x' ≠ x
  big₂ : ∀ y ∈ U₂, ∃ y' ∈ U₂, y' ≠ 1 ∧ y' ≠ y

namespace OrbitHyp

variable {t : G} {U₁ U₂ W D M : Subgroup G}

theorem U₁_le (h : OrbitHyp t U₁ U₂ W D M) : U₁ ≤ W := h.W_eq ▸ le_sup_left

theorem U₂_le (h : OrbitHyp t U₁ U₂ W D M) : U₂ ≤ W := h.W_eq ▸ le_sup_right

theorem comm₁₂ (h : OrbitHyp t U₁ U₂ W D M) {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₂) :
    x * y = y * x :=
  h.comm x (h.U₁_le hx) y (h.U₂_le hy)

theorem swap (h : OrbitHyp t U₁ U₂ W D M) : OrbitHyp t U₂ U₁ W D M where
  W_eq := h.W_eq.trans (sup_comm U₁ U₂)
  inf_eq := inf_comm U₂ U₁ ▸ h.inf_eq
  comm := h.comm
  sq := h.sq
  D_le := h.D_le
  D_fix := h.D_fix
  M_t := h.M_t
  M_U := fun m hm => (h.M_U m hm).imp (fun h' => ⟨h'.2, h'.1⟩) (fun h' => ⟨h'.2, h'.1⟩)
  trans₁ := h.trans₂
  trans₂ := h.trans₁
  trans₃ := fun y hy x hx y' hy' x' hx' hy1 hx1 hy'1 hx'1 => by
    obtain ⟨d, hd, hdx⟩ := h.trans₃ x hx y hy x' hx' y' hy' hx1 hy1 hx'1 hy'1
    exact ⟨d, hd, by rw [← h.comm₁₂ hx hy, hdx, h.comm₁₂ hx' hy']⟩
  big₁ := h.big₂
  big₂ := h.big₁

theorem conj_ne_one {x m : G} (hx : x ≠ 1) : m⁻¹ * x * m ≠ 1 := fun h' => hx (by
  calc x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    _ = 1 := by rw [h']; group)

theorem conj_mem_orbit {x : G} (hx : x ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}) {m : G}
    (hm : m ∈ M) : m⁻¹ * x * m ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a * m, mul_mem ha hm, by group⟩

theorem orbit_D (h : OrbitHyp t U₁ U₂ W D M) {w : G}
    (hw : t * w ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}) {d : G} (hd : d ∈ D) :
    t * (d⁻¹ * w * d) ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
  have h1 := conj_mem_orbit hw (h.D_le hd)
  have e : d⁻¹ * (t * w) * d = (d⁻¹ * t * d) * (d⁻¹ * w * d) := by group
  rwa [e, h.D_fix d hd] at h1

theorem orbit_one : t ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := ⟨1, one_mem M, by group⟩

theorem orbit_U₁ (h : OrbitHyp t U₁ U₂ W D M) {x : G} (hx : x ∈ U₁) (hx1 : x ≠ 1)
    (hxO : t * x ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}) {x' : G} (hx' : x' ∈ U₁) :
    t * x' ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
  by_cases hx'1 : x' = 1
  · rw [hx'1, mul_one]; exact orbit_one
  · obtain ⟨d, hd, hdx⟩ := h.trans₁ x hx x' hx' hx1 hx'1
    have := h.orbit_D hxO hd
    rwa [hdx] at this

theorem orbit_R (h : OrbitHyp t U₁ U₂ W D M) {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₂) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hO : t * (x * y) ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}) {x' y' : G}
    (hx' : x' ∈ U₁) (hy' : y' ∈ U₂) (hx'1 : x' ≠ 1) (hy'1 : y' ≠ 1) :
    t * (x' * y') ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
  obtain ⟨d, hd, hdx⟩ := h.trans₃ x hx y hy x' hx' y' hy' hx1 hy1 hx'1 hy'1
  have := h.orbit_D hO hd
  rwa [hdx] at this

theorem orbit_A (h : OrbitHyp t U₁ U₂ W D M) {x₀ y₀ : G} (hx₀ : x₀ ∈ U₁) (hy₀ : y₀ ∈ U₂)
    (hx₀1 : x₀ ≠ 1) (hy₀1 : y₀ ≠ 1)
    (hO : t * (x₀ * y₀) ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}) :
    ∃ y ∈ U₂, y ≠ 1 ∧ t * y ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
  obtain ⟨m, hm, hm₀⟩ := hO
  obtain ⟨y₁, hy₁, hy₁1, hy₁0⟩ := h.big₂ y₀ hy₀
  have hw : t * (m * (x₀ * y₁) * m⁻¹) ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
    have hx' : m * x₀ * m⁻¹ ≠ 1 := by simpa using conj_ne_one (m := m⁻¹) hx₀1
    have hy' : m * y₁ * m⁻¹ ≠ 1 := by simpa using conj_ne_one (m := m⁻¹) hy₁1
    rcases h.M_U m⁻¹ (inv_mem hm) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hxU : m * x₀ * m⁻¹ ∈ U₁ := by simpa using h1 x₀ hx₀
      have hyU : m * y₁ * m⁻¹ ∈ U₂ := by simpa using h2 y₁ hy₁
      have e : m * (x₀ * y₁) * m⁻¹ = (m * x₀ * m⁻¹) * (m * y₁ * m⁻¹) := by group
      rw [e]
      exact h.orbit_R hx₀ hy₀ hx₀1 hy₀1 ⟨m, hm, hm₀⟩ hxU hyU hx' hy'
    · have hxU : m * x₀ * m⁻¹ ∈ U₂ := by simpa using h1 x₀ hx₀
      have hyU : m * y₁ * m⁻¹ ∈ U₁ := by simpa using h2 y₁ hy₁
      have e : m * (x₀ * y₁) * m⁻¹ = (m * y₁ * m⁻¹) * (m * x₀ * m⁻¹) := by
        rw [h.comm₁₂ hyU hxU]; group
      rw [e]
      exact h.orbit_R hx₀ hy₀ hx₀1 hy₀1 ⟨m, hm, hm₀⟩ hyU hxU hy' hx'
  have h2 := conj_mem_orbit hw hm
  have hc : y₀ * x₀ = x₀ * y₀ := (h.comm₁₂ hx₀ hy₀).symm
  have e : m⁻¹ * (t * (m * (x₀ * y₁) * m⁻¹)) * m = t * (y₀ * y₁) := by
    calc m⁻¹ * (t * (m * (x₀ * y₁) * m⁻¹)) * m = (m⁻¹ * t * m) * (x₀ * y₁) := by group
      _ = t * (x₀ * y₀) * (x₀ * y₁) := by rw [← hm₀]
      _ = t * (x₀ * (y₀ * x₀) * y₁) := by group
      _ = t * ((x₀ * x₀) * y₀ * y₁) := by rw [hc]; group
      _ = t * (y₀ * y₁) := by rw [h.sq x₀ (h.U₁_le hx₀), one_mul]
  rw [e] at h2
  refine ⟨y₀ * y₁, mul_mem hy₀ hy₁, fun h01 => hy₁0 ?_, h2⟩
  have hinv : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right (h.sq y₀ (h.U₂_le hy₀))
  rw [← hinv]
  exact (eq_inv_of_mul_eq_one_right h01)

theorem orbit_B (h : OrbitHyp t U₁ U₂ W D M)
    (hB : ∀ x ∈ U₁, ∀ y ∈ U₂, x ≠ 1 → y ≠ 1 →
      t * (x * y) ∉ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m})
    {x₁ : G} (hx₁ : x₁ ∈ U₁) (hx₁1 : x₁ ≠ 1)
    (hO₁ : t * x₁ ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}) {y₁ : G} (hy₁ : y₁ ∈ U₂)
    (hy₁1 : y₁ ≠ 1) : t * y₁ ∉ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := by
  intro hO₂
  obtain ⟨m, hm, hm₁⟩ := hO₁
  rcases h.M_U m hm with ⟨-, h2⟩ | ⟨h1, -⟩
  · have h3 := conj_mem_orbit hO₂ hm
    have e : m⁻¹ * (t * y₁) * m = t * (x₁ * (m⁻¹ * y₁ * m)) := by
      calc m⁻¹ * (t * y₁) * m = (m⁻¹ * t * m) * (m⁻¹ * y₁ * m) := by group
        _ = t * (x₁ * (m⁻¹ * y₁ * m)) := by rw [← hm₁]; group
    rw [e] at h3
    exact hB x₁ hx₁ _ (h2 y₁ hy₁) hx₁1 (conj_ne_one hy₁1) h3
  · have h3 := conj_mem_orbit ⟨m, hm, hm₁⟩ hm
    have e : m⁻¹ * (t * x₁) * m = t * (x₁ * (m⁻¹ * x₁ * m)) := by
      calc m⁻¹ * (t * x₁) * m = (m⁻¹ * t * m) * (m⁻¹ * x₁ * m) := by group
        _ = t * (x₁ * (m⁻¹ * x₁ * m)) := by rw [← hm₁]; group
    rw [e] at h3
    exact hB x₁ hx₁ _ (h1 x₁ hx₁) hx₁1 (conj_ne_one hx₁1) h3

theorem orbit_shapes (h : OrbitHyp t U₁ U₂ W D M) (hMC : ∃ m ∈ M, m⁻¹ * t * m ≠ t) :
    {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} ∨
      {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ U₂, x = t * u} ∨
      {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ w ∈ W, x = t * w} := by
  have hc : ∀ x ∈ U₁, ∀ y ∈ U₂, x * y = y * x := fun x hx y hy => h.comm₁₂ hx hy
  have hdec : ∀ w ∈ W, ∃ x ∈ U₁, ∃ y ∈ U₂, x * y = w := fun w hw =>
    (mem_sup_of_commute hc).mp (h.W_eq ▸ hw)
  have hOW : ∀ x ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}, ∃ w ∈ W, x = t * w := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, h.M_t m hm, by group⟩
  by_cases hA : ∃ x ∈ U₁, ∃ y ∈ U₂, x ≠ 1 ∧ y ≠ 1 ∧
      t * (x * y) ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}
  ·
    right; right
    obtain ⟨x₀, hx₀, y₀, hy₀, hx₀1, hy₀1, hO₀⟩ := hA
    obtain ⟨y₂, hy₂, hy₂1, hO₂⟩ := h.orbit_A hx₀ hy₀ hx₀1 hy₀1 hO₀
    obtain ⟨x₂, hx₂, hx₂1, hO₁⟩ :=
      h.swap.orbit_A hy₀ hx₀ hy₀1 hx₀1 (by rwa [← h.comm₁₂ hx₀ hy₀])
    ext x
    constructor
    · exact hOW x
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec w hw
      by_cases ha1 : a = 1
      · rw [ha1, one_mul]
        exact h.swap.orbit_U₁ hy₂ hy₂1 hO₂ hb
      · by_cases hb1 : b = 1
        · rw [hb1, mul_one]
          exact h.orbit_U₁ hx₂ hx₂1 hO₁ ha
        · exact h.orbit_R hx₀ hy₀ hx₀1 hy₀1 hO₀ ha hb ha1 hb1
  ·
    push Not at hA
    have hA' : ∀ y ∈ U₂, ∀ x ∈ U₁, y ≠ 1 → x ≠ 1 →
        t * (y * x) ∉ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := fun y hy x hx hy1 hx1 => by
      rw [← h.comm₁₂ hx hy]
      exact hA x hx y hy hx1 hy1
    obtain ⟨m, hm, hmt⟩ := hMC
    obtain ⟨w, hw, hwt⟩ := hOW _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec w hw
    have hwO : t * (a * b) ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} := hwt ▸ ⟨m, hm, rfl⟩
    have hsub : ∀ x ∈ {x : G | ∃ m ∈ M, x = m⁻¹ * t * m}, ∃ c ∈ U₁, ∃ d ∈ U₂,
        x = t * (c * d) ∧ (c = 1 ∨ d = 1) := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := hOW x hx
      obtain ⟨c, hc, d, hd, rfl⟩ := hdec z hz
      refine ⟨c, hc, d, hd, rfl, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hA c hc d hd hcon.1 hcon.2 hx
    by_cases ha1 : a = 1
    ·
      right; left
      have hb1 : b ≠ 1 := fun hb1 => hmt (by rw [hwt, ha1, hb1]; group)
      rw [ha1, one_mul] at hwO
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, d, hd, rfl, hcd⟩ := hsub x hx
        rcases hcd with hc1 | hd1
        · exact ⟨d, hd, by rw [hc1, one_mul]⟩
        · by_cases hc1 : c = 1
          · exact ⟨d, hd, by rw [hc1, one_mul]⟩
          · rw [hd1, mul_one] at hx
            exact absurd hx (h.swap.orbit_B hA' hb hb1 hwO hc hc1)
      · rintro ⟨u, hu, rfl⟩
        exact h.swap.orbit_U₁ hb hb1 hwO hu
    ·
      left
      have hb1 : b = 1 := by
        by_contra hb1
        exact hA a ha b hb ha1 hb1 hwO
      rw [hb1, mul_one] at hwO
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, d, hd, rfl, hcd⟩ := hsub x hx
        rcases hcd with hc1 | hd1
        · by_cases hd1 : d = 1
          · exact ⟨c, hc, by rw [hd1, mul_one]⟩
          · rw [hc1, one_mul] at hx
            exact absurd hx (h.orbit_B hA ha ha1 hwO hd hd1)
        · exact ⟨c, hc, by rw [hd1, mul_one]⟩
      · rintro ⟨u, hu, rfl⟩
        exact h.orbit_U₁ ha ha1 hwO hu

end OrbitHyp

end Orbit
namespace Setup

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {φ : L ≃* antiSp K}
  {TG : Subgroup G} {t : G}

theorem ZP_eq_axis [CharP K 2] :
    pull φ (antiUnipotentCenter K) = pull φ (axisOne K) ⊔ pull φ (axisTwo K) ∧
      pull φ (axisOne K) ⊓ pull φ (axisTwo K) = ⊥ := by
  obtain ⟨h1, h2⟩ := antiUnipotentCenter_eq_axis (K := K)
  exact ⟨by rw [h1, pull_sup], by rw [← pull_inf, h2, pull_bot]⟩

theorem axisOne_le_center [CharP K 2] : axisOne K ≤ antiUnipotentCenter K :=
  (antiUnipotentCenter_eq_axis (K := K)).1 ▸ le_sup_left

theorem axisTwo_le_center [CharP K 2] : axisTwo K ≤ antiUnipotentCenter K :=
  (antiUnipotentCenter_eq_axis (K := K)).1 ▸ le_sup_right

theorem mem_axis_iff_not_sq [Finite G] [CharP K 2] (hS : Setup L K n φ TG t)
    (hT : TG = zpowers t) {z : G} (hz : z ∈ pull φ (antiUnipotentCenter K)) :
    (z ∈ pull φ (axisOne K) ∨ z ∈ pull φ (axisTwo K)) ↔
      (z = 1 ∨ ¬ ∃ y ∈ pull φ (antiUnipotent K) ⊔ TG, z = y * y) := by
  obtain ⟨hzL, hzZ⟩ := mem_pull.mp hz
  have h1 : ∀ S : Subgroup (antiSp K), z ∈ pull φ S ↔ φ ⟨z, hzL⟩ ∈ S := fun S =>
    ⟨fun h => (mem_pull.mp h).2, fun h => mem_pull.mpr ⟨hzL, h⟩⟩
  have h2 : z = 1 ↔ φ ⟨z, hzL⟩ = 1 := by
    rw [φ.map_eq_one_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have h3 : (∃ y ∈ pull φ (antiUnipotent K) ⊔ TG, z = y * y) ↔
      ∃ h ∈ antiUnipotent K, h * h = φ ⟨z, hzL⟩ := by
    have e : z ∈ {x : G | ∃ y ∈ pull φ (antiUnipotent K) ⊔ TG, x = y * y} ↔
        z ∈ (L.subtype.comp φ.symm.toMonoidHom) '' {g | ∃ h ∈ antiUnipotent K, g = h * h} := by
      rw [hS.sq_set_eq hT]
    refine e.trans ⟨?_, ?_⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, he⟩
      refine ⟨h, hh, ?_⟩
      have : φ.symm (h * h) = ⟨z, hzL⟩ := Subtype.ext he
      rw [← this, MulEquiv.apply_symm_apply]
    · rintro ⟨h, hh, he⟩
      refine ⟨h * h, ⟨h, hh, rfl⟩, ?_⟩
      simp [he]
  rw [h1, h1, h2, h3]
  exact mem_axis_iff hzZ

theorem conj_mem_axis [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) {g : G}
    (hg : g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G)) {x : G}
    (hx : x ∈ pull φ (axisOne K) ∨ x ∈ pull φ (axisTwo K)) :
    g⁻¹ * x * g ∈ pull φ (axisOne K) ∨ g⁻¹ * x * g ∈ pull φ (axisTwo K) := by
  have hT := hS.T_eq_zpowers hO hLn
  have hxZ : x ∈ pull φ (antiUnipotentCenter K) := hx.elim
    (fun h => pull_mono φ axisOne_le_center h) (fun h => pull_mono φ axisTwo_le_center h)
  have hgx : g⁻¹ * x * g ∈ pull φ (antiUnipotentCenter K) := by
    rw [← hS.closure_sq_eq hT] at hxZ ⊢
    have := conj_mem_closure_sq (inv_mem hg) hxZ
    rwa [inv_inv] at this
  rw [hS.mem_axis_iff_not_sq hT hgx]
  rcases (hS.mem_axis_iff_not_sq hT hxZ).mp hx with h1 | h1
  · left
    rw [h1]
    group
  · right
    rintro ⟨y, hy, hyy⟩
    apply h1
    refine ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp hy, ?_⟩
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * y * g⁻¹ * (g * y * g⁻¹) := by rw [hyy]; group

theorem conj_axis [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) {g : G}
    (hg : g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G)) :
    ((pull φ (axisOne K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisOne K) ∧
        (pull φ (axisTwo K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisTwo K)) ∨
      ((pull φ (axisOne K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisTwo K) ∧
        (pull φ (axisTwo K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisOne K)) := by
  set U₁ := pull φ (axisOne K) with hU₁
  set U₂ := pull φ (axisTwo K) with hU₂
  obtain ⟨hc1, hc2⟩ := card_axis (K := K)
  have hcard1 : Nat.card U₁ = Nat.card K := by rw [hU₁, card_pull, hc1]
  have hcard2 : Nat.card U₂ = Nat.card K := by rw [hU₂, card_pull, hc2]
  have himg : ∀ V : Subgroup G, (V = U₁ ∨ V = U₂) →
      V.map (MulAut.conj g⁻¹).toMonoidHom = U₁ ∨ V.map (MulAut.conj g⁻¹).toMonoidHom = U₂ := by
    intro V hV
    have hsub : ∀ y ∈ V.map (MulAut.conj g⁻¹).toMonoidHom, y ∈ U₁ ∨ y ∈ U₂ := by
      rintro _ ⟨v, hv, rfl⟩
      have := hS.conj_mem_axis hO hLn hg
        (by rcases hV with rfl | rfl; exacts [Or.inl hv, Or.inr hv])
      simpa using this
    have hVcard : Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card K := by
      rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
      rcases hV with rfl | rfl
      exacts [hcard1, hcard2]
    rcases subgroup_le_of_subset_union hsub with h | h
    · exact Or.inl (eq_of_le_of_card_ge h (by rw [hVcard, hcard1]))
    · exact Or.inr (eq_of_le_of_card_ge h (by rw [hVcard, hcard2]))
  have hne : U₁ ≠ U₂ := by
    intro h
    have hinf := (ZP_eq_axis (φ := φ)).2
    rw [← hU₁, ← hU₂, ← h, inf_idem] at hinf
    have : Nat.card U₁ = 1 := by rw [hinf, card_bot]
    rw [hcard1] at this
    have h4 : 4 ≤ Nat.card K := by
      rw [hS.card_K]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
    omega
  have hinj : ∀ V V' : Subgroup G, V.map (MulAut.conj g⁻¹).toMonoidHom =
      V'.map (MulAut.conj g⁻¹).toMonoidHom → V = V' := fun V V' h =>
    map_injective (MulAut.conj g⁻¹).injective h
  rcases himg U₁ (Or.inl rfl) with h1 | h1 <;> rcases himg U₂ (Or.inr rfl) with h2 | h2
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hne

theorem eq_symm_of_mem_pull {S : Subgroup (antiSp K)} {x : G} (hx : x ∈ pull φ S) :
    ∃ a ∈ S, x = ((φ.symm a : L) : G) := by
  obtain ⟨hxL, hxS⟩ := mem_pull.mp hx
  exact ⟨_, hxS, by rw [MulEquiv.symm_apply_apply]⟩

theorem symm_conj {δ a b : antiSp K} (h : δ⁻¹ * a * δ = b) :
    ((φ.symm δ : L) : G)⁻¹ * ((φ.symm a : L) : G) * ((φ.symm δ : L) : G) =
      ((φ.symm b : L) : G) := by
  rw [← h]
  simp [map_mul, map_inv]

theorem diagTorus_le_normalizer [CharP K 2] [Finite G] (hS : Setup L K n φ TG t) :
    pull φ (diagTorus K) ≤ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) := by
  intro d hd
  obtain ⟨δ, hδ, rfl⟩ := eq_symm_of_mem_pull hd
  refine mem_normalizer_of_conj_le fun q hq => ?_
  obtain ⟨p, hp, c, hc, rfl⟩ := hS.mem_Q.mp hq
  obtain ⟨u, hu, rfl⟩ := eq_symm_of_mem_pull hp
  have hconj : δ * u * δ⁻¹ ∈ antiUnipotent K := by
    have := diagTorus_conj_mem (inv_mem hδ) hu
    rwa [inv_inv] at this
  have e : ((φ.symm δ : L) : G) * (((φ.symm u : L) : G) * c) * ((φ.symm δ : L) : G)⁻¹ =
      ((φ.symm (δ * u * δ⁻¹) : L) : G) * c := by
    have hdc := hS.comm_L_T (φ.symm δ).2 hc
    simp only [map_mul, map_inv, coe_mul, coe_inv]
    calc ((φ.symm δ : L) : G) * (((φ.symm u : L) : G) * c) * ((φ.symm δ : L) : G)⁻¹
        = ((φ.symm δ : L) : G) * ((φ.symm u : L) : G) * (c * ((φ.symm δ : L) : G)⁻¹) := by group
      _ = ((φ.symm δ : L) : G) * ((φ.symm u : L) : G) * (((φ.symm δ : L) : G)⁻¹ * c) := by
          rw [show c * ((φ.symm δ : L) : G)⁻¹ = ((φ.symm δ : L) : G)⁻¹ * c from
            (hS.comm_L_T (inv_mem (φ.symm δ).2) hc).symm]
      _ = _ := by group
  rw [e]
  exact mul_mem (mem_sup_left (symm_mem_pull.mpr hconj)) (mem_sup_right hc)

theorem orbitHyp [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) {M : Subgroup G}
    (hDM : pull φ (diagTorus K) ≤ M)
    (hMN : M ≤ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G)) :
    OrbitHyp t (pull φ (axisOne K)) (pull φ (axisTwo K)) (pull φ (antiUnipotentCenter K))
      (pull φ (diagTorus K)) M := by
  have hT := hS.T_eq_zpowers hO hLn
  have hK2 : 2 < Nat.card K := by
    rw [hS.card_K]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  have htZ : t ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype := by
    have := hS.mul_mem_ZQ (one_mem _) hS.t_mem
    rwa [one_mul] at this
  have hne1 : ∀ {a : antiSp K}, ((φ.symm a : L) : G) ≠ 1 → a ≠ 1 := fun h ha => h (by simp [ha])
  refine
    { W_eq := ZP_eq_axis.1
      inf_eq := ZP_eq_axis.2
      comm := fun x hx y hy => comm_P_ZP (ZP_le_PG hx) hy
      sq := fun x hx => ZP_mul_self hx
      D_le := hDM
      D_fix := fun d hd => by
        rw [mul_assoc, ← hS.comm_L_T (pull_le φ _ hd) hS.t_mem, inv_mul_cancel_left]
      M_t := fun m hm => ?_
      M_U := fun m hm => ?_
      trans₁ := ?_
      trans₂ := ?_
      trans₃ := ?_
      big₁ := ?_
      big₂ := ?_ }
  ·
    have h1 := conj_mem_center (inv_mem (hMN hm)) htZ
    rw [inv_inv] at h1
    obtain ⟨z, hz, c, hc, hzc⟩ := hS.exists_of_mem_ZQ h1
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [mul_one] at hzc
      exact hS.conj_not_mem_L hO hLn m (hzc ▸ pull_le φ _ hz)
    have hct : c = t := by
      refine hS.eq_t_of_mem_T hc (orderOf_eq_prime ?_ hc1)
      rw [hT] at hc
      obtain ⟨j, rfl⟩ := hc
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hS.t_mul_t,
        one_zpow]
    rw [← hzc, hct, hS.comm_L_T (pull_le φ _ hz) hS.t_mem, inv_mul_cancel_left]
    exact hz
  ·
    rcases hS.conj_axis hO hLn (hMN hm) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [← h1]; exact ⟨x, hx, by simp⟩
      · rw [← h2]; exact ⟨x, hx, by simp⟩
    · right
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [← h1]; exact ⟨x, hx, by simp⟩
      · rw [← h2]; exact ⟨x, hx, by simp⟩
  ·
    intro x hx y hy hx1 hy1
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := eq_symm_of_mem_pull hx
    obtain ⟨_, ⟨b', rfl⟩, rfl⟩ := eq_symm_of_mem_pull hy
    have hb : b ≠ 0 := fun h => hne1 hx1 (by rw [h, uElt_zero_eq_one])
    have hb' : b' ≠ 0 := fun h => hne1 hy1 (by rw [h, uElt_zero_eq_one])
    obtain ⟨δ, hδ, hδc⟩ := exists_diagTorus_conj_axisOne hb hb'
    exact ⟨_, symm_mem_pull.mpr hδ, symm_conj hδc⟩
  ·
    intro x hx y hy hx1 hy1
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := eq_symm_of_mem_pull hx
    obtain ⟨_, ⟨c', rfl⟩, rfl⟩ := eq_symm_of_mem_pull hy
    have hc : c ≠ 0 := fun h => hne1 hx1 (by rw [h, uElt_zero_eq_one])
    have hc' : c' ≠ 0 := fun h => hne1 hy1 (by rw [h, uElt_zero_eq_one])
    obtain ⟨δ, hδ, hδc⟩ := exists_diagTorus_conj (b := 0) (b' := 0) hc hc' (Or.inl ⟨rfl, rfl⟩)
    exact ⟨_, symm_mem_pull.mpr hδ, symm_conj hδc⟩
  ·
    intro x hx y hy x' hx' y' hy' hx1 hy1 hx'1 hy'1
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := eq_symm_of_mem_pull hx
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := eq_symm_of_mem_pull hy
    obtain ⟨_, ⟨b', rfl⟩, rfl⟩ := eq_symm_of_mem_pull hx'
    obtain ⟨_, ⟨c', rfl⟩, rfl⟩ := eq_symm_of_mem_pull hy'
    have hb : b ≠ 0 := fun h => hne1 hx1 (by rw [h, uElt_zero_eq_one])
    have hc : c ≠ 0 := fun h => hne1 hy1 (by rw [h, uElt_zero_eq_one])
    have hb' : b' ≠ 0 := fun h => hne1 hx'1 (by rw [h, uElt_zero_eq_one])
    have hc' : c' ≠ 0 := fun h => hne1 hy'1 (by rw [h, uElt_zero_eq_one])
    have hprod : ∀ b c : K, uElt 0 b 0 0 * uElt 0 0 c 0 = uElt 0 b c 0 := fun b c => by
      rw [uElt_mul]; congr 1 <;> ring
    obtain ⟨δ, hδ, hδc⟩ := exists_diagTorus_conj hc hc' (Or.inr ⟨hb, hb'⟩)
    refine ⟨_, symm_mem_pull.mpr hδ, ?_⟩
    have h1 := symm_conj (φ := φ) hδc
    rw [← hprod b c, ← hprod b' c', map_mul, map_mul] at h1
    simpa using h1
  ·
    intro x hx
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := eq_symm_of_mem_pull hx
    obtain ⟨b₁, hb₁, hbb₁⟩ := exists_ne_zero_ne hK2 b
    refine ⟨_, symm_mem_pull.mpr ⟨b₁, rfl⟩, fun h => hb₁ ?_, fun h => hbb₁ ?_⟩
    · have h' : uElt (0 : K) b₁ 0 0 = uElt 0 0 0 0 := by
        rw [uElt_zero_eq_one]
        simpa using h
      exact (uElt_inj h').2.1
    · have h' : uElt (0 : K) b₁ 0 0 = uElt 0 b 0 0 := by
        have := congrArg (fun z : G => z) h
        simpa using h
      exact (uElt_inj h').2.1.symm
  ·
    intro y hy
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := eq_symm_of_mem_pull hy
    obtain ⟨c₁, hc₁, hcc₁⟩ := exists_ne_zero_ne hK2 c
    refine ⟨_, symm_mem_pull.mpr ⟨c₁, rfl⟩, fun h => hc₁ ?_, fun h => hcc₁ ?_⟩
    · have h' : uElt (0 : K) 0 c₁ 0 = uElt 0 0 0 0 := by
        rw [uElt_zero_eq_one]
        simpa using h
      exact (uElt_inj h').2.2.1
    · have h' : uElt (0 : K) 0 c₁ 0 = uElt 0 0 c 0 := by simpa using h
      exact (uElt_inj h').2.2.1.symm

theorem orbits [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal) :
    (pull φ (antiUnipotentCenter K) = pull φ (axisOne K) ⊔ pull φ (axisTwo K) ∧
        pull φ (axisOne K) ⊓ pull φ (axisTwo K) = ⊥ ∧
        ∀ x ∈ pull φ (axisOne K), ∀ y ∈ pull φ (axisTwo K), x * y = y * x) ∧
      pull φ (diagTorus K) ≤
        normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) ∧
      (∀ g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        ((pull φ (axisOne K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisOne K) ∧
            (pull φ (axisTwo K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisTwo K)) ∨
          ((pull φ (axisOne K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisTwo K) ∧
            (pull φ (axisTwo K)).map (MulAut.conj g⁻¹).toMonoidHom = pull φ (axisOne K))) ∧
      (∀ M : Subgroup G, pull φ (diagTorus K) ≤ M →
        M ≤ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) →
        ¬ M ≤ centralizer ({t} : Set G) →
        {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisOne K), x = t * u} ∨
          {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisTwo K), x = t * u} ∨
          {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} =
            {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z}) ∧
      ¬ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) ≤
        centralizer ({t} : Set G) := by
  have hNC : ¬ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) ≤
      centralizer ({t} : Set G) := by
    intro hle
    obtain ⟨s, ⟨g, rfl⟩, hst, hsZ⟩ := hS.exists_conj_mem_ZQ hO hLn
    obtain ⟨m, hm, hgm⟩ := hS.mem_conj_normalizer hsZ
    apply hst
    rw [hgm]
    have := mem_centralizer_singleton_iff.mp (hle hm)
    calc m⁻¹ * t * m = m⁻¹ * (m * t) := by rw [mul_assoc, this]
      _ = t := by group
  refine ⟨⟨ZP_eq_axis.1, ZP_eq_axis.2, fun x hx y hy => ?_⟩, hS.diagTorus_le_normalizer,
    fun g hg => hS.conj_axis hO hLn hg, fun M hDM hMN hMC => ?_, hNC⟩
  · exact comm_P_ZP (ZP_le_PG (pull_mono φ axisOne_le_center hx))
      (pull_mono φ axisTwo_le_center hy)
  · refine (hS.orbitHyp hO hLn hDM hMN).orbit_shapes ?_
    obtain ⟨m, hm, hmC⟩ := Set.not_subset.mp hMC
    refine ⟨m, hm, fun h => hmC ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    calc m * t = m * (m⁻¹ * t * m) := by rw [h]
      _ = t * m := by group

end Setup


end GomiFusion

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

theorem standard_symplectic_four_central_involution_fusion
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (φ : L ≃* antiSp K)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    (∀ R : Subgroup G, R ≤ centralizer ({(t : G)} : Set G) → IsPGroup 2 R → Q ≤ R →
        (CFSG.LocalAnalysis.rankThompson R).map R.subtype = Q) ∧
      {x : G | ∃ g ∈ normalizer (Q : Set G), x = g⁻¹ * t * g} =
        {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ (center Q).map Q.subtype} ∧
      {x : G | ∃ g ∈ normalizer (Q : Set G), x = g⁻¹ * t * g} ≠ {(t : G)} ∧
      (Nat.card (T : Subgroup (centralizer (L : Set G))) = 2 ∧ TG = zpowers (t : G)) ∧
      (∀ g : G, g⁻¹ * t * g ∉ L) ∧
      normalizer (((center Q).map Q.subtype : Subgroup G) : Set G) = normalizer (Q : Set G) ∧
      (Q = zpowers (t : G) ⊔ PG ∧ zpowers (t : G) ⊓ PG = ⊥ ∧ ∀ p ∈ PG, (t : G) * p = p * t) ∧
      closure {x : G | ∃ y ∈ Q, x = y * y} = (center PG).map PG.subtype := by
  intro TG PG Q
  have : CharP K 2 := charP_two_of_card hK
  obtain ⟨φ', hφ'⟩ := exists_equiv_pull_eq φ P
  have hS : Setup L K n φ' TG t := setup_of_standard hL hn hK φ' T hT htT ht hcore
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hS.fusion hO hLn
  rw [← hφ'] at h1 h2 h3 h6 h7 h8
  refine ⟨h1, h2, h3, ⟨?_, h4⟩, h5, h6, h7, h8⟩
  have hcard : Nat.card TG = 2 := by rw [h4, Nat.card_zpowers, hS.order_t]
  rwa [card_map_of_injective (subtype_injective _)] at hcard

theorem standard_symplectic_four_normalizer_fusion_orbits
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let U₁ := ((axisOne K).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((axisTwo K).comap φ.toMonoidHom).map L.subtype
    let D := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let ZP := (center PG).map PG.subtype
    (ZP = U₁ ⊔ U₂ ∧ U₁ ⊓ U₂ = ⊥ ∧ ∀ x ∈ U₁, ∀ y ∈ U₂, x * y = y * x) ∧
      D ≤ normalizer (Q : Set G) ∧
      (∀ g ∈ normalizer (Q : Set G),
        (U₁.map (MulAut.conj g⁻¹).toMonoidHom = U₁ ∧ U₂.map (MulAut.conj g⁻¹).toMonoidHom = U₂) ∨
          (U₁.map (MulAut.conj g⁻¹).toMonoidHom = U₂ ∧
            U₂.map (MulAut.conj g⁻¹).toMonoidHom = U₁)) ∧
      (∀ M : Subgroup G, D ≤ M → M ≤ normalizer (Q : Set G) →
        ¬ M ≤ centralizer ({(t : G)} : Set G) →
        {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} ∨
          {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ U₂, x = t * u} ∨
          {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z}) ∧
      ({x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} ∨
        {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₂, x = t * u} ∨
        {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z}) := by
  intro TG PG Q U₁ U₂ D ZP
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.orbits hO hLn
  rw [← hPG] at h2 h3 h4 h5
  rw [← hZP] at h1 h4
  refine ⟨h1, h2, h3, h4, ?_⟩
  exact h4 _ h2 le_rfl h5

end CFSG.LocalAnalysis.SymplecticFourStandard
