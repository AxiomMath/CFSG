module

public import CFSG.Quasithin.SteinbergBSFixedSpaceStability
public import CFSG.Quasithin.SteinbergCBBinarySixProfile
public import CFSG.LinearAlgebra.SteinbergBQSymplecticFixedDrop
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Module CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

section Lin

variable (V : Type*) [Group V] [IsElementaryAbelian 2 V]

@[expose] noncomputable def mulAutToLin : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun f := (MulEquiv.toAdditive f).toLinearEquiv (ZMod.map_smul _)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

variable {V}

theorem mulAutToLin_apply (f : MulAut V) (x : Additive V) :
    mulAutToLin V f x = Additive.ofMul (f (Additive.toMul x)) := rfl

theorem mulAutToLin_injective : Function.Injective (mulAutToLin V) := fun _ _ h =>
  MulEquiv.ext fun v => LinearEquiv.congr_fun h (Additive.ofMul v)

end Lin

section LinGroups

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem mem_linFix_iff {B : Subgroup (W ≃ₗ[ZMod 2] W)} {x : W} :
    x ∈ linFix B ↔ ∀ g ∈ B, g x = x := by
  simp only [linFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]

theorem linFix_le_ker {B : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W} (he : e ∈ B) :
    linFix B ≤ LinearMap.ker ((e : W →ₗ[ZMod 2] W) - LinearMap.id) :=
  iInf₂_le e he

theorem linFix_antitone {E F : Subgroup (W ≃ₗ[ZMod 2] W)} (hFE : F ≤ E) :
    linFix E ≤ linFix F :=
  le_iInf₂ fun _ he => linFix_le_ker (hFE he)

theorem exists_linFix_lt_of_card_eq_eight [FiniteDimensional (ZMod 2) W]
    (b : LinearMap.BilinForm (ZMod 2) W) (hb : b.Nondegenerate) (halt : b.IsAlt)
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hEab : IsElementaryAbelian 2 E)
    (hEb : ∀ e ∈ E, ∀ x y, b (e x) (e y) = b x y) (hE8 : Nat.card E = 8)
    (hrank : ∃ e ∈ E, e ≠ 1 ∧ linRank e ≤ 2) :
    ∃ F ≤ E, F.relIndex E ≤ 4 ∧ linFix E < linFix F := by
  classical
  set ι := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm with hι
  have hιcoe : ∀ e : W ≃ₗ[ZMod 2] W,
      ((ι e : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) =
        (e : W →ₗ[ZMod 2] W) := by
    intro e
    have h1 := LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (ι e)
    rw [hι, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hιsymm : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) W, ∀ x : W,
      ι.symm g x = (g : W →ₗ[ZMod 2] W) x := fun g x => by
    rw [hι, MulEquiv.symm_symm, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  set E' := E.map ι.toMonoidHom with hE'
  have : IsElementaryAbelian 2 E := hEab
  have : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  have hE'b : E' ≤ LocalAnalysis.ComponentInitial.bilinIsometryGroup b := by
    rintro _ ⟨e, he, rfl⟩
    rw [LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup]
    intro x y
    change b (((ι e : _) : W →ₗ[ZMod 2] W) x) (((ι e : _) : W →ₗ[ZMod 2] W) y) = b x y
    rw [hιcoe]
    exact hEb e he x y
  have hE'card : Nat.card E' = 2 ^ 3 := by
    rw [hE', card_map_of_injective ι.injective, hE8]
    norm_num
  have hE'1 : E' ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hE'card
    norm_num at hE'card
  obtain ⟨e, he, he1, herank⟩ := hrank
  obtain ⟨B', hB'E', hB'idx, hlt⟩ :=
    LinearAlgebra.symplectic_small_rank_fixed_space_drop b hb halt E' hE'b hE'1 hE'card le_rfl
      fun _ => ⟨ι e, ⟨e, he, rfl⟩, fun h => he1 (ι.injective (h.trans (map_one ι).symm)), by
        rw [hιcoe]
        exact herank⟩
  have hEE : E'.map ι.symm.toMonoidHom = E := by
    rw [hE', map_map]
    convert map_id E
    exact MonoidHom.ext fun x => ι.symm_apply_apply x
  refine ⟨B'.map ι.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← hEE]
    exact map_mono hB'E'
  · rw [← hEE, relIndex_map_map_of_injective _ _ ι.symm.injective]
    exact hB'idx
  · rw [← SetLike.coe_ssubset_coe]
    convert hlt using 1
    · ext x
      simp only [SetLike.mem_coe, mem_linFix_iff, Set.mem_ofPred_eq]
      constructor
      · rintro hx _ ⟨g, hg, rfl⟩
        change ((ι g : _) : W →ₗ[ZMod 2] W) x = x
        rw [hιcoe]
        exact hx g hg
      · intro hx g hg
        have h1 := hx _ ⟨g, hg, rfl⟩
        change ((ι g : _) : W →ₗ[ZMod 2] W) x = x at h1
        rwa [hιcoe] at h1
    · ext x
      simp only [SetLike.mem_coe, mem_linFix_iff, Set.mem_ofPred_eq]
      constructor
      · intro hx g hg
        have h1 := hx _ ⟨g, hg, rfl⟩
        change ι.symm g x = x at h1
        rwa [hιsymm] at h1
      · rintro hx _ ⟨g, hg, rfl⟩
        change ι.symm g x = x
        rw [hιsymm]
        exact hx g hg

end LinGroups

theorem ne_bot_of_relIndex_eq_two {W : Type*} [Group W] {F E : Subgroup W} (hFE : F ≤ E)
    (hidx : F.relIndex E = 2) (hE : 4 ≤ Nat.card E) : F ≠ ⊥ := by
  intro hF
  have h1 := relIndex_mul_card F E
  rw [hidx, inf_of_le_left hFE, hF, card_bot] at h1
  omega

variable {G : Type*} [Group G]

section Conj

variable (V H : Subgroup G) [IsElementaryAbelian 2 V] (hH : H ≤ normalizer (V : Set G))

@[expose] noncomputable def u3ConjLin : H →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
  (mulAutToLin V).comp (SteinbergBS.normalizerConjOn V H hH)

@[expose] noncomputable def subOf (K : Subgroup G) : Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (K.subgroupOf V))

variable {V H hH}

theorem coe_u3ConjLin_apply (h : H) (x : Additive V) :
    ((Additive.toMul (u3ConjLin V H hH h x) : V) : G) =
      h * ((Additive.toMul x : V) : G) * (h : G)⁻¹ := rfl

theorem mem_subOf {K : Subgroup G} {x : Additive V} :
    x ∈ subOf V K ↔ ((Additive.toMul x : V) : G) ∈ K := by
  rw [subOf, AddSubgroup.mem_toZModSubmodule]
  exact Iff.rfl

theorem card_subOf (K : Subgroup G) : Nat.card (subOf V K) = Nat.card (V ⊓ K : Subgroup G) :=
  Nat.card_congr
    { toFun := fun x => ⟨((Additive.toMul (x : Additive V) : V) : G),
        (Additive.toMul (x : Additive V)).2, mem_subOf.1 x.2⟩
      invFun := fun y => ⟨Additive.ofMul ⟨y, y.2.1⟩, mem_subOf.2 y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem subOf_le_subOf {K₁ K₂ : Subgroup G} (h : V ⊓ K₁ ≤ K₂) : subOf V K₁ ≤ subOf V K₂ :=
  fun x hx => mem_subOf.2 (h ⟨(Additive.toMul x).2, mem_subOf.1 hx⟩)

theorem subOf_congr {K₁ K₂ : Subgroup G} (h : V ⊓ K₁ = V ⊓ K₂) : subOf V K₁ = subOf V K₂ :=
  le_antisymm (subOf_le_subOf (by rw [h]; exact inf_le_right))
    (subOf_le_subOf (by rw [← h]; exact inf_le_right))

theorem ofMul_mem_subOf {K : Subgroup G} {v : G} (hv : v ∈ V) (hvK : v ∈ K) :
    Additive.ofMul (⟨v, hv⟩ : V) ∈ subOf V K :=
  mem_subOf.2 hvK

theorem u3ConjLin_eq_one_iff (h : H) :
    u3ConjLin V H hH h = 1 ↔ (h : G) ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h1 v hv
    have h2 := congrArg (fun φ : Additive V ≃ₗ[ZMod 2] Additive V =>
      ((Additive.toMul (φ (Additive.ofMul ⟨v, hv⟩)) : V) : G)) h1
    change (h : G) * v * (h : G)⁻¹ = v at h2
    calc v * h = h * v * (h : G)⁻¹ * h := by rw [h2]
      _ = h * v := by group
  · intro h1
    refine LinearEquiv.ext fun x => Additive.toMul.injective (Subtype.ext ?_)
    change (h : G) * ((Additive.toMul x : V) : G) * (h : G)⁻¹ = ((Additive.toMul x : V) : G)
    rw [← h1 _ (Additive.toMul x).2, mul_inv_cancel_right]

theorem u3ConjLin_apply_eq_self_iff (h : H) (x : Additive V) :
    u3ConjLin V H hH h x = x ↔ (h : G) * ((Additive.toMul x : V) : G) =
      ((Additive.toMul x : V) : G) * h := by
  constructor
  · intro h1
    have h2 := congrArg (fun y : Additive V => ((Additive.toMul y : V) : G)) h1
    change (h : G) * ((Additive.toMul x : V) : G) * (h : G)⁻¹ = ((Additive.toMul x : V) : G)
      at h2
    calc (h : G) * ((Additive.toMul x : V) : G)
        = (h : G) * ((Additive.toMul x : V) : G) * (h : G)⁻¹ * h := by group
      _ = ((Additive.toMul x : V) : G) * h := by rw [h2]
  · intro h1
    refine Additive.toMul.injective (Subtype.ext ?_)
    change (h : G) * ((Additive.toMul x : V) : G) * (h : G)⁻¹ = ((Additive.toMul x : V) : G)
    rw [h1, mul_inv_cancel_right]

theorem linFix_map_u3ConjLin (S : Subgroup H) :
    linFix (S.map (u3ConjLin V H hH)) =
      subOf V (centralizer ((S.map H.subtype : Subgroup G) : Set G)) := by
  ext x
  rw [mem_subOf, mem_centralizer_iff]
  simp only [linFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]
  constructor
  · rintro hx _ ⟨s, hs, rfl⟩
    exact ((u3ConjLin_apply_eq_self_iff s x).1 (hx _ ⟨s, hs, rfl⟩))
  · rintro hx _ ⟨s, hs, rfl⟩
    exact (u3ConjLin_apply_eq_self_iff s x).2 (hx _ ⟨s, hs, rfl⟩)

theorem ker_u3ConjLin_sub_id (h : H) :
    LinearMap.ker ((u3ConjLin V H hH h : Additive V →ₗ[ZMod 2] Additive V) - LinearMap.id) =
      subOf V (centralizer ({(h : G)} : Set G)) := by
  ext x
  rw [mem_subOf, mem_centralizer_singleton_iff, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe, u3ConjLin_apply_eq_self_iff]
  exact ⟨fun h1 => h1.symm, fun h1 => h1.symm⟩

theorem two_pow_linRank_mul_card [Finite V] (h : H) :
    2 ^ linRank (u3ConjLin V H hH h) *
      Nat.card (V ⊓ centralizer ({(h : G)} : Set G) : Subgroup G) = Nat.card V := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have h2 : Nat.card (Additive V) = 2 ^ finrank (ZMod 2) (Additive V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [← card_subOf, ← ker_u3ConjLin_sub_id (hH := hH), linRank,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker _), Nat.card_zmod, ← pow_add,
    LinearMap.finrank_range_add_finrank_ker, ← h2]
  rfl

theorem linComm_map_u3ConjLin_le (S : Subgroup H) :
    linComm (S.map (u3ConjLin V H hH)) ≤ subOf V ⁅(S.map H.subtype : Subgroup G), V⁆ := by
  rw [linComm, Submodule.span_le]
  rintro w ⟨_, ⟨s, hs, rfl⟩, v, rfl⟩
  rw [SetLike.mem_coe, mem_subOf]
  have h1 : ((Additive.toMul (u3ConjLin V H hH s v - v) : V) : G) =
      ⁅(s : G), ((Additive.toMul v : V) : G)⁆ := by
    rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv, coe_u3ConjLin_apply,
      commutatorElement_def]
  rw [h1]
  exact commutator_mem_commutator ⟨s, hs, rfl⟩ (Additive.toMul v).2

theorem exists_le_relIndex_linFix {A : Subgroup G} (hAH : A ≤ H)
    {F : Subgroup (Additive V ≃ₗ[ZMod 2] Additive V)}
    (hF : F ≤ (A.subgroupOf H).map (u3ConjLin V H hH)) :
    ∃ B : Subgroup G, B ≤ A ∧
      B.relIndex A = F.relIndex ((A.subgroupOf H).map (u3ConjLin V H hH)) ∧
      linFix F = subOf V (centralizer (B : Set G)) := by
  set φ := u3ConjLin V H hH
  set SA := A.subgroupOf H
  set S := F.comap φ ⊓ SA with hS
  have hSmap : S.map φ = F := by
    refine le_antisymm ((map_mono inf_le_left).trans (map_comap_le _ _)) fun y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hF hy
    exact ⟨s, ⟨hy, hs⟩, rfl⟩
  have hSA : SA.map H.subtype = A := by rw [subgroupOf_map_subtype, inf_of_le_left hAH]
  refine ⟨S.map H.subtype, ?_, ?_, ?_⟩
  · rw [← hSA]
    exact map_mono inf_le_right
  · rw [← hSA, relIndex_map_map_of_injective _ _ H.subtype_injective, hS, inf_relIndex_right,
      relIndex_comap]
  · rw [← hSmap, linFix_map_u3ConjLin]

theorem linFix_map_subgroupOf {A : Subgroup G} (hAH : A ≤ H) :
    linFix ((A.subgroupOf H).map (u3ConjLin V H hH)) =
      subOf V (centralizer (A : Set G)) := by
  rw [linFix_map_u3ConjLin, subgroupOf_map_subtype, inf_of_le_left hAH]

end Conj

section Conjugate

theorem commutator_eq_bot_iff_commute {H₁ H₂ : Subgroup G} :
    ⁅H₁, H₂⁆ = ⊥ ↔ ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x := by
  rw [commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h x hx y hy
    exact (mem_centralizer_iff.1 (h hx) y hy).symm
  · intro h x hx
    exact mem_centralizer_iff.2 fun y hy => (h x hx y hy).symm

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H :=
  SteinbergBS.mem_conjugate_iff

theorem card_conjugate (V : Subgroup G) (g : G) : Nat.card (CFSG.conjugate V g) = Nat.card V :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isElementaryAbelian_conjugate (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G) :
    IsElementaryAbelian 2 (CFSG.conjugate V g) :=
  IsElementaryAbelian.map _

theorem conjugate_TI {V : Subgroup G}
    (hTI : ∀ x : G, V ⊓ CFSG.conjugate V x = ⊥ ∨ CFSG.conjugate V x = V) (g : G) :
    ∀ x : G, CFSG.conjugate V g ⊓ CFSG.conjugate (CFSG.conjugate V g) x = ⊥ ∨
      CFSG.conjugate (CFSG.conjugate V g) x = CFSG.conjugate V g := by
  intro x
  have hcc : ∀ (K : Subgroup G) (a b : G),
      CFSG.conjugate (CFSG.conjugate K a) b = CFSG.conjugate K (a * b) := fun K a b => by
    rw [SteinbergBS.conjugate_mul]
  rw [hcc]
  rcases hTI (g * x * g⁻¹) with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
    rw [mem_conjugate_iff'] at hy1 hy2
    have hmem : g * y * g⁻¹ ∈ V ⊓ CFSG.conjugate V (g * x * g⁻¹) := by
      refine ⟨hy1, mem_conjugate_iff'.2 ?_⟩
      rwa [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * x * y * (g * x)⁻¹ by group]
    rw [h, mem_bot] at hmem
    rw [mem_bot]
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [hmem]; group
  · right
    rw [show g * x = g * x * g⁻¹ * g by group, ← hcc, h]

theorem conj_mem_conjugate_iff {H : Subgroup G} {g y : G} :
    g⁻¹ * y * g ∈ CFSG.conjugate H g ↔ y ∈ H := by
  rw [mem_conjugate_iff', show g * (g⁻¹ * y * g) * g⁻¹ = y by group]

end Conjugate

theorem exists_relIndex_eq_two_pow {A W : Subgroup G} (hAW : A ≤ W) {n : ℕ}
    (hW : Nat.card W = 2 ^ n) : ∃ k ≤ n, A.relIndex W = 2 ^ k := by
  have h1 := relIndex_mul_card A W
  rw [inf_of_le_left hAW, hW] at h1
  exact (Nat.dvd_prime_pow Nat.prime_two).1 ⟨_, h1.symm⟩

theorem card_mul_relIndex {A W : Subgroup G} (hAW : A ≤ W) :
    Nat.card A * A.relIndex W = Nat.card W := by
  have h1 := relIndex_mul_card A W
  rw [inf_of_le_left hAW] at h1
  rw [mul_comm, h1]

end CFSG.Quasithin.H13.U3
