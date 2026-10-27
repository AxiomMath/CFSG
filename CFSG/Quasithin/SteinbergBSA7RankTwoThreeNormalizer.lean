module

public import CFSG.LocalAnalysis.SteinbergBVA7BinaryIsometryTwoParts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergBS

open Module Subgroup CFSG.LocalAnalysis.SteinbergBV

namespace RankTwoThree

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_eq_self (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem sub_eq_add (v w : V) : v - w = v + w := by
  rw [sub_eq_add_neg, neg_eq_self]

theorem zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

theorem zmod_two_add_self (z : ZMod 2) : z + z = 0 := by
  revert z
  decide

section Decomposition

variable (b : V ≃ₗ[ZMod 2] V)

theorem mem_ker_sub_id_iff {v : V} :
    v ∈ LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) ↔ b v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

theorem mem_range_sub_id_iff {v : V} :
    v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) ↔ ∃ w, b w + w = v := by
  rw [LinearMap.mem_range]
  refine exists_congr fun w => ?_
  rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_add]
  rfl

variable {b}

theorem apply_apply_apply (hb3 : b ^ 3 = 1) (v : V) : b (b (b v)) = v := by
  have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) hb3
  simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply] at h
  exact h

theorem apply_mem_range (v : V)
    (hv : v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) :
    b v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  obtain ⟨w, rfl⟩ := (mem_range_sub_id_iff b).1 hv
  exact (mem_range_sub_id_iff b).2 ⟨b w, by rw [map_add]⟩

theorem isCompl_range_ker (hb3 : b ^ 3 = 1) :
    IsCompl (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
      (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.eq_bot_iff]
    rintro v ⟨hvU, hvC⟩
    obtain ⟨w, rfl⟩ := (mem_range_sub_id_iff b).1 hvU
    have hfix : b (b w + w) = b w + w := (mem_ker_sub_id_iff b).1 hvC
    rw [map_add] at hfix
    have h1 : b (b w) = w := add_right_cancel (hfix.trans (add_comm _ _))
    have h2 : b w = w := by
      have := congrArg b h1
      rw [apply_apply_apply hb3] at this
      exact this.symm
    rw [h2, add_self_eq_zero]
  · rw [Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_sup]
    refine ⟨b (b v) + b v, (mem_range_sub_id_iff b).2 ⟨b v, rfl⟩, b (b v) + b v + v,
      (mem_ker_sub_id_iff b).2 ?_, ?_⟩
    · rw [map_add, map_add, apply_apply_apply hb3]
      abel
    · rw [← add_assoc, add_self_eq_zero (b (b v) + b v), zero_add]

theorem zpow_apply_of_apply_eq {v : V} (hv : b v = v) (k : ℤ) : (b ^ k) v = v := by
  induction k using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [add_comm, zpow_one_add, LinearEquiv.mul_apply, ih, hv]
  | pred i ih =>
    have hv' : b⁻¹ v = v := by
      calc b⁻¹ v = b⁻¹ (b v) := by rw [hv]
        _ = v := b.symm_apply_apply v
    rw [zpow_sub_one, LinearEquiv.mul_apply, hv', ih]

theorem zpow_apply_add_mem (k : ℤ) (y : V) :
    (b ^ k) y + y ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  induction k using Int.induction_on generalizing y with
  | zero => exact (mem_range_sub_id_iff b).2 ⟨0, by simp [add_self_eq_zero]⟩
  | succ i ih =>
    rw [add_comm (i : ℤ), zpow_one_add, LinearEquiv.mul_apply,
      show b ((b ^ (i : ℤ)) y) + y = (b ((b ^ (i : ℤ)) y) + (b ^ (i : ℤ)) y) +
        ((b ^ (i : ℤ)) y + y) by
        rw [add_assoc, ← add_assoc ((b ^ (i : ℤ)) y), add_self_eq_zero, zero_add]]
    exact add_mem ((mem_range_sub_id_iff b).2 ⟨_, rfl⟩) (ih y)
  | pred i ih =>
    have hy : b (b⁻¹ y) = y := b.apply_symm_apply y
    rw [zpow_sub_one, LinearEquiv.mul_apply]
    have e : (b ^ (-(i : ℤ))) (b⁻¹ y) + y =
        ((b ^ (-(i : ℤ))) (b⁻¹ y) + b⁻¹ y) + (b (b⁻¹ y) + b⁻¹ y) := by
      rw [hy]
      calc (b ^ (-(i : ℤ))) (b⁻¹ y) + y
          = (b ^ (-(i : ℤ))) (b⁻¹ y) + y + (b⁻¹ y + b⁻¹ y) := by
            rw [add_self_eq_zero, add_zero]
        _ = ((b ^ (-(i : ℤ))) (b⁻¹ y) + b⁻¹ y) + (y + b⁻¹ y) := by abel
    rw [e]
    exact add_mem (ih _) ((mem_range_sub_id_iff b).2 ⟨_, rfl⟩)

end Decomposition

section Normalizer

theorem mem_normalizer_zpowers_of {Γ : Type*} [Group Γ] {b g : Γ} (h1 : g * b * g⁻¹ ∈ zpowers b)
    (h2 : g⁻¹ * b * g ∈ zpowers b) : g ∈ normalizer (zpowers b : Set Γ) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
    rw [← conj_zpow]
    exact zpow_mem h1 m
  · intro hh
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hh
    have : h = (g⁻¹ * b * g⁻¹⁻¹) ^ m := by
      rw [conj_zpow, hm]
      group
    rw [this, inv_inv]
    exact zpow_mem h2 m

theorem map_eq_self_iff (g : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    W.map (g : V →ₗ[ZMod 2] V) = W ↔ ∀ v, g v ∈ W ↔ v ∈ W := by
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      rwa [← g.injective hwv]
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      refine ⟨g.symm v, (h _).1 ?_, g.apply_symm_apply v⟩
      rwa [g.apply_symm_apply]

theorem ofSubmodules_zpow_apply {W : Submodule (ZMod 2) V} {e : V ≃ₗ[ZMod 2] V}
    (h : W.map (e : V →ₗ[ZMod 2] V) = W) (k : ℤ) (w : W) :
    (((e.ofSubmodules W W h) ^ k) w : V) = (e ^ k) w := by
  induction k using Int.induction_on generalizing w with
  | zero => rfl
  | succ i ih =>
    rw [add_comm (i : ℤ), zpow_one_add, zpow_one_add, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, LinearEquiv.ofSubmodules_apply, ih]
  | pred i ih =>
    rw [zpow_sub_one, zpow_sub_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    congr 1

theorem card_linearEquiv_of_finrank_eq_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 2) :
    Nat.card (W ≃ₗ[ZMod 2] W) = 6 := by
  let bW := Module.finBasisOfFinrankEq (ZMod 2) W hW
  have h1 : Nat.card (W ≃ₗ[ZMod 2] W) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' bW).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, ZMod.card]
  decide

variable {b : V ≃ₗ[ZMod 2] V}

theorem stab_of_mem_normalizer {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) :
    (∀ v, g v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) →
      v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) ∧
    (∀ v, v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) →
      g v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) ∧
    (∀ v, v ∈ LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) →
      g v ∈ LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  have hU : ∀ h ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)), ∀ v,
      v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) →
        h v ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := by
    intro h hh v hv
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 hh b).1 (mem_zpowers b))
    obtain ⟨w, rfl⟩ := (mem_range_sub_id_iff b).1 hv
    have e : h (b w) = (b ^ j) (h w) := by
      rw [hj, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      congr 2
      exact (h.symm_apply_apply w).symm
    rw [map_add, e]
    exact zpow_apply_add_mem j (h w)
  refine ⟨fun v hv => ?_, hU g hg, fun v hv => ?_⟩
  · have := hU g⁻¹ (inv_mem hg) _ hv
    rwa [show g⁻¹ (g v) = v from g.symm_apply_apply v] at this
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1
      ((mem_normalizer_iff.1 (inv_mem hg) b).1 (mem_zpowers b))
    rw [mem_ker_sub_id_iff] at hv ⊢
    have e : b (g v) = g ((b ^ k) v) := by
      rw [hk, inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      exact (g.apply_symm_apply _).symm
    rw [e, zpow_apply_of_apply_eq hv]

theorem map_inv_eq_self {g : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V}
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) : W.map ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W := by
  rw [map_eq_self_iff] at h ⊢
  intro v
  rw [← h (g⁻¹ v), show g (g⁻¹ v) = v from g.apply_symm_apply v]

variable [FiniteDimensional (ZMod 2) V]

theorem mem_normalizer_iff_map_eq (hb : orderOf b = 3)
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2)
    (g : V ≃ₗ[ZMod 2] V) :
    g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
      (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).map (g : V →ₗ[ZMod 2] V) =
          LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) ∧
        (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).map (g : V →ₗ[ZMod 2] V) =
          LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  set U := LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hU
  set C := LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hC
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  have hUC : IsCompl U C := isCompl_range_ker hb3
  have hstab : ∀ h ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)),
      U.map (h : V →ₗ[ZMod 2] V) = U ∧ C.map (h : V →ₗ[ZMod 2] V) = C := by
    intro h hh
    obtain ⟨h1, h2, h3⟩ := stab_of_mem_normalizer hh
    obtain ⟨-, -, h3'⟩ := stab_of_mem_normalizer (inv_mem hh)
    refine ⟨(map_eq_self_iff h U).2 fun v => ⟨h1 v, h2 v⟩,
      (map_eq_self_iff h C).2 fun v => ⟨fun hv => ?_, h3 v⟩⟩
    have := h3' _ hv
    rwa [show h⁻¹ (h v) = v from h.symm_apply_apply v] at this
  refine ⟨hstab g, fun ⟨hgU, hgC⟩ => ?_⟩
  have hbU : U.map (b : V →ₗ[ZMod 2] V) = U := (hstab b (le_normalizer (mem_zpowers b))).1
  have hcard : Nat.card (U ≃ₗ[ZMod 2] U) = 6 := card_linearEquiv_of_finrank_eq_two hrank
  have hbU3 : orderOf (b.ofSubmodules U U hbU) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast]
      ext w
      rw [ofSubmodules_zpow_apply hbU, zpow_natCast, hb3]
      rfl
    · intro h1
      have hUne : U ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hrank
        exact absurd hrank (by norm_num)
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
      apply hu0
      refine Submodule.disjoint_def.1 hUC.disjoint u hu ((mem_ker_sub_id_iff b).2 ?_)
      have h1' : ((b.ofSubmodules U U hbU ⟨u, hu⟩ : U) : V) = u := by
        rw [h1]
        rfl
      rwa [LinearEquiv.ofSubmodules_apply] at h1'
  have hidx : (zpowers (b.ofSubmodules U U hbU)).index = 2 := by
    have h := card_mul_index (zpowers (b.ofSubmodules U U hbU))
    rw [Nat.card_zpowers, hbU3, hcard] at h
    omega
  have hnormal := normal_of_index_eq_two hidx
  have key : ∀ h : V ≃ₗ[ZMod 2] V, U.map (h : V →ₗ[ZMod 2] V) = U →
      C.map (h : V →ₗ[ZMod 2] V) = C → h * b * h⁻¹ ∈ zpowers b := by
    intro h hhU hhC
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hnormal.conj_mem (b.ofSubmodules U U hbU)
      (mem_zpowers _) (h.ofSubmodules U U hhU))
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    ext v
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 (hUC.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, map_add]
    congr 1
    · have h1 : (((b.ofSubmodules U U hbU) ^ k) ⟨u, hu⟩ : V) = (b ^ k) u :=
        ofSubmodules_zpow_apply hbU k ⟨u, hu⟩
      have h2 : (((h.ofSubmodules U U hhU * b.ofSubmodules U U hbU *
          (h.ofSubmodules U U hhU)⁻¹) ⟨u, hu⟩ : U) : V) = h (b (h⁻¹ u)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.ofSubmodules_apply,
          LinearEquiv.ofSubmodules_apply]
        congr 2
      rw [hk] at h1
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← h2]
      exact h1.symm
    · have hc' : h⁻¹ c ∈ C := by
        have := map_inv_eq_self hhC
        exact (map_eq_self_iff _ C).1 this c |>.2 hc
      rw [zpow_apply_of_apply_eq ((mem_ker_sub_id_iff b).1 hc), LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, (mem_ker_sub_id_iff b).1 hc']
      exact (h.apply_symm_apply c).symm
  have h2 := key g⁻¹ (map_inv_eq_self hgU) (map_inv_eq_self hgC)
  rw [inv_inv] at h2
  exact mem_normalizer_zpowers_of (key g hgU hgC) h2

end Normalizer

section Restriction

@[expose] def stabPair (U C : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C}
  one_mem' := ⟨(map_eq_self_iff 1 U).2 fun _ => Iff.rfl, (map_eq_self_iff 1 C).2 fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro g h ⟨hgU, hgC⟩ ⟨hhU, hhC⟩
    rw [map_eq_self_iff] at hgU hgC hhU hhC
    exact ⟨(map_eq_self_iff _ U).2 fun v => by rw [LinearEquiv.mul_apply, hgU, hhU],
      (map_eq_self_iff _ C).2 fun v => by rw [LinearEquiv.mul_apply, hgC, hhC]⟩
  inv_mem' := by
    rintro g ⟨hgU, hgC⟩
    exact ⟨map_inv_eq_self hgU, map_inv_eq_self hgC⟩

theorem mem_stabPair {U C : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ stabPair U C ↔
      U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C :=
  Iff.rfl

@[expose] def restrictPair (U C : Submodule (ZMod 2) V) :
    stabPair U C →* (U ≃ₗ[ZMod 2] U) × (C ≃ₗ[ZMod 2] C) where
  toFun g := ((g : V ≃ₗ[ZMod 2] V).ofSubmodules U U (mem_stabPair.1 g.2).1,
    (g : V ≃ₗ[ZMod 2] V).ofSubmodules C C (mem_stabPair.1 g.2).2)
  map_one' := Prod.ext (LinearEquiv.ext fun _ => Subtype.ext rfl)
    (LinearEquiv.ext fun _ => Subtype.ext rfl)
  map_mul' _ _ := Prod.ext (LinearEquiv.ext fun _ => Subtype.ext rfl)
    (LinearEquiv.ext fun _ => Subtype.ext rfl)

theorem restrictPair_fst_apply {U C : Submodule (ZMod 2) V} (g : stabPair U C) (u : U) :
    (((restrictPair U C g).1 u : U) : V) = (g : V ≃ₗ[ZMod 2] V) u :=
  rfl

theorem restrictPair_snd_apply {U C : Submodule (ZMod 2) V} (g : stabPair U C) (c : C) :
    (((restrictPair U C g).2 c : C) : V) = (g : V ≃ₗ[ZMod 2] V) c :=
  rfl

theorem restrictPair_injective {U C : Submodule (ZMod 2) V} (hUC : IsCompl U C) :
    Function.Injective (restrictPair U C) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 (hUC.sup_eq_top ▸ Submodule.mem_top (x := v))
  have h1 := congrArg (fun e => (((e.1 ⟨u, hu⟩ : U) : V))) hg
  have h2 := congrArg (fun e => (((e.2 ⟨c, hc⟩ : C) : V))) hg
  simp only [restrictPair_fst_apply, restrictPair_snd_apply] at h1 h2
  rw [map_add, h1, h2]
  rfl

theorem restrictPair_surjective {U C : Submodule (ZMod 2) V} (hUC : IsCompl U C) :
    Function.Surjective (restrictPair U C) := by
  rintro ⟨a, c⟩
  let e := Submodule.prodEquivOfIsCompl U C hUC
  let g : V ≃ₗ[ZMod 2] V := e.symm.trans ((a.prodCongr c).trans e)
  have hgU : ∀ u : U, g u = a u := by
    intro u
    simp only [g, LinearEquiv.trans_apply, e, Submodule.prodEquivOfIsCompl_symm_apply_left,
      LinearEquiv.prodCongr_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, add_zero]
  have hgC : ∀ x : C, g x = c x := by
    intro x
    simp only [g, LinearEquiv.trans_apply, e, Submodule.prodEquivOfIsCompl_symm_apply_right,
      LinearEquiv.prodCongr_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, zero_add]
  have hmapU : U.map (g : V →ₗ[ZMod 2] V) = U := by
    refine le_antisymm ?_ fun u hu => ⟨(a.symm ⟨u, hu⟩ : U), (a.symm ⟨u, hu⟩).2, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      have := hgU ⟨u, hu⟩
      simp only at this
      change g u ∈ U
      rw [this]
      exact (a ⟨u, hu⟩).2
    · change g (a.symm ⟨u, hu⟩ : U) = u
      rw [hgU, LinearEquiv.apply_symm_apply]
  have hmapC : C.map (g : V →ₗ[ZMod 2] V) = C := by
    refine le_antisymm ?_ fun x hx => ⟨(c.symm ⟨x, hx⟩ : C), (c.symm ⟨x, hx⟩).2, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have := hgC ⟨x, hx⟩
      simp only at this
      change g x ∈ C
      rw [this]
      exact (c ⟨x, hx⟩).2
    · change g (c.symm ⟨x, hx⟩ : C) = x
      rw [hgC, LinearEquiv.apply_symm_apply]
  refine ⟨⟨g, hmapU, hmapC⟩, Prod.ext (LinearEquiv.ext fun u => Subtype.ext ?_)
    (LinearEquiv.ext fun x => Subtype.ext ?_)⟩
  · exact hgU u
  · exact hgC x

theorem exists_mulEquiv_inf_stabPair {U C : Submodule (ZMod 2) V} (hUC : IsCompl U C)
    (G : Subgroup (V ≃ₗ[ZMod 2] V)) (GC : Subgroup (C ≃ₗ[ZMod 2] C))
    (hG : ∀ g : stabPair U C, (g : V ≃ₗ[ZMod 2] V) ∈ G ↔ (restrictPair U C g).2 ∈ GC) :
    ∃ e : ↥(G ⊓ stabPair U C) ≃* (U ≃ₗ[ZMod 2] U) × GC,
      ∀ g : ↥(G ⊓ stabPair U C), (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
        ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c := by
  let ι : ↥(G ⊓ stabPair U C) →* stabPair U C := Subgroup.inclusion inf_le_right
  let φ : ↥(G ⊓ stabPair U C) →* (U ≃ₗ[ZMod 2] U) × GC :=
    ((MonoidHom.fst _ _).comp ((restrictPair U C).comp ι)).prod
      (((MonoidHom.snd _ _).comp ((restrictPair U C).comp ι)).codRestrict GC
        fun g => (hG (ι g)).1 (mem_inf.1 g.2).1)
  have hinj : Function.Injective φ := by
    intro g₁ g₂ h
    have h1 : (φ g₁).1 = (φ g₂).1 := congrArg Prod.fst h
    have h2 : ((φ g₁).2 : C ≃ₗ[ZMod 2] C) = (φ g₂).2 :=
      congrArg (fun z => (z.2 : C ≃ₗ[ZMod 2] C)) h
    have h' : restrictPair U C (ι g₁) = restrictPair U C (ι g₂) := Prod.ext h1 h2
    have h3 : ((ι g₁ : stabPair U C) : V ≃ₗ[ZMod 2] V) = (ι g₂ : stabPair U C) :=
      congrArg Subtype.val (restrictPair_injective hUC h')
    exact Subtype.ext h3
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, c⟩
    obtain ⟨g, hg⟩ := restrictPair_surjective hUC (a, (c : C ≃ₗ[ZMod 2] C))
    have hgG : (g : V ≃ₗ[ZMod 2] V) ∈ G := (hG g).2 (by rw [hg]; exact c.2)
    have hg1 : (restrictPair U C g).1 = a := congrArg Prod.fst hg
    have hg2 : (restrictPair U C g).2 = c := congrArg Prod.snd hg
    exact ⟨⟨g, mem_inf.2 ⟨hgG, g.2⟩⟩, Prod.ext hg1 (Subtype.ext hg2)⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => ⟨fun u => rfl, fun c => rfl⟩⟩

end Restriction

section Forms

open Classical in
theorem bilin_apply_eq_ite {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 2)
    {γ : LinearMap.BilinForm (ZMod 2) W} (hγ : γ.IsAlt) (hnd : γ.Nondegenerate) (x y : W) :
    γ x y = if x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hx, hy, hxy⟩ := h
    rcases zmod_two_eq_zero_or_one (γ x y) with h0 | h1
    · exfalso
      apply hx
      have hli : LinearIndependent (ZMod 2) ![x, y] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
          rcases zmod_two_eq_zero_or_one t with rfl | rfl
        · exact ⟨rfl, rfl⟩
        · rw [zero_smul, one_smul, zero_add] at hst
          exact absurd hst hy
        · rw [zero_smul, one_smul, add_zero] at hst
          exact absurd hst hx
        · rw [one_smul, one_smul] at hst
          exact absurd ((eq_neg_of_add_eq_zero_left hst).trans (neg_eq_self y)) hxy
      have hspan : Submodule.span (ZMod 2) (Set.range ![x, y]) = ⊤ :=
        hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hW])
      have hle : Submodule.span (ZMod 2) (Set.range ![x, y]) ≤ LinearMap.ker (γ x) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        fin_cases i
        · exact hγ x
        · exact h0
      exact hnd.1 x fun z => hle (hspan ▸ Submodule.mem_top)
    · exact h1
  · by_cases hx : x = 0
    · rw [hx, map_zero, LinearMap.zero_apply]
    · by_cases hy : y = 0
      · rw [hy, map_zero]
      · have hxy : x = y := by
          by_contra hxy
          exact h ⟨hx, hy, hxy⟩
        rw [hxy]
        exact hγ y

theorem mem_isometryGroup_of_finrank_eq_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 2)
    {γ : LinearMap.BilinForm (ZMod 2) W} (hγ : γ.IsAlt) (hnd : γ.Nondegenerate)
    (a : W ≃ₗ[ZMod 2] W) : a ∈ TauCeti.BilinForm.isometryGroup γ := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  rw [bilin_apply_eq_ite hW hγ hnd, bilin_apply_eq_ite hW hγ hnd]
  have hiff : (a x ≠ 0 ∧ a y ≠ 0 ∧ a x ≠ a y) ↔ (x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y) := by
    simp only [ne_eq, LinearEquiv.map_eq_zero_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h]

variable {b : V ≃ₗ[ZMod 2] V}

theorem orthogonal_range_ker {β : LinearMap.BilinForm (ZMod 2) V}
    (hb : ∀ x y, β (b x) (b y) = β x y) {u c : V}
    (hu : u ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hc : c ∈ LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) : β u c = 0 ∧ β c u = 0 := by
  obtain ⟨w, rfl⟩ := (mem_range_sub_id_iff b).1 hu
  have hc' := (mem_ker_sub_id_iff b).1 hc
  constructor
  · calc β (b w + w) c = β (b w) (b c) + β w c := by rw [hc', map_add, LinearMap.add_apply]
      _ = β w c + β w c := by rw [hb]
      _ = 0 := zmod_two_add_self _
  · calc β c (b w + w) = β (b c) (b w) + β c w := by rw [hc', map_add]
      _ = β c w + β c w := by rw [hb]
      _ = 0 := zmod_two_add_self _

theorem nondegenerate_restrict_of_isCompl {β : LinearMap.BilinForm (ZMod 2) V}
    (hnd : β.Nondegenerate) {W W' : Submodule (ZMod 2) V} (hWW' : IsCompl W W')
    (horth : ∀ w ∈ W, ∀ w' ∈ W', β w w' = 0 ∧ β w' w = 0) : (β.restrict W).Nondegenerate := by
  refine ⟨fun x hx => Subtype.ext (hnd.1 x fun v => ?_),
    fun y hy => Subtype.ext (hnd.2 y fun v => ?_)⟩
  · obtain ⟨w, hw, w', hw', rfl⟩ :=
      Submodule.mem_sup.1 (hWW'.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, (horth x x.2 w' hw').1, add_zero]
    exact hx ⟨w, hw⟩
  · obtain ⟨w, hw, w', hw', rfl⟩ :=
      Submodule.mem_sup.1 (hWW'.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, LinearMap.add_apply, (horth y y.2 w' hw').2, add_zero]
    exact hy ⟨w, hw⟩

end Forms

section Cases

theorem finite_linearEquiv (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] : Finite (W ≃ₗ[ZMod 2] W) := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) DFunLike.coe_injective

theorem factorization_six_mul {m : ℕ} (hm : m ≠ 0) :
    (6 * m).factorization 2 = 1 + m.factorization 2 := by
  rw [Nat.factorization_mul (by norm_num) hm, Finsupp.add_apply,
    show (6 : ℕ) = 2 ^ 1 * 3 by norm_num,
    BinaryTwoParts.factorization_two_pow_mul_odd (by decide : Odd 3)]

variable [FiniteDimensional (ZMod 2) V] {b : V ≃ₗ[ZMod 2] V}

theorem setup (hb : orderOf b = 3)
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2) :
    b ^ 3 = 1 ∧
      IsCompl (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
        (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) ∧
      normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) =
        stabPair (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
          (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) ∧
      finrank (ZMod 2) (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) =
        finrank (ZMod 2) V - 2 := by
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  have hUC := isCompl_range_ker hb3
  refine ⟨hb3, hUC, ?_, ?_⟩
  · ext g
    exact mem_normalizer_iff_map_eq hb hrank g
  · have := Submodule.finrank_add_eq_of_isCompl hUC
    omega

theorem normalizer_linear {d : ℕ} (hd : finrank (ZMod 2) V = d) (hb : orderOf b = 3)
    {U C : Submodule (ZMod 2) V}
    (hU : U = LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hC : C = LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hrank : finrank (ZMod 2) U = 2) :
    IsCompl U C ∧
      (∀ g : V ≃ₗ[ZMod 2] V, g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
        U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C) ∧
      (∃ e : normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ≃*
          (U ≃ₗ[ZMod 2] U) × (C ≃ₗ[ZMod 2] C),
        ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
          ∀ c : C, ((e g).2 c : V) = (g : V ≃ₗ[ZMod 2] V) c) ∧
      Nat.card (U ≃ₗ[ZMod 2] U) = 6 ∧
      ordProj[2] (Nat.card (normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) =
        2 ^ (1 + (d - 2) * (d - 3) / 2) ∧
      (3 ≤ d → ∀ S : Sylow 2 (V ≃ₗ[ZMod 2] V),
        ¬ (S : Subgroup (V ≃ₗ[ZMod 2] V)) ≤ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) := by
  subst hU hC
  obtain ⟨-, hUC, hN, hdC⟩ := setup hb hrank
  have := finite_linearEquiv V
  have := finite_linearEquiv (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
  let e := (MulEquiv.subgroupCongr hN).trans (MulEquiv.ofBijective _
    ⟨restrictPair_injective hUC, restrictPair_surjective hUC⟩)
  have hcard6 := card_linearEquiv_of_finrank_eq_two hrank
  have hfC : (Nat.card (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) ≃ₗ[ZMod 2]
      LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))).factorization 2 =
      (d - 2) * (d - 3) / 2 := by
    have h := (binary_linear_and_form_isometry_group_two_parts (hdC.trans (by rw [hd]))).1
    rw [show d - 2 - 1 = d - 3 by omega] at h
    exact Nat.pow_right_injective le_rfl h
  have hfN : (Nat.card (normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))).factorization 2 =
      1 + (d - 2) * (d - 3) / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcard6, factorization_six_mul Nat.card_pos.ne',
      hfC]
  refine ⟨hUC, fun g => mem_normalizer_iff_map_eq hb hrank g, ⟨e, fun g => ⟨fun u => rfl,
    fun c => rfl⟩⟩, hcard6, by rw [hfN], fun hd3 S hS => ?_⟩
  have hSV : Nat.card (S : Subgroup (V ≃ₗ[ZMod 2] V)) = 2 ^ (d * (d - 1) / 2) := by
    rw [Sylow.card_eq_multiplicity]
    exact (binary_linear_and_form_isometry_group_two_parts hd).1
  have hdvd := card_dvd_of_le hS
  rw [hSV] at hdvd
  have hle := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hfN] at hle
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
  rw [show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega,
    show k + 3 - 1 = k + 2 by omega,
    show (k + 3) * (k + 2) = (k + 1) * k + 2 * (2 * k + 3) by ring,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)] at hle
  generalize (k + 1) * k / 2 = t at hle
  omega

theorem symplectic_facts {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.IsAlt)
    (hnd : β.Nondegenerate) (hbiso : ∀ x y, β (b x) (b y) = β x y) (hb3 : b ^ 3 = 1)
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2) :
    (∀ u ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id),
        ∀ c ∈ LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id), β u c = 0 ∧ β c u = 0) ∧
      (β.restrict (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))).Nondegenerate ∧
      (β.restrict (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))).Nondegenerate ∧
      (∀ a : LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) ≃ₗ[ZMod 2]
          LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id),
        a ∈ TauCeti.BilinForm.isometryGroup
          (β.restrict (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)))) ∧
      ∀ g : stabPair (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
          (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)),
        (g : V ≃ₗ[ZMod 2] V) ∈ TauCeti.BilinForm.isometryGroup β ↔
          (restrictPair _ _ g).2 ∈ TauCeti.BilinForm.isometryGroup
            (β.restrict (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))) := by
  set U := LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hU
  set C := LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hC
  have hUC : IsCompl U C := isCompl_range_ker hb3
  have horth : ∀ u ∈ U, ∀ c ∈ C, β u c = 0 ∧ β c u = 0 :=
    fun u hu c hc => orthogonal_range_ker hbiso hu hc
  have hndU := nondegenerate_restrict_of_isCompl hnd hUC horth
  have hndC := nondegenerate_restrict_of_isCompl hnd hUC.symm fun c hc u hu =>
    (horth u hu c hc).symm
  have hβU : (β.restrict U).IsAlt := fun x => hβ x
  have hGLU : ∀ a : U ≃ₗ[ZMod 2] U, a ∈ TauCeti.BilinForm.isometryGroup (β.restrict U) :=
    mem_isometryGroup_of_finrank_eq_two hrank hβU hndU
  refine ⟨horth, hndU, hndC, hGLU, fun g => ?_⟩
  rw [TauCeti.BilinForm.mem_isometryGroup_iff, TauCeti.BilinForm.mem_isometryGroup_iff]
  have hgU : ∀ u ∈ U, (g : V ≃ₗ[ZMod 2] V) u ∈ U := fun u hu =>
    ((map_eq_self_iff _ U).1 (mem_stabPair.1 g.2).1 u).2 hu
  have hgC : ∀ c ∈ C, (g : V ≃ₗ[ZMod 2] V) c ∈ C := fun c hc =>
    ((map_eq_self_iff _ C).1 (mem_stabPair.1 g.2).2 c).2 hc
  constructor
  · intro h x y
    exact h x y
  · intro h v w
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 (hUC.sup_eq_top ▸ Submodule.mem_top (x := v))
    obtain ⟨u', hu', c', hc', rfl⟩ :=
      Submodule.mem_sup.1 (hUC.sup_eq_top ▸ Submodule.mem_top (x := w))
    have hUiso : β ((g : V ≃ₗ[ZMod 2] V) u) ((g : V ≃ₗ[ZMod 2] V) u') = β u u' :=
      TauCeti.BilinForm.mem_isometryGroup_iff.1 (hGLU (restrictPair U C g).1) ⟨u, hu⟩ ⟨u', hu'⟩
    have hCiso : β ((g : V ≃ₗ[ZMod 2] V) c) ((g : V ≃ₗ[ZMod 2] V) c') = β c c' :=
      h ⟨c, hc⟩ ⟨c', hc'⟩
    simp only [map_add, LinearMap.add_apply]
    rw [(horth _ (hgU u hu) _ (hgC c' hc')).1, (horth _ (hgU u' hu') _ (hgC c hc)).2,
      (horth u hu c' hc').1, (horth u' hu' c hc).2, hUiso, hCiso]

theorem normalizer_symplectic {n : ℕ} (hd : finrank (ZMod 2) V = 2 * n)
    {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (hbG : b ∈ TauCeti.BilinForm.isometryGroup β) (hb : orderOf b = 3)
    {U C : Submodule (ZMod 2) V}
    (hU : U = LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hC : C = LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hrank : finrank (ZMod 2) U = 2) :
    IsCompl U C ∧ (∀ u ∈ U, ∀ c ∈ C, β u c = 0 ∧ β c u = 0) ∧
      (β.restrict U).Nondegenerate ∧ (β.restrict C).Nondegenerate ∧
      (∀ g ∈ TauCeti.BilinForm.isometryGroup β,
        g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
          U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C) ∧
      (∀ a : U ≃ₗ[ZMod 2] U, a ∈ TauCeti.BilinForm.isometryGroup (β.restrict U)) ∧
      (∃ e : ↥(TauCeti.BilinForm.isometryGroup β ⊓
            normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) ≃*
          (U ≃ₗ[ZMod 2] U) × TauCeti.BilinForm.isometryGroup (β.restrict C),
        ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
          ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c) ∧
      Nat.card (U ≃ₗ[ZMod 2] U) = 6 ∧
      ordProj[2] (Nat.card ↥(TauCeti.BilinForm.isometryGroup β ⊓
        normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) = 2 ^ (1 + (n - 1) ^ 2) ∧
      (2 ≤ n → ∀ S : Sylow 2 (TauCeti.BilinForm.isometryGroup β),
        ¬ (S : Subgroup (TauCeti.BilinForm.isometryGroup β)).map
            (TauCeti.BilinForm.isometryGroup β).subtype ≤
          TauCeti.BilinForm.isometryGroup β ⊓ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) := by
  subst hU hC
  obtain ⟨hb3, hUC, hN, hdC⟩ := setup hb hrank
  set U := LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hU
  set C := LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hC
  have := finite_linearEquiv V
  have := finite_linearEquiv C
  have hbiso := TauCeti.BilinForm.mem_isometryGroup_iff.1 hbG
  obtain ⟨horth, hndU, hndC, hGLU, hG⟩ := symplectic_facts hβ hnd hbiso hb3 hrank
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_inf_stabPair hUC _ _ hG
  have hN' : TauCeti.BilinForm.isometryGroup β ⊓ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) =
      TauCeti.BilinForm.isometryGroup β ⊓ stabPair U C := by
    rw [hN]
  let e := (MulEquiv.subgroupCongr hN').trans e₀
  have he : ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
      ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c :=
    fun g => he₀ (MulEquiv.subgroupCongr hN' g)
  have hcard6 := card_linearEquiv_of_finrank_eq_two hrank
  have hdC' : finrank (ZMod 2) C = 2 * (n - 1) := by
    rw [hdC, hd]
    omega
  have hfC : (Nat.card (TauCeti.BilinForm.isometryGroup (β.restrict C))).factorization 2 =
      (n - 1) ^ 2 :=
    Nat.pow_right_injective le_rfl
      ((binary_linear_and_form_isometry_group_two_parts hdC').2.1 (n - 1) rfl _ (fun x => hβ x)
        hndC)
  have hfN : (Nat.card ↥(TauCeti.BilinForm.isometryGroup β ⊓
      normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))).factorization 2 = 1 + (n - 1) ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcard6,
      factorization_six_mul Nat.card_pos.ne', hfC]
  refine ⟨hUC, horth, hndU, hndC, fun g _ => mem_normalizer_iff_map_eq hb hrank g, hGLU,
    ⟨e, he⟩, hcard6, by rw [hfN], fun hn S hS => ?_⟩
  have hSV : Nat.card (S : Subgroup (TauCeti.BilinForm.isometryGroup β)) = 2 ^ (n ^ 2) := by
    rw [Sylow.card_eq_multiplicity]
    exact (binary_linear_and_form_isometry_group_two_parts hd).2.1 n rfl β hβ hnd
  have hdvd := card_dvd_of_le hS
  rw [card_map_of_injective (TauCeti.BilinForm.isometryGroup β).subtype_injective, hSV] at hdvd
  have hle := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hfN] at hle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega] at hle
  nlinarith

omit [FiniteDimensional (ZMod 2) V] in
theorem quadratic_add (q : QuadraticForm (ZMod 2) V) (x y : V) :
    q (x + y) = q x + q y + QuadraticMap.polar q x y := by
  rw [QuadraticMap.polar]
  ring

theorem orthogonal_facts {q : QuadraticForm (ZMod 2) V}
    (hq : (QuadraticMap.polarBilin q).Nondegenerate) (hbq : ∀ x, q (b x) = q x) (hb3 : b ^ 3 = 1)
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2) :
    (QuadraticMap.polarBilin q).IsAlt ∧
      (∀ x y, QuadraticMap.polarBilin q (b x) (b y) = QuadraticMap.polarBilin q x y) ∧
      (∀ u ∈ LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id), u ≠ 0 → q u = 1) ∧
      (∀ a : LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) ≃ₗ[ZMod 2]
          LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id),
        a ∈ TauCeti.QuadraticMap.orthogonalGroup
          (q.comp (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).subtype)) ∧
      QuadraticMap.polarBilin
          (q.comp (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).subtype) =
        LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q)
          (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) ∧
      ∀ g : stabPair (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
          (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)),
        (g : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup q ↔
          (restrictPair _ _ g).2 ∈ TauCeti.QuadraticMap.orthogonalGroup
            (q.comp (LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id)).subtype) := by
  set U := LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hU
  set C := LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hC
  have hUC : IsCompl U C := isCompl_range_ker hb3
  have halt : (QuadraticMap.polarBilin q).IsAlt := fun x => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      zmod_two_add_self]
  have hbiso : ∀ x y, QuadraticMap.polarBilin q (b x) (b y) = QuadraticMap.polarBilin q x y := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar, QuadraticMap.polar, ← map_add, hbq, hbq, hbq]
  obtain ⟨horth, hndU, -, -, -⟩ := symplectic_facts halt hq hbiso hb3 hrank
  have haltU : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) U).IsAlt := fun x => halt x
  have haniso : ∀ u ∈ U, u ≠ 0 → q u = 1 := by
    intro u hu hu0
    have hbu : b u ∈ U := apply_mem_range u hu
    have hbu0 : b u ≠ 0 := fun h => hu0 ((LinearEquiv.map_eq_zero_iff b).1 h)
    have hbuu : b u ≠ u := fun h =>
      hu0 (Submodule.disjoint_def.1 hUC.disjoint u hu ((mem_ker_sub_id_iff b).2 h))
    have hsum : u + b u = b (b u) := by
      obtain ⟨w, hw⟩ := (mem_range_sub_id_iff b).1 hu
      rw [← hw, map_add, map_add, apply_apply_apply hb3]
      calc b w + w + (b (b w) + b w) = w + b (b w) + (b w + b w) := by abel
        _ = w + b (b w) := by rw [add_self_eq_zero, add_zero]
    have h1 :
        LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) U ⟨u, hu⟩ ⟨b u, hbu⟩ = 1 := by
      rw [bilin_apply_eq_ite hrank haltU hndU]
      refine ite_eq_left ⟨fun h => hu0 (congrArg Subtype.val h),
        fun h => hbu0 (congrArg Subtype.val h), fun h => hbuu (congrArg Subtype.val h).symm⟩
    have h2 : q u = QuadraticMap.polar q u (b u) := by
      rw [QuadraticMap.polar, hsum, hbq, hbq]
      generalize q u = z
      revert z
      decide
    rw [h2]
    exact h1
  have hGLq : ∀ a : U ≃ₗ[ZMod 2] U,
      a ∈ TauCeti.QuadraticMap.orthogonalGroup (q.comp U.subtype) := by
    intro a
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    change q (a x) = q x
    by_cases hx : x = 0
    · rw [hx, map_zero]
    · have hax : (a x : V) ≠ 0 := fun h => hx ((LinearEquiv.map_eq_zero_iff a).1 (Subtype.ext h))
      rw [haniso _ (a x).2 hax, haniso _ x.2 fun h => hx (Subtype.ext h)]
  have hpolC : QuadraticMap.polarBilin (q.comp C.subtype) =
      LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) C :=
    LinearMap.ext₂ fun _ _ => rfl
  refine ⟨halt, hbiso, haniso, hGLq, hpolC, fun g => ?_⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  have hgU : ∀ u ∈ U, (g : V ≃ₗ[ZMod 2] V) u ∈ U := fun u hu =>
    ((map_eq_self_iff _ U).1 (mem_stabPair.1 g.2).1 u).2 hu
  have hgC : ∀ c ∈ C, (g : V ≃ₗ[ZMod 2] V) c ∈ C := fun c hc =>
    ((map_eq_self_iff _ C).1 (mem_stabPair.1 g.2).2 c).2 hc
  constructor
  · intro h x
    exact h x
  · intro h v
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 (hUC.sup_eq_top ▸ Submodule.mem_top (x := v))
    have hUq : q ((g : V ≃ₗ[ZMod 2] V) u) = q u :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (hGLq (restrictPair U C g).1) ⟨u, hu⟩
    have hCq : q ((g : V ≃ₗ[ZMod 2] V) c) = q c := h ⟨c, hc⟩
    have h1 : QuadraticMap.polar q ((g : V ≃ₗ[ZMod 2] V) u) ((g : V ≃ₗ[ZMod 2] V) c) = 0 :=
      (horth _ (hgU u hu) _ (hgC c hc)).1
    have h2 : QuadraticMap.polar q u c = 0 := (horth u hu c hc).1
    rw [map_add, quadratic_add, quadratic_add, hUq, hCq, h1, h2]

theorem normalizer_orthogonal {n : ℕ} (hn : 2 ≤ n) (hd : finrank (ZMod 2) V = 2 * n)
    {q : QuadraticForm (ZMod 2) V} (hq : (QuadraticMap.polarBilin q).Nondegenerate)
    (hbG : b ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hb : orderOf b = 3)
    {U C : Submodule (ZMod 2) V}
    (hU : U = LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hC : C = LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hrank : finrank (ZMod 2) U = 2) :
    IsCompl U C ∧
      (∀ u ∈ U, ∀ c ∈ C,
        QuadraticMap.polarBilin q u c = 0 ∧ QuadraticMap.polarBilin q c u = 0) ∧
      (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) U).Nondegenerate ∧
      (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) C).Nondegenerate ∧
      (∀ u ∈ U, u ≠ 0 → q u = 1) ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup q,
        g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
          U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C) ∧
      (∀ a : U ≃ₗ[ZMod 2] U, a ∈ TauCeti.QuadraticMap.orthogonalGroup (q.comp U.subtype)) ∧
      (QuadraticMap.polarBilin (q.comp C.subtype)).Nondegenerate ∧
      (∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup q ⊓
            normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) ≃*
          (U ≃ₗ[ZMod 2] U) × TauCeti.QuadraticMap.orthogonalGroup (q.comp C.subtype),
        ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
          ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c) ∧
      Nat.card (U ≃ₗ[ZMod 2] U) = 6 ∧
      ordProj[2] (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup q ⊓
        normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) = 2 ^ ((n - 1) * (n - 2) + 2) ∧
      ∀ S : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup q),
        ¬ (S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)).map
            (TauCeti.QuadraticMap.orthogonalGroup q).subtype ≤
          TauCeti.QuadraticMap.orthogonalGroup q ⊓
            normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) := by
  subst hU hC
  obtain ⟨hb3, hUC, hN, hdC⟩ := setup hb hrank
  set U := LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hU
  set C := LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) with hC
  have := finite_linearEquiv V
  have := finite_linearEquiv C
  have hbq := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hbG
  obtain ⟨halt, hbiso, haniso, hGLq, hpolC, hG⟩ := orthogonal_facts hq hbq hb3 hrank
  obtain ⟨horth, hndU, hndC, -, -⟩ := symplectic_facts halt hq hbiso hb3 hrank
  have hndC' : (QuadraticMap.polarBilin (q.comp C.subtype)).Nondegenerate := by
    rw [hpolC]
    exact hndC
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_inf_stabPair hUC _ _ hG
  have hN' : TauCeti.QuadraticMap.orthogonalGroup q ⊓
      normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) =
      TauCeti.QuadraticMap.orthogonalGroup q ⊓ stabPair U C := by
    rw [hN]
  let e := (MulEquiv.subgroupCongr hN').trans e₀
  have he : ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
      ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c :=
    fun g => he₀ (MulEquiv.subgroupCongr hN' g)
  have hcard6 := card_linearEquiv_of_finrank_eq_two hrank
  have hdC' : finrank (ZMod 2) C = 2 * (n - 1) := by
    rw [hdC, hd]
    omega
  have hfC : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q.comp C.subtype))).factorization 2 =
      (n - 1) * (n - 2) + 1 := by
    have h := (binary_linear_and_form_isometry_group_two_parts hdC').2.2 (n - 1) (by omega) rfl
      _ hndC'
    rw [show n - 1 - 1 = n - 2 by omega] at h
    exact Nat.pow_right_injective le_rfl h
  have hfN : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup q ⊓
      normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))).factorization 2 =
        (n - 1) * (n - 2) + 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcard6,
      factorization_six_mul Nat.card_pos.ne', hfC]
    omega
  refine ⟨hUC, horth, hndU, hndC, haniso, fun g _ => mem_normalizer_iff_map_eq hb hrank g, hGLq,
    hndC', ⟨e, he⟩, hcard6, by rw [hfN], fun S hS => ?_⟩
  have hSV : Nat.card (S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)) =
      2 ^ (n * (n - 1) + 1) := by
    rw [Sylow.card_eq_multiplicity]
    exact (binary_linear_and_form_isometry_group_two_parts hd).2.2 n (by omega) rfl q hq
  have hdvd := card_dvd_of_le hS
  rw [card_map_of_injective (TauCeti.QuadraticMap.orthogonalGroup q).subtype_injective,
    hSV] at hdvd
  have hle := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hfN] at hle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at hle
  nlinarith

end Cases

end RankTwoThree

open RankTwoThree

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem rank_two_three_subgroup_classical_normalizer_obstruction {b : V ≃ₗ[ZMod 2] V}
    (hb : orderOf b = 3) {U C : Submodule (ZMod 2) V}
    (hU : U = LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hC : C = LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id))
    (hrank : finrank (ZMod 2) U = 2) :
    (∀ d : ℕ, finrank (ZMod 2) V = d →
      IsCompl U C ∧
        (∀ g : V ≃ₗ[ZMod 2] V, g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
          U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C) ∧
        (∃ e : normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ≃*
            (U ≃ₗ[ZMod 2] U) × (C ≃ₗ[ZMod 2] C),
          ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
            ∀ c : C, ((e g).2 c : V) = (g : V ≃ₗ[ZMod 2] V) c) ∧
        Nat.card (U ≃ₗ[ZMod 2] U) = 6 ∧
        ordProj[2] (Nat.card (normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) =
          2 ^ (1 + (d - 2) * (d - 3) / 2) ∧
        (3 ≤ d → ∀ S : Sylow 2 (V ≃ₗ[ZMod 2] V),
          ¬ (S : Subgroup (V ≃ₗ[ZMod 2] V)) ≤
            normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) ∧
    (∀ (n : ℕ) (β : LinearMap.BilinForm (ZMod 2) V), finrank (ZMod 2) V = 2 * n → β.IsAlt →
      β.Nondegenerate → b ∈ TauCeti.BilinForm.isometryGroup β →
      IsCompl U C ∧ (∀ u ∈ U, ∀ c ∈ C, β u c = 0 ∧ β c u = 0) ∧
        (β.restrict U).Nondegenerate ∧ (β.restrict C).Nondegenerate ∧
        (∀ g ∈ TauCeti.BilinForm.isometryGroup β,
          g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
            U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C) ∧
        (∀ a : U ≃ₗ[ZMod 2] U, a ∈ TauCeti.BilinForm.isometryGroup (β.restrict U)) ∧
        (∃ e : ↥(TauCeti.BilinForm.isometryGroup β ⊓
              normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) ≃*
            (U ≃ₗ[ZMod 2] U) × TauCeti.BilinForm.isometryGroup (β.restrict C),
          ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
            ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c) ∧
        Nat.card (U ≃ₗ[ZMod 2] U) = 6 ∧
        ordProj[2] (Nat.card ↥(TauCeti.BilinForm.isometryGroup β ⊓
          normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) = 2 ^ (1 + (n - 1) ^ 2) ∧
        (2 ≤ n → ∀ S : Sylow 2 (TauCeti.BilinForm.isometryGroup β),
          ¬ (S : Subgroup (TauCeti.BilinForm.isometryGroup β)).map
              (TauCeti.BilinForm.isometryGroup β).subtype ≤
            TauCeti.BilinForm.isometryGroup β ⊓
              normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) ∧
    ∀ (n : ℕ) (q : QuadraticForm (ZMod 2) V), 2 ≤ n → finrank (ZMod 2) V = 2 * n →
      (QuadraticMap.polarBilin q).Nondegenerate → b ∈ TauCeti.QuadraticMap.orthogonalGroup q →
      IsCompl U C ∧
        (∀ u ∈ U, ∀ c ∈ C,
          QuadraticMap.polarBilin q u c = 0 ∧ QuadraticMap.polarBilin q c u = 0) ∧
        (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) U).Nondegenerate ∧
        (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin q) C).Nondegenerate ∧
        (∀ u ∈ U, u ≠ 0 → q u = 1) ∧
        (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup q,
          g ∈ normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) ↔
            U.map (g : V →ₗ[ZMod 2] V) = U ∧ C.map (g : V →ₗ[ZMod 2] V) = C) ∧
        (∀ a : U ≃ₗ[ZMod 2] U,
          a ∈ TauCeti.QuadraticMap.orthogonalGroup (q.comp U.subtype)) ∧
        (QuadraticMap.polarBilin (q.comp C.subtype)).Nondegenerate ∧
        (∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup q ⊓
              normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V))) ≃*
            (U ≃ₗ[ZMod 2] U) × TauCeti.QuadraticMap.orthogonalGroup (q.comp C.subtype),
          ∀ g, (∀ u : U, ((e g).1 u : V) = (g : V ≃ₗ[ZMod 2] V) u) ∧
            ∀ c : C, (((e g).2 : C ≃ₗ[ZMod 2] C) c : V) = (g : V ≃ₗ[ZMod 2] V) c) ∧
        Nat.card (U ≃ₗ[ZMod 2] U) = 6 ∧
        ordProj[2] (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup q ⊓
          normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)))) = 2 ^ ((n - 1) * (n - 2) + 2) ∧
        ∀ S : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup q),
          ¬ (S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)).map
              (TauCeti.QuadraticMap.orthogonalGroup q).subtype ≤
            TauCeti.QuadraticMap.orthogonalGroup q ⊓
              normalizer (zpowers b : Set (V ≃ₗ[ZMod 2] V)) :=
  ⟨fun _ hd => normalizer_linear hd hb hU hC hrank,
    fun _ _ hd hβ hnd hbG => normalizer_symplectic hd hβ hnd hbG hb hU hC hrank,
    fun _ _ hn hd hq hbG => normalizer_orthogonal hn hd hq hbG hb hU hC hrank⟩

end CFSG.Quasithin.SteinbergBS
