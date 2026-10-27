module

public import CFSG.RankThree.CentralLiftU.UnitaryLift
public import CFSG.RankThree.CentralLiftU.CoxeterC
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherReducedWord

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm isLinePerm_one
  isLinePerm_signedPerm signedPermGroup_le sl2W)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (simpleRefl simpleRefl_mem)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (weylPerm_one weylPerm_mul
  weylPerm_lineCoord isLinePerm_torus)
open CFSG.LieType.Universal.SpecialLinear (signedPerm)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r ε : ℕ}

section Mono

variable (r ε)

theorem lineCoord_injective : Function.Injective (lineCoord (r := r) (ε := ε)) := by
  rintro (x | x) (y | y) hxy <;> simp_all [lineCoord]

theorem weylPerm_injective : Function.Injective (weylPerm (r := r) (ε := ε)) := by
  intro w w' hw
  refine Equiv.ext fun x => lineCoord_injective r ε ?_
  rw [← weylPerm_lineCoord, ← weylPerm_lineCoord, hw]

variable {r ε}

theorem weylPerm_inv (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    weylPerm (ε := ε) w⁻¹ = (weylPerm w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← weylPerm_mul, inv_mul_cancel, weylPerm_one]

variable (r ε)

@[expose] def hypMono : Subgroup (hypSU h r ε) where
  carrier := {g | ∃ w ∈ hypWeyl r, IsLinePerm (weylPerm (ε := ε) w)
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)}
  mul_mem' := by
    rintro g g' ⟨w, hw, hg⟩ ⟨w', hw', hg'⟩
    refine ⟨w * w', mul_mem hw hw', ?_⟩
    rw [weylPerm_mul, Subgroup.coe_mul, Units.val_mul]
    exact hg.mul hg'
  one_mem' := ⟨1, one_mem _, by
    rw [weylPerm_one, Subgroup.coe_one, Units.val_one]
    exact isLinePerm_one⟩
  inv_mem' := by
    rintro g ⟨w, hw, hg⟩
    refine ⟨w⁻¹, inv_mem hw, ?_⟩
    rw [weylPerm_inv, Subgroup.coe_inv]
    exact hg.inv

variable {r ε}

theorem mem_hypMono_iff {g : hypSU h r ε} : g ∈ hypMono h r ε ↔ ∃ w ∈ hypWeyl r,
    IsLinePerm (weylPerm (ε := ε) w)
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  Iff.rfl

@[expose] noncomputable def monoW (g : hypMono h r ε) : Equiv.Perm (Fin r ⊕ Fin r) :=
  ((mem_hypMono_iff h).1 g.2).choose

theorem monoW_mem (g : hypMono h r ε) : monoW h g ∈ hypWeyl r :=
  ((mem_hypMono_iff h).1 g.2).choose_spec.1

theorem isLinePerm_monoW (g : hypMono h r ε) :
    IsLinePerm (weylPerm (ε := ε) (monoW h g))
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  ((mem_hypMono_iff h).1 g.2).choose_spec.2

theorem monoW_eq {g : hypMono h r ε} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : IsLinePerm (weylPerm (ε := ε) w)
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    monoW h g = w :=
  weylPerm_injective r ε ((isLinePerm_monoW h g).unique hw)

variable (r ε)

@[expose] noncomputable def monoWeyl : hypMono h r ε →* hypWeyl r where
  toFun g := ⟨monoW h g, monoW_mem h g⟩
  map_one' := Subtype.ext (monoW_eq h (w := 1) (by
    rw [weylPerm_one]
    exact isLinePerm_one))
  map_mul' g g' := Subtype.ext (monoW_eq h (w := monoW h g * monoW h g') (by
    rw [weylPerm_mul]
    exact (isLinePerm_monoW h g).mul (isLinePerm_monoW h g')))

variable {r ε}

theorem isLinePerm_monoWeyl (g : hypMono h r ε) :
    IsLinePerm (weylPerm (ε := ε) (monoWeyl h r ε g : Equiv.Perm (Fin r ⊕ Fin r)))
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  isLinePerm_monoW h g

theorem monoWeyl_eq {g : hypMono h r ε} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : IsLinePerm (weylPerm (ε := ε) w)
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    (monoWeyl h r ε g : Equiv.Perm (Fin r ⊕ Fin r)) = w :=
  monoW_eq h hw

end Mono

section Lines

theorem weylPerm_sumCongr_swap (i j : Fin r) :
    weylPerm (ε := ε) (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) = swapIdx i j := by
  ext x
  rcases x with x | k | x
  · rw [weylPerm_inl, swapIdx_inl]
    rfl
  · rw [weylPerm_inr_inl, swapIdx_z]
  · rw [weylPerm_inr_inr, swapIdx_inr]
    rfl

theorem weylPerm_swap_inl_inr (k : Fin r) :
    weylPerm (ε := ε) (Equiv.swap (Sum.inl k) (Sum.inr k)) =
      Equiv.swap (.inl k) (.inr (.inr k)) := by
  ext x
  rcases x with x | l | x
  · rw [weylPerm_inl]
    by_cases hx : x = k
    · subst hx
      simp [lineCoord]
    · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hx) (by simp),
        Equiv.swap_apply_of_ne_of_ne (by simpa using hx) (by simp)]
      rfl
  · rw [weylPerm_inr_inl, Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
  · rw [weylPerm_inr_inr]
    by_cases hx : x = k
    · subst hx
      simp [lineCoord]
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hx),
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hx)]
      rfl

theorem iotaWSign_ne_zero {c : K} (hc0 : c ≠ 0) (k : Fin r) (x : HypIndex r ε) :
    iotaWSign c k x ≠ 0 := by
  rcases x with x | l | x <;> simp only [iotaWSign] <;> (try split_ifs) <;> simp [hc0]

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem isLinePerm_pi_vIota (k : Fin r) :
    IsLinePerm (weylPerm (ε := ε) (Equiv.swap (Sum.inl k) (Sum.inr k)))
      (((π (vIota h π hc hc0 k) : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  rw [pi_vIota h hS hc hc0, coe_iotaU_sl2W, weylPerm_swap_inl_inr]
  exact isLinePerm_signedPerm _ (iotaWSign_ne_zero hc0 k)

theorem isLinePerm_pi_sLift (i : Fin r) :
    IsLinePerm (weylPerm (ε := ε) (simpleRefl r i))
      (((π (sLift h π hc hc0 i) : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  by_cases hi : i.val + 1 < r
  · rw [sLift_of_lt h π hc hc0 hi, pi_vRho h hS, coe_rhoU_sl2W, simpleRefl, dite_eq_left hi,
      weylPerm_sumCongr_swap]
    exact isLinePerm_signedPerm _ (wSignU_ne_zero _)
  · rw [sLift_of_not_lt h π hc hc0 hi, simpleRefl, dite_eq_right hi]
    exact isLinePerm_pi_vIota h hS hc hc0 i

end Lines

section Core

variable {R : Type*} [Group R] (π : R →* hypSU h r ε) {c : K} (hc : c ∈ h.traceZero)
  (hc0 : c ≠ 0)

structure TorusHyp (H : Subgroup R) : Prop where
  diag : H ≤ (hypTorus h r ε).comap π
  rho : ∀ (i j : Fin r) (hij : i ≠ j) (t : Kˣ), hRho h π hij t ∈ H
  iota : ∀ (k : Fin r) (b : h.fixedFieldˣ), hIota h π hc hc0 k b ∈ H

@[expose] noncomputable def liftWeylU (H : Subgroup R) : Subgroup R :=
  Subgroup.closure ((H : Set R) ∪ Set.range (sLift h π hc hc0))

theorem le_liftWeylU (H : Subgroup R) : H ≤ liftWeylU h π hc hc0 H :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem sLift_mem_liftWeylU (H : Subgroup R) (i : Fin r) :
    sLift h π hc hc0 i ∈ liftWeylU h π hc hc0 H :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

end Core

section Normalizer

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {H : Subgroup R} (hT : TorusHyp h π hc hc0 H)
include hS hT

theorem sLift_conj_mem (i : Fin r) {y : R} (hy : y ∈ H) :
    sLift h π hc hc0 i * y * (sLift h π hc hc0 i)⁻¹ ∈ H := by
  obtain ⟨a, d, -, -, hm⟩ := hT.diag hy
  by_cases hi : i.val + 1 < r
  · rw [sLift_of_lt h π hc hc0 hi, vRho_conj_of_diag h hS hm]
    exact mul_mem (hT.rho _ _ _ _) hy
  · rw [sLift_of_not_lt h π hc hc0 hi, vIota_conj_of_diag h hS hc hc0 hm]
    exact mul_mem (hT.iota _ _) hy

omit hS [Finite R] in
theorem sLift_mul_self_mem (i : Fin r) : sLift h π hc hc0 i * sLift h π hc hc0 i ∈ H := by
  by_cases hi : i.val + 1 < r
  · rw [sLift_of_lt h π hc hc0 hi, vRho_mul_self]
    exact hT.rho _ _ _ _
  · rw [sLift_of_not_lt h π hc hc0 hi, vIota_mul_self]
    exact hT.iota _ _

theorem sLift_mem_normalizer (i : Fin r) :
    sLift h π hc hc0 i ∈ Subgroup.normalizer (H : Set R) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨sLift_conj_mem h hS hc hc0 hT i, fun hy => ?_⟩
  have h2 := sLift_mul_self_mem h hc hc0 hT i
  have e : y = (sLift h π hc hc0 i * sLift h π hc hc0 i)⁻¹ *
      (sLift h π hc hc0 i * (sLift h π hc hc0 i * y * (sLift h π hc hc0 i)⁻¹) *
        (sLift h π hc hc0 i)⁻¹) * (sLift h π hc hc0 i * sLift h π hc hc0 i) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem h2) (sLift_conj_mem h hS hc hc0 hT i hy)) h2

theorem liftWeylU_le_normalizer : liftWeylU h π hc hc0 H ≤ Subgroup.normalizer (H : Set R) := by
  rw [liftWeylU, Subgroup.closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  · exact Subgroup.le_normalizer hx
  · exact sLift_mem_normalizer h hS hc hc0 hT i

theorem normal_subgroupOf_liftWeylU : (H.subgroupOf (liftWeylU h π hc hc0 H)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_liftWeylU h π hc hc0 H)).2
    (liftWeylU_le_normalizer h hS hc hc0 hT)

omit hT in
theorem vIota_mem_liftWeylU (k : Fin r) : vIota h π hc hc0 k ∈ liftWeylU h π hc hc0 H := by
  have hk := k.isLt
  suffices hm : ∀ m : ℕ, ∀ i : Fin r, i.val + m + 1 = r →
      vIota h π hc hc0 i ∈ liftWeylU h π hc hc0 H from hm (r - 1 - k.val) k (by omega)
  intro m
  induction m with
  | zero =>
    intro i hi
    rw [← sLift_of_not_lt h π hc hc0 (by omega)]
    exact sLift_mem_liftWeylU h π hc hc0 H i
  | succ m ih =>
    intro i hi
    have hlt : i.val + 1 < r := by omega
    rw [← vRho_conj_vIota h hS hc hc0 (ne_succ_of_lt hlt)]
    have hs := sLift_mem_liftWeylU h π hc hc0 H i
    rw [sLift_of_lt h π hc hc0 hlt] at hs
    exact mul_mem (mul_mem hs (ih ⟨i.val + 1, hlt⟩ (by simp only; omega))) (inv_mem hs)

theorem pi_mem_hypMono {n : R} (hn : n ∈ liftWeylU h π hc hc0 H) : π n ∈ hypMono h r ε := by
  have hle : liftWeylU h π hc hc0 H ≤ (hypMono h r ε).comap π := by
    rw [liftWeylU, Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · exact ⟨1, one_mem _, isLinePerm_torus (hT.diag hx)⟩
    · exact ⟨simpleRefl r i, simpleRefl_mem i, isLinePerm_pi_sLift h hS hc hc0 i⟩
  exact hle hn

end Normalizer

section WeylHom

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {H : Subgroup R} (hT : TorusHyp h π hc hc0 H)

@[expose] noncomputable def weylHomU : liftWeylU h π hc hc0 H →* hypWeyl r :=
  (monoWeyl h r ε).comp (((π.comp (liftWeylU h π hc hc0 H).subtype)).codRestrict
    (hypMono h r ε) fun n => pi_mem_hypMono h hS hc hc0 hT n.2)

theorem isLinePerm_weylHomU (n : liftWeylU h π hc hc0 H) :
    IsLinePerm (weylPerm (ε := ε) (weylHomU h hS hc hc0 hT n : Equiv.Perm (Fin r ⊕ Fin r)))
      (((π n : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  isLinePerm_monoWeyl h _

theorem weylHomU_eq {n : liftWeylU h π hc hc0 H} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : IsLinePerm (weylPerm (ε := ε) w)
      (((π n : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    (weylHomU h hS hc hc0 hT n : Equiv.Perm (Fin r ⊕ Fin r)) = w :=
  monoWeyl_eq h hw

theorem weylHomU_sLift (i : Fin r) :
    (weylHomU h hS hc hc0 hT ⟨sLift h π hc hc0 i, sLift_mem_liftWeylU h π hc hc0 H i⟩ :
      Equiv.Perm (Fin r ⊕ Fin r)) = simpleRefl r i :=
  weylHomU_eq h hS hc hc0 hT (isLinePerm_pi_sLift h hS hc hc0 i)

theorem weylHomU_vIota (k : Fin r) :
    (weylHomU h hS hc hc0 hT ⟨vIota h π hc hc0 k, vIota_mem_liftWeylU h hS hc hc0 k⟩ :
      Equiv.Perm (Fin r ⊕ Fin r)) = Equiv.swap (Sum.inl k) (Sum.inr k) :=
  weylHomU_eq h hS hc hc0 hT (isLinePerm_pi_vIota h hS hc hc0 k)

theorem le_ker_weylHomU :
    H.subgroupOf (liftWeylU h π hc hc0 H) ≤ (weylHomU h hS hc hc0 hT).ker := fun _ hn =>
  Subtype.ext (weylHomU_eq h hS hc hc0 hT (isLinePerm_torus (hT.diag
    (Subgroup.mem_subgroupOf.1 hn))))

theorem weylHomU_surjective : Function.Surjective (weylHomU h hS hc hc0 hT) := by
  rintro ⟨σ, hσ⟩
  have hle : hypWeyl r ≤ (weylHomU h hS hc hc0 hT).range.map (hypWeyl r).subtype :=
    signedPermGroup_le
      (fun i => ⟨_, ⟨⟨vIota h π hc hc0 i, vIota_mem_liftWeylU h hS hc hc0 i⟩, rfl⟩,
        weylHomU_vIota h hS hc hc0 hT i⟩)
      (fun i hi => ⟨_, ⟨⟨sLift h π hc hc0 i, sLift_mem_liftWeylU h π hc hc0 H i⟩, rfl⟩, by
        rw [Subgroup.coe_subtype, weylHomU_sLift, simpleRefl, dite_eq_left hi]⟩)
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hle hσ
  exact ⟨n, Subtype.ext hn⟩

end WeylHom

section Kernel

variable {R : Type*} [Group R] {N H : Subgroup R}

theorem qmk_congr {x y : R} (hx : x ∈ N) (hy : y ∈ N) (hxy : x = y) :
    (QuotientGroup.mk ⟨x, hx⟩ : N ⧸ H.subgroupOf N) = QuotientGroup.mk ⟨y, hy⟩ := by
  subst hxy
  rfl

theorem qmk_eq_iff {x y : R} (hx : x ∈ N) (hy : y ∈ N) :
    (QuotientGroup.mk ⟨x, hx⟩ : N ⧸ H.subgroupOf N) = QuotientGroup.mk ⟨y, hy⟩ ↔
      x⁻¹ * y ∈ H := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

variable [(H.subgroupOf N).Normal]

theorem qmk_mul {x y : R} (hx : x ∈ N) (hy : y ∈ N) :
    (QuotientGroup.mk ⟨x, hx⟩ : N ⧸ H.subgroupOf N) * QuotientGroup.mk ⟨y, hy⟩ =
      QuotientGroup.mk ⟨x * y, mul_mem hx hy⟩ :=
  rfl

theorem qmk_eq_one_iff {x : R} (hx : x ∈ N) :
    (QuotientGroup.mk ⟨x, hx⟩ : N ⧸ H.subgroupOf N) = 1 ↔ x ∈ H := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

end Kernel

section Coxeter

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {H : Subgroup R} (hT : TorusHyp h π hc hc0 H)
include hS hT

theorem sLift_braid {i j : Fin r} (hij : i.val + 1 = j.val) (hj : j.val + 1 < r) :
    (sLift h π hc hc0 j * sLift h π hc hc0 i * sLift h π hc hc0 j)⁻¹ *
      (sLift h π hc hc0 i * sLift h π hc hc0 j * sLift h π hc hc0 i) ∈ H := by
  have hi : i.val + 1 < r := by omega
  obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
  rw [sLift_of_lt h π hc hc0 hi, sLift_of_lt h π hc hc0 hj]
  set j : Fin r := ⟨i.val + 1, hi⟩
  set l : Fin r := ⟨j.val + 1, hj⟩
  have hil : i ≠ l := Fin.ne_of_val_ne (by simp only [l, j]; omega)
  set A := vRho h π (ne_succ_of_lt hi)
  set B := vRho h π (ne_succ_of_lt hj)
  set C := vRho h π hil
  have e1 : B * A * B = C * (B * B) := by
    calc B * A * B = (B * A * B⁻¹) * (B * B) := by group
      _ = C * (B * B) := by
        rw [vRho_conj_vRho_right h hS (ne_succ_of_lt hi) (ne_succ_of_lt hj) hil]
  have e2 : A * B * A = C⁻¹ * (A * A) := by
    calc A * B * A = (A * B * A⁻¹) * (A * A) := by group
      _ = C⁻¹ * (A * A) := by
        rw [vRho_conj_vRho_left h hS (ne_succ_of_lt hi) (ne_succ_of_lt hj) hil]
  have e3 : (B * A * B)⁻¹ * (A * B * A) = (B * B)⁻¹ * (C * C)⁻¹ * (A * A) := by
    rw [e1, e2]
    group
  rw [e3, vRho_mul_self, vRho_mul_self, vRho_mul_self]
  exact mul_mem (mul_mem (inv_mem (hT.rho _ _ _ _)) (inv_mem (hT.rho _ _ _ _))) (hT.rho _ _ _ _)

omit hT in
theorem sLift_commute {i j : Fin r} (hij : i.val + 1 < j.val) :
    sLift h π hc hc0 i * sLift h π hc hc0 j = sLift h π hc hc0 j * sLift h π hc hc0 i := by
  have hi : i.val + 1 < r := by omega
  rw [sLift_of_lt h π hc hc0 hi]
  by_cases hj : j.val + 1 < r
  · rw [sLift_of_lt h π hc hc0 hj]
    exact (commute_vRho_vRho h hS _ _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega)) (Fin.ne_of_val_ne (by simp only; omega))
      (Fin.ne_of_val_ne (by simp only; omega))).eq
  · rw [sLift_of_not_lt h π hc hc0 hj]
    exact (commute_vRho_vIota h hS hc hc0 _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega))).eq

theorem sLift_long {i j : Fin r} (hij : i.val + 1 = j.val) (hj : ¬j.val + 1 < r) :
    (sLift h π hc hc0 i * sLift h π hc hc0 j * sLift h π hc hc0 i)⁻¹ * vIota h π hc hc0 i ∈ H := by
  have hi : i.val + 1 < r := by omega
  obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
  rw [sLift_of_lt h π hc hc0 hi, sLift_of_not_lt h π hc hc0 hj]
  have e0 := vRho_conj_vIota h hS hc hc0 (ne_succ_of_lt hi)
  have e : (vRho h π (ne_succ_of_lt hi) * vIota h π hc hc0 ⟨i.val + 1, hi⟩ *
      vRho h π (ne_succ_of_lt hi))⁻¹ * vIota h π hc hc0 i =
      (vRho h π (ne_succ_of_lt hi) * vRho h π (ne_succ_of_lt hi))⁻¹ := by
    rw [← e0]
    group
  rw [e, vRho_mul_self]
  exact inv_mem (hT.rho _ _ _ _)

theorem ker_weylHomU_le :
    (weylHomU h hS hc hc0 hT).ker ≤ H.subgroupOf (liftWeylU h π hc hc0 H) := by
  have := normal_subgroupOf_liftWeylU h hS hc hc0 hT
  set N := liftWeylU h π hc hc0 H
  let q : Fin r → N ⧸ H.subgroupOf N := fun i =>
    QuotientGroup.mk ⟨sLift h π hc hc0 i, sLift_mem_liftWeylU h π hc hc0 H i⟩
  let ψ : N ⧸ H.subgroupOf N →* hypWeyl r :=
    QuotientGroup.lift _ (weylHomU h hS hc hc0 hT) (le_ker_weylHomU h hS hc hc0 hT)
  have hvmem := fun k => vIota_mem_liftWeylU (H := H) h hS hc hc0 k
  have hgen : Subgroup.closure (Set.range q) = ⊤ := by
    have key : ∀ x (hx : x ∈ N),
        (QuotientGroup.mk ⟨x, hx⟩ : N ⧸ H.subgroupOf N) ∈ Subgroup.closure (Set.range q) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨i, rfl⟩
        · have h1 := (qmk_eq_one_iff (N := N) (H := H)
            (Subgroup.subset_closure (Or.inl hx) : x ∈ N)).2 hx
          exact (congrArg (fun z => z ∈ Subgroup.closure (Set.range q)) h1).mpr (one_mem _)
        · exact Subgroup.subset_closure ⟨i, rfl⟩
      | one => exact one_mem _
      | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
      | inv x hx ihx => exact inv_mem ihx
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective z
    exact key x hx
  have hsq : ∀ i, q i * q i = 1 := fun i => by
    rw [qmk_mul, qmk_eq_one_iff]
    exact sLift_mul_self_mem h hc hc0 hT i
  have hbraid : ∀ i j : Fin r, i.val + 1 = j.val → j.val + 1 < r →
      q j * q i * q j = q i * q j * q i := fun i j hij hj => by
    simp only [q, qmk_mul]
    exact (qmk_eq_iff _ _).2 (sLift_braid h hS hc hc0 hT hij hj)
  have hfar : ∀ i j : Fin r, i.val + 1 < j.val → q i * q j = q j * q i := fun i j hij => by
    simp only [q, qmk_mul]
    exact qmk_congr _ _ (sLift_commute h hS hc hc0 hij)
  have hlong : ∀ i j : Fin r, i.val + 1 = j.val → ¬j.val + 1 < r →
      q i * q j * q i * (q i * q j * q i) = 1 ∧
        q i * q j * q i * q j = q j * (q i * q j * q i) := fun i j hij hj => by
    have ht : q i * q j * q i = QuotientGroup.mk ⟨vIota h π hc hc0 i, hvmem i⟩ := by
      simp only [q, qmk_mul]
      exact (qmk_eq_iff _ _).2 (sLift_long h hS hc hc0 hT hij hj)
    have hji : j ≠ i := Fin.ne_of_val_ne (by omega)
    rw [ht]
    constructor
    · rw [qmk_mul, qmk_eq_one_iff, vIota_mul_self]
      exact hT.iota _ _
    · simp only [q, qmk_mul]
      refine qmk_congr _ _ ?_
      rw [sLift_of_not_lt h π hc hc0 hj]
      exact (commute_vIota_vIota h hS hc hc0 hji.symm).eq
  have hψ : ∀ i, (ψ (q i) : Equiv.Perm (Fin r ⊕ Fin r)) = simpleRefl r i := fun i =>
    weylHomU_sLift h hS hc hc0 hT i
  have hinj := injective_of_coxeterC hgen hsq hbraid hfar hlong ψ hψ
  intro n hn
  have h1 : ψ (QuotientGroup.mk n) = 1 := hn
  exact (QuotientGroup.eq_one_iff n).1 (hinj (h1.trans (map_one ψ).symm))

theorem ker_weylHomU :
    (weylHomU h hS hc hc0 hT).ker = H.subgroupOf (liftWeylU h π hc hc0 H) :=
  le_antisymm (ker_weylHomU_le h hS hc hc0 hT) (le_ker_weylHomU h hS hc hc0 hT)

theorem injective_pi_liftWeylU (hinj : Set.InjOn π H) :
    Function.Injective (π.comp (liftWeylU h π hc hc0 H).subtype) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hn' : π n = 1 := hn
  have hw : weylHomU h hS hc hc0 hT n = 1 := Subtype.ext (weylHomU_eq h hS hc hc0 hT (w := 1) (by
    rw [hn', weylPerm_one, Subgroup.coe_one, Units.val_one]
    exact isLinePerm_one))
  have hH : (n : R) ∈ H := Subgroup.mem_subgroupOf.1 (ker_weylHomU_le h hS hc hc0 hT hw)
  exact Subtype.ext (hinj hH (one_mem H) (hn'.trans (map_one π).symm))

@[expose] noncomputable def weylQuotEquivU [(H.subgroupOf (liftWeylU h π hc hc0 H)).Normal] :
    liftWeylU h π hc hc0 H ⧸ H.subgroupOf (liftWeylU h π hc hc0 H) ≃* hypWeyl r :=
  (QuotientGroup.quotientMulEquivOfEq (ker_weylHomU h hS hc hc0 hT).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (weylHomU_surjective h hS hc hc0 hT))

theorem weylQuotEquivU_mk [(H.subgroupOf (liftWeylU h π hc hc0 H)).Normal]
    (n : liftWeylU h π hc hc0 H) :
    weylQuotEquivU h hS hc hc0 hT n = weylHomU h hS hc hc0 hT n :=
  rfl

end Coxeter

end CFSG.RankThree.CentralLiftU
