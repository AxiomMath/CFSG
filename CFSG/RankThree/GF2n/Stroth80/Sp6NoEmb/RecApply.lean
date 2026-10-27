module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Rec
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Slot
public import Mathlib.RepresentationTheory.Invariants
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Pattern
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open Representation CFSG.Open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
open CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor frobTensor_isIrreducible
  frobTensor_empty_apply dElt finrank_frobTensor tensorRep_apply tmatE twistMat twistMat_dElt)

variable {K : Type} [Field K]

@[expose] def trivLabel : Fin 3 → Finset ℕ := fun _ => ∅

@[expose] def slotLabel (s : Fin 3) (A : Finset ℕ) : Fin 3 → Finset ℕ :=
  fun t => if t = s then A else ∅

theorem slotLabel_self (s : Fin 3) (A : Finset ℕ) : slotLabel s A s = A := if_pos rfl

theorem slotLabel_of_ne {s t : Fin 3} (h : t ≠ s) (A : Finset ℕ) : slotLabel s A t = ∅ :=
  if_neg h

theorem isLabel_trivLabel {n : ℕ} : IsLabel n trivLabel := fun _ i hi =>
  absurd hi (Finset.notMem_empty i)

theorem isLabel_slotLabel {n : ℕ} {A : Finset ℕ} (hA : ∀ i ∈ A, i < n) (s : Fin 3) :
    IsLabel n (slotLabel s A) := by
  intro t i hi
  by_cases h : t = s
  · subst h
    rw [slotLabel_self] at hi
    exact hA i hi
  · rw [slotLabel_of_ne h] at hi
    exact absurd hi (Finset.notMem_empty i)

theorem slotLabel_ne_trivLabel {A : Finset ℕ} (hA : A.Nonempty) (s : Fin 3) :
    slotLabel s A ≠ trivLabel := by
  intro h
  have := congrFun h s
  rw [slotLabel_self] at this
  exact hA.ne_empty this

theorem slotLabel_inj {A : Finset ℕ} (hA : A.Nonempty) {s t : Fin 3}
    (h : slotLabel s A = slotLabel t A) : s = t := by
  by_contra hst
  have := congrFun h s
  rw [slotLabel_self, slotLabel_of_ne hst] at this
  exact hA.ne_empty this

theorem sum_labels_slot_pattern {n b t : ℕ} (hb : b < n) (p : (Fin 3 → Finset ℕ) → ℕ)
    (hp : ∀ J, IsLabel n J → p J =
      (if J = trivLabel then t else 0) + ∑ s : Fin 3, if J = slotLabel s {b} then 1 else 0)
    (φ : (Fin 3 → Finset ℕ) → ℕ) :
    ∑ J ∈ labels n, p J * φ J = t * φ trivLabel + ∑ s : Fin 3, φ (slotLabel s {b}) := by
  have hb' : ∀ i ∈ ({b} : Finset ℕ), i < n := fun i hi => (Finset.mem_singleton.mp hi) ▸ hb
  rw [Finset.sum_congr rfl fun J hJ => by rw [hp J (mem_labels.mp hJ)]]
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  congr 1
  · rw [Finset.sum_ite_eq' (labels n) trivLabel, if_pos (mem_labels.mpr isLabel_trivLabel)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_ite_eq' (labels n) (slotLabel s {b}),
      if_pos (mem_labels.mpr (isLabel_slotLabel hb' s))]

variable [CharP K 2]

theorem frobTensor_eq_one_of_eq_empty {A : Finset ℕ} (h : A = ∅) (g : SL(2, K)) :
    frobTensor K K A g = 1 := by
  subst h
  exact LinearMap.ext fun v => frobTensor_empty_apply g v

theorem cubeRep_slot_eq_one {J : Fin 3 → Finset ℕ} {s : Fin 3} (h : J s = ∅) (g : SL(2, K)) :
    cubeRep K J (slot K s g) = 1 := by
  have h1 : ∀ t, frobTensor K K (J t) (slot K s g t) = 1 := by
    intro t
    by_cases ht : t = s
    · subst ht
      rw [slot_apply_self]
      exact frobTensor_eq_one_of_eq_empty h g
    · rw [slot_apply_of_ne ht, map_one]
  rw [cubeRep_apply, h1 0, h1 1, h1 2, TensorProduct.map_one, TensorProduct.map_one]

theorem slotEmb_injective (J : Fin 3 → Finset ℕ) (s : Fin 3) :
    Function.Injective (slotEmb (K := K) J s) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  fin_cases s
  · exact tmul_ne_zero_of_ne_zero hne (tmul_ne_zero_of_ne_zero (e0_ne_zero _) (e0_ne_zero _)) hx
  · exact tmul_ne_zero_of_ne_zero (e0_ne_zero _) (tmul_ne_zero_of_ne_zero hne (e0_ne_zero _)) hx
  · exact tmul_ne_zero_of_ne_zero (e0_ne_zero _) (tmul_ne_zero_of_ne_zero (e0_ne_zero _) hne) hx

theorem slotEmb_bijective {J : Fin 3 → Finset ℕ} {s : Fin 3} (h : ∀ t, t ≠ s → J t = ∅) :
    Function.Bijective (slotEmb (K := K) J s) := by
  refine ⟨slotEmb_injective J s, ?_⟩
  have hdim : finrank K ((J s → Fin 2) → K) = finrank K (CubeSpace K J) := by
    rw [finrank_frobTensor, finrank_cubeRep]
    fin_cases s
    · simp [h 1 (by decide), h 2 (by decide)]
    · simp [h 0 (by decide), h 2 (by decide)]
    · simp [h 0 (by decide), h 1 (by decide)]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (slotEmb_injective J s)

@[expose] noncomputable def slotEquiv {J : Fin 3 → Finset ℕ} {s : Fin 3}
    (h : ∀ t, t ≠ s → J t = ∅) : (frobTensor K K (J s)).Equiv ((cubeRep K J).comp (slot K s)) :=
  Representation.Equiv.mk (LinearEquiv.ofBijective (slotEmb J s) (slotEmb_bijective h))
    fun g => LinearMap.ext fun x => slotEmb_comm J s g x

theorem slotLabel_other {s : Fin 3} (A : Finset ℕ) : ∀ t, t ≠ s → slotLabel s A t = ∅ :=
  fun _ ht => slotLabel_of_ne ht A

section Invariants

variable {Γ : Type} [Group Γ] [Fintype Γ] [Invertible (Fintype.card Γ : K)]
  {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

omit [CharP K 2] in
theorem averageMap_eq_smul_sum (ρ : Representation K Γ V) (v : V) :
    ρ.averageMap v = ⅟(Fintype.card Γ : K) • ∑ g, ρ g v := by
  rw [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
  simp [Representation.asAlgebraHom_of]

omit [CharP K 2] in
theorem quotient_averageMap_mk (ρ : Representation K Γ V) (U : Subrepresentation ρ) (v : V) :
    U.quotient.averageMap (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ.averageMap v) := by
  rw [averageMap_eq_smul_sum, averageMap_eq_smul_sum]
  change _ = U.toSubmodule.mkQ (⅟(Fintype.card Γ : K) • ∑ g, ρ g v)
  rw [map_smul, map_sum]
  rfl

omit [CharP K 2] in
theorem finrank_invariants_congr {ρ : Representation K Γ V} {σ : Representation K Γ W}
    (e : ρ.Equiv σ) : finrank K ρ.invariants = finrank K σ.invariants := by
  have hmap : ρ.invariants.map e.toLinearEquiv.toLinearMap = σ.invariants := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      have h1 : e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v) :=
        LinearMap.congr_fun (e.isIntertwining' g) v
      change σ g (e.toLinearEquiv v) = e.toLinearEquiv v
      rw [← h1, hv g]
    · intro hw
      refine ⟨e.toLinearEquiv.symm w, fun g => ?_, e.toLinearEquiv.apply_symm_apply w⟩
      apply e.toLinearEquiv.injective
      have h1 : e.toLinearEquiv (ρ g (e.toLinearEquiv.symm w)) =
          σ g (e.toLinearEquiv (e.toLinearEquiv.symm w)) :=
        LinearMap.congr_fun (e.isIntertwining' g) (e.toLinearEquiv.symm w)
      rw [h1, LinearEquiv.apply_symm_apply]
      exact hw g
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e.toLinearEquiv _).symm

omit [CharP K 2] in
theorem finrank_invariants_eq_add [Module.Finite K V] (ρ : Representation K Γ V)
    (U : Subrepresentation ρ) :
    finrank K ρ.invariants =
      finrank K U.toRepresentation.invariants + finrank K U.quotient.invariants := by
  let π : ρ.invariants →ₗ[K] U.quotient.invariants :=
    { toFun := fun v => ⟨Submodule.Quotient.mk (v : V), fun g => by
        change Submodule.Quotient.mk (ρ g v) = Submodule.Quotient.mk (v : V)
        rw [v.2 g]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨⟨ρ.averageMap y, ρ.averageMap_invariant y⟩, Subtype.ext ?_⟩
    change Submodule.Quotient.mk (ρ.averageMap y) = Submodule.Quotient.mk y
    rw [← quotient_averageMap_mk, U.quotient.averageMap_id _ hx]
  have h1 : (LinearMap.ker π).map ρ.invariants.subtype = ρ.invariants ⊓ U.toSubmodule := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      have : Submodule.Quotient.mk (u : V) = (0 : V ⧸ U.toSubmodule) :=
        congrArg Subtype.val (LinearMap.mem_ker.mp hu)
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    · rintro ⟨hv, hvU⟩
      refine ⟨⟨v, hv⟩, LinearMap.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).mpr hvU
  have h2 : U.toRepresentation.invariants.map U.toSubmodule.subtype =
      ρ.invariants ⊓ U.toSubmodule := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨fun g => congrArg Subtype.val (hw g), w.2⟩
    · rintro ⟨hv, hvU⟩
      exact ⟨⟨v, hvU⟩, fun g => Subtype.ext (hv g), rfl⟩
  have hker : finrank K (LinearMap.ker π) = finrank K U.toRepresentation.invariants := by
    rw [← Submodule.finrank_map_subtype_eq ρ.invariants (LinearMap.ker π), h1, ← h2,
      Submodule.finrank_map_subtype_eq]
  have := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at this
  omega

end Invariants

section Comp

variable {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module K V]

omit [CharP K 2] in
@[expose] def subComp {ρ : Representation K G V} (U : Subrepresentation ρ) (α : G' →* G) :
    Subrepresentation (ρ.comp α) where
  toSubmodule := U.toSubmodule
  apply_mem_toSubmodule g _ hv := U.apply_mem_toSubmodule (α g) hv

omit [CharP K 2] in
@[expose] def equivComp {W : Type} [AddCommGroup W] [Module K W] {ρ : Representation K G V}
    {σ : Representation K G W} (e : ρ.Equiv σ) (α : G' →* G) :
    Representation.Equiv (ρ.comp α) (σ.comp α) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' (α g)

omit [CharP K 2] in
theorem nontrivCount_congr {W : Type} [AddCommGroup W] [Module K W] {ρ : Representation K G V}
    {σ : Representation K G W} (e : ρ.Equiv σ) : nontrivCount ρ = nontrivCount σ := by
  unfold nontrivCount repLength
  rw [(asModuleEquivOfEquiv e).length_eq, repMultiplicity_congr_left e]

end Comp

@[expose] noncomputable def torusOne (l : Fin 3) : Kˣ →* Cube K :=
  (slot K l).comp dEltHom

@[expose] noncomputable def torusTwo {l m : Fin 3} (hlm : l ≠ m) : Kˣ × Kˣ →* Cube K :=
  (torusOne l).noncommCoprod (torusOne m) fun _ _ => Pi.mulSingle_commute hlm _ _

theorem torusTwo_apply {l m : Fin 3} (hlm : l ≠ m) (c : Kˣ × Kˣ) :
    torusTwo hlm c = torusOne l c.1 * torusOne m c.2 := rfl

theorem torusOne_apply (l : Fin 3) (c : Kˣ) : torusOne l c = slot K l (dElt c) := rfl

variable [Fintype K] [DecidableEq K]

omit [CharP K 2] in
theorem card_units_cast [CharP K 2] {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) :
    ((Fintype.card Kˣ : ℕ) : K) = 1 := by
  rw [Fintype.card_units, hK]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n - 1 = 2 * k + 1 := ⟨2 ^ (n - 1) - 1, by
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega⟩
  rw [hk]
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add]

@[expose] noncomputable abbrev invertibleCardUnits {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (hn : 1 ≤ n) : Invertible (Fintype.card Kˣ : K) :=
  invertibleOfNonzero (by rw [card_units_cast hK hn]; exact one_ne_zero)

@[expose] noncomputable abbrev invertibleCardUnitsProd {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (hn : 1 ≤ n) : Invertible (Fintype.card (Kˣ × Kˣ) : K) :=
  invertibleOfNonzero (by
    rw [Fintype.card_prod, Nat.cast_mul, card_units_cast hK hn, mul_one]
    exact one_ne_zero)

theorem frobTensor_dElt_fixed_eq_zero (hK3 : 3 ≤ Fintype.card K) {A : Finset ℕ} {b : ℕ}
    (hA : A = {b}) {x : (A → Fin 2) → K} (hx : ∀ c : Kˣ, frobTensor K K A (dElt c) x = x) :
    x = 0 := by
  subst hA
  haveI : Unique ↥({b} : Finset ℕ) :=
    { default := ⟨b, Finset.mem_singleton_self b⟩
      uniq := fun y => Subtype.ext (Finset.mem_singleton.mp y.2) }
  have frob : ∀ z : K, z ^ 2 ^ b = 1 → z = 1 := fun z hz => by
    have : (z - 1) ^ 2 ^ b = 0 := by rw [sub_pow_char_pow, hz, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp this)
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have key : ∀ c : Kˣ, twistMat K ((default : ↥({b} : Finset ℕ)) : ℕ) (dElt c) (y default)
      (y default) = 1 := by
    intro c
    have h1 := congrFun (hx c) y
    rw [frobTensor, tensorRep_apply, Fintype.sum_eq_single y] at h1
    · simp only [tmatE, Fintype.prod_unique] at h1
      have h2 : (twistMat K ((default : ↥({b} : Finset ℕ)) : ℕ) (dElt c) (y default)
          (y default) - 1) * x y = 0 := by
        rw [sub_mul, one_mul, h1, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hy)
    · intro y' hy'
      simp only [tmatE, Fintype.prod_unique]
      have hne' : y default ≠ y' default := fun h =>
        hy' (funext fun i => by rw [Subsingleton.elim i default]; exact h.symm)
      rw [twistMat_dElt]
      revert hne'
      generalize y default = a
      generalize y' default = a'
      intro hne'
      fin_cases a <;> fin_cases a' <;> simp_all
  have hdef : ((default : ↥({b} : Finset ℕ)) : ℕ) = b :=
    Finset.mem_singleton.mp (default : ↥({b} : Finset ℕ)).2
  have hall : ∀ c : Kˣ, c = 1 := by
    intro c
    have h1 := key c
    rw [twistMat_dElt, hdef] at h1
    revert h1
    generalize y default = a
    intro h1
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Algebra.algebraMap_self, RingHom.id_apply] at h1
      exact Units.ext (frob _ h1)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Algebra.algebraMap_self, RingHom.id_apply] at h1
      have h2 : ((c⁻¹ : Kˣ) : K) = 1 := frob _ h1
      have h3 : c⁻¹ = 1 := Units.ext h2
      exact inv_eq_one.mp h3
  have hcard : Fintype.card Kˣ ≤ 1 :=
    Fintype.card_le_one_iff.mpr fun a b => (hall a).trans (hall b).symm
  rw [Fintype.card_units] at hcard
  omega

@[expose] noncomputable def fixDim {Γ : Type} [Group Γ] (α : Γ →* Cube K) {V : Type}
    [AddCommGroup V] [Module K V] (ρ : Representation K (Cube K) V) : ℕ :=
  finrank K (Representation.invariants (ρ.comp α))

theorem fixDim_eq_finrank_of_trivial {Γ : Type} [Group Γ] (α : Γ →* Cube K) {V : Type}
    [AddCommGroup V] [Module K V] (ρ : Representation K (Cube K) V) (h : ∀ g, ρ (α g) = 1) :
    fixDim α ρ = finrank K V := by
  rw [fixDim]
  have : Representation.invariants (ρ.comp α) = ⊤ := eq_top_iff.mpr fun v _ g => by
    change ρ (α g) v = v
    rw [h g]
    rfl
  rw [this, finrank_top]

theorem fixDim_torusOne_slotLabel_self (hK3 : 3 ≤ Fintype.card K) (l : Fin 3) (b : ℕ) :
    fixDim (torusOne l) (cubeRep K (slotLabel l {b})) = 0 := by
  rw [fixDim, Submodule.finrank_eq_zero]
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  let e := slotEquiv (K := K) (slotLabel_other (s := l) {b})
  have hx : ∀ c : Kˣ, frobTensor K K (slotLabel l {b} l) (dElt c) (e.toLinearEquiv.symm v) =
      e.toLinearEquiv.symm v := by
    intro c
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h1 := LinearMap.congr_fun (e.isIntertwining' (dElt c)) (e.toLinearEquiv.symm v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    change e.toLinearMap _ = v
    rw [h1]
    change cubeRep K _ (slot K l (dElt c)) (e.toLinearEquiv (e.toLinearEquiv.symm v)) = v
    rw [LinearEquiv.apply_symm_apply]
    exact hv c
  have := frobTensor_dElt_fixed_eq_zero hK3 (slotLabel_self l {b}) hx
  rw [← e.toLinearEquiv.apply_symm_apply v, this, LinearEquiv.map_zero]

theorem fixDim_torusOne_slotLabel_of_ne {l s : Fin 3} (h : l ≠ s) (b : ℕ) :
    fixDim (torusOne l) (cubeRep K (slotLabel s {b})) = 2 := by
  rw [fixDim_eq_finrank_of_trivial _ _ fun c => by
      rw [torusOne_apply]; exact cubeRep_slot_eq_one (slotLabel_of_ne h _) _,
    finrank_cubeRep]
  fin_cases s <;> fin_cases l <;> simp_all [slotLabel]

theorem fixDim_torusOne_slotLabel (hK3 : 3 ≤ Fintype.card K) (l s : Fin 3) (b : ℕ) :
    fixDim (torusOne l) (cubeRep K (slotLabel s {b})) = if s = l then 0 else 2 := by
  split_ifs with h
  · subst h
    exact fixDim_torusOne_slotLabel_self hK3 s b
  · exact fixDim_torusOne_slotLabel_of_ne (Ne.symm h) b

theorem fixDim_torusOne_triv (l : Fin 3) : fixDim (torusOne l) (cubeRep K trivLabel) = 1 := by
  rw [fixDim_eq_finrank_of_trivial _ _ fun c => by
      rw [torusOne_apply]; exact cubeRep_slot_eq_one (J := trivLabel) (s := l) rfl _,
    finrank_cubeRep]
  simp [trivLabel]

theorem fixDim_torusTwo_le {l m : Fin 3} (hlm : l ≠ m) {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    fixDim (torusTwo hlm) ρ ≤ fixDim (torusOne l) ρ ∧ fixDim (torusTwo hlm) ρ ≤ fixDim (torusOne m) ρ := by
  constructor
  · refine Submodule.finrank_mono (show Representation.invariants (ρ.comp (torusTwo hlm)) ≤
      Representation.invariants (ρ.comp (torusOne l)) from fun v hv c => ?_)
    have := hv (c, 1)
    rwa [MonoidHom.comp_apply, torusTwo_apply, map_one, mul_one] at this
  · refine Submodule.finrank_mono (show Representation.invariants (ρ.comp (torusTwo hlm)) ≤
      Representation.invariants (ρ.comp (torusOne m)) from fun v hv c => ?_)
    have := hv (1, c)
    rwa [MonoidHom.comp_apply, torusTwo_apply, map_one, one_mul] at this

theorem fixDim_torusTwo_slotLabel (hK3 : 3 ≤ Fintype.card K) {l m s : Fin 3} (hlm : l ≠ m)
    (b : ℕ) : fixDim (torusTwo hlm) (cubeRep K (slotLabel s {b})) =
      if s = l ∨ s = m then 0 else 2 := by
  split_ifs with h
  · rcases h with rfl | rfl
    · exact Nat.le_zero.mp ((fixDim_torusTwo_le hlm _).1.trans
        (fixDim_torusOne_slotLabel_self hK3 s b).le)
    · exact Nat.le_zero.mp ((fixDim_torusTwo_le hlm _).2.trans
        (fixDim_torusOne_slotLabel_self hK3 s b).le)
  · push Not at h
    rw [fixDim_eq_finrank_of_trivial _ _ fun c => ?_, finrank_cubeRep]
    · fin_cases s <;> simp [slotLabel]
    · rw [torusTwo_apply, map_mul, torusOne_apply, torusOne_apply,
        cubeRep_slot_eq_one (slotLabel_of_ne (Ne.symm h.1) _),
        cubeRep_slot_eq_one (slotLabel_of_ne (Ne.symm h.2) _), mul_one]

theorem fixDim_torusTwo_triv {l m : Fin 3} (hlm : l ≠ m) :
    fixDim (torusTwo hlm) (cubeRep K trivLabel) = 1 := by
  rw [fixDim_eq_finrank_of_trivial _ _ fun c => ?_, finrank_cubeRep]
  · simp [trivLabel]
  · rw [torusTwo_apply, map_mul, torusOne_apply, torusOne_apply,
      cubeRep_slot_eq_one (J := trivLabel) (s := l) rfl,
      cubeRep_slot_eq_one (J := trivLabel) (s := m) rfl, mul_one]

variable {n : ℕ}

theorem sum_pat_fixDim (hK : Fintype.card K = 2 ^ n) {Γ : Type} [Group Γ] [Fintype Γ]
    [Invertible (Fintype.card Γ : K)] (α : Γ →* Cube K) {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    fixDim α ρ = ∑ J ∈ labels n, pat ρ J * fixDim α (cubeRep K J) :=
  sum_pat hK (fun {V} _ _ _ ρ => fixDim α ρ)
    (fun {V} _ _ _ ρ hsub => by
      haveI := hsub
      exact finrank_zero_of_subsingleton)
    (fun {V W} _ _ _ _ _ _ ρ σ e => finrank_invariants_congr (equivComp e α))
    (fun {V} _ _ _ ρ U => finrank_invariants_eq_add (ρ.comp α) (subComp U α))
    ρ

theorem sum_pat_nontrivCount (hK : Fintype.card K = 2 ^ n) (s : Fin 3) {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    nontrivCount (ρ.comp (slot K s)) =
      ∑ J ∈ labels n, pat ρ J * nontrivCount ((cubeRep K J).comp (slot K s)) :=
  sum_pat hK (fun {V} _ _ _ ρ => nontrivCount (ρ.comp (slot K s)))
    (fun {V} _ _ _ ρ hsub => by
      haveI := hsub
      exact nontrivCount_of_subsingleton _)
    (fun {V W} _ _ _ _ _ _ ρ σ e => nontrivCount_congr (equivComp e (slot K s)))
    (fun {V} _ _ _ ρ U => nontrivCount_sub_quot (ρ.comp (slot K s)) (subComp U (slot K s)))
    ρ

theorem sum_pat_trivMult (hK : Fintype.card K = 2 ^ n) (s : Fin 3) {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    repMultiplicity (ρ.comp (slot K s)) (Representation.trivial K SL(2, K) K) =
      ∑ J ∈ labels n, pat ρ J *
        repMultiplicity ((cubeRep K J).comp (slot K s)) (Representation.trivial K SL(2, K) K) :=
  sum_pat hK (fun {V} _ _ _ ρ =>
      repMultiplicity (ρ.comp (slot K s)) (Representation.trivial K SL(2, K) K))
    (fun {V} _ _ _ ρ hsub => by
      haveI := hsub
      have : Subsingleton (Representation.asModule (ρ.comp (slot K s))) :=
        inferInstanceAs (Subsingleton V)
      rw [repMultiplicity, compositionMultiplicity_of_subsingleton])
    (fun {V W} _ _ _ _ _ _ ρ σ e => repMultiplicity_congr_left (equivComp e (slot K s)) _)
    (fun {V} _ _ _ ρ U => repMultiplicity_sub_quot (ρ.comp (slot K s)) (subComp U (slot K s)) _)
    ρ

theorem nontrivCount_slot_of_eq_empty {J : Fin 3 → Finset ℕ} {s : Fin 3} (h : J s = ∅) :
    nontrivCount ((cubeRep K J).comp (slot K s)) = 0 :=
  nontrivCount_eq_zero_of_trivial _ fun g => cubeRep_slot_eq_one h g

theorem trivMult_slot_of_eq_empty {J : Fin 3 → Finset ℕ} {s : Fin 3} (h : J s = ∅) :
    repMultiplicity ((cubeRep K J).comp (slot K s)) (Representation.trivial K SL(2, K) K) =
      finrank K (CubeSpace K J) :=
  repMultiplicity_trivial_of_trivial _ fun g => cubeRep_slot_eq_one h g

theorem not_equiv_trivial_frobTensor {A : Finset ℕ} (hA : A.Nonempty) :
    ¬ Nonempty ((frobTensor K K A).Equiv (Representation.trivial K SL(2, K) K)) := by
  rintro ⟨e⟩
  have h := e.toLinearEquiv.finrank_eq
  rw [finrank_frobTensor, finrank_self] at h
  have : 2 ≤ 2 ^ A.card := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ A.card := Nat.pow_le_pow_right (by norm_num) (Finset.card_pos.mpr hA)
  omega

theorem nontrivCount_slot_slotLabel (hK : Fintype.card K = 2 ^ n) {b : ℕ} (hb : b < n)
    (s : Fin 3) : nontrivCount ((cubeRep K (slotLabel s {b})).comp (slot K s)) = 1 := by
  rw [← nontrivCount_congr (slotEquiv (K := K) (slotLabel_other (s := s) {b}))]
  have hJ : ∀ i ∈ slotLabel s {b} s, i < n := by
    rw [slotLabel_self]
    exact fun i hi => (Finset.mem_singleton.mp hi) ▸ hb
  rw [nontrivCount_of_isIrreducible _ (frobTensor_isIrreducible hK hJ), if_neg]
  rw [slotLabel_self]
  exact not_equiv_trivial_frobTensor (Finset.singleton_nonempty b)

theorem trivMult_slot_slotLabel (hK : Fintype.card K = 2 ^ n) {b : ℕ} (hb : b < n)
    (s : Fin 3) : repMultiplicity ((cubeRep K (slotLabel s {b})).comp (slot K s))
      (Representation.trivial K SL(2, K) K) = 0 := by
  rw [← repMultiplicity_congr_left (slotEquiv (K := K) (slotLabel_other (s := s) {b}))]
  have hJ : ∀ i ∈ slotLabel s {b} s, i < n := by
    rw [slotLabel_self]
    exact fun i hi => (Finset.mem_singleton.mp hi) ▸ hb
  rw [repMultiplicity_of_isIrreducible (frobTensor_isIrreducible hK hJ), if_neg]
  rw [slotLabel_self]
  exact not_equiv_trivial_frobTensor (Finset.singleton_nonempty b)

section Trivial

variable {Y : Type} [AddCommGroup Y] [Module K Y]

theorem trivial_of_slot0_trivial (hK3 : 3 ≤ Fintype.card K)
    {ρ : Representation K (StatedSp 3 K) Y} (h : ∀ g : SL(2, K), ρ (slotSL 0 g) = 1) :
    ∀ g, ρ g = 1 := by
  have hslot : ∀ (j : Fin 3) (g : SL(2, K)), ρ (slotSL j g) = 1 := by
    intro j g
    rw [← wSwap_conj_slotSL 0 j g, map_mul, map_mul, h g, mul_one, ← map_mul, mul_inv_cancel,
      map_one]
  have hfix : ∀ l y, y ∈ fixT ρ l := fun l y c => by
    rw [show ρ (dSlot l c) = 1 from hslot l _]
    rfl
  have hsc : SingleCoord ρ := fun l m _ =>
    eq_top_iff.mpr fun y _ => Submodule.mem_sup_left (hfix l y)
  have hzero : ∀ y, y ∈ zeroSp ρ := fun y => ⟨⟨hfix 0 y, hfix 1 y⟩, hfix 2 y⟩
  obtain ⟨c₀, hgen⟩ := exists_gen (K := K)
  have hS : ρ.ker = ⊤ := by
    rw [eq_top_iff, ← closure_slot_rootE_eq_top, Subgroup.closure_le]
    rintro x (⟨g, rfl⟩ | ⟨i, j, hij, c, rfl⟩)
    · exact MonoidHom.mem_ker.mpr (hslot 0 g)
    · exact MonoidHom.mem_ker.mpr
        (LinearMap.ext fun y => rootE_fix_of_mem_zeroSp hK3 hsc hgen hij c (hzero y))
  intro g
  exact MonoidHom.mem_ker.mp (hS ▸ Subgroup.mem_top g)

theorem trivial_of_pat_trivial (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n) [Module.Finite K Y]
    {ρ : Representation K (StatedSp 3 K) Y}
    (h : ∀ J, IsLabel n J → J ≠ trivLabel → pat (ρ.comp block) J = 0) : ∀ g, ρ g = 1 := by
  have hK4 : 4 ≤ Fintype.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h0 : nontrivCount (ρ.comp (slotSL 0)) = 0 := by
    change nontrivCount ((ρ.comp block).comp (slot K 0)) = 0
    rw [sum_pat_nontrivCount hK 0 (ρ.comp block)]
    refine Finset.sum_eq_zero fun J hJ => ?_
    by_cases hJt : J = trivLabel
    · subst hJt
      rw [nontrivCount_slot_of_eq_empty rfl, mul_zero]
    · rw [h J (mem_labels.mp hJ) hJt, zero_mul]
  have hperf : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalInvolution.sl2_isPerfect (by rw [Nat.card_eq_fintype_card]; omega)).commutator_eq_top
  exact trivial_of_slot0_trivial (by omega) (trivial_of_nontrivCount_eq_zero hperf _ h0)

theorem finrank_eq_one_of_trivial [FiniteDimensional K Y] {G : Type} [Group G]
    {ρ : Representation K G Y} (hirr : ρ.IsIrreducible) (h : ∀ g, ρ g = 1) : finrank K Y = 1 := by
  obtain ⟨e⟩ := equiv_trivial_of_trivial_isIrreducible ρ hirr h
  rw [e.toLinearEquiv.finrank_eq, finrank_self]

end Trivial

theorem slot_pattern_eq_zero (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n)
    {Y : Type} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    {ρ : Representation K (StatedSp 3 K) Y} (hirr : ρ.IsIrreducible) {b : ℕ} (hb : b < n) {t : ℕ}
    (hpat : ∀ J, IsLabel n J → pat (ρ.comp block) J =
      (if J = trivLabel then t else 0) + ∑ s : Fin 3, if J = slotLabel s {b} then 1 else 0) :
    t = 0 := by
  have hK4 : 4 ≤ Fintype.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK3 : 3 ≤ Fintype.card K := by omega
  have hn1 : 1 ≤ n := by omega
  have hb' : ∀ i ∈ ({b} : Finset ℕ), i < n := fun i hi => (Finset.mem_singleton.mp hi) ▸ hb
  set ρH := ρ.comp block with hρH
  have hdim : finrank K Y = t + 6 := by
    rw [finrank_eq_sum_pat hK ρH, sum_labels_slot_pattern hb _ hpat]
    simp [trivLabel, slotLabel, Fin.sum_univ_three]
  have hone : nontrivCount (ρ.comp (slotSL 0)) = 1 := by
    change nontrivCount (ρH.comp (slot K 0)) = 1
    rw [sum_pat_nontrivCount hK 0 ρH, sum_labels_slot_pattern hb _ hpat,
      nontrivCount_slot_of_eq_empty rfl, Fin.sum_univ_three, nontrivCount_slot_slotLabel hK hb,
      nontrivCount_slot_of_eq_empty (slotLabel_of_ne (by decide) _),
      nontrivCount_slot_of_eq_empty (slotLabel_of_ne (by decide) _)]
    simp
  have htriv : repMultiplicity (ρ.comp (slotSL 0)) (Representation.trivial K SL(2, K) K) =
      t + 4 := by
    change repMultiplicity (ρH.comp (slot K 0)) _ = t + 4
    rw [sum_pat_trivMult hK 0 ρH, sum_labels_slot_pattern hb _ hpat,
      trivMult_slot_of_eq_empty rfl, Fin.sum_univ_three, trivMult_slot_slotLabel hK hb,
      trivMult_slot_of_eq_empty (slotLabel_of_ne (by decide) _),
      trivMult_slot_of_eq_empty (slotLabel_of_ne (by decide) _),
      finrank_cubeRep, finrank_cubeRep, finrank_cubeRep]
    simp [trivLabel, slotLabel]
  have hfixOne : ∀ l, fixT ρ l = Representation.invariants (ρH.comp (torusOne l)) := fun l => by
    ext y
    rfl
  have hfixTwo : ∀ {l m : Fin 3} (hlm : l ≠ m),
      fixT ρ l ⊓ fixT ρ m = Representation.invariants (ρH.comp (torusTwo hlm)) := by
    intro l m hlm
    ext y
    rw [Representation.mem_invariants]
    constructor
    · rintro ⟨h1, h2⟩ c
      rw [MonoidHom.comp_apply, torusTwo_apply, map_mul, Module.End.mul_apply]
      change ρ (dSlot l c.1) (ρ (dSlot m c.2) y) = y
      rw [h2 c.2, h1 c.1]
    · intro h
      refine ⟨fun c => ?_, fun c => ?_⟩
      · have := h (c, 1)
        rwa [MonoidHom.comp_apply, torusTwo_apply, map_one, mul_one] at this
      · have := h (1, c)
        rwa [MonoidHom.comp_apply, torusTwo_apply, map_one, one_mul] at this
  have hdimOne : ∀ l, finrank K (fixT ρ l) = t + 4 := by
    intro l
    haveI := invertibleCardUnits hK hn1
    rw [hfixOne l]
    change fixDim (torusOne l) ρH = t + 4
    rw [sum_pat_fixDim hK (torusOne l) ρH, sum_labels_slot_pattern hb _ hpat,
      fixDim_torusOne_triv,
      Finset.sum_congr rfl fun s _ => fixDim_torusOne_slotLabel hK3 l s b]
    fin_cases l <;> simp [Fin.sum_univ_three]
  have hdimTwo : ∀ {l m : Fin 3} (hlm : l ≠ m), finrank K ↥(fixT ρ l ⊓ fixT ρ m) = t + 2 := by
    intro l m hlm
    haveI := invertibleCardUnitsProd hK hn1
    rw [hfixTwo hlm]
    change fixDim (torusTwo hlm) ρH = t + 2
    rw [sum_pat_fixDim hK (torusTwo hlm) ρH, sum_labels_slot_pattern hb _ hpat,
      fixDim_torusTwo_triv,
      Finset.sum_congr rfl fun s _ => fixDim_torusTwo_slotLabel hK3 hlm b]
    fin_cases l <;> fin_cases m <;> simp_all [Fin.sum_univ_three]
  have hsc : SingleCoord ρ := by
    intro l m hlm
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixT ρ l) (fixT ρ m)
    rw [hdimOne, hdimOne, hdimTwo hlm] at h
    rw [hdim]
    omega
  have hnt : ∃ g y, ρ g y ≠ y := by
    by_contra hcon
    push Not at hcon
    have : nontrivCount (ρ.comp (slotSL 0)) = 0 :=
      nontrivCount_eq_zero_of_trivial _ fun g => LinearMap.ext fun y => hcon _ y
    omega
  obtain ⟨-, hrec⟩ := rec_main hK4 hirr hnt hsc hone
  rw [htriv, hdimTwo (show (1 : Fin 3) ≠ 2 by decide), hdim] at hrec
  omega

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
