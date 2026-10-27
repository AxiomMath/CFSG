module

public import CFSG.RankThree.PartTwo.Census.Spin.Basic
public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

theorem x_inv (i : ι) (u : K) : (R.x i u)⁻¹ = R.x i (-u) := by
  rw [x, x, ← map_inv, ofAdd_neg]

theorem y_inv (i : ι) (u : K) : (R.y i u)⁻¹ = R.y i (-u) := by
  rw [y, y, ← map_inv, ofAdd_neg]

theorem prod_mulSingle_zpow (i j : ι) (c : Kˣ) :
    (∏ k, (Pi.mulSingle i c : ι → Kˣ) k ^ R.CM k j) = c ^ R.CM i j := by
  rw [Finset.prod_eq_single i
    (fun k _ hk => by rw [Pi.mulSingle_eq_of_ne hk, _root_.one_zpow])
    (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]

theorem torus_conj_x (s : ι → Kˣ) (j : ι) (u : K) :
    R.torus s * R.x j u * (R.torus s)⁻¹ = R.x j (((∏ k, s k ^ R.CM k j : Kˣ) : K) * u) := by
  rw [x, R.torus_conj_inl, toAdd_ofAdd, x]

theorem torus_conj_y (s : ι → Kˣ) (j : ι) (u : K) :
    R.torus s * R.y j u * (R.torus s)⁻¹ =
      R.y j ((((∏ k, s k ^ R.CM k j)⁻¹ : Kˣ) : K) * u) := by
  rw [y, R.torus_conj_inr, toAdd_ofAdd, y]

theorem h_conj_x (i j : ι) (c : Kˣ) (u : K) :
    R.h i c * R.x j u * (R.h i c)⁻¹ = R.x j (((c ^ R.CM i j : Kˣ) : K) * u) := by
  rw [h, torus_conj_x, prod_mulSingle_zpow]

theorem h_conj_y (i j : ι) (c : Kˣ) (u : K) :
    R.h i c * R.y j u * (R.h i c)⁻¹ = R.y j ((((c ^ R.CM i j)⁻¹ : Kˣ) : K) * u) := by
  rw [h, torus_conj_y, prod_mulSingle_zpow]

theorem torus_mem_of_h_mem {D : Subgroup R.G} {s : ι → Kˣ} (hs : ∀ i, R.h i (s i) ∈ D) :
    R.torus s ∈ D := by
  rw [← Finset.univ_prod_mulSingle s]
  exact Finset.prod_induction _ (fun t => R.torus t ∈ D)
    (fun a b ha hb => by rw [map_mul]; exact D.mul_mem ha hb)
    (by rw [map_one]; exact D.one_mem) (fun i _ => hs i)

@[expose] def weyl (i : ι) : R.G := R.x i 1 * R.y i (-1) * R.x i 1

theorem coroot_mul_weyl (i : ι) (c : Kˣ) :
    R.h i c * R.weyl i = R.x i c * R.y i (-((c⁻¹ : Kˣ) : K)) * R.x i c := by
  apply R.mat_injective
  have hφ := SqZeroPair.φ_mul (R.sqZero i)
  simp only [weyl, mat_mul, mat_h, mat_x, mat_y, hφ, Units.val_inv_eq_inv_val]
  have hc : (c : K) ≠ 0 := c.ne_zero
  congr 1 <;> field_simp <;> ring

theorem h_eq (i : ι) (c : Kˣ) :
    R.h i c = R.x i c * R.y i (-((c⁻¹ : Kˣ) : K)) * R.x i c * (R.weyl i)⁻¹ := by
  rw [← coroot_mul_weyl, mul_inv_cancel_right]

section Frobenius

variable (σ : K →+* K) (F : R.G →* R.G)

@[expose] def fixedField : Subfield K where
  carrier := {u | σ u = u}
  mul_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq, map_mul] at *; rw [ha, hb]
  one_mem' := map_one σ
  add_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq, map_add] at *; rw [ha, hb]
  zero_mem' := map_zero σ
  neg_mem' {a} ha := by simp only [Set.mem_ofPred_eq, map_neg] at *; rw [ha]
  inv_mem' a ha := by simp only [Set.mem_ofPred_eq, map_inv₀] at *; rw [ha]

theorem mem_fixedField {u : K} : u ∈ fixedField σ ↔ σ u = u := Iff.rfl

structure IsFrobenius : Prop where
  map_x : ∀ i u, F (R.x i u) = R.x i (σ u)
  map_y : ∀ i u, F (R.y i u) = R.y i (σ u)
  map_torus : ∀ s, F (R.torus s) = R.torus fun j => Units.map (σ : K →* K) (s j)

variable {R σ F} (hF : R.IsFrobenius σ F)
include hF

theorem x_mem_fixed {i : ι} {u : K} (hu : u ∈ fixedField σ) : R.x i u ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, hF.map_x, hu]

theorem y_mem_fixed {i : ι} {u : K} (hu : u ∈ fixedField σ) : R.y i u ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, hF.map_y, hu]

theorem torus_mem_fixed {s : ι → Kˣ} (hs : ∀ j, ((s j : Kˣ) : K) ∈ fixedField σ) :
    R.torus s ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup, hF.map_torus]
  congr 1
  funext j
  exact Units.ext (hs j)

theorem h_mem_fixed {i : ι} {c : Kˣ} (hc : (c : K) ∈ fixedField σ) :
    R.h i c ∈ fixedSubgroup F := by
  refine torus_mem_fixed hF fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same]
    exact hc
  · rw [Pi.mulSingle_eq_of_ne hj, Units.val_one]
    exact (fixedField σ).one_mem

theorem weyl_mem_fixed (i : ι) : R.weyl i ∈ fixedSubgroup F := by
  refine (fixedSubgroup F).mul_mem ((fixedSubgroup F).mul_mem ?_ ?_) ?_
  · exact x_mem_fixed hF (fixedField σ).one_mem
  · exact y_mem_fixed hF ((fixedField σ).neg_mem (fixedField σ).one_mem)
  · exact x_mem_fixed hF (fixedField σ).one_mem

theorem x_mem_commutator (hdiag : ∀ j, R.CM j j = 2) {μ : Kˣ} (hμ : (μ : K) ∈ fixedField σ)
    (hμ2 : (μ : K) ^ 2 ≠ 1) {i : ι} {u : K} (hu : u ∈ fixedField σ) :
    R.x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hd : (μ : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hμ2
  set w := u / ((μ : K) ^ 2 - 1) with hw
  have hwF : w ∈ fixedField σ :=
    (fixedField σ).div_mem hu ((fixedField σ).sub_mem ((fixedField σ).pow_mem hμ 2)
      (fixedField σ).one_mem)
  have hcomm : R.x i u = ⁅R.h i μ, R.x i w⁆ := by
    rw [commutatorElement_def, h_conj_x, hdiag, x_inv, ← x_add]
    congr 1
    rw [hw, Units.val_zpow_eq_zpow_val, zpow_ofNat]
    field_simp
    ring
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (h_mem_fixed hF hμ) (x_mem_fixed hF hwF)

theorem y_mem_commutator (hdiag : ∀ j, R.CM j j = 2) {μ : Kˣ} (hμ : (μ : K) ∈ fixedField σ)
    (hμ2 : (μ : K) ^ 2 ≠ 1) {i : ι} {u : K} (hu : u ∈ fixedField σ) :
    R.y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hd : (μ : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hμ2
  set w := u / ((μ : K) ^ 2 - 1) with hw
  have hwF : w ∈ fixedField σ :=
    (fixedField σ).div_mem hu ((fixedField σ).sub_mem ((fixedField σ).pow_mem hμ 2)
      (fixedField σ).one_mem)
  have hμ' : ((μ⁻¹ : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_inv_eq_inv_val]
    exact (fixedField σ).inv_mem hμ
  have hcomm : R.y i u = ⁅R.h i μ⁻¹, R.y i w⁆ := by
    rw [commutatorElement_def, h_conj_y, hdiag, y_inv, ← y_add]
    congr 1
    rw [hw, inv_zpow', zpow_neg, inv_inv, Units.val_zpow_eq_zpow_val, zpow_ofNat]
    field_simp
    ring
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (h_mem_fixed hF hμ') (y_mem_fixed hF hwF)

theorem h_mem_commutator (hdiag : ∀ j, R.CM j j = 2) {μ : Kˣ} (hμ : (μ : K) ∈ fixedField σ)
    (hμ2 : (μ : K) ^ 2 ≠ 1) {i : ι} {c : Kˣ} (hc : (c : K) ∈ fixedField σ) :
    R.h i c ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hc' : -((c⁻¹ : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_inv_eq_inv_val]
    exact (fixedField σ).neg_mem ((fixedField σ).inv_mem hc)
  have hone := (fixedField σ).one_mem
  have hmone := (fixedField σ).neg_mem hone
  rw [h_eq]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    (Subgroup.inv_mem _ ?_)
  · exact x_mem_commutator hF hdiag hμ hμ2 hc
  · exact y_mem_commutator hF hdiag hμ hμ2 hc'
  · exact x_mem_commutator hF hdiag hμ hμ2 hc
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (x_mem_commutator hF hdiag hμ hμ2 hone)
      (y_mem_commutator hF hdiag hμ hμ2 hmone)) (x_mem_commutator hF hdiag hμ hμ2 hone)

theorem torus_mem_commutator (hdiag : ∀ j, R.CM j j = 2) {μ : Kˣ}
    (hμ : (μ : K) ∈ fixedField σ) (hμ2 : (μ : K) ^ 2 ≠ 1) {s : ι → Kˣ}
    (hs : ∀ j, ((s j : Kˣ) : K) ∈ fixedField σ) :
    R.torus s ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
  R.torus_mem_of_h_mem fun i => h_mem_commutator hF hdiag hμ hμ2 (hs i)

end Frobenius

end RootData

structure IsWitness {M : Type*} [Group M] (H : Subgroup M) (p k : ℕ) (E P : Subgroup M) :
    Prop where
  comm : IsMulCommutative E
  pow : ∀ x ∈ E, x ^ p = 1
  card : Nat.card E = p ^ k
  le_E : E ≤ ⁅H, H⁆
  le_P : P ≤ ⁅H, H⁆
  isPGroup : IsPGroup 2 P
  center : ∀ x ∈ E, (∀ y ∈ ⁅H, H⁆, x * y = y * x) → x = 1
  noncentral : ∃ x ∈ P, ∃ y ∈ ⁅H, H⁆, x * y ≠ y * x
  normalizes : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P

@[expose] def HasWitness (Q : Type*) [Group Q] (p k : ℕ) : Prop :=
  ∃ E P : Subgroup Q, IsMulCommutative E ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ k ∧
    P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set Q)

theorem IsWitness.hasWitness {M : Type*} [Group M] {H : Subgroup M} {p k : ℕ}
    {E P : Subgroup M} (h : IsWitness H p k E P) :
    HasWitness (DerivedCentralQuotient H) p k :=
  exists_quotient_witness h.comm h.pow h.card h.le_E h.le_P h.isPGroup h.center h.noncentral
    h.normalizes

section ZModPow

variable {K : Type*} [Field K] {s : ℕ} [NeZero s]

@[expose] def zpowHom (ζ : Kˣ) (hζ : orderOf ζ = s) : Multiplicative (ZMod s) →* Kˣ where
  toFun a := ζ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ m, ζ ^ (m % s) = ζ ^ m := fun m => by
      have h := pow_mod_orderOf ζ m
      rwa [hζ] at h
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, key]

variable (ζ : Kˣ) (hζ : orderOf ζ = s)

theorem zpowHom_apply (a : Multiplicative (ZMod s)) :
    zpowHom ζ hζ a = ζ ^ (Multiplicative.toAdd a).val := rfl

theorem zpowHom_eq_one_iff (a : Multiplicative (ZMod s)) : zpowHom ζ hζ a = 1 ↔ a = 1 := by
  rw [zpowHom_apply, ← orderOf_dvd_iff_pow_eq_one, hζ]
  constructor
  · intro h
    have h2 : (Multiplicative.toAdd a).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt _)
    rw [ZMod.val_eq_zero] at h2
    exact (Multiplicative.ofAdd.injective.eq_iff.mp (by simpa using h2) : _)
  · rintro rfl
    simp

theorem zpowHom_mem {L : Subfield K} (hζL : (ζ : K) ∈ L) (a : Multiplicative (ZMod s)) :
    ((zpowHom ζ hζ a : Kˣ) : K) ∈ L := by
  rw [zpowHom_apply, Units.val_pow_eq_pow_val]
  exact L.pow_mem hζL _

end ZModPow

section FiniteSubfield

variable {K : Type*} [Field K] (L : Subfield K) [Finite L]

theorem exists_unit_orderOf_eq_card : ∃ g : Kˣ, (g : K) ∈ L ∧ orderOf g = Nat.card L - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  refine ⟨Units.map L.subtype.toMonoidHom g, (g : L).2, ?_⟩
  rw [orderOf_injective _ (Units.map_injective (f := L.subtype.toMonoidHom)
    Subtype.val_injective) g, hg, Nat.card_units]

theorem exists_unit_orderOf {s : ℕ} (hs : s ∣ Nat.card L - 1) :
    ∃ ζ : Kˣ, (ζ : K) ∈ L ∧ orderOf ζ = s := by
  obtain ⟨g, hgL, hg⟩ := exists_unit_orderOf_eq_card L
  have h2 : 2 ≤ Nat.card L := by
    have := Finite.one_lt_card (α := L)
    omega
  have hpos : orderOf g ≠ 0 := by
    rw [hg]
    omega
  refine ⟨g ^ (orderOf g / s), ?_, orderOf_pow_orderOf_div hpos (hg ▸ hs)⟩
  rw [Units.val_pow_eq_pow_val]
  exact L.pow_mem hgL _

theorem exists_unit_sq_ne_one (h4 : 4 ≤ Nat.card L) :
    ∃ μ : Kˣ, (μ : K) ∈ L ∧ (μ : K) ^ 2 ≠ 1 := by
  obtain ⟨g, hgL, hg⟩ := exists_unit_orderOf_eq_card L
  refine ⟨g, hgL, fun h => ?_⟩
  have h1 : g ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  have h3 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

end FiniteSubfield

section TorusPoint

variable {K : Type*} [Field K] {s : ℕ} [NeZero s] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] (ζ : Kˣ) (hζ : orderOf ζ = s) (J : κ → ι)

@[expose] noncomputable def torusPointHom : (κ → Multiplicative (ZMod s)) →* (ι → Kˣ) :=
  ∏ b, (MonoidHom.mulSingle (fun _ : ι => Kˣ) (J b)).comp
    ((zpowHom ζ hζ).comp (Pi.evalMonoidHom (fun _ : κ => Multiplicative (ZMod s)) b))

omit [Fintype ι] [DecidableEq κ] in
theorem torusPointHom_apply (e : κ → Multiplicative (ZMod s)) :
    torusPointHom ζ hζ J e = ∏ b, Pi.mulSingle (J b) (zpowHom ζ hζ (e b)) := by
  simp [torusPointHom]

omit [Fintype ι] [DecidableEq κ] in
theorem torusPointHom_mem {L : Subfield K} (hζL : (ζ : K) ∈ L) (e : κ → Multiplicative (ZMod s))
    (k : ι) : ((torusPointHom ζ hζ J e k : Kˣ) : K) ∈ L := by
  rw [torusPointHom_apply, Finset.prod_apply, Units.coe_prod]
  refine L.prod_mem fun b _ => ?_
  by_cases hk : k = J b
  · subst hk
    rw [Pi.mulSingle_eq_same]
    exact zpowHom_mem ζ hζ hζL _
  · rw [Pi.mulSingle_eq_of_ne hk, Units.val_one]
    exact L.one_mem

omit [DecidableEq κ] in
theorem prod_torusPointHom_zpow (CM : Matrix ι ι ℤ) (e : κ → Multiplicative (ZMod s)) (i : ι) :
    ∏ k, (torusPointHom ζ hζ J e k) ^ CM k i = zpowHom ζ hζ (∏ b, e b ^ CM (J b) i) := by
  rw [map_prod]
  simp only [map_zpow, torusPointHom_apply, Finset.prod_apply]
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_eq_single (J b) (fun k _ hk => by rw [Pi.mulSingle_eq_of_ne hk, one_zpow])
    (fun h => absurd (Finset.mem_univ _) h), Pi.mulSingle_eq_same]

theorem eq_one_of_prod_zpow (hs : s.Prime) (CM : Matrix ι ι ℤ) (rw : κ → ι)
    (hdet : (Matrix.of fun a b => ((CM (J b) (rw a) : ℤ) : ZMod s)).det ≠ 0)
    (e : κ → Multiplicative (ZMod s))
    (he : ∀ a, ∏ k, (torusPointHom ζ hζ J e k) ^ CM k (rw a) = 1) : e = 1 := by
  have hfact : Fact s.Prime := ⟨hs⟩
  set v : κ → ZMod s := fun b => Multiplicative.toAdd (e b)
  have hv : Matrix.mulVec (Matrix.of fun a b => ((CM (J b) (rw a) : ℤ) : ZMod s)) v = 0 := by
    funext a
    have h1 := he a
    rw [prod_torusPointHom_zpow, zpowHom_eq_one_iff] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_prod, toAdd_one] at h2
    simp only [toAdd_zpow] at h2
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [zsmul_eq_mul]
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  funext b
  have h3 := congrFun hv0 b
  exact Multiplicative.toAdd.injective (by simpa [v] using h3)

end TorusPoint

section TorusWitness

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
  (R : RootData K N ι)

theorem RootData.char_eq_one_of_commute {t : ι → Kˣ} {j : ι}
    (h : R.torus t * R.x j 1 = R.x j 1 * R.torus t) : (∏ k, t k ^ R.CM k j) = 1 := by
  have h1 := R.torus_conj_x t j 1
  rw [h, mul_inv_cancel_right, mul_one] at h1
  exact Units.ext (R.x_injective j h1).symm

variable {R} {σ : K →+* K} {F : R.G →* R.G}

theorem torus_witness (hF : R.IsFrobenius σ F) (hdiag : ∀ j, R.CM j j = 2) {μ : Kˣ}
    (hμ : (μ : K) ∈ RootData.fixedField σ) (hμ2 : (μ : K) ^ 2 ≠ 1) (h2 : (2 : K) = 0)
    {s : ℕ} [NeZero s] (hs : s.Prime) {ζ : Kˣ} (hζF : (ζ : K) ∈ RootData.fixedField σ)
    (hζ : orderOf ζ = s) (J rw : κ → ι)
    (hdet : (Matrix.of fun a b => ((R.CM (J b) (rw a) : ℤ) : ZMod s)).det ≠ 0) (i₀ : ι) :
    ∃ E P : Subgroup R.G, IsWitness (fixedSubgroup F) s (Fintype.card κ) E P := by
  set Fq := RootData.fixedField σ
  set D := ⁅fixedSubgroup F, fixedSubgroup F⁆
  set θ := R.torus.comp (torusPointHom ζ hζ J)
  have hcoord : ∀ e k, ((torusPointHom ζ hζ J e k : Kˣ) : K) ∈ Fq :=
    fun e k => torusPointHom_mem ζ hζ J hζF e k
  have hdetect : ∀ e, (∀ a, R.torus (torusPointHom ζ hζ J e) * R.x (rw a) 1 =
      R.x (rw a) 1 * R.torus (torusPointHom ζ hζ J e)) → e = 1 := fun e he =>
    eq_one_of_prod_zpow ζ hζ J hs R.CM rw hdet e fun a => R.char_eq_one_of_commute (he a)
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    refine (Subgroup.mem_bot).mpr (hdetect e fun a => ?_)
    change θ e * _ = _ * θ e
    rw [he, one_mul, mul_one]
  set P : Subgroup R.G := (Fq.toAddSubgroup.toSubgroup).map (R.root (.inl i₀))
  have hxP : ∀ u ∈ Fq, R.x i₀ u ∈ P := fun u hu => ⟨Multiplicative.ofAdd u, hu, rfl⟩
  refine ⟨θ.range, P, ⟨⟨⟨fun a b => ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : R.G) * (b : R.G) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ s = 1 := by
      funext b
      change Multiplicative.ofAdd (s • Multiplicative.toAdd (e b)) = Multiplicative.ofAdd 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_fun,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · rintro _ ⟨e, rfl⟩
    exact RootData.torus_mem_commutator hF hdiag hμ hμ2 (hcoord e)
  · rintro _ ⟨u, hu, rfl⟩
    exact RootData.x_mem_commutator hF hdiag hμ hμ2 hu
  · rintro ⟨_, u, hu, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change R.root (.inl i₀) u ^ 2 = 1
    rw [← map_pow]
    have : u ^ 2 = 1 := by
      change Multiplicative.ofAdd (2 • Multiplicative.toAdd u) = Multiplicative.ofAdd 0
      rw [nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul]
    rw [this, map_one]
  · rintro _ ⟨e, rfl⟩ hc
    have he : e = 1 := hdetect e fun a =>
      hc _ (RootData.x_mem_commutator hF hdiag hμ hμ2 (Fq.one_mem))
    rw [he, map_one]
  · refine ⟨R.x i₀ 1, hxP 1 Fq.one_mem, R.h i₀ μ,
      RootData.h_mem_commutator hF hdiag hμ hμ2 hμ, fun hc => hμ2 ?_⟩
    have h1 := R.h_conj_x i₀ i₀ μ 1
    rw [← hc, mul_inv_cancel_right, mul_one] at h1
    have h3 := R.x_injective i₀ h1
    rw [hdiag, Units.val_zpow_eq_zpow_val, zpow_ofNat] at h3
    exact h3.symm
  · rintro _ ⟨e, rfl⟩ _ ⟨u, hu, rfl⟩
    change R.torus (torusPointHom ζ hζ J e) * R.x i₀ (Multiplicative.toAdd u) *
      (R.torus (torusPointHom ζ hζ J e))⁻¹ ∈ P
    replace hu : Multiplicative.toAdd u ∈ Fq := hu
    rw [RootData.torus_conj_x]
    refine hxP _ (Fq.mul_mem ?_ hu)
    rw [Units.coe_prod]
    exact Fq.prod_mem fun k _ => by
      rw [Units.val_zpow_eq_zpow_val]
      exact Fq.zpow_mem (hcoord e k) _

end TorusWitness

theorem two_ne_zero_zmod {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) : ((2 : ℤ) : ZMod s) ≠ 0 := by
  have : Fact s.Prime := ⟨hs⟩
  intro h
  rw [show ((2 : ℤ) : ZMod s) = ((2 : ℕ) : ZMod s) by norm_num, ZMod.natCast_eq_zero_iff] at h
  exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h)

theorem four_ne_zero_zmod {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) : ((4 : ℤ) : ZMod s) ≠ 0 := by
  rw [show ((4 : ℤ) : ZMod s) = ((2 : ℤ) : ZMod s) * ((2 : ℤ) : ZMod s) by push_cast; norm_num]
  have : Fact s.Prime := ⟨hs⟩
  exact mul_ne_zero (two_ne_zero_zmod hs hs2) (two_ne_zero_zmod hs hs2)

end CFSG.RankThree.PartTwo.Census.Spin
