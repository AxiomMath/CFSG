module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.B.Pinned

open Subgroup
open scoped Matrix

variable {G : Type*} [Group G]

@[expose] def bcomm (a b : G) : G := a⁻¹ * b⁻¹ * a * b

theorem bcomm_mul_left (g h k : G) : bcomm (g * h) k = h⁻¹ * bcomm g k * h * bcomm h k := by
  simp only [bcomm]; group

theorem bcomm_inv_left (g k : G) : bcomm g⁻¹ k = g * (bcomm g k)⁻¹ * g⁻¹ := by
  simp only [bcomm]; group

theorem bcomm_swap (a b : G) : bcomm b a = (bcomm a b)⁻¹ := by
  simp only [bcomm]; group

theorem bcomm_one_left (k : G) : bcomm 1 k = 1 := by simp [bcomm]

theorem bcomm_eq_one_iff {a b : G} : bcomm a b = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    calc a * b = b * a * bcomm a b := by simp only [bcomm]; group
      _ = b * a := by rw [h, mul_one]
  · intro h
    calc bcomm a b = a⁻¹ * b⁻¹ * (a * b) := by simp only [bcomm]; group
      _ = 1 := by rw [h]; group

open commutatorElement in
theorem commutatorElement_eq_bcomm (a b : G) : ⁅a, b⁆ = bcomm a⁻¹ b⁻¹ := by
  simp only [bcomm, commutatorElement_def, inv_inv]

open _root_.Classical in
@[expose] noncomputable def lg (p : ℕ) (z y : G) : ZMod p :=
  if h : ∃ k : ℤ, z ^ k = y then (h.choose : ZMod p) else 0

theorem lg_zpow {p : ℕ} {z : G} (hz : orderOf z = p) (k : ℤ) : lg p z (z ^ k) = k := by
  unfold lg
  split_ifs with h
  · have e := h.choose_spec
    rw [zpow_eq_zpow_iff_modEq, hz] at e
    exact (ZMod.intCast_eq_intCast_iff _ _ _).2 e
  · exact absurd ⟨k, rfl⟩ h

theorem lg_pow {p : ℕ} {z : G} (hz : orderOf z = p) (k : ℕ) : lg p z (z ^ k) = k := by
  have := lg_zpow hz k
  rwa [zpow_natCast, Int.cast_natCast] at this

theorem lg_one {p : ℕ} {z : G} (hz : orderOf z = p) : lg p z 1 = 0 := by
  have := lg_pow hz 0
  rwa [pow_zero, Nat.cast_zero] at this

theorem lg_mul {p : ℕ} {z y y' : G} (hz : orderOf z = p) (hy : y ∈ zpowers z)
    (hy' : y' ∈ zpowers z) : lg p z (y * y') = lg p z y + lg p z y' := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hy'
  rw [← zpow_add, lg_zpow hz, lg_zpow hz, lg_zpow hz, Int.cast_add]

theorem pow_lg {p : ℕ} [NeZero p] {z y : G} (hz : orderOf z = p) (hy : y ∈ zpowers z) :
    z ^ (lg p z y).val = y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [lg_zpow hz, ← zpow_natCast, ZMod.val_intCast, ← hz, zpow_mod_orderOf]

structure CommData (p : ℕ) {n : ℕ} (q : Fin n → G) (z : G)
    (M : Matrix (Fin n) (Fin n) (ZMod p)) : Prop where
  pow_q : ∀ i, q i ^ p = 1
  orderOf_z : orderOf z = p
  comm_z : ∀ i, q i * z = z * q i
  bcomm_q : ∀ i j, bcomm (q i) (q j) = z ^ (M i j).val
  isUnit_det : IsUnit M.det
  mem_z : z ∈ closure (Set.range q)

@[expose] noncomputable def psi (p : ℕ) {n : ℕ} (q : Fin n → G) (z g : G) : Fin n → ZMod p :=
  fun j => lg p z (bcomm g (q j))

@[expose] noncomputable def coord (p : ℕ) {n : ℕ} (q : Fin n → G) (z : G)
    (M : Matrix (Fin n) (Fin n) (ZMod p)) (g : G) : Fin n → ZMod p :=
  psi p q z g ᵥ* M⁻¹

abbrev zQ {n : ℕ} (q : Fin n → G) (z : G) : Subgroup (closure (Set.range q)) :=
  (zpowers z).subgroupOf (closure (Set.range q))

abbrev qQ {n : ℕ} (q : Fin n → G) (i : Fin n) : closure (Set.range q) :=
  ⟨q i, subset_closure ⟨i, rfl⟩⟩

theorem closure_range_qQ {n : ℕ} (q : Fin n → G) : closure (Set.range (qQ q)) = ⊤ := by
  have e : Set.range (qQ q) = Subtype.val ⁻¹' Set.range q := by
    ext ⟨g, hg⟩
    simp only [Set.mem_range, Set.mem_preimage, Subtype.mk.injEq]
  rw [e]
  exact closure_closure_coe_preimage

namespace CommData

variable {p n : ℕ} {q : Fin n → G} {z : G} {M : Matrix (Fin n) (Fin n) (ZMod p)}

theorem le_centralizer (hD : CommData p q z M) : closure (Set.range q) ≤ centralizer {z} := by
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  exact mem_centralizer_singleton_iff.2 (hD.comm_z i)

theorem commute_of_mem (hD : CommData p q z M) {g y : G} (hg : g ∈ closure (Set.range q))
    (hy : y ∈ zpowers z) : g * y = y * g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have h : Commute g z := mem_centralizer_singleton_iff.1 (hD.le_centralizer hg)
  exact (h.zpow_right k).eq

theorem bcomm_mem_aux (hD : CommData p q z M) {k : G} (hk : ∀ i, bcomm (q i) k ∈ zpowers z)
    {g : G} (hg : g ∈ closure (Set.range q)) : bcomm g k ∈ zpowers z := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hk i
  | one => rw [bcomm_one_left]; exact one_mem _
  | mul x y hx hy ihx ihy =>
    rw [bcomm_mul_left]
    have e : y⁻¹ * bcomm x k * y = bcomm x k := by
      rw [mul_assoc, ← hD.commute_of_mem hy ihx, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    rw [bcomm_inv_left]
    have e : x * (bcomm x k)⁻¹ * x⁻¹ = (bcomm x k)⁻¹ := by
      rw [hD.commute_of_mem hx (inv_mem ihx), mul_inv_cancel_right]
    rw [e]
    exact inv_mem ihx

theorem bcomm_mem (hD : CommData p q z M) {g k : G} (hg : g ∈ closure (Set.range q))
    (hk : k ∈ closure (Set.range q)) : bcomm g k ∈ zpowers z := by
  have h1 : ∀ j, ∀ {g : G}, g ∈ closure (Set.range q) → bcomm g (q j) ∈ zpowers z :=
    fun j _ hg => hD.bcomm_mem_aux (fun i => by rw [hD.bcomm_q]; exact pow_mem (mem_zpowers z) _) hg
  refine hD.bcomm_mem_aux (fun i => ?_) hg
  rw [bcomm_swap k (q i)]
  exact inv_mem (h1 i hk)

theorem bcomm_mul (hD : CommData p q z M) {g h k : G} (hg : g ∈ closure (Set.range q))
    (hh : h ∈ closure (Set.range q)) (hk : k ∈ closure (Set.range q)) :
    bcomm (g * h) k = bcomm g k * bcomm h k := by
  rw [bcomm_mul_left, mul_assoc h⁻¹, ← hD.commute_of_mem hh (hD.bcomm_mem hg hk), ← mul_assoc,
    inv_mul_cancel, one_mul]

theorem psi_mul (hD : CommData p q z M) {g h : G} (hg : g ∈ closure (Set.range q))
    (hh : h ∈ closure (Set.range q)) : psi p q z (g * h) = psi p q z g + psi p q z h := by
  funext j
  simp only [psi, Pi.add_apply]
  rw [hD.bcomm_mul hg hh (subset_closure ⟨j, rfl⟩),
    lg_mul hD.orderOf_z (hD.bcomm_mem hg (subset_closure ⟨j, rfl⟩))
      (hD.bcomm_mem hh (subset_closure ⟨j, rfl⟩))]

theorem psi_one (hD : CommData p q z M) : psi p q z 1 = 0 := by
  funext j
  simp only [psi, bcomm_one_left, lg_one hD.orderOf_z, Pi.zero_apply]

theorem psi_inv (hD : CommData p q z M) {g : G} (hg : g ∈ closure (Set.range q)) :
    psi p q z g⁻¹ = -psi p q z g := by
  have h := hD.psi_mul (inv_mem hg) hg
  rw [inv_mul_cancel, hD.psi_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem psi_q [NeZero p] (hD : CommData p q z M) (i : Fin n) : psi p q z (q i) = M i := by
  funext j
  simp only [psi]
  rw [hD.bcomm_q, lg_pow hD.orderOf_z, ZMod.natCast_zmod_val]

theorem psi_of_mem_zpowers (hD : CommData p q z M) {y : G} (hy : y ∈ zpowers z) :
    psi p q z y = 0 := by
  funext j
  simp only [psi, Pi.zero_apply]
  rw [bcomm_eq_one_iff.2 (hD.commute_of_mem (subset_closure ⟨j, rfl⟩) hy).symm,
    lg_one hD.orderOf_z]

theorem psi_conj (hD : CommData p q z M) {b g : G} (hb : b ∈ closure (Set.range q))
    (hg : g ∈ closure (Set.range q)) : psi p q z (b⁻¹ * g * b) = psi p q z g := by
  rw [hD.psi_mul (mul_mem (inv_mem hb) hg) hb, hD.psi_mul (inv_mem hb) hg, hD.psi_inv hb]
  abel

@[expose] noncomputable def psiHom (hD : CommData p q z M) :
    closure (Set.range q) →* Multiplicative (Fin n → ZMod p) where
  toFun g := Multiplicative.ofAdd (psi p q z g)
  map_one' := by rw [OneMemClass.coe_one, hD.psi_one, ofAdd_zero]
  map_mul' g h := by rw [Subgroup.coe_mul, hD.psi_mul g.2 h.2, ofAdd_add]

theorem psiHom_apply (hD : CommData p q z M) (g : closure (Set.range q)) :
    hD.psiHom g = Multiplicative.ofAdd (psi p q z g) := rfl

theorem psiHom_prod [NeZero p] (hD : CommData p q z M) (a : Fin n → ZMod p) :
    hD.psiHom (List.ofFn fun i => qQ q i ^ (a i).val).prod = Multiplicative.ofAdd (a ᵥ* M) := by
  rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, map_pow, psiHom_apply, hD.psi_q, ← ofAdd_nsmul, ← ofAdd_sum]
  congr 1
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, Matrix.vecMul, dotProduct]

theorem psiHom_surjective [NeZero p] (hD : CommData p q z M) : Function.Surjective hD.psiHom := by
  intro t
  refine ⟨(List.ofFn fun i => qQ q i ^ ((Multiplicative.toAdd t ᵥ* M⁻¹) i).val).prod, ?_⟩
  rw [psiHom_prod, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hD.isUnit_det,
    Matrix.vecMul_one, ofAdd_toAdd]

theorem zQ_le_ker (hD : CommData p q z M) : zQ q z ≤ hD.psiHom.ker := by
  intro g hg
  rw [MonoidHom.mem_ker, psiHom_apply, hD.psi_of_mem_zpowers (mem_subgroupOf.1 hg), ofAdd_zero]

theorem zQ_normal (hD : CommData p q z M) : (zQ q z).Normal :=
  ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hD.commute_of_mem g.2 ha,
      mul_inv_cancel_right]
    exact ha⟩

theorem card_zQ (hD : CommData p q z M) : Nat.card (zQ q z) = p := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hD.mem_z)).toEquiv, Nat.card_zpowers,
    hD.orderOf_z]

theorem quot_mem (hD : CommData p q z M) (a b : closure (Set.range q)) :
    (b * a)⁻¹ * (a * b) ∈ zQ q z := by
  rw [mem_subgroupOf]
  have h := hD.bcomm_mem a.2 b.2
  simp only [bcomm] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using h

theorem card_mult (p n : ℕ) [NeZero p] : Nat.card (Multiplicative (Fin n → ZMod p)) = p ^ n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_le [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    Nat.card (closure (Set.range q)) ≤ p ^ (n + 1) := by
  have := hD.zQ_normal
  let _ : CommGroup (closure (Set.range q) ⧸ zQ q z) :=
    { (inferInstance : Group (closure (Set.range q) ⧸ zQ q z)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H a =>
        induction b using QuotientGroup.induction_on with | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        exact hD.quot_mem b a }
  let c : Fin n → closure (Set.range q) ⧸ zQ q z := fun i => (qQ q i : closure (Set.range q))
  have hc : ∀ i, c i ^ p = 1 := fun i => by
    rw [← QuotientGroup.mk_pow, show qQ q i ^ p = 1 from Subtype.ext (hD.pow_q i),
      QuotientGroup.mk_one]
  let Φ : Multiplicative (Fin n → ZMod p) →* closure (Set.range q) ⧸ zQ q z :=
    { toFun := fun a => ∏ i, c i ^ (Multiplicative.toAdd a i).val
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [toAdd_mul, Pi.add_apply, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [ZMod.val_add, ← pow_eq_pow_mod _ (hc i), pow_add] }
  have hΦc : ∀ i, Φ (Multiplicative.ofAdd (Pi.single i 1)) = c i := fun i => by
    show ∏ j, c j ^ ((Pi.single i 1 : Fin n → ZMod p) j).val = c i
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, ZMod.val_zero,
      pow_zero]) (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, ZMod.val_one,
      pow_one]
  have hΦ : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    have htop : (⊤ : Subgroup (closure (Set.range q) ⧸ zQ q z)) = closure (Set.range c) := by
      rw [show Set.range c = (QuotientGroup.mk' (zQ q z)) '' Set.range (qQ q) by
        rw [← Set.range_comp]; rfl, ← MonoidHom.map_closure, closure_range_qQ,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    rw [htop, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, hΦc i⟩
  have h1 := Nat.card_le_card_of_surjective Φ hΦ
  rw [card_mult] at h1
  rw [card_eq_card_quotient_mul_card_subgroup (zQ q z), hD.card_zQ, pow_succ]
  exact Nat.mul_le_mul_right _ h1

theorem card_eq_and_ker [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    Nat.card (closure (Set.range q)) = p ^ (n + 1) ∧ hD.psiHom.ker = zQ q z := by
  have hrange : Nat.card hD.psiHom.range = p ^ n := by
    rw [MonoidHom.range_eq_top.2 hD.psiHom_surjective, Subgroup.card_top, card_mult]
  have hQ := hD.psiHom.ker.card_mul_index
  rw [Subgroup.index_ker, hrange] at hQ
  have hle : Nat.card (zQ q z) ≤ Nat.card hD.psiHom.ker := Subgroup.card_le_of_le hD.zQ_le_ker
  rw [hD.card_zQ] at hle
  have hup := hD.card_le
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hker : Nat.card hD.psiHom.ker = p := by
    rw [← hQ, pow_succ, mul_comm (p ^ n)] at hup
    exact le_antisymm (le_of_mul_le_mul_right hup hp) hle
  refine ⟨by rw [← hQ, hker, pow_succ, mul_comm], ?_⟩
  exact (eq_of_le_of_card_ge hD.zQ_le_ker (by rw [hker, hD.card_zQ])).symm

theorem card_eq [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    Nat.card (closure (Set.range q)) = p ^ (n + 1) :=
  hD.card_eq_and_ker.1

theorem ker_psiHom [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    hD.psiHom.ker = zQ q z :=
  hD.card_eq_and_ker.2

theorem center_eq [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    center (closure (Set.range q)) = zQ q z := by
  apply le_antisymm
  · intro g hg
    rw [← hD.ker_psiHom, MonoidHom.mem_ker, psiHom_apply]
    have e : psi p q z g = 0 := by
      funext j
      have hc : (g : G) * q j = q j * g := congrArg Subtype.val (mem_center_iff.1 hg (qQ q j)).symm
      simp only [psi, Pi.zero_apply]
      rw [bcomm_eq_one_iff.2 hc, lg_one hD.orderOf_z]
    rw [e, ofAdd_zero]
  · intro g hg
    rw [mem_center_iff]
    intro h
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hD.commute_of_mem h.2 (mem_subgroupOf.1 hg)

open commutatorElement in
theorem commutator_eq [Fact p.Prime] [Finite G] (hD : CommData p q z M) {i₀ j₀ : Fin n}
    (hz : bcomm (q i₀) (q j₀) = z) : commutator (closure (Set.range q)) = zQ q z := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have e : ((⁅a, b⁆ : closure (Set.range q)) : G) = bcomm (a : G)⁻¹ (b : G)⁻¹ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, bcomm, inv_inv]
    rw [mem_subgroupOf, e]
    exact hD.bcomm_mem (inv_mem a.2) (inv_mem b.2)
  · intro g hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_subgroupOf.1 hg)
    have hz' : (⟨z, hD.mem_z⟩ : closure (Set.range q)) ∈ commutator (closure (Set.range q)) := by
      have e : (⟨z, hD.mem_z⟩ : closure (Set.range q)) = ⁅(qQ q i₀)⁻¹, (qQ q j₀)⁻¹⁆ := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [← hz, bcomm]
      rw [e, _root_.commutator_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    have e : g = (⟨z, hD.mem_z⟩ : closure (Set.range q)) ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [e]
    exact zpow_mem hz' k

theorem coord_mul (hD : CommData p q z M) {g h : G} (hg : g ∈ closure (Set.range q))
    (hh : h ∈ closure (Set.range q)) :
    coord p q z M (g * h) = coord p q z M g + coord p q z M h := by
  simp only [coord, hD.psi_mul hg hh, Matrix.add_vecMul]

theorem coord_one (hD : CommData p q z M) : coord p q z M 1 = 0 := by
  simp only [coord, hD.psi_one, Matrix.zero_vecMul]

theorem coord_inv (hD : CommData p q z M) {g : G} (hg : g ∈ closure (Set.range q)) :
    coord p q z M g⁻¹ = -coord p q z M g := by
  simp only [coord, hD.psi_inv hg, Matrix.neg_vecMul]

theorem coord_q [NeZero p] (hD : CommData p q z M) (i : Fin n) :
    coord p q z M (q i) = Pi.single i 1 := by
  have e : M i = Pi.single i 1 ᵥ* M := by
    rw [Matrix.single_vecMul, one_smul]
    rfl
  rw [coord, hD.psi_q, e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hD.isUnit_det,
    Matrix.vecMul_one]

theorem coord_of_mem_zpowers (hD : CommData p q z M) {y : G} (hy : y ∈ zpowers z) :
    coord p q z M y = 0 := by
  simp only [coord, hD.psi_of_mem_zpowers hy, Matrix.zero_vecMul]

theorem coord_conj_of_mem (hD : CommData p q z M) {b g : G} (hb : b ∈ closure (Set.range q))
    (hg : g ∈ closure (Set.range q)) : coord p q z M (b⁻¹ * g * b) = coord p q z M g := by
  simp only [coord, hD.psi_conj hb hg]

theorem coord_prod [NeZero p] (hD : CommData p q z M) (a : Fin n → ZMod p) (c : ℕ) :
    coord p q z M ((List.ofFn fun i => q i ^ (a i).val).prod * z ^ c) = a := by
  have h := congrArg Multiplicative.toAdd (hD.psiHom_prod a)
  rw [psiHom_apply, toAdd_ofAdd, toAdd_ofAdd] at h
  have hmem : ((List.ofFn fun i => qQ q i ^ (a i).val).prod : G) =
      (List.ofFn fun i => q i ^ (a i).val).prod := by
    rw [Subgroup.val_list_prod, List.map_ofFn]
    rfl
  rw [hmem] at h
  rw [hD.coord_mul (by rw [← hmem]; exact SetLike.coe_mem _)
      (pow_mem hD.mem_z c), hD.coord_of_mem_zpowers (pow_mem (mem_zpowers z) c), add_zero,
    coord, h, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hD.isUnit_det, Matrix.vecMul_one]

@[expose] noncomputable def coordHom (hD : CommData p q z M) :
    closure (Set.range q) →* Multiplicative (Fin n → ZMod p) where
  toFun g := Multiplicative.ofAdd (coord p q z M g)
  map_one' := by rw [OneMemClass.coe_one, hD.coord_one, ofAdd_zero]
  map_mul' g h := by rw [Subgroup.coe_mul, hD.coord_mul g.2 h.2, ofAdd_add]

theorem coordHom_apply (hD : CommData p q z M) (g : closure (Set.range q)) :
    hD.coordHom g = Multiplicative.ofAdd (coord p q z M g) := rfl

theorem coordHom_qQ [NeZero p] (hD : CommData p q z M) (i : Fin n) :
    hD.coordHom (qQ q i) = Multiplicative.ofAdd (Pi.single i 1) := by
  rw [coordHom_apply, hD.coord_q]

theorem coordHom_surjective [NeZero p] (hD : CommData p q z M) :
    Function.Surjective hD.coordHom := by
  intro t
  obtain ⟨g, hg⟩ := hD.psiHom_surjective (Multiplicative.ofAdd (Multiplicative.toAdd t ᵥ* M))
  refine ⟨g, ?_⟩
  rw [psiHom_apply] at hg
  rw [coordHom_apply, coord, Multiplicative.ofAdd.injective hg, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hD.isUnit_det, Matrix.vecMul_one, ofAdd_toAdd]

theorem ker_coordHom [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    hD.coordHom.ker = zQ q z := by
  rw [← hD.ker_psiHom]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, coordHom_apply, psiHom_apply, coord]
  constructor
  · intro h
    have h' : psi p q z g ᵥ* M⁻¹ = 0 := Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm)
    have e := congrArg (· ᵥ* M) h'
    simp only [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hD.isUnit_det, Matrix.vecMul_one,
      Matrix.zero_vecMul] at e
    rw [e, ofAdd_zero]
  · intro h
    have h' : psi p q z g = 0 := Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm)
    rw [h', Matrix.zero_vecMul, ofAdd_zero]

theorem quotient_equiv [Fact p.Prime] [Finite G] (hD : CommData p q z M) :
    ∃ _ : (zQ q z).Normal, ∃ e : closure (Set.range q) ⧸ zQ q z ≃* Multiplicative (Fin n → ZMod p),
      (∀ i, e (qQ q i : closure (Set.range q)) = Multiplicative.ofAdd (Pi.single i 1)) ∧
      ∀ g : closure (Set.range q), e g = Multiplicative.ofAdd (coord p q z M g) := by
  have := hD.zQ_normal
  refine ⟨this, (QuotientGroup.quotientMulEquivOfEq hD.ker_coordHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hD.coordHom_surjective), fun i => ?_,
    fun g => ?_⟩
  · rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    exact hD.coordHom_qQ i
  · rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl

theorem not_mem_of_conj [NeZero p] (hD : CommData p q z M) {x : G} {i j : Fin n}
    (hx : x⁻¹ * q i * x = q j) (hij : M i ≠ M j) : x ∉ closure (Set.range q) := by
  intro hxQ
  have h := hD.psi_conj hxQ (subset_closure ⟨i, rfl⟩)
  rw [hx, hD.psi_q, hD.psi_q] at h
  exact hij h.symm

@[expose] noncomputable def actMat (p : ℕ) {n : ℕ} (q : Fin n → G) (z : G)
    (M : Matrix (Fin n) (Fin n) (ZMod p)) (b : G) : Matrix (Fin n) (Fin n) (ZMod p) :=
  Matrix.of fun i => coord p q z M (b⁻¹ * q i * b)

theorem conj_mem {b : G} (hb : ∀ i, b⁻¹ * q i * b ∈ closure (Set.range q)) {g : G}
    (hg : g ∈ closure (Set.range q)) : b⁻¹ * g * b ∈ closure (Set.range q) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hb i
  | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
  | mul x y _ _ ihx ihy =>
    have e : b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) := by group
    rw [e]
    exact mul_mem ihx ihy
  | inv x _ ihx =>
    have e : b⁻¹ * x⁻¹ * b = (b⁻¹ * x * b)⁻¹ := by group
    rw [e]
    exact inv_mem ihx

theorem coord_conj [NeZero p] (hD : CommData p q z M) {b : G}
    (hb : ∀ i, b⁻¹ * q i * b ∈ closure (Set.range q)) {g : G} (hg : g ∈ closure (Set.range q)) :
    coord p q z M (b⁻¹ * g * b) = coord p q z M g ᵥ* actMat p q z M b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hD.coord_q, Matrix.single_vecMul, one_smul]
    rfl
  | one => rw [mul_one, inv_mul_cancel, hD.coord_one, Matrix.zero_vecMul]
  | mul x y hx hy ihx ihy =>
    have e : b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) := by group
    rw [e, hD.coord_mul (conj_mem hb hx) (conj_mem hb hy), ihx, ihy, hD.coord_mul hx hy,
      Matrix.add_vecMul]
  | inv x hx ihx =>
    have e : b⁻¹ * x⁻¹ * b = (b⁻¹ * x * b)⁻¹ := by group
    rw [e, hD.coord_inv (conj_mem hb hx), ihx, hD.coord_inv hx, Matrix.neg_vecMul]

theorem actMat_one [NeZero p] (hD : CommData p q z M) : actMat p q z M 1 = 1 := by
  ext i j
  simp only [actMat, Matrix.of_apply, inv_one, one_mul, mul_one, hD.coord_q, Matrix.one_apply,
    Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem actMat_mul [NeZero p] (hD : CommData p q z M) {b c : G}
    (hb : ∀ i, b⁻¹ * q i * b ∈ closure (Set.range q))
    (hc : ∀ i, c⁻¹ * q i * c ∈ closure (Set.range q)) :
    actMat p q z M (b * c) = actMat p q z M b * actMat p q z M c := by
  ext i j
  have e : (b * c)⁻¹ * q i * (b * c) = c⁻¹ * (b⁻¹ * q i * b) * c := by group
  simp only [actMat, Matrix.of_apply, e, hD.coord_conj hc (hb i), Matrix.mul_apply,
    Matrix.vecMul, dotProduct]

theorem actMat_of_mem [NeZero p] (hD : CommData p q z M) {b : G}
    (hb : b ∈ closure (Set.range q)) : actMat p q z M b = 1 := by
  rw [← hD.actMat_one]
  ext i j
  simp only [actMat, Matrix.of_apply, hD.coord_conj_of_mem hb (subset_closure ⟨i, rfl⟩),
    inv_one, one_mul, mul_one]

@[expose] noncomputable def actHom [NeZero p] (hD : CommData p q z M) (L : Subgroup G)
    (hL : ∀ b ∈ L, ∀ i, b⁻¹ * q i * b ∈ closure (Set.range q)) :
    L →* Matrix (Fin n) (Fin n) (ZMod p) where
  toFun b := actMat p q z M b
  map_one' := hD.actMat_one
  map_mul' b c := hD.actMat_mul (hL b b.2) (hL c c.2)

theorem actHom_apply [NeZero p] (hD : CommData p q z M) (L : Subgroup G)
    (hL : ∀ b ∈ L, ∀ i, b⁻¹ * q i * b ∈ closure (Set.range q)) (b : L) :
    hD.actHom L hL b = actMat p q z M b := rfl

theorem actMat_eq [NeZero p] (hD : CommData p q z M) {b : G}
    (R : Matrix (Fin n) (Fin n) (ZMod p)) (c : Fin n → ℕ)
    (hR : ∀ i, b⁻¹ * q i * b = (List.ofFn fun j => q j ^ (R i j).val).prod * z ^ c i) :
    actMat p q z M b = R := by
  ext i j
  rw [actMat, Matrix.of_apply, hR i, hD.coord_prod]

end CommData

theorem conj_pow_mem {Q : Subgroup G} {x : G} (hx : ∀ g ∈ Q, x⁻¹ * g * x ∈ Q) (k : ℕ) {g : G}
    (hg : g ∈ Q) : (x ^ k)⁻¹ * g * x ^ k ∈ Q := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have e : (x ^ (k + 1))⁻¹ * g * x ^ (k + 1) = x⁻¹ * ((x ^ k)⁻¹ * g * x ^ k) * x := by
      rw [pow_succ]; group
    rw [e]
    exact hx _ ih

theorem mem_normalizer_of_conj [Finite G] {Q : Subgroup G} {x : G}
    (hx : ∀ g ∈ Q, x⁻¹ * g * x ∈ Q) : x ∈ normalizer (Q : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hpow : x ^ (orderOf x - 1) = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos x),
        pow_orderOf_eq_one]
    have := conj_pow_mem hx (orderOf x - 1) hh
    rwa [hpow, inv_inv] at this
  · intro hh
    have := hx _ hh
    rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at this

theorem conj_mem_of_mem_closure [Finite G] {Q : Subgroup G} {S : Set G}
    (hS : ∀ b ∈ S, ∀ g ∈ Q, b⁻¹ * g * b ∈ Q) {b : G} (hb : b ∈ closure S) :
    ∀ g ∈ Q, b⁻¹ * g * b ∈ Q := by
  have hb' : b ∈ Submonoid.closure S := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hb
  clear hb
  induction hb' using Submonoid.closure_induction with
  | mem x hx => exact hS x hx
  | one => intro g hg; simpa using hg
  | mul x y _ _ ihx ihy =>
    intro g hg
    have e : (x * y)⁻¹ * g * (x * y) = y⁻¹ * (x⁻¹ * g * x) * y := by group
    rw [e]
    exact ihy _ (ihx g hg)

theorem card_sup_zpowers {p : ℕ} [Fact p.Prime] [Finite G] {Q : Subgroup G} {x : G}
    (hx : orderOf x = p) (hxQ : x ∉ Q) (hconj : ∀ g ∈ Q, x⁻¹ * g * x ∈ Q) :
    Nat.card (Q ⊔ zpowers x : Subgroup G) = Nat.card Q * p := by
  have hN : zpowers x ≤ normalizer (Q : Set G) := zpowers_le.2 (mem_normalizer_of_conj hconj)
  have hdisj : ∀ y ∈ zpowers x, y ∈ Q → y = 1 := by
    intro y hy hyQ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    by_contra hne
    have hk : (k : ZMod p) ≠ 0 := by
      intro h0
      apply hne
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hx] at h0
      exact (orderOf_dvd_iff_zpow_eq_one).1 h0
    have hxk : x = (x ^ k) ^ ((k : ZMod p)⁻¹.val : ℤ) := by
      rw [← zpow_mul]
      conv_lhs => rw [← zpow_one x]
      rw [zpow_eq_zpow_iff_modEq, hx, ← ZMod.intCast_eq_intCast_iff, Int.cast_mul,
        Int.cast_one, Int.cast_natCast, ZMod.natCast_zmod_val, mul_inv_cancel₀ hk]
    exact hxQ (hxk ▸ zpow_mem hyQ _)
  have hinj : Set.InjOn (QuotientGroup.mk : G → G ⧸ Q) (zpowers x : Set G) := by
    intro y hy y' hy' h
    have h' := QuotientGroup.eq.1 h
    have := hdisj _ (mul_mem (inv_mem hy) hy') h'
    exact (inv_mul_eq_one.1 this)
  have hcard := card_mul_eq_card_subgroup_mul_card_quotient Q (zpowers x : Set G)
  rw [Nat.card_image_of_injOn hinj, ← coe_mul_of_left_le_normalizer_right _ _ hN,
    sup_comm] at hcard
  rw [← hx, ← Nat.card_zpowers]
  exact hcard

end CFSG.Monster.B.Pinned
