module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisBaer
public import CFSG.Permutation.UnitaryThreeRecognition.HeisLinear
public import CFSG.Permutation.UnitaryThreeRecognition.HeisNumber
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open scoped commutatorElement

structure Hyp {G : Type*} [Group G] (Q T Z W : Subgroup G) (p f d : ℕ) : Prop where
  hpodd : p ≠ 2
  hf : 1 ≤ f
  hd : d = Nat.gcd (p ^ f + 1) 3
  hTQ : ∀ t ∈ T, ∀ x ∈ Q, t * x * t⁻¹ ∈ Q
  hTcomm : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁
  hZQ : Z ≤ Q
  hZcent : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x
  hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z
  hexp : ∀ x ∈ Q, x ^ p = 1
  hnonab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x
  hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z * t⁻¹ ∈ Z
  hfree : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ Q, t * x = x * t → x ∈ Z
  hTZtrans : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ ≠ 1 → z₂ ≠ 1 → ∃ t ∈ T, t * z₁ * t⁻¹ = z₂
  hWT : W ≤ T
  hWZ : ∀ w ∈ W, ∀ z ∈ Z, w * z = z * w
  hirr : ∀ N : Subgroup G, Z ≤ N → N ≤ Q → (∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N) →
    N = Z ∨ N = Q
  hQcard : Nat.card Q = p ^ (3 * f)
  hZcard : Nat.card Z = p ^ f
  hTcard : Nat.card T * d = p ^ (2 * f) - 1
  hWcard : Nat.card W * d = p ^ f + 1

namespace Hyp

variable {G : Type*} [Group G] {Q T Z W : Subgroup G} {p f d : ℕ}
  (S : Hyp Q T Z W p f d)
include S

theorem commutator_mem (x y : Q) : ((⁅x, y⁆ : Q) : G) ∈ Z := by
  rw [commutatorElement_def]
  simpa using S.hcomm x x.2 y y.2

variable [Fact p.Prime]

theorem isBaer : IsBaerGroup Q p where
  odd := (Fact.out : p.Prime).odd_of_ne_two S.hpodd
  pow_eq_one x := Subtype.ext (by simpa using S.hexp x x.2)
  comm_mem_center x y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (S.hZcent g g.2 _ (S.commutator_mem x y))

abbrev V : Type _ := Baer Q p S.isBaer

@[expose] def ZsAdd : AddSubgroup S.V where
  carrier := {v | ((Baer.ofB v : Q) : G) ∈ Z}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Baer.ofB_add, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow]
    exact Z.mul_mem (Z.mul_mem hu hv) (Z.pow_mem (S.commutator_mem _ _) _)
  zero_mem' := Z.one_mem
  neg_mem' {v} hv := by
    simp only [Set.mem_ofPred_eq, Baer.ofB_neg, Subgroup.coe_inv] at *
    exact Z.inv_mem hv

@[expose] def Zs : Submodule (ZMod p) S.V := AddSubgroup.toZModSubmodule p S.ZsAdd

theorem mem_Zs {v : S.V} : v ∈ S.Zs ↔ ((Baer.ofB v : Q) : G) ∈ Z := Iff.rfl

@[expose] def conjQ (t : T) : Q →* Q where
  toFun x := ⟨t * x * t⁻¹, S.hTQ t t.2 x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)

@[expose] def rho (t : T) : Module.End (ZMod p) S.V :=
  (Baer.homOf (S.conjQ t)).toZModLinearMap p

@[simp] theorem coe_ofB_rho (t : T) (v : S.V) :
    ((Baer.ofB (S.rho t v) : Q) : G) = (t : G) * (Baer.ofB v : Q) * (t : G)⁻¹ := rfl

theorem rho_ext {u v : S.V} (h : ((Baer.ofB u : Q) : G) = (Baer.ofB v : Q)) : u = v :=
  Baer.ofB_injective (Subtype.ext h)

theorem rho_mul (t₁ t₂ : T) : S.rho (t₁ * t₂) = S.rho t₁ * S.rho t₂ := by
  ext v
  apply S.rho_ext
  rw [Module.End.mul_apply, coe_ofB_rho, coe_ofB_rho, coe_ofB_rho, Subgroup.coe_mul]
  simp only [mul_inv_rev]
  group

theorem rho_one : S.rho 1 = 1 := by
  ext v
  apply S.rho_ext
  rw [coe_ofB_rho, Module.End.one_apply]
  simp

@[expose] def rhoHom : T →* Module.End (ZMod p) S.V where
  toFun := S.rho
  map_one' := S.rho_one
  map_mul' := S.rho_mul

theorem rho_comm (t₁ t₂ : T) : S.rho t₁ * S.rho t₂ = S.rho t₂ * S.rho t₁ := by
  rw [← rho_mul, ← rho_mul, show t₁ * t₂ = t₂ * t₁ from Subtype.ext (S.hTcomm _ t₁.2 _ t₂.2)]

theorem rho_mem_Zs (t : T) {v : S.V} (hv : v ∈ S.Zs) : S.rho t v ∈ S.Zs :=
  S.hTZ t t.2 _ hv

theorem three_le_q : 3 ≤ p ^ f := three_le_prime_pow Fact.out S.hpodd S.hf

omit [Fact p.Prime] in
theorem d_le_three : d ≤ 3 := S.hd ▸ gcd_succ_three_le _

omit [Fact p.Prime] in
theorem d_pos : 0 < d := S.hd ▸ gcd_succ_three_pos _

theorem exists_w : ∃ w ∈ W, w ≠ 1 := by
  by_contra h
  push Not at h
  have hW : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr h
  have h1 := S.hWcard
  rw [hW, Subgroup.card_bot, one_mul] at h1
  have := S.d_le_three
  have := S.three_le_q
  omega

noncomputable def w : T :=
  ⟨Classical.choose S.exists_w, S.hWT (Classical.choose_spec S.exists_w).1⟩

theorem w_mem : (S.w : G) ∈ W := (Classical.choose_spec S.exists_w).1

theorem w_ne_one : (S.w : G) ≠ 1 := (Classical.choose_spec S.exists_w).2

theorem ker_rho_w : LinearMap.ker (S.rho S.w - 1) = S.Zs := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, mem_Zs]
  constructor
  · intro h
    have h' : (S.w : G) * (Baer.ofB v : Q) * (S.w : G)⁻¹ = (Baer.ofB v : Q) := by
      rw [← coe_ofB_rho, h]
    apply S.hfree S.w S.w.2 S.w_ne_one _ (Baer.ofB v).2
    calc (S.w : G) * (Baer.ofB v : Q)
        = ((S.w : G) * (Baer.ofB v : Q) * (S.w : G)⁻¹) * S.w := by group
      _ = (Baer.ofB v : Q) * S.w := by rw [h']
  · intro h
    apply S.rho_ext
    rw [coe_ofB_rho, S.hWZ _ S.w_mem _ h]
    group

theorem rho_w_pow : S.rho S.w ^ Nat.card W = 1 := by
  have h1 : S.w ^ Nat.card W = 1 := by
    have := pow_card_eq_one' (x := (⟨S.w, S.w_mem⟩ : W))
    rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one] at this
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact this
  rw [show S.rho S.w = S.rhoHom S.w from rfl, ← map_pow, h1, map_one]

theorem cast_card_W_ne_zero : ((Nat.card W : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have h1 : p ∣ p ^ f + 1 := h.trans ⟨d, S.hWcard.symm⟩
  have h2 : p ∣ p ^ f := dvd_pow_self p (by have := S.hf; omega)
  have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h3)

@[expose] noncomputable def Vp : Submodule (ZMod p) S.V := LinearMap.range (S.rho S.w - 1)

variable [Finite G]

theorem isCompl_Zs_Vp : IsCompl S.Zs S.Vp := by
  rw [← S.ker_rho_w]
  exact isCompl_ker_range_sub_one (K := ZMod p) (S.rho S.w) (Nat.card W) S.rho_w_pow
    S.cast_card_W_ne_zero

omit [Finite G] in
theorem card_Zs : Nat.card S.Zs = p ^ f := by
  rw [← S.hZcard]
  exact Nat.card_congr
    { toFun := fun v => ⟨((Baer.ofB (v : S.V) : Q) : G), v.2⟩
      invFun := fun z => ⟨Baer.toB S.isBaer ⟨z, S.hZQ z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_Vp : Nat.card S.Vp = p ^ (2 * f) := by
  have h := Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ S.isCompl_Zs_Vp).toEquiv
  rw [Nat.card_prod, S.card_Zs] at h
  have h' : Nat.card S.V = p ^ f * p ^ (2 * f) := by
    change Nat.card Q = _
    rw [S.hQcard, ← pow_add]
    ring_nf
  rw [h'] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos f) h

omit [Finite G] in
theorem rho_mem_Vp (t : T) {v : S.V} (hv : v ∈ S.Vp) : S.rho t v ∈ S.Vp := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨S.rho t u, ?_⟩
  change ((S.rho S.w - 1) * S.rho t) u = (S.rho t * (S.rho S.w - 1)) u
  rw [sub_mul, mul_sub, one_mul, mul_one, S.rho_comm]

omit [Finite G] in
theorem toB_commutator_mem_Zs (x y : Q) : Baer.toB S.isBaer ⁅x, y⁆ ∈ S.Zs :=
  S.commutator_mem x y

theorem irred_Vp (U : Submodule (ZMod p) S.V) (hU : U ≤ S.Vp)
    (hinv : ∀ t : T, ∀ v ∈ U, S.rho t v ∈ U) : U = ⊥ ∨ U = S.Vp := by
  set N := S.Zs ⊔ U with hN
  have hNc : ∀ x y : Q, Baer.toB S.isBaer ⁅x, y⁆ ∈ N.toAddSubgroup :=
    fun x y => Submodule.mem_sup_left (S.toB_commutator_mem_Zs x y)
  set NQ := Baer.toSubgroup N.toAddSubgroup hNc
  set NG := NQ.map Q.subtype with hNG
  have hmemNG : ∀ x : Q, (x : G) ∈ NG ↔ Baer.toB S.isBaer x ∈ N := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [Subgroup.coe_subtype] at hyx
      rw [← Subtype.ext hyx]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hZN : Z ≤ NG := by
    intro z hz
    exact (hmemNG ⟨z, S.hZQ hz⟩).mpr (Submodule.mem_sup_left hz)
  have hNQ : NG ≤ Q := Subgroup.map_subtype_le NQ
  have hrhoN : ∀ t : T, ∀ v ∈ N, S.rho t v ∈ N := by
    intro t v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (S.rho_mem_Zs t ha) (hinv t b hb)
  have hTN : ∀ t ∈ T, ∀ x ∈ NG, t * x * t⁻¹ ∈ NG := by
    intro t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := (hmemNG (S.conjQ ⟨t, ht⟩ y)).mpr (hrhoN ⟨t, ht⟩ _ hy)
    exact this
  rcases S.hirr NG hZN hNQ hTN with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have hu' : u ∈ S.Zs := by
      have := (hmemNG (Baer.ofB u)).mpr (Submodule.mem_sup_right hu)
      rw [h] at this
      exact this
    have := Submodule.disjoint_def.mp S.isCompl_Zs_Vp.disjoint u hu' (hU hu)
    rw [this]
    exact Submodule.zero_mem _
  · right
    apply le_antisymm hU
    intro v hv
    have hvN : v ∈ N := by
      have : ((Baer.ofB v : Q) : G) ∈ NG := by rw [h]; exact (Baer.ofB v).2
      exact (hmemNG _).mp this
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvN
    have haV : a ∈ S.Vp := by
      rw [show a = v - b by rw [← hab]; abel]
      exact S.Vp.sub_mem hv (hU hb)
    have ha0 := Submodule.disjoint_def.mp S.isCompl_Zs_Vp.disjoint a ha haV
    rw [← hab, ha0, zero_add]
    exact hb

@[expose] noncomputable def rhoV (t : T) : Module.End (ZMod p) S.Vp :=
  (S.rho t).restrict (fun _ hv => S.rho_mem_Vp t hv)

omit [Finite G] in
@[simp] theorem coe_rhoV (t : T) (v : S.Vp) : (S.rhoV t v : S.V) = S.rho t v := rfl

theorem isIrred_Vp : IsIrred (Set.range S.rhoV) := by
  intro U hU
  have hle : U.map S.Vp.subtype ≤ S.Vp := Submodule.map_subtype_le _ _
  have hinv : ∀ t : T, ∀ v ∈ U.map S.Vp.subtype, S.rho t v ∈ U.map S.Vp.subtype := by
    rintro t _ ⟨u, hu, rfl⟩
    exact ⟨S.rhoV t u, hU _ ⟨t, rfl⟩ u hu, rfl⟩
  have hinj := Submodule.map_injective_of_injective S.Vp.injective_subtype
  rcases S.irred_Vp _ hle hinv with h | h
  · left
    apply hinj
    rw [h, Submodule.map_bot]
  · right
    apply hinj
    rw [h, Submodule.map_subtype_top]

end Hyp

end CFSG.UnitaryThreeRecognition.Heisenberg
