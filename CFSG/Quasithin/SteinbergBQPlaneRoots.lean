module

public import CFSG.Quasithin.SteinbergBQPlaneDiagonal
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.Quasithin.SteinbergBQ

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

@[expose] def fixVec (A : Matrix (Fin 3) (Fin 3) F) : Submodule F (Fin 3 → F) where
  carrier := {v | A *ᵥ v = v}
  add_mem' {v w} hv hw := by
    have h1 : A *ᵥ v = v := hv
    have h2 : A *ᵥ w = w := hw
    change A *ᵥ (v + w) = v + w
    rw [mulVec_add, h1, h2]
  zero_mem' := mulVec_zero A
  smul_mem' c v hv := by
    have h1 : A *ᵥ v = v := hv
    change A *ᵥ (c • v) = c • v
    rw [mulVec_smul, h1]

theorem mem_fixVec {A : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F} :
    v ∈ fixVec A ↔ A *ᵥ v = v :=
  Iff.rfl

theorem eq_one_of_fixVec_eq_top {A : Matrix (Fin 3) (Fin 3) F} (h : fixVec A = ⊤) : A = 1 := by
  refine ext_of_mulVec_single fun m => ?_
  rw [one_mulVec]
  exact mem_fixVec.1 (h ▸ Submodule.mem_top)

abbrev pairMat (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (y : ZMod p × ZMod p) : Matrix (Fin 3) (Fin 3) F :=
  (φ (Multiplicative.ofAdd y) : Matrix (Fin 3) (Fin 3) F)

theorem pairMat_add (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (y y' : ZMod p × ZMod p) : pairMat φ (y + y') = pairMat φ y * pairMat φ y' := by
  rw [pairMat, pairMat, pairMat, ofAdd_add, map_mul]
  rfl

theorem pairMat_zero (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F) :
    pairMat φ 0 = 1 := by
  rw [pairMat, ofAdd_zero, map_one]
  rfl

@[expose] def lineSum [NeZero p]
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (x : ZMod p × ZMod p) : Matrix (Fin 3) (Fin 3) F :=
  ∑ j : ZMod p, pairMat φ (j • x)

@[expose] def planeSum [NeZero p]
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  ∑ y : ZMod p × ZMod p, pairMat φ y

theorem pairMat_mul_lineSum [NeZero p]
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (x : ZMod p × ZMod p) : pairMat φ x * lineSum φ x = lineSum φ x := by
  rw [lineSum, Finset.mul_sum]
  have h : ∀ j : ZMod p, pairMat φ x * pairMat φ (j • x) = pairMat φ ((j + 1) • x) := fun j => by
    rw [← pairMat_add, add_smul, one_smul, add_comm]
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl

theorem pairMat_mul_planeSum [NeZero p]
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (y : ZMod p × ZMod p) : pairMat φ y * planeSum φ = planeSum φ := by
  rw [planeSum, Finset.mul_sum]
  simp_rw [← pairMat_add]
  exact Fintype.sum_equiv (Equiv.addLeft y) _ _ fun _ => rfl

theorem lineSum_identity [Fact p.Prime]
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∑ l : ZMod p, lineSum φ (1, l) + lineSum φ (0, 1) = (p : F) • 1 + planeSum φ := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : ∑ l : ZMod p, lineSum φ (1, l) =
      ∑ j : ZMod p, ∑ l : ZMod p, pairMat φ (j, j * l) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_one]
  have h2 : lineSum φ (0, 1) = ∑ k : ZMod p, pairMat φ (0, k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_zero, mul_one]
  have h3 : planeSum φ = ∑ j : ZMod p, ∑ k : ZMod p, pairMat φ (j, k) :=
    Fintype.sum_prod_type _
  have h4 : ∀ j ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ∑ l : ZMod p, pairMat φ (j, j * l) = ∑ k : ZMod p, pairMat φ (j, k) := fun j hj =>
    Fintype.sum_equiv (Equiv.mulLeft₀ j (Finset.ne_of_mem_erase hj)) _ _ fun _ => rfl
  have h5 : ∑ l : ZMod p, pairMat φ (0, 0 * l) = (p : F) • 1 := by
    simp_rw [zero_mul]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul F, ← pairMat_zero φ]
    rfl
  rw [h1, h2, h3, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), h5,
    ← Finset.add_sum_erase (Finset.univ : Finset (ZMod p))
      (fun j => ∑ k : ZMod p, pairMat φ (j, k)) (Finset.mem_univ 0), Finset.sum_congr rfl h4]
  abel

theorem dvd_card_sub_one_of_injective [Finite F] [hp : Fact p.Prime] (hpF : (p : F) ≠ 0)
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (hφ : Function.Injective φ) : p ∣ Nat.card F - 1 := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : Fintype F := Fintype.ofFinite F
  set q := Nat.card F with hq
  set G := Multiplicative (ZMod p × ZMod p)
  let _ : MulAction G (Fin 3 → F) := MulAction.compHom _ φ
  have hsmul : ∀ (y : G) (v : Fin 3 → F),
      y • v = (φ y : Matrix (Fin 3) (Fin 3) F) *ᵥ v := fun y v => by
    change (φ y : Matrix (Fin 3) (Fin 3) F) • v = _
    exact smul_eq_mulVec _ _
  have hGp : IsPGroup p G := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, sq])
  have hcard : ∀ W : Submodule F (Fin 3 → F), Nat.card W = q ^ Module.finrank F W := fun W =>
    Module.natCard_eq_pow_finrank
  have hV : Nat.card (Fin 3 → F) = q ^ 3 := by rw [Nat.card_fun, Nat.card_fin]
  set W₀ : Submodule F (Fin 3 → F) := ⨅ y, fixVec (pairMat φ y) with hW₀
  have hW₀mem : ∀ v, v ∈ W₀ ↔ ∀ y, pairMat φ y *ᵥ v = v := fun v => by
    rw [hW₀, Submodule.mem_iInf]
    rfl
  have hfixG : Nat.card (MulAction.fixedPoints G (Fin 3 → F)) = Nat.card W₀ := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [MulAction.mem_fixedPoints, hW₀mem]
    exact ⟨fun h y => (hsmul (Multiplicative.ofAdd y) v).symm.trans (h _),
      fun h y => (hsmul y v).trans (h (Multiplicative.toAdd y))⟩
  have hcongG := hGp.card_modEq_card_fixedPoints (Fin 3 → F)
  rw [hfixG, hV, hcard] at hcongG
  have hcongx : ∀ x : ZMod p × ZMod p,
      q ^ 3 ≡ q ^ Module.finrank F (fixVec (pairMat φ x)) [MOD p] := by
    intro x
    set H := Subgroup.zpowers (Multiplicative.ofAdd x : G)
    have hHp : IsPGroup p H := hGp.to_subgroup H
    have hfixH : Nat.card (MulAction.fixedPoints H (Fin 3 → F)) =
        Nat.card (fixVec (pairMat φ x)) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      rw [MulAction.mem_fixedPoints, mem_fixVec]
      constructor
      · intro h
        have h1 := h ⟨_, Subgroup.mem_zpowers _⟩
        rwa [Subgroup.mk_smul, hsmul] at h1
      · intro h y
        have hst : (Multiplicative.ofAdd x : G) ∈ MulAction.stabilizer G v := by
          rw [MulAction.mem_stabilizer_iff, hsmul]
          exact h
        have hy := Subgroup.zpowers_le.2 hst y.2
        rw [MulAction.mem_stabilizer_iff] at hy
        exact hy
    have h := hHp.card_modEq_card_fixedPoints (Fin 3 → F)
    rwa [hfixH, hV, hcard] at h
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card (G := F) p (by
      rw [← Nat.card_eq_fintype_card]
      exact (ZMod.natCast_eq_zero_iff _ _).1 h)
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at ha
      exact hp.out.one_lt.ne ha
    have h1 : (p : F) * a = 0 := by
      rw [← nsmul_eq_mul, ← ha]
      exact addOrderOf_nsmul_eq_zero a
    exact hpF ((mul_eq_zero.1 h1).resolve_right ha0)
  by_contra hndvd
  have hu1 : (q : ZMod p) ≠ 1 := by
    intro h
    apply hndvd
    have hq1 : 1 ≤ q := Nat.card_pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h, Nat.cast_one, sub_self]
  have hmod : ∀ {a b : ℕ}, q ^ a ≡ q ^ b [MOD p] → (q : ZMod p) ^ a = (q : ZMod p) ^ b := by
    intro a b h
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    push_cast at this
    exact this
  have hfixeq : ∀ x : ZMod p × ZMod p, x ≠ 0 → fixVec (pairMat φ x) = W₀ := by
    intro x hx
    have hle : W₀ ≤ fixVec (pairMat φ x) := fun v hv => (hW₀mem v).1 hv x
    have hdx : Module.finrank F (fixVec (pairMat φ x)) ≤ 2 := by
      by_contra h3
      have h3' : Module.finrank F (fixVec (pairMat φ x)) = Module.finrank F (Fin 3 → F) := by
        have := Submodule.finrank_le (fixVec (pairMat φ x))
        rw [Module.finrank_fin_fun] at this ⊢
        omega
      have htop := Submodule.eq_top_of_finrank_eq h3'
      have h1 := eq_one_of_fixVec_eq_top htop
      apply hx
      have h2 : φ (Multiplicative.ofAdd x) = 1 := Subtype.ext h1
      have h3 := hφ (h2.trans (map_one φ).symm)
      exact h3
    have hd0 := Submodule.finrank_mono hle
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have e1 := hmod (hcongx x)
    have e2 := hmod hcongG
    generalize Module.finrank F (fixVec (pairMat φ x)) = dx at e1 hdx hd0 ⊢
    generalize Module.finrank F W₀ = d0 at e2 hd0 ⊢
    have h1 : (q : ZMod p) ^ (dx - d0) = 1 := by
      have h3 : (q : ZMod p) ^ d0 * (q : ZMod p) ^ (dx - d0) = (q : ZMod p) ^ d0 * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hd0, mul_one, ← e1, e2]
      exact mul_left_cancel₀ (pow_ne_zero _ hq0) h3
    have h2 : (q : ZMod p) ^ (3 - dx) = 1 := by
      have h3 : (q : ZMod p) ^ dx * (q : ZMod p) ^ (3 - dx) = (q : ZMod p) ^ dx * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega : dx ≤ 3), mul_one, e1]
      exact mul_left_cancel₀ (pow_ne_zero _ hq0) h3
    by_contra hne
    have hcases : dx - d0 = 1 ∨ (dx - d0 = 2 ∧ 3 - dx = 1) := by omega
    rcases hcases with h | ⟨-, h'⟩
    · rw [h, pow_one] at h1
      exact hu1 h1
    · rw [h', pow_one] at h2
      exact hu1 h2
  have htop : W₀ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hid := congrArg (· *ᵥ v) (lineSum_identity φ)
    simp only [add_mulVec, sum_mulVec, smul_mulVec, one_mulVec] at hid
    have hmem : ∀ x : ZMod p × ZMod p, x ≠ 0 → lineSum φ x *ᵥ v ∈ W₀ := fun x hx => by
      rw [← hfixeq x hx, mem_fixVec, mulVec_mulVec, pairMat_mul_lineSum]
    have hsum : ∑ l : ZMod p, lineSum φ (1, l) *ᵥ v ∈ W₀ :=
      W₀.sum_mem fun l _ => hmem _ fun h => one_ne_zero (congrArg Prod.fst h)
    have hN : planeSum φ *ᵥ v ∈ W₀ := (hW₀mem _).2 fun y => by
      rw [mulVec_mulVec, pairMat_mul_planeSum]
    have hpv : (p : F) • v ∈ W₀ := by
      have h1 : (p : F) • v = ∑ l : ZMod p, lineSum φ (1, l) *ᵥ v + lineSum φ (0, 1) *ᵥ v -
          planeSum φ *ᵥ v := by
        rw [hid]
        abel
      rw [h1]
      exact W₀.sub_mem (W₀.add_mem hsum (hmem _ fun h => one_ne_zero (congrArg Prod.snd h))) hN
    have h2 := W₀.smul_mem (p : F)⁻¹ hpv
    rwa [smul_smul, inv_mul_cancel₀ hpF, one_smul] at h2
  have h1 : fixVec (pairMat φ (1, 0)) = ⊤ := by
    rw [hfixeq _ fun h => one_ne_zero (congrArg Prod.fst h), htop]
  have h2 : φ (Multiplicative.ofAdd (1, 0)) = 1 := Subtype.ext (eq_one_of_fixVec_eq_top h1)
  have h3 := hφ (h2.trans (map_one φ).symm)
  exact one_ne_zero (congrArg Prod.fst (congrArg Multiplicative.toAdd h3))

end CFSG.Quasithin.SteinbergBQ
