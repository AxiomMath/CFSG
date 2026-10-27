module

public import CFSG.RankThree.Chevalley.SteinbergBIE6D4CertOne
public import CFSG.RankThree.Chevalley.SteinbergBIE6D4CertTwo
public import CFSG.RankThree.Chevalley.SteinbergBIE6A2Layers
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Monster.B.Classical.E6Adjoint
  CFSG.Monster.B.E6.StdF4 CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {Ω : Type} [Field Ω]

theorem exists_finset_pow_eq_self [IsAlgClosed Ω] {ℓ : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] {m : ℕ}
    (hm : m ≠ 0) : ∃ F : Finset Ω, F.card = ℓ ^ m ∧ ∀ a, a ∈ F ↔ a ^ ℓ ^ m = a := by
  have h := natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) hm
  have hfin : ({c : Ω | c ^ ℓ ^ m = c}).Finite := by
    have : Finite ({c : Ω | c ^ ℓ ^ m = c}) := Nat.finite_of_card_ne_zero (by
      rw [h]
      exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
    exact Set.toFinite _
  exact ⟨hfin.toFinset, (Nat.card_eq_card_finite_toFinset hfin).symm.trans h,
    fun a => hfin.mem_toFinset⟩

@[expose] def d4Layer (Fr : Ω →+* Ω) (e : ℕ) : Subgroup (ModGL Tag.E6 Ω) :=
  (d4ThetaFixed Ω Fr e).map (subsystemGroup Tag.E6 Ω d4Support).subtype

theorem d4Layer_le (Fr : Ω →+* Ω) (e : ℕ) : d4Layer Fr e ≤ subsystemGroup Tag.E6 Ω d4Support := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem coe_d4OuterX (a b c : Ω) :
    (((d4OuterX a b c : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) =
      xOp Tag.E6 Ω (d4Idx 0) a * xOp Tag.E6 Ω (d4Idx 1) b * xOp Tag.E6 Ω (d4Idx 3) c := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_xUnit]

theorem coe_d4OuterY (a b c : Ω) :
    (((d4OuterY a b c : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) =
      yOp Tag.E6 Ω (d4Idx 0) a * yOp Tag.E6 Ω (d4Idx 1) b * yOp Tag.E6 Ω (d4Idx 3) c := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_yUnit]

section Facts

variable {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ} (he : e = 1 ∨ e = 2)
  {X : Module.End Ω (RootModule Tag.E6 Ω)}

include hFr he

theorem commute_outerX_of_mem (hX : X ∈ e6Commutant (d4Layer Fr e : Set (ModGL Tag.E6 Ω)))
    {a : Ω} (ha : a ^ (q ^ 3) = a) :
    Commute X (xOp Tag.E6 Ω (d4Idx 0) a * xOp Tag.E6 Ω (d4Idx 1) (a ^ (q ^ e)) *
      xOp Tag.E6 Ω (d4Idx 3) (a ^ (q ^ (2 * e)))) := by
  rw [← coe_d4OuterX]
  exact hX _ ⟨_, d4OuterX_mem_d4ThetaFixed hFr he ha, rfl⟩

theorem commute_outerY_of_mem (hX : X ∈ e6Commutant (d4Layer Fr e : Set (ModGL Tag.E6 Ω)))
    {a : Ω} (ha : a ^ (q ^ 3) = a) :
    Commute X (yOp Tag.E6 Ω (d4Idx 0) a * yOp Tag.E6 Ω (d4Idx 1) (a ^ (q ^ e)) *
      yOp Tag.E6 Ω (d4Idx 3) (a ^ (q ^ (2 * e)))) := by
  rw [← coe_d4OuterY]
  exact hX _ ⟨_, d4OuterY_mem_d4ThetaFixed hFr he ha, rfl⟩

theorem commute_middle_of_mem (hX : X ∈ e6Commutant (d4Layer Fr e : Set (ModGL Tag.E6 Ω)))
    {b : Ω} (hb : b ^ q = b) :
    Commute X (xOp Tag.E6 Ω (d4Idx 2) b) ∧ Commute X (yOp Tag.E6 Ω (d4Idx 2) b) := by
  obtain ⟨h1, h2⟩ := d4Middle_mem_d4ThetaFixed hFr he hb
  have e1 := hX _ ⟨_, h1, rfl⟩
  have e2 := hX _ ⟨_, h2, rfl⟩
  simp only [Subgroup.coe_subtype, coe_xUnit, coe_yUnit] at e1 e2
  exact ⟨e1, e2⟩

end Facts

section Separation

variable {M : Type*} [Ring M] [Algebra Ω M]

theorem commute_sum_smul_iff {ι : Type*} [Fintype ι] (X : M) (f : ι → Ω) (C : ι → M) :
    Commute X (∑ t, f t • C t) ↔ ∑ t, f t • (X * C t - C t * X) = 0 := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem commute_of_forall_commute_sum_pow {ι : Type*} [Fintype ι] {X : M} {C : ι → M}
    {n : ι → ℕ} (hn : Function.Injective n) {F : Finset Ω} (hF : ∀ t, n t < F.card)
    (h : ∀ a ∈ F, Commute X (∑ t, a ^ n t • C t)) (t : ι) : Commute X (C t) :=
  sub_eq_zero.1 (eq_zero_of_forall_sum_pow_smul hn hF
    (fun a ha => (commute_sum_smul_iff X _ C).1 (h a ha)) t)

theorem commute_of_commute_one_add {X Y : M} (h : Commute X (1 + Y)) : Commute X Y := by
  have e := h.eq
  rw [mul_add, add_mul, mul_one, one_mul] at e
  exact add_left_cancel e

end Separation

theorem digits3_injective {q : ℕ} (hq : 3 ≤ q) :
    Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
      (t.1 : ℕ) + q * ((t.2.1 : ℕ) + q * (t.2.2 : ℕ)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only at h
  have ha : (a : ℕ) < q := by have := a.2; omega
  have ha' : (a' : ℕ) < q := by have := a'.2; omega
  have hb : (b : ℕ) < q := by have := b.2; omega
  have hb' : (b' : ℕ) < q := by have := b'.2; omega
  have h1 := congrArg (· % q) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1
  have h2 := congrArg (· / q) h
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha', zero_add, zero_add] at h2
  have h3 := congrArg (· % q) h2
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h3
  have h4 := congrArg (· / q) h2
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hb', zero_add, zero_add] at h4
  rw [Fin.ext h1, Fin.ext h3, Fin.ext h4]

theorem digits3_lt {q : ℕ} (hq : 3 ≤ q) (t : Fin 3 × Fin 3 × Fin 3) :
    (t.1 : ℕ) + q * ((t.2.1 : ℕ) + q * (t.2.2 : ℕ)) < q ^ 3 := by
  have h1 : (t.1 : ℕ) ≤ 2 := by have := t.1.2; omega
  have h2 : (t.2.1 : ℕ) ≤ 2 := by have := t.2.1.2; omega
  have h3 : (t.2.2 : ℕ) ≤ 2 := by have := t.2.2.2; omega
  have : (t.1 : ℕ) + q * ((t.2.1 : ℕ) + q * (t.2.2 : ℕ)) ≤ 2 + q * (2 + q * 2) := by
    gcongr
  have e1 : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have e2 : 3 * (q * q) ≤ q * (q * q) := Nat.mul_le_mul_right (q * q) hq
  rw [show q ^ 3 = q * (q * q) by ring]
  nlinarith

theorem outer_expand_x (a b c : Ω) :
    xOp Tag.E6 Ω (d4Idx 0) a * xOp Tag.E6 Ω (d4Idx 1) b * xOp Tag.E6 Ω (d4Idx 3) c =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ)) •
        (quadCoeff (xCoeff Tag.E6 Ω (d4Idx 0) 1) (xCoeff Tag.E6 Ω (d4Idx 0) 2) t.1 *
          quadCoeff (xCoeff Tag.E6 Ω (d4Idx 1) 1) (xCoeff Tag.E6 Ω (d4Idx 1) 2) t.2.1 *
          quadCoeff (xCoeff Tag.E6 Ω (d4Idx 3) 1) (xCoeff Tag.E6 Ω (d4Idx 3) 2) t.2.2) := by
  rw [xOp_E6_eq, xOp_E6_eq, xOp_E6_eq, triple_expand]

theorem outer_expand_y (a b c : Ω) :
    yOp Tag.E6 Ω (d4Idx 0) a * yOp Tag.E6 Ω (d4Idx 1) b * yOp Tag.E6 Ω (d4Idx 3) c =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ)) •
        (quadCoeff (yCoeff Tag.E6 Ω (d4Idx 0) 1) (yCoeff Tag.E6 Ω (d4Idx 0) 2) t.1 *
          quadCoeff (yCoeff Tag.E6 Ω (d4Idx 1) 1) (yCoeff Tag.E6 Ω (d4Idx 1) 2) t.2.1 *
          quadCoeff (yCoeff Tag.E6 Ω (d4Idx 3) 1) (yCoeff Tag.E6 Ω (d4Idx 3) 2) t.2.2) := by
  rw [yOp_E6_eq, yOp_E6_eq, yOp_E6_eq, triple_expand]

theorem outer_expand_x_two [CharP Ω 2] (a b c : Ω) :
    xOp Tag.E6 Ω (d4Idx 0) a * xOp Tag.E6 Ω (d4Idx 1) b * xOp Tag.E6 Ω (d4Idx 3) c =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ)) •
        (coeffEnd (R := Ω) 7 t.1 * coeffEnd 8 t.2.1 * coeffEnd 10 t.2.2) := by
  rw [xOp_eq_lab, xOp_eq_lab, xOp_eq_lab, triple_expand]
  rfl

theorem outer_expand_y_two [CharP Ω 2] (a b c : Ω) :
    yOp Tag.E6 Ω (d4Idx 0) a * yOp Tag.E6 Ω (d4Idx 1) b * yOp Tag.E6 Ω (d4Idx 3) c =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ)) •
        (coeffEnd (R := Ω) 14 t.1 * coeffEnd 16 t.2.1 * coeffEnd 20 t.2.2) := by
  rw [yOp_eq_lab, yOp_eq_lab, yOp_eq_lab, triple_expand]
  rfl

section Large

variable {M : Type*} [Ring M] [Algebra Ω M]

theorem digits3_swap_injective {q : ℕ} (hq : 3 ≤ q) :
    Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
      (t.1 : ℕ) + q * ((t.2.2 : ℕ) + q * (t.2.1 : ℕ)) := by
  intro t s h
  have := digits3_injective hq (a₁ := (t.1, t.2.2, t.2.1)) (a₂ := (s.1, s.2.2, s.2.1)) h
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (Prod.ext this.2.2 this.2.1)

theorem commute_coeffs_of_outer {q e : ℕ} (hq : 3 ≤ q) (he : e = 1 ∨ e = 2) {F : Finset Ω}
    (hFc : F.card = q ^ 3) (hF : ∀ a ∈ F, a ^ (q ^ 3) = a) {X : M}
    {C : Fin 3 × Fin 3 × Fin 3 → M}
    (h : ∀ a ∈ F, Commute X (∑ t : Fin 3 × Fin 3 × Fin 3,
      (a ^ (t.1 : ℕ) * (a ^ (q ^ e)) ^ (t.2.1 : ℕ) * (a ^ (q ^ (2 * e))) ^ (t.2.2 : ℕ)) • C t))
    (t : Fin 3 × Fin 3 × Fin 3) : Commute X (C t) := by
  rcases he with rfl | rfl
  · refine commute_of_forall_commute_sum_pow (digits3_injective hq)
      (fun t => hFc ▸ digits3_lt hq t) (fun a ha => ?_) t
    convert h a ha using 3 with s
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  · refine commute_of_forall_commute_sum_pow (digits3_swap_injective hq)
      (fun t => hFc ▸ digits3_lt hq (t.1, t.2.2, t.2.1)) (fun a ha => ?_) t
    convert h a ha using 3 with s
    have h4 : a ^ (q ^ (2 * 2)) = a ^ q := by
      rw [show 2 * 2 = 3 + 1 by rfl, pow_succ, pow_mul, hF a ha]
    rw [h4, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring

end Large

section Small

variable {M : Type*} [Ring M] [Algebra Ω M]

theorem classList_toFinset (e r : ℕ) :
    (classList e r).toFinset = Finset.univ.filter fun t => tripleExp e t % 7 = r := by
  ext t
  simp [classList, mem_tripleList]

theorem sum_classList (e r : ℕ) (C : Fin 3 × Fin 3 × Fin 3 → M) :
    ((classList e r).map C).sum =
      ∑ t ∈ Finset.univ.filter (fun t => tripleExp e t % 7 = r), C t := by
  classical
  rw [← classList_toFinset]
  exact (List.sum_toFinset C (nodup_tripleList.filter _)).symm

theorem sum_pow_tripleExp {a : Ω} (ha : a ^ 7 = 1) (e : ℕ) (C : Fin 3 × Fin 3 × Fin 3 → M) :
    ∑ t : Fin 3 × Fin 3 × Fin 3, a ^ tripleExp e t • C t =
      ∑ r : Fin 7, a ^ (r : ℕ) • ((classList e r).map C).sum := by
  classical
  set g : Fin 3 × Fin 3 × Fin 3 → Fin 7 := fun t => ⟨tripleExp e t % 7, Nat.mod_lt _ (by norm_num)⟩
  rw [← Finset.sum_fiberwise Finset.univ g]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_classList, Finset.smul_sum]
  have hfilter : (Finset.univ.filter fun t => g t = r) =
      Finset.univ.filter fun t => tripleExp e t % 7 = r := by
    ext t
    simp [g, Fin.ext_iff]
  rw [hfilter]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_filter] at ht
  rw [pow_eq_pow_mod (tripleExp e t) ha, ht.2]

theorem commute_classes_of_outer {e : ℕ} {F : Finset Ω} (hFc : F.card = 7)
    (hF : ∀ a ∈ F, a ^ 7 = 1) {X : M} {C : Fin 3 × Fin 3 × Fin 3 → M}
    (h : ∀ a ∈ F, Commute X (∑ t : Fin 3 × Fin 3 × Fin 3,
      (a ^ (t.1 : ℕ) * (a ^ (2 ^ e)) ^ (t.2.1 : ℕ) * (a ^ (2 ^ (2 * e))) ^ (t.2.2 : ℕ)) • C t))
    {r : ℕ} (hr : r < 7) : Commute X ((classList e r).map C).sum := by
  have key := commute_of_forall_commute_sum_pow (n := fun r : Fin 7 => (r : ℕ))
    (fun a b hab => Fin.ext hab) (F := F) (fun r => by rw [hFc]; exact r.2)
    (C := fun r : Fin 7 => ((classList e (r : ℕ)).map C).sum)
    (fun a ha => by
      rw [← sum_pow_tripleExp (hF a ha)]
      convert h a ha using 3 with t
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, tripleExp]
      congr 1
      ring) ⟨r, hr⟩
  exact key

end Small

theorem natCast_d4Idx_val (k : Fin Tag.D4.rank) : d4Idx k = ⟨(k : ℕ) + 1, by
    have h := k.2
    change (k : ℕ) < 4 at h
    change (k : ℕ) + 1 < 6
    omega⟩ := rfl

theorem e6Commutant_d4Layer [IsAlgClosed Ω] {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) [CharP Ω ℓ]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) {e : ℕ} (he : e = 1 ∨ e = 2) :
    e6Commutant (d4Layer Fr e : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  refine Set.Subset.antisymm (fun X hX => ?_) (e6Commutant_anti (d4Layer_le Fr e))
  suffices key : ∀ k : Fin Tag.D4.rank, ∀ c : Ω,
      Commute X (xOp Tag.E6 Ω (d4Idx k) c) ∧ Commute X (yOp Tag.E6 Ω (d4Idx k) c) by
    refine mem_e6Commutant_subsystemGroup (fun i hi c => ?_) (fun i hi c => ?_)
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      exact (key k c).1
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      exact (key k c).2
  obtain ⟨FK, hFKc, hFK⟩ := exists_finset_pow_eq_self (Ω := Ω) (ℓ := ℓ) (m := d * 3) (by omega)
  rw [pow_mul] at hFKc
  have hFK' : ∀ a ∈ FK, a ^ ((ℓ ^ d) ^ 3) = a := fun a ha => by rw [← pow_mul]; exact (hFK a).1 ha
  by_cases hq : 3 ≤ ℓ ^ d
  · obtain ⟨Fk, hFkc, hFk⟩ := exists_finset_pow_eq_self (Ω := Ω) (ℓ := ℓ) (m := d) (by omega)
    have hk3 : 3 ≤ Fk.card := hFkc ▸ hq
    have hcx := commute_coeffs_of_outer hq he hFKc hFK' (fun a ha => by
      rw [← outer_expand_x]
      exact commute_outerX_of_mem hFr he hX (hFK' a ha))
    have hcy := commute_coeffs_of_outer hq he hFKc hFK' (fun a ha => by
      rw [← outer_expand_y]
      exact commute_outerY_of_mem hFr he hX (hFK' a ha))
    have hmid : ∀ b ∈ Fk, Commute X (xOp Tag.E6 Ω (d4Idx 2) b) ∧
        Commute X (yOp Tag.E6 Ω (d4Idx 2) b) := fun b hb =>
      commute_middle_of_mem hFr he hX ((hFk b).1 hb)
    intro k c
    fin_cases k
    · have a1 := hcx (1, 0, 0)
      have a2 := hcx (2, 0, 0)
      have b1 := hcy (1, 0, 0)
      have b2 := hcy (2, 0, 0)
      simp only [quadCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        mul_one] at a1 a2 b1 b2
      rw [xOp_E6_eq, yOp_E6_eq]
      exact ⟨commute_one_add_of_commute a1 a2 c, commute_one_add_of_commute b1 b2 c⟩
    · have a1 := hcx (0, 1, 0)
      have a2 := hcx (0, 2, 0)
      have b1 := hcy (0, 1, 0)
      have b2 := hcy (0, 2, 0)
      simp only [quadCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        mul_one, one_mul] at a1 a2 b1 b2
      rw [xOp_E6_eq, yOp_E6_eq]
      exact ⟨commute_one_add_of_commute a1 a2 c, commute_one_add_of_commute b1 b2 c⟩
    · exact ⟨commute_xOp_of_three_le_card hk3 (fun b hb => (hmid b hb).1) c,
        commute_yOp_of_three_le_card hk3 (fun b hb => (hmid b hb).2) c⟩
    · have a1 := hcx (0, 0, 1)
      have a2 := hcx (0, 0, 2)
      have b1 := hcy (0, 0, 1)
      have b2 := hcy (0, 0, 2)
      simp only [quadCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        one_mul] at a1 a2 b1 b2
      rw [xOp_E6_eq, yOp_E6_eq]
      exact ⟨commute_one_add_of_commute a1 a2 c, commute_one_add_of_commute b1 b2 c⟩
  ·
    classical
    have h2 : ℓ ^ d = 2 := by
      have h1 : 2 ≤ ℓ ^ d := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
      omega
    have hℓ2 := two_of_prime_pow_eq_two hℓ hd h2
    subst hℓ2
    have : CharP Ω 2 := inferInstance
    rw [h2] at hFr hFKc hFK'
    set Fs := FK.erase 0 with hFs
    have h0 : (0 : Ω) ∈ FK := (hFK 0).2 (zero_pow (pow_ne_zero _ two_ne_zero))
    have hFsc : Fs.card = 7 := by
      rw [hFs, Finset.card_erase_of_mem h0, hFKc]
      norm_num
    have hFs7 : ∀ a ∈ Fs, a ^ 7 = 1 := fun a ha => by
      obtain ⟨ha0, haK⟩ := Finset.mem_erase.1 ha
      have h8 : a ^ (7 + 1) = a := by simpa using hFK' a haK
      rw [pow_succ] at h8
      exact mul_right_cancel₀ ha0 (h8.trans (one_mul a).symm)
    have hFs8 : ∀ a ∈ Fs, a ^ (2 ^ 3) = a := fun a ha => hFK' a (Finset.mem_of_mem_erase ha)
    have hP : ∀ r < 7, Commute X (classEnd (R := Ω) 7 8 10 e r) := fun r hr =>
      commute_classes_of_outer hFsc hFs7 (fun a ha => by
        rw [← outer_expand_x_two]
        exact commute_outerX_of_mem hFr he hX (hFs8 a ha)) hr
    have hQ : ∀ r < 7, Commute X (classEnd (R := Ω) 14 16 20 e r) := fun r hr =>
      commute_classes_of_outer hFsc hFs7 (fun a ha => by
        rw [← outer_expand_y_two]
        exact commute_outerY_of_mem hFr he hX (hFs8 a ha)) hr
    obtain ⟨m1, m2⟩ := commute_middle_of_mem hFr he hX (one_pow 2)
    rw [xOp_eq_lab, one_smul, one_pow, one_smul, add_assoc] at m1
    rw [yOp_eq_lab, one_smul, one_pow, one_smul, add_assoc] at m2
    have hM₁ := commute_of_commute_one_add m1
    have hM₂ := commute_of_commute_one_add m2
    intro k c
    rcases he with rfl | rfl
    · exact commute_of_d4Cert d4LettersOK_one d4TargetsOK_one hP hQ hM₁ hM₂ k k.2 c
    · exact commute_of_d4Cert d4LettersOK_two d4TargetsOK_two hP hQ hM₁ hM₂ k k.2 c

theorem simpleRootSL2_mem_d4Layer {q : ℕ} {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ}
    (he : e = 1 ∨ e = 2) {k : Type} [Field k] (ι : k →+* Ω) (hι : ∀ b, ι b ^ q = ι b)
    (A : SL(2, k)) :
    simpleRootSL2 Tag.E6 Ω (d4Idx 2) (Matrix.SpecialLinearGroup.map ι A) ∈ d4Layer Fr e := by
  have hT : (d4Layer Fr e).comap ((simpleRootSL2 Tag.E6 Ω (d4Idx 2)).comp
      (Matrix.SpecialLinearGroup.map ι)) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower :
      Subgroup.closure (Set.range (uSL (K := k)) ∪ Set.range vSL) = ⊤), Subgroup.closure_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · change simpleRootSL2 Tag.E6 Ω (d4Idx 2) (Matrix.SpecialLinearGroup.map ι (uSL b)) ∈
        d4Layer Fr e
      rw [map_uSL, simpleRootSL2_uSL]
      exact ⟨_, (d4Middle_mem_d4ThetaFixed hFr he (hι b)).1, rfl⟩
    · change simpleRootSL2 Tag.E6 Ω (d4Idx 2) (Matrix.SpecialLinearGroup.map ι (vSL b)) ∈
        d4Layer Fr e
      rw [map_vSL, simpleRootSL2_vSL]
      exact ⟨_, (d4Middle_mem_d4ThetaFixed hFr he (hι b)).2, rfl⟩
  have hA : A ∈ (d4Layer Fr e).comap ((simpleRootSL2 Tag.E6 Ω (d4Idx 2)).comp
      (Matrix.SpecialLinearGroup.map ι)) := hT ▸ Subgroup.mem_top A
  exact hA

end CFSG.RankThree.Chevalley
