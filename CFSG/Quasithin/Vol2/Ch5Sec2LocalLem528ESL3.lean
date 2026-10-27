module

public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic

public section

namespace CFSG.Quasithin.H13.SL3E

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a

variable {F : Type} [Field F]

@[expose] def wSub : Subgroup (Multiplicative (Fin 3 → F)) where
  carrier := {x | Multiplicative.toAdd x 2 = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, toAdd_mul, Pi.add_apply] at hx hy ⊢
    rw [hx, hy, add_zero]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, toAdd_inv, Pi.neg_apply] at hx ⊢
    rw [hx, neg_zero]

@[expose] def fixSub (g : SpecialLinearGroup (Fin 3) F) :
    Subgroup (Multiplicative (Fin 3 → F)) where
  carrier := {x | (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, toAdd_mul, Matrix.mulVec_add] at hx hy ⊢
    rw [hx, hy]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, toAdd_inv, Matrix.mulVec_neg] at hx ⊢
    rw [hx]

theorem mem_fixSub {g : SpecialLinearGroup (Fin 3) F} {x : Multiplicative (Fin 3 → F)} :
    x ∈ fixSub g ↔
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x :=
  Iff.rfl

@[expose] def fixSubOf (E : Subgroup (SpecialLinearGroup (Fin 3) F)) :
    Subgroup (Multiplicative (Fin 3 → F)) :=
  ⨅ g ∈ E, fixSub g

theorem mem_fixSubOf {E : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {x : Multiplicative (Fin 3 → F)} : x ∈ fixSubOf E ↔ ∀ g ∈ E, x ∈ fixSub g := by
  simp [fixSubOf, Subgroup.mem_iInf]

theorem card_wSub_le [Finite F] : Nat.card (wSub (F := F)) ≤ Nat.card F ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x => (Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 0,
      Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 1)) fun x y hxy => ?_
  simp only [Prod.mk.injEq] at hxy
  have hx : Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 2 = 0 := x.2
  have hy : Multiplicative.toAdd (y : Multiplicative (Fin 3 → F)) 2 = 0 := y.2
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact hxy.1
  · exact hxy.2
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [hx, hy]

@[expose] def IsU2Mat (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∀ v : Fin 3 → F, (M *ᵥ v) 2 = v 2 ∧ (v 2 = 0 → M *ᵥ v = v)

@[expose] def IsU1Mat (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∀ v : Fin 3 → F, ((M *ᵥ v) 1 = v 1 ∧ (M *ᵥ v) 2 = v 2) ∧ (v 1 = 0 → v 2 = 0 → M *ᵥ v = v)

theorem IsU2Mat.mul {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsU2Mat M) (hN : IsU2Mat N) :
    IsU2Mat (M * N) := fun v => by
  rw [← Matrix.mulVec_mulVec]
  refine ⟨by rw [(hM _).1, (hN v).1], fun hv => ?_⟩
  rw [(hN v).2 hv, (hM v).2 hv]

theorem IsU2Mat.of_mul_eq_one {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsU2Mat M) (h : M * N = 1) :
    IsU2Mat N := fun v => by
  have hgw : M *ᵥ (N *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have h2 : (N *ᵥ v) 2 = v 2 := by
    have := (hM (N *ᵥ v)).1
    rw [hgw] at this
    exact this.symm
  refine ⟨h2, fun hv => ?_⟩
  have := (hM (N *ᵥ v)).2 (h2.trans hv)
  rw [hgw] at this
  exact this.symm

theorem IsU1Mat.mul {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsU1Mat M) (hN : IsU1Mat N) :
    IsU1Mat (M * N) := fun v => by
  rw [← Matrix.mulVec_mulVec]
  refine ⟨⟨by rw [(hM _).1.1, (hN v).1.1], by rw [(hM _).1.2, (hN v).1.2]⟩, fun h1 h2 => ?_⟩
  rw [(hN v).2 h1 h2, (hM v).2 h1 h2]

theorem IsU1Mat.of_mul_eq_one {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsU1Mat M) (h : M * N = 1) :
    IsU1Mat N := fun v => by
  have hgw : M *ᵥ (N *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have h1 : (N *ᵥ v) 1 = v 1 := by
    have := (hM (N *ᵥ v)).1.1
    rw [hgw] at this
    exact this.symm
  have h2 : (N *ᵥ v) 2 = v 2 := by
    have := (hM (N *ᵥ v)).1.2
    rw [hgw] at this
    exact this.symm
  refine ⟨⟨h1, h2⟩, fun hv1 hv2 => ?_⟩
  have := (hM (N *ᵥ v)).2 (h1.trans hv1) (h2.trans hv2)
  rw [hgw] at this
  exact this.symm

theorem coe_mul_coe_inv (g : SpecialLinearGroup (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] def U2 : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | IsU2Mat (g : Matrix (Fin 3) (Fin 3) F)}
  one_mem' := fun v => by simp
  mul_mem' := fun {g h} hg hh => by
    show IsU2Mat ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact IsU2Mat.mul hg hh
  inv_mem' := fun {g} hg => IsU2Mat.of_mul_eq_one hg (coe_mul_coe_inv g)

@[expose] def U1 : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | IsU1Mat (g : Matrix (Fin 3) (Fin 3) F)}
  one_mem' := fun v => by simp
  mul_mem' := fun {g h} hg hh => by
    show IsU1Mat ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact IsU1Mat.mul hg hh
  inv_mem' := fun {g} hg => IsU1Mat.of_mul_eq_one hg (coe_mul_coe_inv g)

theorem mem_U2 {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ U2 ↔ IsU2Mat (g : Matrix (Fin 3) (Fin 3) F) := Iff.rfl

theorem U2_entries {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ U2) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  have e0 := (hg (Pi.single 0 1)).2 (by simp)
  have e1 := (hg (Pi.single 1 1)).2 (by simp)
  have e2 := (hg (Pi.single 2 1)).1
  have c00 := congrFun e0 0
  have c10 := congrFun e0 1
  have c20 := congrFun e0 2
  have c01 := congrFun e1 0
  have c11 := congrFun e1 1
  have c21 := congrFun e1 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at c00 c10 c20 c01 c11 c21 e2
  exact ⟨c00, c10, c20, c01, c11, c21, e2⟩

theorem U1_entries {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ U1) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  have e0 := (hg (Pi.single 0 1)).2 (by simp) (by simp)
  have e1 := (hg (Pi.single 1 1)).1
  have e2 := (hg (Pi.single 2 1)).1
  have c00 := congrFun e0 0
  have c10 := congrFun e0 1
  have c20 := congrFun e0 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at c00 c10 c20 e1 e2
  exact ⟨c00, c10, c20, e1.1, e1.2, e2.1, e2.2⟩

theorem U2_le_unitriangular : (U2 : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ unitriangular 3 F :=
  fun g hg => by
    obtain ⟨h00, h10, h20, -, h11, h21, h22⟩ := U2_entries hg
    exact mem_unitriangular_three h10 h20 h21 h00 h11 h22

theorem U1_le_unitriangular : (U1 : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ unitriangular 3 F :=
  fun g hg => by
    obtain ⟨h00, h10, h20, h11, h21, -, h22⟩ := U1_entries hg
    exact mem_unitriangular_three h10 h20 h21 h00 h11 h22

theorem unitriangular_entries {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ unitriangular 3 F) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 :=
  ⟨hg.2 0, hg.1 1 0 (by decide), hg.1 2 0 (by decide), hg.2 1, hg.1 2 1 (by decide), hg.2 2⟩

theorem mem_U2_of {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ unitriangular 3 F)
    (h01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) : g ∈ U2 := by
  obtain ⟨h00, h10, h20, h11, h21, h22⟩ := unitriangular_entries hg
  intro v
  refine ⟨?_, fun hv => ?_⟩
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22]
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h10, h20, h01, h11,
      h21, h22, hv]

theorem mem_U1_of {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ unitriangular 3 F)
    (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) : g ∈ U1 := by
  obtain ⟨h00, h10, h20, h11, h21, h22⟩ := unitriangular_entries hg
  intro v
  refine ⟨⟨?_, ?_⟩, fun hv1 hv2 => ?_⟩
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h11, h12]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22]
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h10, h20, h11, h21,
      h12, h22, hv1, hv2]

theorem mul_apply_01 {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ unitriangular 3 F)
    (hh : h ∈ unitriangular 3 F) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 =
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 + (h : Matrix (Fin 3) (Fin 3) F) 0 1 := by
  obtain ⟨g00, -, -, g11, -, -⟩ := unitriangular_entries hg
  obtain ⟨-, -, -, h11, h21, -⟩ := unitriangular_entries hh
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, g00, h11, h21]
  ring

theorem mul_apply_12 {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ unitriangular 3 F)
    (hh : h ∈ unitriangular 3 F) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 1 2 + (h : Matrix (Fin 3) (Fin 3) F) 1 2 := by
  obtain ⟨-, g10, -, g11, -, -⟩ := unitriangular_entries hg
  obtain ⟨-, -, -, -, -, h22⟩ := unitriangular_entries hh
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, g10, g11, h22]
  ring

theorem mul_01_12_eq_zero [CharP F 2] {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ unitriangular 3 F) (h2 : g * g = 1) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have hc : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨g00, -, -, g11, -, g22⟩ := unitriangular_entries hg
  have := congrArg (fun x : SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) 0 2) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, g00, g22,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] at this
  simp at this
  linear_combination this - (g : Matrix (Fin 3) (Fin 3) F) 0 2 * hc

theorem le_U1_or_le_U2 [CharP F 2] {E : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hE : E ≤ unitriangular 3 F) (h2 : ∀ x ∈ E, x * x = 1) : E ≤ U1 ∨ E ≤ U2 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨x, hxE, hx⟩ := Set.not_subset.mp hcon.1
  obtain ⟨y, hyE, hy⟩ := Set.not_subset.mp hcon.2
  have hx12 : (x : Matrix (Fin 3) (Fin 3) F) 1 2 ≠ 0 := fun h => hx (mem_U1_of (hE hxE) h)
  have hy01 : (y : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0 := fun h => hy (mem_U2_of (hE hyE) h)
  have hx01 : (x : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 :=
    (mul_eq_zero.mp (mul_01_12_eq_zero (hE hxE) (h2 x hxE))).resolve_right hx12
  have hy12 : (y : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 :=
    (mul_eq_zero.mp (mul_01_12_eq_zero (hE hyE) (h2 y hyE))).resolve_left hy01
  have hz := mul_01_12_eq_zero (hE (E.mul_mem hxE hyE)) (h2 _ (E.mul_mem hxE hyE))
  rw [mul_apply_01 (hE hxE) (hE hyE), mul_apply_12 (hE hxE) (hE hyE), hx01, hy12, zero_add,
    add_zero] at hz
  exact mul_ne_zero hy01 hx12 hz

theorem fixSub_le_wSub {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ U2) (hu1 : u ≠ 1) :
    fixSub u ≤ wSub := by
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := U2_entries hu
  intro x hx
  rw [mem_fixSub] at hx
  show Multiplicative.toAdd x 2 = 0
  by_contra hx2
  apply hu1
  have e0 := congrFun hx 0
  have e1 := congrFun hx 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h01, h10, h11] at e0 e1
  have c02 : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
    rcases e0 with h | h
    · exact h
    · exact absurd h hx2
  have c12 : (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    rcases e1 with h | h
    · exact h
    · exact absurd h hx2
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h01, h11, h21, h22, c02, c12]

theorem card_fixSub_le_of_mem_U1 [Finite F] {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ U1)
    (hu1 : u ≠ 1) : Nat.card (fixSub u) ≤ Nat.card F ^ 2 := by
  obtain ⟨h00, h10, h20, h11, h21, h12, h22⟩ := U1_entries hu
  have hfix : ∀ x : Multiplicative (Fin 3 → F), x ∈ fixSub u →
      (u : Matrix (Fin 3) (Fin 3) F) 0 1 * Multiplicative.toAdd x 1 +
        (u : Matrix (Fin 3) (Fin 3) F) 0 2 * Multiplicative.toAdd x 2 = 0 := by
    intro x hx
    have e0 := congrFun (mem_fixSub.mp hx) 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00] at e0
    linear_combination e0
  have hne : (u : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0 ∨ (u : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hu1
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h11, h21, h12, h22, hcon.1, hcon.2]
  rw [sq, ← Nat.card_prod]
  rcases hne with ha | hc
  ·
    refine Nat.card_le_card_of_injective
      (fun x => (Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 0,
        Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 2)) fun x y hxy => ?_
    simp only [Prod.mk.injEq] at hxy
    have hx := hfix x x.2
    have hy := hfix y y.2
    have h1 : Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 1 =
        Multiplicative.toAdd (y : Multiplicative (Fin 3 → F)) 1 := by
      apply mul_left_cancel₀ ha
      linear_combination hx - hy - (u : Matrix (Fin 3) (Fin 3) F) 0 2 * hxy.2
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hxy.1
    · exact h1
    · exact hxy.2
  · refine Nat.card_le_card_of_injective
      (fun x => (Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 0,
        Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 1)) fun x y hxy => ?_
    simp only [Prod.mk.injEq] at hxy
    have hx := hfix x x.2
    have hy := hfix y y.2
    have h2 : Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 2 =
        Multiplicative.toAdd (y : Multiplicative (Fin 3 → F)) 2 := by
      apply mul_left_cancel₀ hc
      linear_combination hx - hy - (u : Matrix (Fin 3) (Fin 3) F) 0 1 * hxy.2
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hxy.1
    · exact hxy.2
    · exact h2

@[expose] def u1El (a c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, a, c; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem u1El_mem (a c : F) : u1El a c ∈ U1 := by
  refine mem_U1_of (mem_unitriangular_three ?_ ?_ ?_ ?_ ?_ ?_) ?_ <;> simp [u1El]

theorem card_fixSubOf_U1_le [Finite F] :
    Nat.card (fixSubOf (U1 : Subgroup (SpecialLinearGroup (Fin 3) F))) ≤ Nat.card F := by
  refine Nat.card_le_card_of_injective
    (fun x => Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)) 0) fun x y hxy => ?_
  have hx := mem_fixSubOf.mp x.2
  have hy := mem_fixSubOf.mp y.2
  have h1 : ∀ z : Multiplicative (Fin 3 → F), (∀ g ∈ U1, z ∈ fixSub g) →
      Multiplicative.toAdd z 1 = 0 ∧ Multiplicative.toAdd z 2 = 0 := by
    intro z hz
    have e1 := congrFun (mem_fixSub.mp (hz _ (u1El_mem 1 0))) 0
    have e2 := congrFun (mem_fixSub.mp (hz _ (u1El_mem 0 1))) 0
    simp [u1El, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1 e2
    exact ⟨e1, e2⟩
  obtain ⟨x1, x2⟩ := h1 _ hx
  obtain ⟨y1, y2⟩ := h1 _ hy
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact hxy
  · simp only [Fin.mk_one, Fin.isValue]; rw [x1, y1]
  · simp only [Fin.reduceFinMk, Fin.isValue]; rw [x2, y2]

theorem card_U1_le [Finite F] :
    Nat.card (U1 : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ Nat.card F ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun g => (((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1,
      ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2)) fun g h hgh => ?_
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨g00, g10, g20, g11, g21, g12, g22⟩ := U1_entries g.2
  obtain ⟨h00, h10, h20, h11, h21, h12, h22⟩ := U1_entries h.2
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem card_U2_le [Finite F] :
    Nat.card (U2 : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ Nat.card F ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun g => (((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2,
      ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2)) fun g h hgh => ?_
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨g00, g10, g20, g01, g11, g21, g22⟩ := U2_entries g.2
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := U2_entries h.2
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem mulVec_two_eq_zero_of_mem_Q31 {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ Q3 F 1)
    {v : Fin 3 → F} (hv : v 2 = 0) : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 = 0 := by
  have hg' : g ∈ stabilizer (flagSpace 3 F 2) := hg
  have h20 := stabilizer_entries (k := 2) (l := 0) hg' (by norm_num) (by norm_num)
  have h21 := stabilizer_entries (k := 2) (l := 1) hg' (by norm_num) (by norm_num)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, hv]

theorem U2_normal {g u : SpecialLinearGroup (Fin 3) F} (hg : g ∈ Q3 F 1) (hu : u ∈ U2) :
    g * u * g⁻¹ ∈ U2 := by
  have hgi : g⁻¹ ∈ Q3 F 1 := (Q3 F 1).inv_mem hg
  rw [mem_U2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  intro v
  set v' := ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hv'
  have hgv' : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v' = v := by
    rw [hv', Matrix.mulVec_mulVec, coe_mul_coe_inv, Matrix.one_mulVec]
  have hu' := (mem_U2.mp hu) v'
  set w := (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v' - v' with hw
  have hw2 : w 2 = 0 := by rw [hw, Pi.sub_apply, hu'.1, sub_self]
  have huv : (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v' = v' + w := by rw [hw]; abel
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hv', huv, Matrix.mulVec_add, hgv']
  refine ⟨?_, fun hv2 => ?_⟩
  · rw [Pi.add_apply, mulVec_two_eq_zero_of_mem_Q31 hg hw2, add_zero]
  · have hv'2 : v' 2 = 0 := mulVec_two_eq_zero_of_mem_Q31 hgi hv2
    have hw0 : w = 0 := by rw [hw, hu'.2 hv'2, sub_self]
    rw [hw0, Matrix.mulVec_zero, add_zero]

@[expose] def xEl (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def yEl (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def diag2 (μ : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem coe_xEl (t : F) : ((xEl t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, t; 0, 1] := rfl

theorem coe_yEl (t : F) : ((yEl t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, 0; t, 1] := rfl

theorem coe_diag2 (μ : Fˣ) : ((diag2 μ : SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)] := rfl

@[expose] noncomputable def dMat (μ : Fˣ) : SpecialLinearGroup (Fin 3) F := embSL 1 (diag2 μ)

theorem coe_dMat (μ : Fˣ) : ((dMat μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![(μ : F), 0, 0; 0, ((μ⁻¹ : Fˣ) : F), 0; 0, 0, 1] := by
  rw [dMat, coe_embSL, coe_diag2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat]

theorem diag2_mul (μ ν : Fˣ) : diag2 (μ * ν) = diag2 μ * diag2 ν := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag2, coe_diag2, coe_diag2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dMat_mul (μ ν : Fˣ) : dMat (μ * ν) = dMat μ * dMat ν := by
  rw [dMat, dMat, dMat, diag2_mul, map_mul]

theorem dMat_one : dMat (1 : Fˣ) = 1 := by
  have h := dMat_mul (F := F) 1 1
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem dMat_pow (μ : Fˣ) (k : ℕ) : dMat (μ ^ k) = dMat μ ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, dMat_one]
  | succ k ih => rw [pow_succ, dMat_mul, ih, pow_succ]

theorem xEl_mul_self [CharP F 2] (t : F) : xEl t * xEl t = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_xEl, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination t * h2

theorem yEl_mul_self [CharP F 2] (t : F) : yEl t * yEl t = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_yEl, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination t * h2

@[expose] def wEl [CharP F 2] (μ : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, (μ : F); ((μ⁻¹ : Fˣ) : F), 0], by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [Matrix.det_fin_two_of]
    simp only [zero_mul, Units.mul_inv, zero_sub]
    linear_combination -h2⟩

theorem coe_wEl [CharP F 2] (μ : Fˣ) :
    ((wEl μ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, (μ : F); ((μ⁻¹ : Fˣ) : F), 0] := rfl

theorem xyx_eq [CharP F 2] (μ : Fˣ) : xEl (μ : F) * yEl ((μ⁻¹ : Fˣ) : F) * xEl (μ : F) = wEl μ := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_xEl, coe_yEl, coe_wEl]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem diag2_eq [CharP F 2] (μ : Fˣ) :
    diag2 μ = xEl (μ : F) * yEl ((μ⁻¹ : Fˣ) : F) * xEl (μ : F) * (xEl 1 * yEl 1 * xEl 1) := by
  have h1 := xyx_eq (F := F) 1
  simp only [Units.val_one, inv_one] at h1
  rw [xyx_eq, h1]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_wEl, coe_diag2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dMat_mem_closure [CharP F 2] (μ : Fˣ) :
    dMat μ ∈ Subgroup.closure {x : SpecialLinearGroup (Fin 3) F | x ∈ Q3 F 1 ∧ x * x = 1} := by
  have hgen : ∀ A : SpecialLinearGroup (Fin 2) F, A * A = 1 →
      embSL 1 A ∈ Subgroup.closure {x : SpecialLinearGroup (Fin 3) F | x ∈ Q3 F 1 ∧ x * x = 1} :=
    fun A hA => Subgroup.subset_closure ⟨embSL_mem_Q3 1 A, by rw [← map_mul, hA, map_one]⟩
  rw [dMat, diag2_eq, map_mul, map_mul, map_mul, map_mul, map_mul]
  refine mul_mem (mul_mem (mul_mem (hgen _ (xEl_mul_self _)) (hgen _ (yEl_mul_self _)))
    (hgen _ (xEl_mul_self _))) (mul_mem (mul_mem (hgen _ (xEl_mul_self _))
      (hgen _ (yEl_mul_self _))) (hgen _ (xEl_mul_self _)))

theorem fixSub_dMat_inf_wSub {μ : Fˣ} (hμ : μ ≠ 1) (x : Multiplicative (Fin 3 → F))
    (hx : x ∈ fixSub (dMat μ)) (hxW : x ∈ wSub) : x = 1 := by
  rw [mem_fixSub, coe_dMat] at hx
  have hx2 : Multiplicative.toAdd x 2 = 0 := hxW
  have e0 := congrFun hx 0
  have e1 := congrFun hx 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1
  have hμ1 : (μ : F) ≠ 1 := fun h => hμ (Units.ext h)
  have hμi : (μ : F)⁻¹ ≠ 1 := fun h => hμ1 (inv_eq_one.mp h)
  have x0 : Multiplicative.toAdd x 0 = 0 := by
    have : ((μ : F) - 1) * Multiplicative.toAdd x 0 = 0 := by linear_combination e0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ1)
  have x1 : Multiplicative.toAdd x 1 = 0 := by
    have : ((μ : F)⁻¹ - 1) * Multiplicative.toAdd x 1 = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμi)
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact x0
  · exact x1
  · exact hx2

theorem eq_one_of_dMat_conj {μ : Fˣ} (hμ : μ ≠ 1) {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ U2) (hc : dMat μ * u = u * dMat μ) : u = 1 := by
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := U2_entries hu
  have e02 := congrArg
    (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 2) hc
  have e12 := congrArg
    (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 2) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat, Matrix.mul_apply,
    Fin.sum_univ_three] at e02 e12
  simp [h00, h10, h01, h11, h22] at e02 e12
  have hμ1 : (μ : F) ≠ 1 := fun h => hμ (Units.ext h)
  have hμi : (μ : F)⁻¹ ≠ 1 := fun h => hμ1 (inv_eq_one.mp h)
  have c02 : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
    have : ((μ : F) - 1) * (u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by linear_combination e02
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ1)
  have c12 : (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    have : ((μ : F)⁻¹ - 1) * (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
      linear_combination e12
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμi)
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h01, h11, h21, h22, c02, c12]

theorem conj_mem_perfectCore {G : Type*} [Group G] {H : Subgroup G} {g h : G} (hg : g ∈ H)
    (hh : h ∈ perfectCore H) : g * h * g⁻¹ ∈ perfectCore H := by
  have hn := CFSG.Quasithin.perfectCore_normal H
  have hhH : h ∈ H := CFSG.Quasithin.perfectCore_le H hh
  have := hn.conj_mem ⟨h, hhH⟩ hh ⟨g, hg⟩
  exact this

theorem exists_unit_ne_one (hK : ∃ s : Finset F, s.card = 4) : ∃ μ : Fˣ, μ ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := hK
  have hcard : 0 < ((s.erase 0).erase 1).card := by
    have h1 := Finset.pred_card_le_card_erase (s := s.erase 0) (a := 1)
    have h2 := Finset.pred_card_le_card_erase (s := s) (a := 0)
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard
  have ha1 : a ≠ 1 := Finset.ne_of_mem_erase ha
  have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha)
  refine ⟨Units.mk0 a ha0, fun h => ha1 ?_⟩
  have := congrArg Units.val h
  simpa using this

@[expose] def u2El (b c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem u2El_mem (b c : F) : u2El b c ∈ U2 := by
  refine mem_U2_of (mem_unitriangular_three ?_ ?_ ?_ ?_ ?_ ?_) ?_ <;> simp [u2El]

theorem unitriangular_le_Q3 (j : Fin 2) : unitriangular 3 F ≤ Q3 F j := by
  rw [Q3_eq]
  exact (unitriangular_le_upperTriangular 3 F).trans (upperTriangular_le_flagStabilizer _)

theorem eq_one_of_fixed_perfectCore_Q31 [Finite F] [CharP F 2]
    (hK : ∃ s : Finset F, s.card = 4) (x : Multiplicative (Fin 3 → F))
    (hx : ∀ g ∈ perfectCore (Q3 F 1), x ∈ fixSub g) : x = 1 := by
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one hK
  have hμ1 : (μ : F) ≠ 1 := fun h => hμ (Units.ext h)
  have hD : dMat μ ∈ perfectCore (Q3 F 1) := embSL_mem_perfectCore hK 1 _
  set v := Multiplicative.toAdd x with hv
  have hX := mem_fixSub.mp (hx _ (embSL_mem_perfectCore hK 1 (xEl 1)))
  have hY := mem_fixSub.mp (hx _ (embSL_mem_perfectCore hK 1 (yEl 1)))
  rw [coe_embSL, coe_xEl] at hX
  rw [coe_embSL, coe_yEl] at hY
  have v1 : v 1 = 0 := by
    have := congrFun hX 0
    simp [embMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    exact this
  have v0 : v 0 = 0 := by
    have := congrFun hY 1
    simp [embMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    exact this
  set u := u2El (F := F) 0 1 with hu
  have huQ : u ∈ Q3 F 1 := unitriangular_le_Q3 1 (U2_le_unitriangular (u2El_mem 0 1))
  have hc := mem_fixSub.mp (hx _ (conj_mem_perfectCore huQ hD))
  set y := ((u⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hy
  have huy : (u : Matrix (Fin 3) (Fin 3) F) *ᵥ y = v := by
    rw [hy, Matrix.mulVec_mulVec, coe_mul_coe_inv, Matrix.one_mulVec]
  have hcancel : ∀ w : Fin 3 → F, ((u⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hDy : ((dMat μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
    have h1 := congrArg (fun w => ((u⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w) hc
    simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec] at h1
    rw [← hv, ← hy, hcancel] at h1
    exact h1
  have e0 := congrFun huy 0
  have e2 := congrFun huy 2
  have d0 := congrFun hDy 0
  simp [hu, u2El, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e2
  rw [coe_dMat] at d0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at d0
  have y0 : y 0 = 0 := by
    have : ((μ : F) - 1) * y 0 = 0 := by linear_combination d0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ1)
  have v2 : v 2 = 0 := by
    rw [← e2]
    linear_combination e0 + v0 - y0
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact v0
  · exact v1
  · exact v2

theorem u1El_mem_Q30 (a c : F) : u1El a c ∈ Q3 F 0 :=
  unitriangular_le_Q3 0 (U1_le_unitriangular (u1El_mem a c))

theorem mulVec_u1El (a c : F) (v : Fin 3 → F) :
    ((u1El a c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ![v 0 + a * v 1 + c * v 2, v 1, v 2] := by
  funext i
  fin_cases i <;> simp [u1El, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mulVec_embMat0_diag (μ : Fˣ) (v : Fin 3 → F) :
    embMat 0 !![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)] *ᵥ v =
      ![v 0, (μ : F) * v 1, ((μ⁻¹ : Fˣ) : F) * v 2] := by
  funext i
  fin_cases i <;> simp [embMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem eq_top_of_perfectCore_Q30 [Finite F] [CharP F 2] (hK : ∃ s : Finset F, s.card = 4)
    (S : Subgroup (Multiplicative (Fin 3 → F)))
    (hS : ∀ g ∈ perfectCore (Q3 F 0), ∀ x : Multiplicative (Fin 3 → F),
      Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd x) * x⁻¹ ∈ S) :
    S = ⊤ := by
  have hS' : ∀ g ∈ perfectCore (Q3 F 0), ∀ v : Fin 3 → F,
      Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) ∈ S := by
    intro g hg v
    have := hS g hg (Multiplicative.ofAdd v)
    simpa [sub_eq_add_neg] using this
  have h1 : ∀ c : F, Multiplicative.ofAdd (![0, c, 0] : Fin 3 → F) ∈ S := by
    intro c
    have := hS' _ (embSL_mem_perfectCore hK 0 (xEl c)) (Pi.single 2 1)
    rw [coe_embSL, coe_xEl] at this
    convert this using 2
    funext i
    fin_cases i <;> simp [embMat]
  have h2 : ∀ c : F, Multiplicative.ofAdd (![0, 0, c] : Fin 3 → F) ∈ S := by
    intro c
    have := hS' _ (embSL_mem_perfectCore hK 0 (yEl c)) (Pi.single 1 1)
    rw [coe_embSL, coe_yEl] at this
    convert this using 2
    funext i
    fin_cases i <;> simp [embMat]
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one hK
  have hμ1 : (μ : F) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hμ (Units.ext h)
  have h0 : ∀ c : F, Multiplicative.ofAdd (![c, 0, 0] : Fin 3 → F) ∈ S := by
    intro c
    have hdP : embSL (K := F) 0 (diag2 μ) ∈ perfectCore (Q3 F 0) := embSL_mem_perfectCore hK 0 _
    have hc := hS' _ (conj_mem_perfectCore (u1El_mem_Q30 (c / ((μ : F) - 1)) 0) hdP)
      (((u1El (c / ((μ : F) - 1)) 0 : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1)
    have hcancel : (((u1El (c / ((μ : F) - 1)) 0)⁻¹ : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ (((u1El (c / ((μ : F) - 1)) 0 :
          SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1) =
          Pi.single 1 1 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel, coe_embSL, coe_diag2] at hc
    rw [mulVec_u1El, mulVec_embMat0_diag, mulVec_u1El] at hc
    have hm := mul_mem hc (inv_mem (h1 ((μ : F) - 1)))
    convert hm using 1
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    have hμ0 : (μ : F) - 1 ≠ 0 := hμ1
    funext i
    fin_cases i <;> simp
    field_simp
  rw [eq_top_iff]
  intro x _
  have hx : x = Multiplicative.ofAdd (![Multiplicative.toAdd x 0, 0, 0] : Fin 3 → F) *
      Multiplicative.ofAdd (![0, Multiplicative.toAdd x 1, 0] : Fin 3 → F) *
        Multiplicative.ofAdd (![0, 0, Multiplicative.toAdd x 2] : Fin 3 → F) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  rw [hx]
  exact mul_mem (mul_mem (h0 _) (h1 _)) (h2 _)

theorem eq_Q3_of_isMaxParabolic2 [Finite F] [CharP F 2]
    {P : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : CFSG.Quasithin.IsMaxParabolic2 ⊤ P)
    (hB : upperTriangular 3 F ≤ P) : P = Q3 F 0 ∨ P = Q3 F 1 := by
  have := Fintype.ofFinite F
  obtain ⟨k, hp, hk⟩ := FiniteField.card F 2
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨k, by rw [Nat.card_eq_fintype_card, hk]⟩
  obtain ⟨-, -, hmax, -⟩ := CFSG.Quasithin.SzN2.sl3_residualOvergroupsAt hK
  obtain ⟨M, hMc, hPM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom P).resolve_left hP.2.1
  have hUM : unitriangular 3 F ≤ M :=
    (unitriangular_le_upperTriangular 3 F).trans (hB.trans hPM)
  obtain ⟨j, rfl⟩ := (hmax M hUM).mp (covBy_top_iff.mpr hMc)
  have hpar : CFSG.Quasithin.IsParabolic2 ⊤ (Q3 F j) := by
    refine ⟨le_top, unitriangular 3 F,
      CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (by norm_num), ?_⟩
    rw [normalizer_unitriangular, Q3_eq]
    exact inf_le_right.trans (upperTriangular_le_flagStabilizer _)
  have := hP.2.2 (Q3 F j) hpar hMc.1 hPM
  fin_cases j
  · exact Or.inl this.symm
  · exact Or.inr this.symm

theorem mulVec_of_mem_U2 {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ U2) (v : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 0 + (g : Matrix (Fin 3) (Fin 3) F) 0 2 * v 2,
      v 1 + (g : Matrix (Fin 3) (Fin 3) F) 1 2 * v 2, v 2] := by
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := U2_entries hg
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h10, h20, h01, h11,
    h21, h22]

theorem mul_apply_U2 {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ U2) (hh : h ∈ U2) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 0 2 + (h : Matrix (Fin 3) (Fin 3) F) 0 2 ∧
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 1 2 + (h : Matrix (Fin 3) (Fin 3) F) 1 2 := by
  obtain ⟨g00, g10, g20, g01, g11, g21, g22⟩ := U2_entries hg
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := U2_entries hh
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [g00, g01, g11, g10, h22]
  constructor <;> ring

theorem U2_ne_one {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ U2) (hu1 : u ≠ 1) :
    (u : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 ∨ (u : Matrix (Fin 3) (Fin 3) F) 1 2 ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := U2_entries hu
  apply hu1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h01, h11, h21, h22, hcon.1, hcon.2]

end CFSG.Quasithin.H13.SL3E
