module

public import CFSG.Quasithin.H13.NQCatA314CentL35
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Quasithin

theorem sl35_mul_apply (a b : SpecialLinearGroup (Fin 3) (ZMod 5)) (i j : Fin 3) :
    ((a * b : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) i j =
      ∑ k, (a : Matrix (Fin 3) (Fin 3) (ZMod 5)) i k * (b : Matrix (Fin 3) (Fin 3) (ZMod 5)) k j :=
  rfl

theorem sl35_inv_eq (a : SpecialLinearGroup (Fin 3) (ZMod 5)) :
    ((a⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      adjugate (a : Matrix (Fin 3) (Fin 3) (ZMod 5)) :=
  Matrix.SpecialLinearGroup.coe_inv a

theorem sl35_det (a : SpecialLinearGroup (Fin 3) (ZMod 5)) :
    (a : Matrix (Fin 3) (Fin 3) (ZMod 5)).det = 1 :=
  a.2

@[expose] def Pl : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2⟩ := ha
    obtain ⟨b1, b2⟩ := hb
    refine ⟨?_, ?_⟩ <;> rw [sl35_mul_apply, Fin.sum_univ_three] <;> simp [a1, a2, b1, b2]
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2⟩ := ha
    refine ⟨?_, ?_⟩ <;> rw [sl35_inv_eq] <;> simp [adjugate_fin_three, a1, a2]

@[expose] def Ppl : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1 = 0}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2⟩ := ha
    obtain ⟨b1, b2⟩ := hb
    refine ⟨?_, ?_⟩ <;> rw [sl35_mul_apply, Fin.sum_univ_three] <;> simp [a1, a2, b1, b2]
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2⟩ := ha
    refine ⟨?_, ?_⟩ <;> rw [sl35_inv_eq] <;> simp [adjugate_fin_three, a1, a2]

@[expose] def Kl : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3⟩ := ha
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨?_, ?_, ?_⟩ <;> rw [sl35_mul_apply, Fin.sum_univ_three] <;>
      simp [a1, a2, a3, b1, b2, b3]
  one_mem' := ⟨by simp, by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2, a3⟩ := ha
    have hdet := sl35_det a
    rw [Matrix.det_fin_three, a1, a2, a3] at hdet
    refine ⟨?_, ?_, ?_⟩ <;> rw [sl35_inv_eq] <;> simp [adjugate_fin_three, a1, a2]
    linear_combination hdet

@[expose] def Kpl : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3⟩ := ha
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨?_, ?_, ?_⟩ <;> rw [sl35_mul_apply, Fin.sum_univ_three] <;>
      simp [a1, a2, a3, b1, b2, b3]
  one_mem' := ⟨by simp, by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2, a3⟩ := ha
    have hdet := sl35_det a
    rw [Matrix.det_fin_three, a1, a2, a3] at hdet
    refine ⟨?_, ?_, ?_⟩ <;> rw [sl35_inv_eq] <;> simp [adjugate_fin_three, a1, a2]
    linear_combination hdet

@[expose] def U5 : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 = 1 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [sl35_mul_apply, Fin.sum_univ_three] <;>
      simp [a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
  one_mem' := ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [sl35_inv_eq] <;>
      simp [adjugate_fin_three, a1, a2, a3, a4, a5, a6]

theorem Kl_le_Pl : Kl ≤ Pl := fun _ h => ⟨h.1, h.2.1⟩

theorem Kpl_le_Ppl : Kpl ≤ Ppl := fun _ h => ⟨h.1, h.2.1⟩

theorem card_sl35 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 5)) = 372000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three, ZMod.card]

@[expose] def klMk (p : ZMod 5 × ZMod 5 ×
    {q : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1}) :
    SpecialLinearGroup (Fin 3) (ZMod 5) :=
  ⟨!![1, p.1, p.2.1; 0, p.2.2.1.1, p.2.2.1.2.1; 0, p.2.2.1.2.2.1, p.2.2.1.2.2.2], by
    rw [Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    have h := p.2.2.2
    linear_combination h⟩

theorem card_Kl : Nat.card Kl = 3000 := by
  have hrow : ∀ g ∈ Kl, (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 - (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1 = 1 := by
    intro g hg
    obtain ⟨a, b, c⟩ := hg
    have hdet := sl35_det g
    rw [Matrix.det_fin_three, a, b, c] at hdet
    linear_combination hdet
  let f : Kl → ZMod 5 × ZMod 5 ×
      {q : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1} := fun g =>
    ((g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 1, (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 2,
      ⟨((g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 1,
        (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 2,
        (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 2 1,
        (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 2 2), hrow _ g.2⟩)
  have hmk : ∀ p, klMk p ∈ Kl := fun p => ⟨rfl, rfl, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      obtain ⟨a, b, c⟩ := g.2
      obtain ⟨a', b', c'⟩ := g'.2
      apply Subtype.ext
      ext r s
      fin_cases r <;> fin_cases s
      · exact c.trans c'.symm
      · exact h1
      · exact h2
      · exact a.trans a'.symm
      · exact h3
      · exact h4
      · exact b.trans b'.symm
      · exact h5
      · exact h6
    · intro p
      refine ⟨⟨klMk p, hmk p⟩, ?_⟩
      rfl
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, card_detPairs,
    Nat.card_zmod]

@[expose] def kplMk (p : ZMod 5 × ZMod 5 ×
    {q : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1}) :
    SpecialLinearGroup (Fin 3) (ZMod 5) :=
  ⟨!![p.2.2.1.1, p.2.2.1.2.1, p.1; p.2.2.1.2.2.1, p.2.2.1.2.2.2, p.2.1; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    have h := p.2.2.2
    linear_combination h⟩

theorem card_Kpl : Nat.card Kpl = 3000 := by
  have hrow : ∀ g ∈ Kpl, (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 - (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 1 *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0 = 1 := by
    intro g hg
    obtain ⟨a, b, c⟩ := hg
    have hdet := sl35_det g
    rw [Matrix.det_fin_three, a, b, c] at hdet
    linear_combination hdet
  let f : Kpl → ZMod 5 × ZMod 5 ×
      {q : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1} := fun g =>
    ((g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 2, (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 2,
      ⟨((g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 0,
        (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 1,
        (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 0,
        (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 1), hrow _ g.2⟩)
  have hmk : ∀ p, kplMk p ∈ Kpl := fun p => ⟨rfl, rfl, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      obtain ⟨a, b, c⟩ := g.2
      obtain ⟨a', b', c'⟩ := g'.2
      apply Subtype.ext
      ext r s
      fin_cases r <;> fin_cases s
      · exact h3
      · exact h4
      · exact h1
      · exact h5
      · exact h6
      · exact h2
      · exact a.trans a'.symm
      · exact b.trans b'.symm
      · exact c.trans c'.symm
    · intro p
      refine ⟨⟨kplMk p, hmk p⟩, ?_⟩
      rfl
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, card_detPairs,
    Nat.card_zmod]

theorem Pl_det {g : SpecialLinearGroup (Fin 3) (ZMod 5)} (hg : g ∈ Pl) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 * ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 - (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1) = 1 := by
  obtain ⟨a, b⟩ := hg
  have hdet := sl35_det g
  rw [Matrix.det_fin_three, a, b] at hdet
  linear_combination hdet

theorem Ppl_det {g : SpecialLinearGroup (Fin 3) (ZMod 5)} (hg : g ∈ Ppl) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 * ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 - (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 1 *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0) = 1 := by
  obtain ⟨a, b⟩ := hg
  have hdet := sl35_det g
  rw [Matrix.det_fin_three, a, b] at hdet
  linear_combination hdet

theorem mul00_of_mem_Pl (a : SpecialLinearGroup (Fin 3) (ZMod 5))
    {b : SpecialLinearGroup (Fin 3) (ZMod 5)} (hb : b ∈ Pl) :
    ((a * b : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 =
      (a : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 * (b : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 := by
  obtain ⟨b1, b2⟩ := hb
  rw [sl35_mul_apply, Fin.sum_univ_three, b1, b2]
  ring

theorem mul22_of_mem_Ppl {a : SpecialLinearGroup (Fin 3) (ZMod 5)} (ha : a ∈ Ppl)
    (b : SpecialLinearGroup (Fin 3) (ZMod 5)) :
    ((a * b : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 =
      (a : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 * (b : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 := by
  obtain ⟨a1, a2⟩ := ha
  rw [sl35_mul_apply, Fin.sum_univ_three, a1, a2]
  ring

@[expose] noncomputable def chiPl : ↥Pl →* (ZMod 5)ˣ where
  toFun g := Units.mkOfMulEqOne _ _ (Pl_det g.2)
  map_one' := Units.ext (by simp)
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mkOfMulEqOne, Units.val_mul]
    exact mul00_of_mem_Pl a b.2

@[expose] noncomputable def chiPpl : ↥Ppl →* (ZMod 5)ˣ where
  toFun g := Units.mkOfMulEqOne _ _ (Ppl_det g.2)
  map_one' := Units.ext (by simp)
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mkOfMulEqOne, Units.val_mul]
    exact mul22_of_mem_Ppl a.2 b

theorem ker_chiPl : chiPl.ker = Kl.subgroupOf Pl := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 := congrArg Units.val h
    simp only [chiPl, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mkOfMulEqOne, Units.val_one] at h1
    exact ⟨g.2.1, g.2.2, h1⟩
  · intro h
    apply Units.ext
    simp only [chiPl, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mkOfMulEqOne, Units.val_one]
    exact h.2.2

theorem ker_chiPpl : chiPpl.ker = Kpl.subgroupOf Ppl := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 := congrArg Units.val h
    simp only [chiPpl, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mkOfMulEqOne,
      Units.val_one] at h1
    exact ⟨g.2.1, g.2.2, h1⟩
  · intro h
    apply Units.ext
    simp only [chiPpl, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mkOfMulEqOne, Units.val_one]
    exact h.2.2

@[expose] def diagU (u : (ZMod 5)ˣ) : SpecialLinearGroup (Fin 3) (ZMod 5) :=
  ⟨diagonal ![(u : ZMod 5), (u⁻¹ : (ZMod 5)ˣ), 1], by
    simp [det_diagonal, Fin.prod_univ_three]⟩

theorem chiPl_surjective : Function.Surjective chiPl := by
  intro u
  refine ⟨⟨diagU u⁻¹⁻¹, ⟨by simp [diagU], by simp [diagU]⟩⟩, ?_⟩
  apply Units.ext
  simp [chiPl, diagU]

@[expose] def diagU' (u : (ZMod 5)ˣ) : SpecialLinearGroup (Fin 3) (ZMod 5) :=
  ⟨diagonal ![1, (u⁻¹ : (ZMod 5)ˣ), (u : ZMod 5)], by
    simp [det_diagonal, Fin.prod_univ_three]⟩

theorem chiPpl_surjective : Function.Surjective chiPpl := by
  intro u
  refine ⟨⟨diagU' u, ⟨by simp [diagU'], by simp [diagU']⟩⟩, ?_⟩
  apply Units.ext
  simp [chiPpl, diagU']

theorem card_units_five : Nat.card (ZMod 5)ˣ = 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units]

theorem card_Pl : Nat.card Pl = 12000 := by
  have h := Subgroup.card_ker_mul_card_of_surjective chiPl_surjective
  rw [ker_chiPl, card_units_five,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Kl_le_Pl).toEquiv, card_Kl] at h
  omega

theorem card_Ppl : Nat.card Ppl = 12000 := by
  have h := Subgroup.card_ker_mul_card_of_surjective chiPpl_surjective
  rw [ker_chiPpl, card_units_five,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Kpl_le_Ppl).toEquiv, card_Kpl] at h
  omega

theorem isCoatom_Pl : IsCoatom Pl := by
  apply Subgroup.isCoatom_of_index_prime
  have h := Pl.index_mul_card
  rw [card_Pl, card_sl35] at h
  have h31 : Pl.index = 31 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 12000) (h.trans (by norm_num))
  rw [h31]
  norm_num

theorem isCoatom_Ppl : IsCoatom Ppl := by
  apply Subgroup.isCoatom_of_index_prime
  have h := Ppl.index_mul_card
  rw [card_Ppl, card_sl35] at h
  have h31 : Ppl.index = 31 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 12000) (h.trans (by norm_num))
  rw [h31]
  norm_num

theorem commutator_Pl_le : ⁅Pl, Pl⁆ ≤ Kl := by
  have h : ⁅(⊤ : Subgroup ↥Pl), (⊤ : Subgroup ↥Pl)⁆ ≤ Kl.subgroupOf Pl := by
    rw [← ker_chiPl]
    exact Abelianization.commutator_subset_ker chiPl
  intro x hx
  have h1 : x ∈ (⁅(⊤ : Subgroup ↥Pl), (⊤ : Subgroup ↥Pl)⁆).map Pl.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hx
  obtain ⟨y, hy, rfl⟩ := h1
  exact Subgroup.mem_subgroupOf.mp (h hy)

theorem commutator_Ppl_le : ⁅Ppl, Ppl⁆ ≤ Kpl := by
  have h : ⁅(⊤ : Subgroup ↥Ppl), (⊤ : Subgroup ↥Ppl)⁆ ≤ Kpl.subgroupOf Ppl := by
    rw [← ker_chiPpl]
    exact Abelianization.commutator_subset_ker chiPpl
  intro x hx
  have h1 : x ∈ (⁅(⊤ : Subgroup ↥Ppl), (⊤ : Subgroup ↥Ppl)⁆).map Ppl.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hx
  obtain ⟨y, hy, rfl⟩ := h1
  exact Subgroup.mem_subgroupOf.mp (h hy)

@[expose] def uMk (p : ZMod 5 × ZMod 5 × ZMod 5) : SpecialLinearGroup (Fin 3) (ZMod 5) :=
  ⟨!![1, p.1, p.2.1; 0, 1, p.2.2; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp⟩

theorem card_U5 : Nat.card U5 = 125 := by
  let f : U5 → ZMod 5 × ZMod 5 × ZMod 5 := fun g =>
    ((g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 1, (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 2,
      (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 2)
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨a, b, c, d, e, k⟩ := g.2
      obtain ⟨a', b', c', d', e', k'⟩ := g'.2
      apply Subtype.ext
      ext r s
      fin_cases r <;> fin_cases s
      · exact d.trans d'.symm
      · exact h1
      · exact h2
      · exact a.trans a'.symm
      · exact e.trans e'.symm
      · exact h3
      · exact b.trans b'.symm
      · exact c.trans c'.symm
      · exact k.trans k'.symm
    · intro p
      exact ⟨⟨uMk p, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, Nat.card_zmod]

theorem isSylowOf_U5 : IsSylowOf 5 U5 ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_U5]; norm_num), ?_⟩
  have e : (U5.subgroupOf ⊤).index = U5.index := Subgroup.relIndex_top_right _
  rw [e]
  have h := U5.index_mul_card
  rw [card_U5, card_sl35] at h
  have h2 : U5.index = 2976 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 125) (h.trans (by norm_num))
  rw [h2]
  norm_num

theorem uMk_mem (p : ZMod 5 × ZMod 5 × ZMod 5) : uMk p ∈ U5 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem normalizer_U5_le_Pl :
    ⊤ ⊓ Subgroup.normalizer (U5 : Set (SpecialLinearGroup (Fin 3) (ZMod 5))) ≤ Pl := by
  rintro g ⟨-, hg⟩
  have key : ∀ p, ∀ i : Fin 3, ((uMk p * g : SpecialLinearGroup (Fin 3) (ZMod 5)) :
      Matrix (Fin 3) (Fin 3) (ZMod 5)) i 0 = (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) i 0 := by
    intro p i
    have hv : g⁻¹ * uMk p * g ∈ U5 := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (uMk p)).mp (uMk_mem p)
      simpa using this
    obtain ⟨v1, v2, -, v4, -, -⟩ := hv
    have e : uMk p * g = g * (g⁻¹ * uMk p * g) := by group
    rw [e, sl35_mul_apply, Fin.sum_univ_three, v1, v2, v4]
    ring
  have h1 := key (1, 0, 0) 0
  have h2 := key (0, 0, 1) 1
  rw [sl35_mul_apply, Fin.sum_univ_three] at h1 h2
  simp [uMk] at h1 h2
  exact ⟨h1, h2⟩

theorem normalizer_U5_le_Ppl :
    ⊤ ⊓ Subgroup.normalizer (U5 : Set (SpecialLinearGroup (Fin 3) (ZMod 5))) ≤ Ppl := by
  rintro g ⟨-, hg⟩
  have key : ∀ p, ∀ j : Fin 3, ((g * uMk p : SpecialLinearGroup (Fin 3) (ZMod 5)) :
      Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 j = (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 j := by
    intro p j
    have hv : g * uMk p * g⁻¹ ∈ U5 :=
      (Subgroup.mem_normalizer_iff.mp hg (uMk p)).mp (uMk_mem p)
    obtain ⟨-, v2, v3, -, -, v6⟩ := hv
    have e : g * uMk p = (g * uMk p * g⁻¹) * g := by group
    rw [e, sl35_mul_apply, Fin.sum_univ_three, v2, v3, v6]
    ring
  have h1 := key (1, 0, 0) 1
  have h2 := key (0, 0, 1) 2
  rw [sl35_mul_apply, Fin.sum_univ_three] at h1 h2
  simp [uMk] at h1 h2
  exact ⟨h1, h2⟩

theorem isMaxParabolicOf_Pl : IsMaxParabolicOf 5 ⊤ Pl := by
  refine ⟨⟨le_top, U5, isSylowOf_U5, normalizer_U5_le_Pl⟩, isCoatom_Pl.1, ?_⟩
  intro Q _ hQ hPQ
  by_contra hne
  exact hQ (isCoatom_Pl.2 Q (lt_of_le_of_ne hPQ (Ne.symm hne)))

theorem isMaxParabolicOf_Ppl : IsMaxParabolicOf 5 ⊤ Ppl := by
  refine ⟨⟨le_top, U5, isSylowOf_U5, normalizer_U5_le_Ppl⟩, isCoatom_Ppl.1, ?_⟩
  intro Q _ hQ hPQ
  by_contra hne
  exact hQ (isCoatom_Ppl.2 Q (lt_of_le_of_ne hPQ (Ne.symm hne)))

end CFSG.Quasithin.H13.NQCat.A314D
