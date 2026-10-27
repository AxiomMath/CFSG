module

public import CFSG.Quasithin.H13.A6Model
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Quasithin

@[expose] def nrm (y : P6) : P6 :=
  if Multiplicative.toAdd y 5 = 0 then y else y * G6.allOnes 6

theorem nrm_mul : ∀ x y : P6, nrm (x * y) = nrm x * nrm y := by
  decide +kernel

theorem nrm_mul_allOnes : ∀ y : P6, nrm (y * G6.allOnes 6) = nrm y := by
  decide +kernel

theorem nrm_of_five : ∀ y : P6, Multiplicative.toAdd y 5 = 0 → nrm y = y := by
  decide +kernel

theorem nrm_eq_or : ∀ y : P6, nrm y = y ∨ nrm y = y * G6.allOnes 6 := by
  decide +kernel

@[expose] def InW4 (x : P6) : Prop :=
  ∑ i, Multiplicative.toAdd x i = 0 ∧ Multiplicative.toAdd x 5 = 0

instance : DecidablePred InW4 := fun x => by unfold InW4; infer_instance

theorem inW4_nrm : ∀ y : P6, ∑ i, Multiplicative.toAdd y i = 0 → InW4 (nrm y) := by
  decide +kernel

@[expose] def W4 : Subgroup P6 where
  carrier := {x | InW4 x}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : P6, InW4 a → InW4 b → InW4 (a * b) := by decide +kernel
    exact key a b ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : P6, InW4 a → InW4 a⁻¹ := by decide +kernel
    exact key a ha)

theorem mem_W4 {x : P6} : x ∈ W4 ↔ InW4 x := Iff.rfl

instance (x : P6) : Decidable (x ∈ W4) := decidable_of_iff _ mem_W4.symm

theorem nrm_permAct_nrm (σ : Perm (Fin 6)) (y : P6) :
    nrm (G6.permAct 6 σ (nrm y)) = nrm (G6.permAct 6 σ y) := by
  rcases nrm_eq_or y with h | h <;> rw [h]
  rw [map_mul, permAct_allOnes, nrm_mul_allOnes]

@[expose] def act4f (σ : Perm (Fin 6)) (x : P6) : P6 := nrm (G6.permAct 6 σ x)

theorem act4f_mul (σ τ : Perm (Fin 6)) (x : P6) :
    act4f (σ * τ) x = act4f σ (act4f τ x) := by
  unfold act4f
  rw [nrm_permAct_nrm, map_mul, MulAut.mul_apply]

theorem act4f_one (x : P6) (hx : x ∈ W4) : act4f 1 x = x := by
  unfold act4f
  rw [map_one, MulAut.one_apply, nrm_of_five x hx.2]

theorem act4f_mem (σ : Perm (Fin 6)) {x : P6} (hx : x ∈ W4) : act4f σ x ∈ W4 :=
  inW4_nrm _ (G6.mem_coreMod.1 (G6.permAct_mem_coreMod σ (G6.mem_coreMod.2 hx.1)))

theorem act4f_mul_apply (σ : Perm (Fin 6)) (x y : P6) :
    act4f σ (x * y) = act4f σ x * act4f σ y := by
  unfold act4f
  rw [map_mul, nrm_mul]

@[expose] noncomputable def act4 : Perm (Fin 6) →* MulAut ↥W4 where
  toFun σ :=
    { toFun := fun x => ⟨act4f σ x, act4f_mem σ x.2⟩
      invFun := fun x => ⟨act4f σ⁻¹ x, act4f_mem σ⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (by
        show act4f σ⁻¹ (act4f σ x) = x
        rw [← act4f_mul, inv_mul_cancel, act4f_one x x.2])
      right_inv := fun x => Subtype.ext (by
        show act4f σ (act4f σ⁻¹ x) = x
        rw [← act4f_mul, mul_inv_cancel, act4f_one x x.2])
      map_mul' := fun x y => Subtype.ext (act4f_mul_apply σ x y) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (act4f_one x x.2)
  map_mul' := fun σ τ => MulEquiv.ext fun x => Subtype.ext (act4f_mul σ τ x)

theorem act4_coe (σ : Perm (Fin 6)) (x : ↥W4) :
    ((act4 σ x : ↥W4) : P6) = nrm (G6.permAct 6 σ x) := rfl

@[expose] def dot (x y : P6) : ZMod 2 := ∑ i, Multiplicative.toAdd x i * Multiplicative.toAdd y i

@[expose] def dv (i j : Fin 6) : P6 := nrm (pv i j)

@[expose] def HasD (a : Fin 6) (x : P6) : Prop :=
  (Multiplicative.toAdd x a = 1 ∧ wt x = 2) ∨ (Multiplicative.toAdd x a = 0 ∧ wt x = 4)

instance (a : Fin 6) : DecidablePred (HasD a) := fun x => by unfold HasD; infer_instance

@[expose] def Adj4 (x y : P6) : Prop := InW4 x ∧ InW4 y ∧ x ≠ y ∧ dot x y = 1

instance : DecidableRel Adj4 := fun x y => by unfold Adj4; infer_instance

@[expose] def Common4D (y₁ y₂ y₃ y₄ : P6) : Prop :=
  ∃ a : Fin 6, HasD a y₁ ∧ HasD a y₂ ∧ HasD a y₃ ∧ HasD a y₄

instance (y₁ y₂ y₃ y₄ : P6) : Decidable (Common4D y₁ y₂ y₃ y₄) := by
  unfold Common4D; infer_instance

@[expose] def Star4Dc (y₁ y₂ y₃ : P6) : Prop :=
  ∀ y₄ : P6, Adj4 y₁ y₄ → Adj4 y₂ y₄ → Adj4 y₃ y₄ → Common4D y₁ y₂ y₃ y₄

instance (y₁ y₂ y₃ : P6) : Decidable (Star4Dc y₁ y₂ y₃) := by unfold Star4Dc; infer_instance

@[expose] def Star4Db (y₁ y₂ : P6) : Prop :=
  ∀ y₃ : P6, Adj4 y₁ y₃ → Adj4 y₂ y₃ → Star4Dc y₁ y₂ y₃

instance (y₁ y₂ : P6) : Decidable (Star4Db y₁ y₂) := by unfold Star4Db; infer_instance

theorem star4D : ∀ y₁ y₂ : P6, Adj4 y₁ y₂ → Star4Db y₁ y₂ := by
  decide +kernel

@[expose] def UniqCommonD (y₁ y₂ : P6) : Prop :=
  ∀ a b : Fin 6, HasD a y₁ → HasD a y₂ → HasD b y₁ → HasD b y₂ → a = b

instance (y₁ y₂ : P6) : Decidable (UniqCommonD y₁ y₂) := by unfold UniqCommonD; infer_instance

theorem uniq_commonD : ∀ y₁ y₂ : P6, Adj4 y₁ y₂ → UniqCommonD y₁ y₂ := by
  decide +kernel

theorem exists_dv : ∀ (a : Fin 6) (y : P6), InW4 y → y ≠ 1 → HasD a y →
    ∃ b : Fin 6, b ≠ a ∧ y = dv a b := by
  decide +kernel

theorem act4f_dv (σ : Perm (Fin 6)) (i j : Fin 6) : act4f σ (dv i j) = dv (σ i) (σ j) := by
  unfold act4f dv
  rw [nrm_permAct_nrm, permAct_pv]

theorem dv_mem (i j : Fin 6) : dv i j ∈ W4 := inW4_nrm _ (by revert i j; decide)

theorem dv_zero_facts : (∀ j : Fin 6, j ≠ 0 → dv 0 j ≠ 1) ∧
    (∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → Adj4 (dv 0 i) (dv 0 j)) ∧
    (∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → dv 0 i = dv 0 j → i = j) ∧
    ∀ j : Fin 6, j ≠ 0 → HasD 0 (dv 0 j) := by
  decide +kernel

theorem eq_prod_dv : ∀ x : P6, InW4 x →
    x = dv 0 1 ^ (Multiplicative.toAdd x 1).val * dv 0 2 ^ (Multiplicative.toAdd x 2).val *
      dv 0 3 ^ (Multiplicative.toAdd x 3).val * dv 0 4 ^ (Multiplicative.toAdd x 4).val := by
  decide +kernel

theorem dot_act4f : ∀ x y : P6, InW4 x → InW4 y → ∀ σ : Perm (Fin 6),
    dot (act4f σ x) (act4f σ y) = dot x y := by
  intro x y hx hy σ
  unfold act4f
  have hx' : G6.permAct 6 σ x ∈ G6.coreMod 6 := G6.permAct_mem_coreMod σ (G6.mem_coreMod.2 hx.1)
  have hy' : G6.permAct 6 σ y ∈ G6.coreMod 6 := G6.permAct_mem_coreMod σ (G6.mem_coreMod.2 hy.1)
  have key : ∀ u v : P6, ∑ i, Multiplicative.toAdd u i = 0 → ∑ i, Multiplicative.toAdd v i = 0 →
      dot (nrm u) (nrm v) = dot u v := by decide +kernel
  rw [key _ _ (G6.mem_coreMod.1 hx') (G6.mem_coreMod.1 hy')]
  unfold dot
  simp only [G6.permAct_apply]
  exact Equiv.sum_comp σ⁻¹ (fun i => Multiplicative.toAdd x i * Multiplicative.toAdd y i)

@[expose] def TriWit (a b : P6) : Prop :=
  ∃ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ act4f σ (dv 0 1) = a ∧ act4f σ (dv 0 2) = b

instance (a b : P6) : Decidable (TriWit a b) := by unfold TriWit; infer_instance

@[expose] def TriAll (a : P6) : Prop := ∀ b : P6, InW4 b → dot a b = 1 → TriWit a b

instance (a : P6) : Decidable (TriAll a) := by unfold TriAll; infer_instance

theorem trans_tri' : ∀ a : P6, InW4 a → TriAll a := by
  decide +kernel

theorem trans_tri (a b : P6) (ha : InW4 a) (hb : InW4 b) (hab : dot a b = 1) :
    ∃ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ act4f σ (dv 0 1) = a ∧ act4f σ (dv 0 2) = b :=
  trans_tri' a ha b hb hab

theorem card_tri : (Finset.univ.filter fun b : P6 => InW4 b ∧ dot (dv 0 1) b = 1).card = 8 := by
  decide +kernel

theorem card_syn : ∀ u : P6, InW4 u → u ≠ 1 →
    (Finset.univ.filter fun b : P6 => InW4 b ∧ b ≠ 1 ∧ b ≠ u ∧ dot u b = 0).card = 6 := by
  decide +kernel

theorem dot_self_one : (∀ x : P6, InW4 x → dot x x = 0) ∧ ∀ x : P6, dot x 1 = 0 := by
  decide +kernel

theorem exists_perm_of_normalizes_W4 (ρ : MulAut ↥W4)
    (h1 : ∀ σ ∈ alternatingGroup (Fin 6), ∃ τ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (act4 σ x) = act4 τ (ρ x)) :
    ∃ π : Perm (Fin 6), ∀ x, ρ x = act4 π x := by
  let r : ↥W4 → P6 := fun x => (ρ x : P6)
  have hrmul : ∀ x y : ↥W4, r (x * y) = r x * r y := fun x y => by
    simp only [r, map_mul, Subgroup.coe_mul]
  have hrinj : ∀ x y : ↥W4, r x = r y → x = y := fun x y h => ρ.injective (Subtype.ext h)
  have hrW : ∀ x : ↥W4, InW4 (r x) := fun x => (ρ x).2
  have hr1 : ∀ x : ↥W4, r x = 1 → x = 1 := fun x h => hrinj x 1 (by rw [h]; simp [r])
  let a₀ : ↥W4 := ⟨dv 0 1, dv_mem 0 1⟩
  let b₀ : ↥W4 := ⟨dv 0 2, dv_mem 0 2⟩
  have hconst : ∀ x y : ↥W4, dot (x : P6) (y : P6) = 1 → dot (r x) (r y) = dot (r a₀) (r b₀) := by
    intro x y hxy
    obtain ⟨σ, hσ, hσx, hσy⟩ := trans_tri _ _ x.2 y.2 hxy
    obtain ⟨τ, -, hτ⟩ := h1 σ (Equiv.Perm.mem_alternatingGroup.2 hσ)
    have ex : x = act4 σ a₀ := Subtype.ext hσx.symm
    have ey : y = act4 σ b₀ := Subtype.ext hσy.symm
    rw [ex, ey]
    simp only [r, hτ]
    rw [act4_coe, act4_coe]
    exact dot_act4f _ _ (hrW a₀) (hrW b₀) τ
  have hmeet : dot (r a₀) (r b₀) = 1 := by
    by_contra hc
    have hc0 : dot (r a₀) (r b₀) = 0 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (dot (r a₀) (r b₀)) with h | h
      · exact h
      · exact absurd h hc
    obtain ⟨f, hf⟩ : ∃ f : P6 → P6, ∀ (y : P6) (hy : y ∈ W4), f y = r ⟨y, hy⟩ :=
      ⟨fun y => if hy : y ∈ W4 then r ⟨y, hy⟩ else 1, fun y hy => by simp only [hy, ↓reduceDIte]⟩
    have hmaps : ∀ y ∈ (Finset.univ.filter fun b : P6 => InW4 b ∧ dot (dv 0 1) b = 1),
        f y ∈ (Finset.univ.filter fun b : P6 => InW4 b ∧ b ≠ 1 ∧ b ≠ r a₀ ∧ dot (r a₀) b = 0) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨-, hyW, hdy⟩ := hy
      have hy1 : (⟨y, hyW⟩ : ↥W4) ≠ 1 := fun h => by
        have : y = 1 := congrArg Subtype.val h
        rw [this, dot_self_one.2] at hdy
        exact absurd hdy (by decide)
      have hya : (⟨y, hyW⟩ : ↥W4) ≠ a₀ := fun h => by
        have : y = dv 0 1 := congrArg Subtype.val h
        rw [this, dot_self_one.1 _ (dv_mem 0 1)] at hdy
        exact absurd hdy (by decide)
      rw [Finset.mem_filter, hf y hyW]
      refine ⟨Finset.mem_univ _, hrW _, fun h => hy1 (hr1 _ h), fun h => hya (hrinj _ _ h), ?_⟩
      have := hconst a₀ ⟨y, hyW⟩ hdy
      rw [this, hc0]
    have hinj : Set.InjOn f ↑(Finset.univ.filter fun b : P6 => InW4 b ∧ dot (dv 0 1) b = 1) := by
      intro y hy y' hy' hff
      have hyW : InW4 y := (Finset.mem_filter.mp hy).2.1
      have hyW' : InW4 y' := (Finset.mem_filter.mp hy').2.1
      rw [hf y hyW, hf y' hyW'] at hff
      exact congrArg Subtype.val (hrinj _ _ hff)
    have hle := Finset.card_le_card_of_injOn f hmaps hinj
    rw [card_tri, card_syn _ (hrW a₀) (fun h => by
      have := hr1 a₀ h
      exact dv_zero_facts.1 1 (by decide) (congrArg Subtype.val this))] at hle
    omega
  have hpres : ∀ x y : ↥W4, dot (x : P6) (y : P6) = 1 → dot (r x) (r y) = 1 := fun x y h =>
    (hconst x y h).trans hmeet
  obtain ⟨hq1, hqadj, hqinj, -⟩ := dv_zero_facts
  let q : Fin 6 → ↥W4 := fun j => ⟨dv 0 j, dv_mem 0 j⟩
  have hadj : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → Adj4 (r (q i)) (r (q j)) := by
    intro i j hi hj hij
    refine ⟨hrW _, hrW _, fun h => hij (hqinj i j hi hj (congrArg Subtype.val (hrinj _ _ h))), ?_⟩
    exact hpres _ _ (hqadj i j hi hj hij).2.2.2
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := star4D _ _ (hadj 1 2 (by decide) (by decide) (by decide)) _
    (hadj 1 3 (by decide) (by decide) (by decide)) (hadj 2 3 (by decide) (by decide) (by decide))
    _ (hadj 1 4 (by decide) (by decide) (by decide))
    (hadj 2 4 (by decide) (by decide) (by decide)) (hadj 3 4 (by decide) (by decide) (by decide))
  obtain ⟨a', ha1', ha2', -, ha5⟩ := star4D _ _ (hadj 1 2 (by decide) (by decide) (by decide)) _
    (hadj 1 3 (by decide) (by decide) (by decide)) (hadj 2 3 (by decide) (by decide) (by decide))
    _ (hadj 1 5 (by decide) (by decide) (by decide))
    (hadj 2 5 (by decide) (by decide) (by decide)) (hadj 3 5 (by decide) (by decide) (by decide))
  have haa : a = a' := uniq_commonD _ _ (hadj 1 2 (by decide) (by decide) (by decide)) a a'
    ha1 ha2 ha1' ha2'
  subst haa
  have hHas : ∀ j : Fin 6, j ≠ 0 → HasD a (r (q j)) := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · exact ha1
    · exact ha2
    · exact ha3
    · exact ha4
    · exact ha5
  have hb : ∀ j : Fin 6, ∃ b : Fin 6, j ≠ 0 → b ≠ a ∧ r (q j) = dv a b := by
    intro j
    by_cases hj : j = 0
    · exact ⟨a, fun h => absurd hj h⟩
    · obtain ⟨b, hb⟩ := exists_dv a (r (q j)) (hrW _) (fun h => hq1 j hj
        (congrArg Subtype.val (hr1 _ h))) (hHas j hj)
      exact ⟨b, fun _ => hb⟩
  choose b hb using hb
  let πf : Fin 6 → Fin 6 := fun j => if j = 0 then a else b j
  have hπinj : Function.Injective πf := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · rw [hi, hj]
      · simp only [πf, hi, hj, ↓reduceIte] at hij
        exact absurd hij.symm (hb j hj).1
    · by_cases hj : j = 0
      · simp only [πf, hi, hj, ↓reduceIte] at hij
        exact absurd hij (hb i hi).1
      · simp only [πf, hi, hj, ↓reduceIte] at hij
        have h1 : r (q i) = r (q j) := by rw [(hb i hi).2, (hb j hj).2, hij]
        exact hqinj i j hi hj (congrArg Subtype.val (hrinj _ _ h1))
  let π : Perm (Fin 6) := Equiv.ofBijective πf (Finite.injective_iff_bijective.mp hπinj)
  have hπ0 : π 0 = a := by simp [π, πf]
  have hπj : ∀ j : Fin 6, j ≠ 0 → π j = b j := fun j hj => by simp [π, πf, hj]
  have hq : ∀ j : Fin 6, j ≠ 0 → ρ (q j) = act4 π (q j) := by
    intro j hj
    apply Subtype.ext
    show r (q j) = act4f π (dv 0 j)
    rw [act4f_dv, hπ0, hπj j hj, (hb j hj).2]
  refine ⟨π, fun x => ?_⟩
  have hx : x = q 1 ^ (Multiplicative.toAdd (x : P6) 1).val *
      q 2 ^ (Multiplicative.toAdd (x : P6) 2).val * q 3 ^ (Multiplicative.toAdd (x : P6) 3).val *
      q 4 ^ (Multiplicative.toAdd (x : P6) 4).val := by
    apply Subtype.ext
    simp only [q, Subgroup.coe_mul, Subgroup.coe_pow]
    exact eq_prod_dv x x.2
  rw [hx]
  simp only [map_mul, map_pow]
  rw [hq 1 (by decide), hq 2 (by decide), hq 3 (by decide), hq 4 (by decide)]

end CFSG.Quasithin.H13.A6
