module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Quasithin

abbrev P6 : Type := G6.PermMod 6

@[expose] def wt (x : P6) : ℕ :=
  (Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0).card

@[expose] def pv (i j : Fin 6) : P6 :=
  Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1)

theorem wt_permAct (σ : Perm (Fin 6)) (x : P6) : wt (G6.permAct 6 σ x) = wt x := by
  unfold wt
  refine Finset.card_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · intro i _ j _ h
    exact σ⁻¹.injective h
  · intro j hj
    refine ⟨σ j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    show Multiplicative.toAdd x (σ⁻¹ (σ j)) ≠ 0
    simpa using hj

theorem permAct_ofAdd_single (σ : Perm (Fin 6)) (i : Fin 6) :
    G6.permAct 6 σ (Multiplicative.ofAdd (Pi.single i 1)) =
      Multiplicative.ofAdd (Pi.single (σ i) 1) := by
  apply Multiplicative.toAdd.injective
  funext l
  rw [G6.permAct_apply]
  simp only [toAdd_ofAdd]
  by_cases hl : l = σ i
  · subst hl
    simp
  · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne]
    intro h
    exact hl (by rw [← h]; simp)

theorem permAct_pv (σ : Perm (Fin 6)) (i j : Fin 6) :
    G6.permAct 6 σ (pv i j) = pv (σ i) (σ j) := by
  rw [pv, ofAdd_add, map_mul, permAct_ofAdd_single, permAct_ofAdd_single, pv, ofAdd_add]

theorem permAct_allOnes (σ : Perm (Fin 6)) : G6.permAct 6 σ (G6.allOnes 6) = G6.allOnes 6 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  rfl

@[expose] def Adj (x y : P6) : Prop :=
  wt x = 2 ∧ wt y = 2 ∧ x ≠ y ∧ wt (x * y) = 2

instance : DecidableRel Adj := fun x y =>
  inferInstanceAs (Decidable (wt x = 2 ∧ wt y = 2 ∧ x ≠ y ∧ wt (x * y) = 2))

@[expose] def Has (a : Fin 6) (x : P6) : Prop :=
  Multiplicative.toAdd x a = 1

instance (a : Fin 6) : DecidablePred (Has a) := fun x =>
  inferInstanceAs (Decidable (Multiplicative.toAdd x a = 1))

@[expose] def Common4 (y₁ y₂ y₃ y₄ : P6) : Prop :=
  ∃ a : Fin 6, Has a y₁ ∧ Has a y₂ ∧ Has a y₃ ∧ Has a y₄

instance (y₁ y₂ y₃ y₄ : P6) : Decidable (Common4 y₁ y₂ y₃ y₄) := by
  unfold Common4; infer_instance

@[expose] def Star4c (y₁ y₂ y₃ : P6) : Prop :=
  ∀ y₄ : P6, Adj y₁ y₄ → Adj y₂ y₄ → Adj y₃ y₄ → Common4 y₁ y₂ y₃ y₄

instance (y₁ y₂ y₃ : P6) : Decidable (Star4c y₁ y₂ y₃) := by
  unfold Star4c; infer_instance

@[expose] def Star4b (y₁ y₂ : P6) : Prop :=
  ∀ y₃ : P6, Adj y₁ y₃ → Adj y₂ y₃ → Star4c y₁ y₂ y₃

instance (y₁ y₂ : P6) : Decidable (Star4b y₁ y₂) := by
  unfold Star4b; infer_instance

theorem star4 : ∀ y₁ y₂ : P6, Adj y₁ y₂ → Star4b y₁ y₂ := by
  decide +kernel

@[expose] def UniqCommon (y₁ y₂ : P6) : Prop :=
  ∀ a b : Fin 6, Has a y₁ → Has a y₂ → Has b y₁ → Has b y₂ → a = b

instance (y₁ y₂ : P6) : Decidable (UniqCommon y₁ y₂) := by
  unfold UniqCommon; infer_instance

theorem uniq_common : ∀ y₁ y₂ : P6, Adj y₁ y₂ → UniqCommon y₁ y₂ := by
  decide +kernel

theorem exists_pv : ∀ (a : Fin 6) (y : P6), wt y = 2 → Has a y →
    ∃ b : Fin 6, b ≠ a ∧ y = pv a b := by
  decide +kernel

theorem fixed_three_cycles : ∀ x : P6,
    G6.permAct 6 (swap 0 1 * swap 1 2) x = x → G6.permAct 6 (swap 1 2 * swap 2 3) x = x →
    G6.permAct 6 (swap 2 3 * swap 3 4) x = x → G6.permAct 6 (swap 3 4 * swap 4 5) x = x →
    x = 1 ∨ x = G6.allOnes 6 := by
  decide +kernel

theorem three_cycles_mem : swap (0 : Fin 6) 1 * swap 1 2 ∈ alternatingGroup (Fin 6) ∧
    swap (1 : Fin 6) 2 * swap 2 3 ∈ alternatingGroup (Fin 6) ∧
    swap (2 : Fin 6) 3 * swap 3 4 ∈ alternatingGroup (Fin 6) ∧
    swap (3 : Fin 6) 4 * swap 4 5 ∈ alternatingGroup (Fin 6) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem wt_core : ∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 → x ≠ 1 → x ≠ G6.allOnes 6 →
    wt x = 2 ∨ wt x = 4 := by
  decide +kernel

theorem sum_eq_zero_of_wt_two : ∀ x : P6, wt x = 2 → ∑ i, Multiplicative.toAdd x i = 0 := by
  decide +kernel

theorem wt_mul_allOnes_of_four : ∀ x : P6, wt x = 4 → wt (x * G6.allOnes 6) = 2 := by
  decide +kernel

theorem allOnes_ne_one : G6.allOnes 6 ≠ 1 := by decide

theorem allOnes_mul_self : G6.allOnes 6 * G6.allOnes 6 = (1 : P6) := by decide

theorem trans_two : ∀ y : P6, wt y = 2 →
    ∃ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧ G6.permAct 6 σ (pv 0 1) = y := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem card_nbr_two :
    (Finset.univ.filter fun y : P6 => wt y = 2 ∧ wt (pv 0 1 * y) = 2).card = 8 := by
  decide +kernel

theorem card_disj_two : ∀ u : P6, wt u = 2 →
    (Finset.univ.filter fun v : P6 => wt v = 2 ∧ wt (u * v) = 4).card = 6 := by
  decide +kernel

theorem wt_pv_zero : ∀ j : Fin 6, j ≠ 0 → wt (pv 0 j) = 2 := by decide

theorem wt_pv_mul : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → wt (pv 0 i * pv 0 j) = 2 := by
  decide

theorem pv_zero_inj : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → pv 0 i = pv 0 j → i = j := by
  decide +kernel

theorem eq_prod_pv : ∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 →
    x = pv 0 1 ^ (Multiplicative.toAdd x 1).val * pv 0 2 ^ (Multiplicative.toAdd x 2).val *
      pv 0 3 ^ (Multiplicative.toAdd x 3).val * pv 0 4 ^ (Multiplicative.toAdd x 4).val *
      pv 0 5 ^ (Multiplicative.toAdd x 5).val := by
  decide +kernel

instance (x : P6) : Decidable (x ∈ G6.coreMod 6) :=
  decidable_of_iff _ G6.mem_coreMod.symm

theorem pv_mem_core (i j : Fin 6) : pv i j ∈ G6.coreMod 6 :=
  G6.mem_coreMod.2 (by revert i j; decide)

theorem allOnes_mem_core : G6.allOnes 6 ∈ G6.coreMod 6 :=
  G6.mem_coreMod.2 (by decide)

theorem pv01_ne_one : pv 0 1 ≠ 1 := by decide

theorem pv01_ne_allOnes : pv 0 1 ≠ G6.allOnes 6 := by decide

theorem exists_perm_of_normalizes_core (ρ : MulAut ↥(G6.coreMod 6))
    (h1 : ∀ σ ∈ alternatingGroup (Fin 6), ∃ τ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (G6.coreAct 6 σ x) = G6.coreAct 6 τ (ρ x))
    (h2 : ∀ τ ∈ alternatingGroup (Fin 6), ∃ σ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (G6.coreAct 6 σ x) = G6.coreAct 6 τ (ρ x)) :
    ∃ π : Perm (Fin 6), ∀ x, ρ x = G6.coreAct 6 π x := by
  let e : ↥(G6.coreMod 6) := ⟨G6.allOnes 6, allOnes_mem_core⟩
  let r : ↥(G6.coreMod 6) → P6 := fun x => (ρ x : P6)
  have hrmul : ∀ x y : ↥(G6.coreMod 6), r (x * y) = r x * r y := fun x y => by
    simp only [r, map_mul, Subgroup.coe_mul]
  have hrinj : ∀ x y : ↥(G6.coreMod 6), r x = r y → x = y := fun x y h =>
    ρ.injective (Subtype.ext h)
  have hr1 : ∀ x : ↥(G6.coreMod 6), r x = 1 → x = 1 := fun x h =>
    hrinj x 1 (by rw [h]; simp [r])
  have hrcore : ∀ x : ↥(G6.coreMod 6), ∑ i, Multiplicative.toAdd (r x) i = 0 := fun x =>
    (ρ x).2
  have hfix : ∀ τ ∈ alternatingGroup (Fin 6), G6.permAct 6 τ (r e) = r e := by
    intro τ hτ
    obtain ⟨σ, -, hσ⟩ := h2 τ hτ
    have h := hσ e
    have he : G6.coreAct 6 σ e = e := Subtype.ext (permAct_allOnes σ)
    rw [he] at h
    have := congrArg Subtype.val h
    rw [G6.coreAct_coe] at this
    exact this.symm
  have hre : r e = G6.allOnes 6 := by
    obtain ⟨c1, c2, c3, c4⟩ := three_cycles_mem
    rcases fixed_three_cycles (r e) (hfix _ c1) (hfix _ c2) (hfix _ c3) (hfix _ c4) with h | h
    · exfalso
      exact allOnes_ne_one (congrArg Subtype.val (hr1 e h))
    · exact h
  have hwt_orbit : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) →
      ∀ x : ↥(G6.coreMod 6), wt (r (G6.coreAct 6 σ x)) = wt (r x) := by
    intro σ hσ x
    obtain ⟨τ, -, hτ⟩ := h1 σ hσ
    simp only [r, hτ x, G6.coreAct_coe, wt_permAct]
  let p01 : ↥(G6.coreMod 6) := ⟨pv 0 1, pv_mem_core 0 1⟩
  have hwt2 : ∀ x : ↥(G6.coreMod 6), wt (x : P6) = 2 → wt (r x) = wt (r p01) := by
    intro x hx
    obtain ⟨σ, hσ, hσx⟩ := trans_two x hx
    have : x = G6.coreAct 6 σ p01 := Subtype.ext (by rw [G6.coreAct_coe]; exact hσx.symm)
    rw [this]
    exact hwt_orbit σ hσ p01
  have hp01 : wt (r p01) = 2 ∨ wt (r p01) = 4 := by
    refine wt_core (r p01) (hrcore p01) (fun h => pv01_ne_one ?_) (fun h => pv01_ne_allOnes ?_)
    · exact congrArg Subtype.val (hr1 p01 h)
    · exact congrArg Subtype.val (hrinj p01 e (h.trans hre.symm))
  have hw : wt (r p01) = 2 := by
    rcases hp01 with h | h
    · exact h
    exfalso
    obtain ⟨f, hf⟩ : ∃ f : P6 → P6, ∀ (y : P6) (hy : y ∈ G6.coreMod 6),
        f y = r ⟨y, hy⟩ * G6.allOnes 6 :=
      ⟨fun y => if hy : y ∈ G6.coreMod 6 then r ⟨y, hy⟩ * G6.allOnes 6 else 1,
        fun y hy => by simp only [hy, ↓reduceDIte]⟩
    obtain ⟨u, hu_def⟩ : ∃ u : P6, u = r p01 * G6.allOnes 6 := ⟨_, rfl⟩
    have hu : wt u = 2 := hu_def ▸ wt_mul_allOnes_of_four _ h
    have hmaps : ∀ y ∈ (Finset.univ.filter fun y : P6 => wt y = 2 ∧ wt (pv 0 1 * y) = 2),
        f y ∈ (Finset.univ.filter fun v : P6 => wt v = 2 ∧ wt (u * v) = 4) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨-, hy1, hy2⟩ := hy
      have hyc : y ∈ G6.coreMod 6 := G6.mem_coreMod.2 (sum_eq_zero_of_wt_two y hy1)
      obtain ⟨py, hpy⟩ : ∃ py : ↥(G6.coreMod 6), py = p01 * ⟨y, hyc⟩ := ⟨_, rfl⟩
      have hpyv : (py : P6) = pv 0 1 * y := by rw [hpy]; rfl
      have h4 : wt (r ⟨y, hyc⟩) = 4 := (hwt2 ⟨y, hyc⟩ hy1).trans h
      have h4py : wt (r py) = 4 := (hwt2 py (hpyv ▸ hy2)).trans h
      have hprod : u * f y = r py := by
        rw [hf y hyc, hu_def, hpy, hrmul]
        rw [mul_mul_mul_comm, allOnes_mul_self, mul_one]
      have h2' : wt (f y) = 2 := by
        rw [hf y hyc]
        exact wt_mul_allOnes_of_four _ h4
      have h4' : wt (u * f y) = 4 := by
        rw [hprod]
        exact h4py
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2', h4'⟩
    have hinj : Set.InjOn f
        ↑(Finset.univ.filter fun y : P6 => wt y = 2 ∧ wt (pv 0 1 * y) = 2) := by
      intro y hy y' hy' hff
      have hy1 : wt y = 2 := (Finset.mem_filter.mp hy).2.1
      have hy1' : wt y' = 2 := (Finset.mem_filter.mp hy').2.1
      have hyc : y ∈ G6.coreMod 6 := G6.mem_coreMod.2 (sum_eq_zero_of_wt_two y hy1)
      have hyc' : y' ∈ G6.coreMod 6 := G6.mem_coreMod.2 (sum_eq_zero_of_wt_two y' hy1')
      rw [hf y hyc, hf y' hyc', mul_left_inj] at hff
      exact congrArg Subtype.val (hrinj _ _ hff)
    have hle := Finset.card_le_card_of_injOn f hmaps hinj
    rw [card_nbr_two, card_disj_two u hu] at hle
    omega
  have hpres : ∀ x : ↥(G6.coreMod 6), wt (x : P6) = 2 → wt (r x) = 2 := fun x hx =>
    (hwt2 x hx).trans hw
  let q : Fin 6 → ↥(G6.coreMod 6) := fun j => ⟨pv 0 j, pv_mem_core 0 j⟩
  have hadj : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → Adj (r (q i)) (r (q j)) := by
    intro i j hi hj hij
    refine ⟨hpres _ (wt_pv_zero i hi), hpres _ (wt_pv_zero j hj), fun h => ?_, ?_⟩
    · exact hij (pv_zero_inj i j hi hj (congrArg Subtype.val (hrinj _ _ h)))
    · rw [← hrmul]
      exact hpres (q i * q j) (wt_pv_mul i j hi hj hij)
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := star4 _ _ (hadj 1 2 (by decide) (by decide) (by decide)) _
    (hadj 1 3 (by decide) (by decide) (by decide)) (hadj 2 3 (by decide) (by decide) (by decide))
    _ (hadj 1 4 (by decide) (by decide) (by decide))
    (hadj 2 4 (by decide) (by decide) (by decide)) (hadj 3 4 (by decide) (by decide) (by decide))
  obtain ⟨a', ha1', ha2', -, ha5⟩ := star4 _ _ (hadj 1 2 (by decide) (by decide) (by decide)) _
    (hadj 1 3 (by decide) (by decide) (by decide)) (hadj 2 3 (by decide) (by decide) (by decide))
    _ (hadj 1 5 (by decide) (by decide) (by decide))
    (hadj 2 5 (by decide) (by decide) (by decide)) (hadj 3 5 (by decide) (by decide) (by decide))
  have haa : a = a' := uniq_common _ _ (hadj 1 2 (by decide) (by decide) (by decide)) a a'
    ha1 ha2 ha1' ha2'
  subst haa
  have hHas : ∀ j : Fin 6, j ≠ 0 → Has a (r (q j)) := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · exact ha1
    · exact ha2
    · exact ha3
    · exact ha4
    · exact ha5
  have hb : ∀ j : Fin 6, ∃ b : Fin 6, j ≠ 0 → b ≠ a ∧ r (q j) = pv a b := by
    intro j
    by_cases hj : j = 0
    · exact ⟨a, fun h => absurd hj h⟩
    · obtain ⟨b, hb⟩ := exists_pv a (r (q j)) (hpres _ (wt_pv_zero j hj)) (hHas j hj)
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
        exact pv_zero_inj i j hi hj (congrArg Subtype.val (hrinj _ _ h1))
  let π : Perm (Fin 6) := Equiv.ofBijective πf (Finite.injective_iff_bijective.mp hπinj)
  have hπ0 : π 0 = a := by simp [π, πf]
  have hπj : ∀ j : Fin 6, j ≠ 0 → π j = b j := fun j hj => by simp [π, πf, hj]
  have hq : ∀ j : Fin 6, j ≠ 0 → ρ (q j) = G6.coreAct 6 π (q j) := by
    intro j hj
    apply Subtype.ext
    rw [G6.coreAct_coe]
    show r (q j) = G6.permAct 6 π (pv 0 j)
    rw [permAct_pv, hπ0, hπj j hj, (hb j hj).2]
  refine ⟨π, fun x => ?_⟩
  have hx : x = q 1 ^ (Multiplicative.toAdd (x : P6) 1).val *
      q 2 ^ (Multiplicative.toAdd (x : P6) 2).val * q 3 ^ (Multiplicative.toAdd (x : P6) 3).val *
      q 4 ^ (Multiplicative.toAdd (x : P6) 4).val * q 5 ^ (Multiplicative.toAdd (x : P6) 5).val := by
    apply Subtype.ext
    simp only [q, Subgroup.coe_mul, Subgroup.coe_pow]
    exact eq_prod_pv x x.2
  rw [hx]
  simp only [map_mul, map_pow]
  rw [hq 1 (by decide), hq 2 (by decide), hq 3 (by decide), hq 4 (by decide), hq 5 (by decide)]

end CFSG.Quasithin.H13.A6
