module

public import CFSG.RankThree.GF2n.Parrott.SpinRigidityBridge
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "P45" => Equiv.Perm (Fin 45)

namespace SpinRigid

@[expose] def eltRaw (t : Fin 3 × Fin 3 × Fin 3) : List Nat :=
  tcomp (tcomp (tpow tM1 (t.1 : Nat)) (tpow tM2 (t.2.1 : Nat))) (tpow tM3 (t.2.2 : Nat))

@[expose] def eltList : List (List Nat) :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).flatMap fun b =>
    (List.finRange 3).map fun c => eltRaw (a, b, c)

@[expose] def eltT (t : Fin 3 × Fin 3 × Fin 3) : List Nat :=
  eltList.getD (9 * (t.1 : Nat) + 3 * (t.2.1 : Nat) + (t.2.2 : Nat)) []

theorem eltRaw_eq_eltT : ∀ t : Fin 3 × Fin 3 × Fin 3, eltRaw t = eltT t := by decide +kernel

theorem eltT_mul : ∀ s t : Fin 3 × Fin 3 × Fin 3, tcomp (eltT s) (eltT t) = eltT (s + t) := by
  decide +kernel

theorem eltT_zero : eltT 0 = tone := by decide +kernel

theorem eltT_injective : ∀ s t : Fin 3 × Fin 3 × Fin 3, eltT s = eltT t → s = t := by
  decide +kernel

@[expose] def repT : Nat → List Nat
  | 1 => tM1
  | 2 => tcomp tM1 tM2
  | _ => tcomp tM1 (tpow tM2 2)

@[expose] def e27Data : List ((Fin 3 × Fin 3 × Fin 3) × Nat × List (Fin 3 × Nat)) :=
  [
    ((0, 0, 1), 3, [(1, 2), (0, 1), (1, 4), (2, 1), (1, 4), (0, 1), (1, 4)]),
    ((0, 0, 2), 3, [(1, 1), (0, 1), (1, 1), (2, 1), (1, 1), (0, 1), (1, 3)]),
    ((0, 1, 0), 1, [(1, 1), (0, 1), (1, 4), (0, 1), (1, 4)]),
    ((0, 1, 1), 3, [(1, 2), (0, 1), (1, 3), (2, 1)]),
    ((0, 1, 2), 3, [(1, 1), (0, 1), (1, 1), (2, 1), (1, 4), (2, 1)]),
    ((0, 2, 0), 1, [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4)]),
    ((0, 2, 1), 3, [(1, 1), (0, 1), (1, 1), (2, 1), (1, 4)]),
    ((0, 2, 2), 3, [(1, 2), (0, 1), (1, 3)]),
    ((1, 0, 0), 1, []),
    ((1, 0, 1), 3, [(0, 1), (1, 1), (2, 1), (1, 4), (0, 1), (1, 4)]),
    ((1, 0, 2), 3, [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4)]),
    ((1, 1, 0), 2, []),
    ((1, 1, 1), 1, [(2, 1), (0, 1), (1, 2), (2, 1), (1, 1)]),
    ((1, 1, 2), 1, [(2, 1), (1, 2), (2, 1), (1, 1)]),
    ((1, 2, 0), 3, []),
    ((1, 2, 1), 2, [(1, 1), (0, 1), (1, 1), (2, 1), (1, 4)]),
    ((1, 2, 2), 2, [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4), (2, 1)]),
    ((2, 0, 0), 1, [(2, 1)]),
    ((2, 0, 1), 3, [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4), (2, 1)]),
    ((2, 0, 2), 3, [(1, 4), (2, 1), (1, 1), (2, 1), (0, 1), (1, 2)]),
    ((2, 1, 0), 3, [(2, 1)]),
    ((2, 1, 1), 2, [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4)]),
    ((2, 1, 2), 2, [(1, 1), (0, 1), (1, 1), (2, 1), (1, 4), (2, 1)]),
    ((2, 2, 0), 2, [(2, 1)]),
    ((2, 2, 1), 1, [(1, 2), (2, 1), (1, 1)]),
    ((2, 2, 2), 1, [(0, 1), (1, 2), (2, 1), (1, 1)])]

theorem tab_e27 : ∀ e ∈ e27Data,
    tcomp (evalT t3 e.2.2) (repT e.2.1) = tcomp (eltT e.1) (evalT t3 e.2.2) := by
  decide +kernel

theorem e27Data_nodup : (e27Data.map (·.1)).Nodup := by decide +kernel

theorem e27Data_ne_zero : ∀ e ∈ e27Data, e.1 ≠ 0 := by decide +kernel

theorem e27Data_complete : ∀ t : Fin 3 × Fin 3 × Fin 3, t ≠ 0 → ∃ e ∈ e27Data, e.1 = t := by
  decide +kernel

theorem e27Data_label : ∀ e ∈ e27Data, e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 3 := by decide +kernel

theorem e27Data_neg : ∀ e ∈ e27Data, ∃ e' ∈ e27Data, e'.1 = -e.1 ∧ e'.2.1 = e.2.1 := by
  decide +kernel

theorem e27Data_count :
    (e27Data.filter fun e => e.2.1 = 1).length = 8 ∧
    (e27Data.filter fun e => e.2.1 = 2).length = 6 ∧
    (e27Data.filter fun e => e.2.1 = 3).length = 12 := by
  decide +kernel

end SpinRigid

@[expose] def spinE27Elt (t : Fin 3 × Fin 3 × Fin 3) : A45 :=
  spinE27a ^ (t.1 : ℕ) * spinE27b ^ (t.2.1 : ℕ) * spinE27c ^ (t.2.2 : ℕ)

namespace SpinRigid

theorem permTab_spinE27Elt (t : Fin 3 × Fin 3 × Fin 3) :
    permTab ((spinE27Elt t : A45) : P45) = eltT t := by
  rw [← eltRaw_eq_eltT]
  have ha : permTab ((spinE27a : A45) : P45) = tM1 := permTab_spinG5 2
  have hb : permTab ((spinE27b : A45) : P45) = tM2 := permTab_spinG5 3
  have hc : permTab ((spinE27c : A45) : P45) = tM3 := permTab_spinG5 4
  unfold spinE27Elt eltRaw
  rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_pow, permTab_coe_pow, permTab_coe_pow, ha,
    hb, hc]

theorem spinE27Elt_mul (s t : Fin 3 × Fin 3 × Fin 3) :
    spinE27Elt s * spinE27Elt t = spinE27Elt (s + t) := by
  apply eq_of_permTab_eq
  rw [permTab_coe_mul, permTab_spinE27Elt, permTab_spinE27Elt, permTab_spinE27Elt]
  exact eltT_mul s t

theorem spinE27Elt_zero : spinE27Elt 0 = 1 := by
  apply eq_of_permTab_eq
  rw [permTab_spinE27Elt, permTab_coe_one]
  exact eltT_zero

theorem spinE27Elt_injective : Function.Injective spinE27Elt := by
  intro s t h
  apply eltT_injective
  rw [← permTab_spinE27Elt, h, permTab_spinE27Elt]

theorem spinE27Elt_neg (t : Fin 3 × Fin 3 × Fin 3) : (spinE27Elt t)⁻¹ = spinE27Elt (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [spinE27Elt_mul, add_neg_cancel, spinE27Elt_zero]

theorem mem_spinE27_iff (g : A45) : g ∈ spinE27 ↔ ∃ t, g = spinE27Elt t := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨(1, 0, 0), by simp [spinE27Elt]⟩
      · exact ⟨(0, 1, 0), by simp [spinE27Elt]⟩
      · exact ⟨(0, 0, 1), by simp [spinE27Elt]⟩
    | one => exact ⟨0, spinE27Elt_zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, by rw [hs, ht, spinE27Elt_mul]⟩
    | inv x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨-s, by rw [hs, spinE27Elt_neg]⟩
  · rintro ⟨t, rfl⟩
    have ha : spinE27a ∈ spinE27 := Subgroup.subset_closure (by simp)
    have hb : spinE27b ∈ spinE27 := Subgroup.subset_closure (by simp)
    have hc : spinE27c ∈ spinE27 := Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha _)
      (Subgroup.pow_mem _ hb _)) (Subgroup.pow_mem _ hc _)

end SpinRigid

theorem isElemAbelian_spinE27 : CFSG.Open.IsElemAbelian 3 spinE27 := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := (SpinRigid.mem_spinE27_iff a.1).1 a.2
    obtain ⟨t, ht⟩ := (SpinRigid.mem_spinE27_iff b.1).1 b.2
    apply Subtype.ext
    show (a : A45) * b = b * a
    rw [hs, ht, SpinRigid.spinE27Elt_mul, SpinRigid.spinE27Elt_mul, add_comm]
  · obtain ⟨t, rfl⟩ := (SpinRigid.mem_spinE27_iff x).1 hx
    have h3 : ∀ t : Fin 3 × Fin 3 × Fin 3, t + (t + t) = 0 := by decide
    rw [pow_three, SpinRigid.spinE27Elt_mul, SpinRigid.spinE27Elt_mul, h3,
      SpinRigid.spinE27Elt_zero]

theorem spinE27b_pow_three : spinE27b ^ 3 = 1 :=
  isElemAbelian_spinE27.2 _ (Subgroup.subset_closure (by simp))

theorem spinE27b_inv : spinE27b⁻¹ = spinE27b ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', spinE27b_pow_three]

@[expose] def spinE27Class (ℓ : ℕ) : Finset A45 :=
  ((SpinRigid.e27Data.filter fun e => e.2.1 = ℓ).map fun e => spinE27Elt e.1).toFinset

namespace SpinRigid

theorem mem_spinE27Class (ℓ : ℕ) (g : A45) :
    g ∈ spinE27Class ℓ ↔ ∃ e ∈ e27Data, e.2.1 = ℓ ∧ spinE27Elt e.1 = g := by
  simp [spinE27Class, and_assoc]

theorem card_spinE27Class (ℓ : ℕ) :
    (spinE27Class ℓ).card = (e27Data.filter fun e => e.2.1 = ℓ).length := by
  unfold spinE27Class
  rw [List.toFinset_card_of_nodup, List.length_map]
  have h2 : ((e27Data.filter fun e => e.2.1 = ℓ).map (·.1)).Nodup :=
    e27Data_nodup.sublist (List.Sublist.map _ List.filter_sublist)
  have h3 : ((e27Data.filter fun e => e.2.1 = ℓ).map fun e => spinE27Elt e.1) =
      ((e27Data.filter fun e => e.2.1 = ℓ).map (·.1)).map spinE27Elt := by
    simp [List.map_map, Function.comp_def]
  rw [h3]
  exact h2.map spinE27Elt_injective

theorem disjoint_spinE27Class {ℓ ℓ' : ℕ} (h : ℓ ≠ ℓ') :
    Disjoint (spinE27Class ℓ) (spinE27Class ℓ') := by
  rw [Finset.disjoint_left]
  intro g hg hg'
  obtain ⟨e, he, hl, rfl⟩ := (mem_spinE27Class _ _).1 hg
  obtain ⟨e', he', hl', heq⟩ := (mem_spinE27Class _ _).1 hg'
  have h1 : e'.1 = e.1 := spinE27Elt_injective heq
  have hee : e = e' := List.inj_on_of_nodup_map e27Data_nodup he he' h1.symm
  subst hee
  exact h (hl.symm.trans hl')

theorem mem_ne_one_iff (g : A45) :
    (g ∈ spinE27 ∧ g ≠ 1) ↔ (g ∈ spinE27Class 1 ∨ g ∈ spinE27Class 2 ∨ g ∈ spinE27Class 3) := by
  constructor
  · rintro ⟨hg, hne⟩
    obtain ⟨t, rfl⟩ := (mem_spinE27_iff g).1 hg
    have ht : t ≠ 0 := fun h => hne (by rw [h, spinE27Elt_zero])
    obtain ⟨e, he, rfl⟩ := e27Data_complete t ht
    rcases e27Data_label e he with hl | hl | hl
    · exact Or.inl ((mem_spinE27Class 1 _).2 ⟨e, he, hl, rfl⟩)
    · exact Or.inr (Or.inl ((mem_spinE27Class 2 _).2 ⟨e, he, hl, rfl⟩))
    · exact Or.inr (Or.inr ((mem_spinE27Class 3 _).2 ⟨e, he, hl, rfl⟩))
  · intro h
    have key : ∀ ℓ, g ∈ spinE27Class ℓ → g ∈ spinE27 ∧ g ≠ 1 := by
      intro ℓ hg
      obtain ⟨e, he, -, rfl⟩ := (mem_spinE27Class _ _).1 hg
      refine ⟨(mem_spinE27_iff _).2 ⟨e.1, rfl⟩, fun h1 => e27Data_ne_zero e he ?_⟩
      exact spinE27Elt_injective (h1.trans spinE27Elt_zero.symm)
    rcases h with h | h | h
    · exact key 1 h
    · exact key 2 h
    · exact key 3 h

theorem isConj_of_mem_spinE27Class {ℓ : ℕ} {rep g : A45}
    (hrep : permTab (rep : P45) = repT ℓ) (hg : g ∈ spinE27Class ℓ) : IsConj rep g := by
  obtain ⟨e, he, hl, rfl⟩ := (mem_spinE27Class _ _).1 hg
  have htab := tab_e27 e he
  rw [hl] at htab
  rw [isConj_iff]
  refine ⟨evalSpinWord spinGenA e.2.2, ?_⟩
  have key : evalSpinWord spinGenA e.2.2 * rep = spinE27Elt e.1 * evalSpinWord spinGenA e.2.2 := by
    apply eq_of_permTab_eq
    rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_evalSpinWord, hrep, permTab_spinE27Elt]
    have h3 : (fun i => permTab ((spinGenA i : A45) : P45)) = t3 := funext permTab_spinGenA
    rw [h3]
    exact htab
  rw [key, mul_inv_cancel_right]

theorem inv_mem_spinE27Class {ℓ : ℕ} {g : A45} (hg : g ∈ spinE27Class ℓ) :
    g⁻¹ ∈ spinE27Class ℓ := by
  obtain ⟨e, he, hl, rfl⟩ := (mem_spinE27Class _ _).1 hg
  obtain ⟨e', he', h1, h2⟩ := e27Data_neg e he
  refine (mem_spinE27Class _ _).2 ⟨e', he', h2.trans hl, ?_⟩
  rw [h1, ← spinE27Elt_neg]

end SpinRigid

theorem spinE27_classes :
    ∃ L₁ L₂ L₃ : Finset A45, L₁.card = 8 ∧ L₂.card = 6 ∧ L₃.card = 12 ∧
      Disjoint L₁ L₂ ∧ Disjoint L₁ L₃ ∧ Disjoint L₂ L₃ ∧
      (∀ g : A45, (g ∈ spinE27 ∧ g ≠ 1) ↔ (g ∈ L₁ ∨ g ∈ L₂ ∨ g ∈ L₃)) ∧
      (∀ g ∈ L₁, IsConj spinE27a g) ∧ (∀ g ∈ L₂, IsConj (spinE27a * spinE27b) g) ∧
      (∀ g ∈ L₃, IsConj (spinE27a * spinE27b⁻¹) g) ∧
      (∀ g ∈ L₁, g⁻¹ ∈ L₁) ∧ (∀ g ∈ L₂, g⁻¹ ∈ L₂) ∧ (∀ g ∈ L₃, g⁻¹ ∈ L₃) := by
  have ha : SpinRigid.permTab ((spinE27a : A45) : P45) = SpinRigid.tM1 := SpinRigid.permTab_spinG5 2
  have hb : SpinRigid.permTab ((spinE27b : A45) : P45) = SpinRigid.tM2 := SpinRigid.permTab_spinG5 3
  refine ⟨spinE27Class 1, spinE27Class 2, spinE27Class 3, ?_, ?_, ?_,
    SpinRigid.disjoint_spinE27Class (by decide), SpinRigid.disjoint_spinE27Class (by decide),
    SpinRigid.disjoint_spinE27Class (by decide), SpinRigid.mem_ne_one_iff, ?_, ?_, ?_,
    fun g hg => SpinRigid.inv_mem_spinE27Class hg, fun g hg => SpinRigid.inv_mem_spinE27Class hg,
    fun g hg => SpinRigid.inv_mem_spinE27Class hg⟩
  · rw [SpinRigid.card_spinE27Class]
    exact SpinRigid.e27Data_count.1
  · rw [SpinRigid.card_spinE27Class]
    exact SpinRigid.e27Data_count.2.1
  · rw [SpinRigid.card_spinE27Class]
    exact SpinRigid.e27Data_count.2.2
  · intro g hg
    exact SpinRigid.isConj_of_mem_spinE27Class (ℓ := 1) ha hg
  · intro g hg
    refine SpinRigid.isConj_of_mem_spinE27Class (ℓ := 2) ?_ hg
    rw [permTab_coe_mul, ha, hb]
    rfl
  · intro g hg
    rw [spinE27b_inv]
    refine SpinRigid.isConj_of_mem_spinE27Class (ℓ := 3) ?_ hg
    rw [permTab_coe_mul, permTab_coe_pow, ha, hb]
    rfl

end CFSG.RankThree.GF2n.Parrott
