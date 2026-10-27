module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

section Generic

variable {G : Type} [Group G] {W : Type} [CommGroup W]

theorem crossed_one (ρ : G →* MulAut W) {f : G → W}
    (hf : ∀ g h, f (g * h) = f g * ρ g (f h)) : f 1 = 1 := by
  have h := hf 1 1
  rw [one_mul, map_one, MulAut.one_apply] at h
  exact (mul_eq_left.mp h.symm)

theorem crossed_inv (ρ : G →* MulAut W) {f : G → W}
    (hf : ∀ g h, f (g * h) = f g * ρ g (f h)) (g : G) : f g⁻¹ = ρ g⁻¹ (f g)⁻¹ := by
  have h := hf g g⁻¹
  rw [mul_inv_cancel, crossed_one ρ hf] at h
  have h2 : ρ g (f g⁻¹) = (f g)⁻¹ := by rw [eq_inv_iff_mul_eq_one, mul_comm]; exact h.symm
  rw [← h2, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem crossed_principal_of_closure (ρ : G →* MulAut W) {f : G → W}
    (hf : ∀ g h, f (g * h) = f g * ρ g (f h)) (S : Set G) (hS : Subgroup.closure S = ⊤) (w : W)
    (hw : ∀ s ∈ S, f s = ρ s w * w⁻¹) (g : G) : f g = ρ g w * w⁻¹ := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hw x hx
  | one => rw [crossed_one ρ hf, map_one, MulAut.one_apply, mul_inv_cancel]
  | mul a b _ _ ha hb =>
    have hab : ρ (a * b) w = ρ a (ρ b w) := by rw [map_mul]; rfl
    rw [hf, ha, hb, hab, map_mul (ρ a), map_inv (ρ a)]
    simp [mul_comm, mul_left_comm]
  | inv a _ ha =>
    have h1 : ρ a⁻¹ (ρ a w) = w := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [crossed_inv ρ hf, ha, map_inv (ρ a⁻¹), map_mul (ρ a⁻¹), map_inv (ρ a⁻¹), h1]
    simp [mul_comm]

@[expose] def wordG (a b : G) : List Bool → G
  | [] => 1
  | c :: l => (if c then b else a) * wordG a b l

@[expose] def wordV (ρ : G →* MulAut W) (a b : G) (x y : W) : List Bool → W
  | [] => 1
  | c :: l => (if c then y else x) * ρ (if c then b else a) (wordV ρ a b x y l)

theorem crossed_word (ρ : G →* MulAut W) {f : G → W}
    (hf : ∀ g h, f (g * h) = f g * ρ g (f h)) (a b : G) (l : List Bool) :
    f (wordG a b l) = wordV ρ a b (f a) (f b) l := by
  induction l with
  | nil => exact crossed_one ρ hf
  | cons c l ih =>
    cases c
    · simp only [wordG, wordV, Bool.false_eq_true, ite_false]
      rw [hf, ih]
    · simp only [wordG, wordV, ite_true]
      rw [hf, ih]

theorem crossed_relator (ρ : G →* MulAut W) {f : G → W}
    (hf : ∀ g h, f (g * h) = f g * ρ g (f h)) (a b : G) (l : List Bool)
    (hl : wordG a b l = 1) : wordV ρ a b (f a) (f b) l = 1 := by
  rw [← crossed_word ρ hf, hl, crossed_one ρ hf]

end Generic

private def pA : Perm (Fin 5) := swap 0 1

private def pB : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

private def pw (n : ℕ) (l : List Bool) : List Bool := (List.replicate n l).flatten

private def rels5 : List (List Bool) :=
  [[false, false], pw 5 [true], pw 4 [false, true],
   pw 3 ([false] ++ pw 4 [true] ++ [false, true]),
   pw 2 ([false] ++ pw 3 [true] ++ [false] ++ pw 2 [true])]

private theorem rels5_one : ∀ l ∈ rels5, wordG pA pB l = 1 := by decide +kernel

private theorem pB_eq : pB = finRotate 5 := by decide +kernel

private theorem closure_pA_pB : Subgroup.closure ({pA, pB} : Set (Perm (Fin 5))) = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (σ := pB) (x := 0)
    (by rw [pB_eq]; exact isCycle_finRotate) (by rw [pB_eq]; exact support_finRotate)
  have e : swap (0 : Fin 5) (pB 0) = pA := by decide
  rw [e, Set.pair_comm] at h
  exact h

private theorem check_S5 : ∀ x y : orth.W, (∀ l ∈ rels5, wordV orth.act pA pB x y l = 1) →
    ∃ w : orth.W, orth.act pA w * w⁻¹ = x ∧ orth.act pB w * w⁻¹ = y := by
  decide +kernel

theorem h1_perm5_orth (f : Equiv.Perm (Fin 5) → orth.W)
    (hf : ∀ g h, f (g * h) = f g * orth.act g (f h)) :
    ∃ w : orth.W, ∀ g, f g = orth.act g w * w⁻¹ := by
  obtain ⟨w, hA, hB⟩ := check_S5 (f pA) (f pB)
    (fun l hl => crossed_relator orth.act hf pA pB l (rels5_one l hl))
  refine ⟨w, crossed_principal_of_closure orth.act hf {pA, pB} closure_pA_pB w ?_⟩
  rintro s (rfl | rfl)
  · exact hA.symm
  · exact hB.symm

private def qa : Perm (Fin 5) := swap 0 1 * swap 2 3

private def qb : Perm (Fin 5) := swap 0 2 * swap 2 4

private def qA : alternatingGroup (Fin 5) :=
  ⟨qa, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def qB : alternatingGroup (Fin 5) :=
  ⟨qb, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def rels3 : List (List Bool) := [[false, false], pw 3 [true], pw 5 [false, true]]

private theorem rels3_one : ∀ l ∈ rels3, wordG qA qB l = 1 := by decide +kernel

@[irreducible] private def altF : Finset (Perm (Fin 5)) := wordSet [qa, qb] 10

private theorem alt_wordSet : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ∈ altF := by
  unfold altF
  decide +kernel

private theorem altF_closure : ∀ σ ∈ altF, σ ∈ Subgroup.closure {g | g ∈ [qa, qb]} := by
  unfold altF
  exact wordSet_subset_closure [qa, qb] 10

private theorem closure_qA_qB :
    Subgroup.closure ({qA, qB} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  have e : (alternatingGroup (Fin 5)).subtype '' ({qA, qB} : Set (alternatingGroup (Fin 5))) =
      {g | g ∈ [qa, qb]} := by
    rw [Set.image_pair]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.not_mem_nil,
      or_false, Set.mem_ofPred_eq]
    exact Iff.rfl
  have h1 := altF_closure g.1 (alt_wordSet g.1 (Equiv.Perm.mem_alternatingGroup.mp g.2))
  rw [← e, ← MonoidHom.map_closure] at h1
  obtain ⟨h, hh, hg⟩ := Subgroup.mem_map.mp h1
  have : h = g := Subtype.ext hg
  rwa [this] at hh

private def actA : alternatingGroup (Fin 5) →* MulAut orth.W :=
  orth.act.comp (alternatingGroup (Fin 5)).subtype

private theorem check_A5 : ∀ x y : orth.W, (∀ l ∈ rels3, wordV actA qA qB x y l = 1) →
    ∃ w : orth.W, actA qA w * w⁻¹ = x ∧ actA qB w * w⁻¹ = y := by
  decide +kernel

theorem h1_alt5_orth (f : alternatingGroup (Fin 5) → orth.W)
    (hf : ∀ g h, f (g * h) = f g * orth.act (g : Equiv.Perm (Fin 5)) (f h)) :
    ∃ w : orth.W, ∀ g, f g = orth.act (g : Equiv.Perm (Fin 5)) w * w⁻¹ := by
  obtain ⟨w, hA, hB⟩ := check_A5 (f qA) (f qB)
    (fun l hl => crossed_relator actA hf qA qB l (rels3_one l hl))
  exact ⟨w, crossed_principal_of_closure actA hf {qA, qB} closure_qA_qB w (by
    rintro s (rfl | rfl)
    · exact hA.symm
    · exact hB.symm)⟩

end CFSG.Quasithin.F53Mod
