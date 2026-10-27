module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpA5Vec
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpRec
public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFiveGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

open CFSG.HardMathSupport.RichardWeiss.Proving

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {a b : W ≃ₗ[ZMod 2] W}

theorem exists_permHom {Y : Subgroup (W ≃ₗ[ZMod 2] W)} {w : Fin 5 → W}
    (hw : Function.Injective w) (hY : ∀ y ∈ Y, ∀ i, ∃ j, y (w i) = w j) :
    ∃ ρ : ↥Y →* Equiv.Perm (Fin 5),
      ∀ (y : ↥Y) (i : Fin 5), w (ρ y i) = (y : W ≃ₗ[ZMod 2] W) (w i) := by
  choose f hf using fun (y : ↥Y) i => hY y.1 y.2 i
  have hinj : ∀ y : ↥Y, Function.Injective (f y) := by
    intro y i j hij
    apply hw
    apply (y : W ≃ₗ[ZMod 2] W).injective
    rw [hf y i, hf y j, hij]
  let σ : ↥Y → Equiv.Perm (Fin 5) := fun y =>
    Equiv.ofBijective (f y) ⟨hinj y, Finite.injective_iff_surjective.mp (hinj y)⟩
  refine ⟨MonoidHom.mk' σ ?_, ?_⟩
  · intro y y'
    refine Equiv.ext fun i => ?_
    apply hw
    show w (f (y * y') i) = w (f y (f y' i))
    rw [← hf (y * y') i, ← hf y (f y' i), ← hf y' i]
    rfl
  · intro y i
    exact (hf y i).symm

theorem fiveVec_a_eq {w : Fin 5 → W} (h : FiveVec a b w) (i : Fin 5) :
    a (w i) = w (altFiveUPerm i) := by
  fin_cases i
  · exact h.a0
  · exact h.a1
  · exact h.a2
  · exact h.a3
  · exact h.a4

theorem fiveVec_b_eq {w : Fin 5 → W} (h : FiveVec a b w) (i : Fin 5) :
    b (w i) = w (altFiveVPerm i) := by
  fin_cases i
  · exact h.b0
  · exact h.b1
  · exact h.b2
  · exact h.b3
  · exact h.b4

@[expose] def permStab (w : Fin 5 → W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {y | ∃ σ : Equiv.Perm (Fin 5), ∀ i, y (w i) = w (σ i)}
  mul_mem' := by
    rintro y y' ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    exact ⟨σ * σ', fun i => by rw [LinearEquiv.mul_apply, hσ', hσ]; rfl⟩
  one_mem' := ⟨1, fun i => rfl⟩
  inv_mem' := by
    rintro y ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun i => ?_⟩
    apply (y : W ≃ₗ[ZMod 2] W).injective
    have h1 : y (y⁻¹ (w i)) = w i := by simp
    rw [h1, hσ]
    simp

theorem fiveVec_mem_perm {w : Fin 5 → W} (h : FiveVec a b w) :
    ∀ y ∈ Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)), ∀ i, ∃ j, y (w i) = w j := by
  have hle : Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)) ≤ permStab w := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨altFiveUPerm, fiveVec_a_eq h⟩
    · exact ⟨altFiveVPerm, fiveVec_b_eq h⟩
  intro y hy i
  obtain ⟨σ, hσ⟩ := hle hy
  exact ⟨σ i, hσ i⟩

@[expose] def actTriv (S : Submodule (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {y | ∀ x, y x - x ∈ S}
  mul_mem' := by
    intro y y' hy hy' x
    have e : (y * y') x - x = (y (y' x) - y' x) + (y' x - x) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [e]
    exact add_mem (hy _) (hy' x)
  one_mem' := fun x => by simp
  inv_mem' := by
    intro y hy x
    have e : y⁻¹ x - x = -(y (y⁻¹ x) - y⁻¹ x) := by
      have h2 : y (y⁻¹ x) = x := by simp
      rw [h2]; abel
    rw [e]
    exact neg_mem (hy _)

theorem fiveVec_sub_mem {w : Fin 5 → W} (h : FiveVec a b w) :
    ∀ y ∈ Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)), ∀ x,
      y x - x ∈ Submodule.span (ZMod 2) (Set.range w) := by
  have hle : Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)) ≤
      actTriv (Submodule.span (ZMod 2) (Set.range w)) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact fun x => h.span_a (sub_mem_commSp _ x)
    · exact fun x => h.span_b (sub_mem_commSp _ x)
  exact fun y hy => hle hy

theorem fiveVec_pow_two {w : Fin 5 → W} (h : FiveVec a b w) {y : W ≃ₗ[ZMod 2] W}
    (hy : y ∈ Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) (hfix : ∀ i, y (w i) = w i) :
    y ^ 2 = 1 := by
  have hS : ∀ s ∈ Submodule.span (ZMod 2) (Set.range w), y s = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfix i
    | zero => simp
    | add x z _ _ hx hz => rw [map_add, hx, hz]
    | smul c x _ hx => rw [map_smul, hx]
  ext x
  have hs := fiveVec_sub_mem h y hy x
  have h1 : y (y x) - y x = y x - x := by rw [← map_sub]; exact hS _ hs
  have e : y (y x) = x :=
    calc y (y x) = (y (y x) - y x) + y x := by abel
      _ = (y x - x) + y x := by rw [h1]
      _ = (y x + y x) - x := by abel
      _ = x := by rw [add_self_eq_zero', zero_sub, neg_eq_self']
  rw [pow_two, LinearEquiv.mul_apply]
  exact e

theorem pairShapeHom_of_fiveVec {w : Fin 5 → W} (h : FiveVec a b w) :
    PairShapeHom ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) := by
  obtain ⟨ρ, hρ⟩ := exists_permHom h.inj (fiveVec_mem_perm h)
  have hρa : ρ (memA a b) = altFiveUPerm :=
    Equiv.ext fun i => h.inj (by rw [hρ]; exact fiveVec_a_eq h i)
  have hρb : ρ (memB a b) = altFiveVPerm :=
    Equiv.ext fun i => h.inj (by rw [hρ]; exact fiveVec_b_eq h i)
  have hA : ∀ y, ρ y ∈ alternatingGroup (Fin 5) := by
    refine closure_pair_induction (p := fun y => ρ y ∈ alternatingGroup (Fin 5)) ?_ ?_ ?_ ?_ ?_
    · rw [hρa]; exact altFiveU.2
    · rw [hρb]; exact altFiveV.2
    · rw [map_one]; exact one_mem _
    · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy
    · intro x hx; rw [map_inv]; exact inv_mem hx
  let f : ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) →* ↥(alternatingGroup (Fin 5)) :=
    ρ.codRestrict (alternatingGroup (Fin 5)) hA
  have hfa : f (memA a b) = altFiveU := Subtype.ext hρa
  have hfb : f (memB a b) = altFiveV := Subtype.ext hρb
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← altFive_closure_pair_eq_top, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ⟨memA a b, hfa⟩
    · exact ⟨memB a b, hfb⟩
  refine pairShapeHom_of_alt5 f hsurj (isPGroup_two_ker_of_pow_four f ?_)
  intro y hy
  have hρy : ρ y = 1 := congrArg Subtype.val hy
  have hfix : ∀ i, (y : W ≃ₗ[ZMod 2] W) (w i) = w i := fun i => by rw [← hρ, hρy]; rfl
  have h2 := fiveVec_pow_two h y.2 hfix
  have h4 : (y : W ≃ₗ[ZMod 2] W) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]
  exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h4)

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
