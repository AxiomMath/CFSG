module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev SLt (n : ℕ) : Type := SpecialLinearGroup (Fin n) (ZMod 2)

abbrev Vt (n : ℕ) : Type := Fin n → ZMod 2

abbrev mat {n : ℕ} (g : SLt n) : Matrix (Fin n) (Fin n) (ZMod 2) := g

theorem mat_mul {n : ℕ} (a b : SLt n) : mat (a * b) = mat a * mat b :=
  Matrix.SpecialLinearGroup.coe_mul a b

theorem mat_one {n : ℕ} : mat (1 : SLt n) = 1 := Matrix.SpecialLinearGroup.coe_one

@[expose] def SInv {n : ℕ} (Q : Subgroup (SLt n)) (W : Submodule (ZMod 2) (Vt n)) : Prop :=
  ∀ q ∈ Q, ∀ v ∈ W, mat q *ᵥ v ∈ W

theorem mat_conj_mul {n : ℕ} (g u : SLt n) :
    mat (g * u * g⁻¹) * mat g = mat g * mat u := by
  rw [← mat_mul, ← mat_mul]
  congr 1
  group

theorem mat_inv_conj_mul {n : ℕ} (g u : SLt n) :
    mat g⁻¹ * mat (g * u * g⁻¹) = mat u * mat g⁻¹ := by
  rw [← mat_mul, ← mat_mul]
  congr 1
  group

theorem mat_mul_inv {n : ℕ} (g : SLt n) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem exists_conj_eq_unitriangular {n : ℕ} (hn : 1 ≤ n) (Q : Sylow 2 (SLt n)) :
    ∃ g : SLt n, (Q : Subgroup (SLt n)) =
      (unitriangular n (ZMod 2)).map (MulAut.conj g : SLt n →* SLt n) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SLt n) P Q
  refine ⟨g, ?_⟩
  rw [← hg, coe_sylow_smul, hP]

theorem sInv_conj_iff {n : ℕ} (g : SLt n) (W : Submodule (ZMod 2) (Vt n)) :
    SInv ((unitriangular n (ZMod 2)).map (MulAut.conj g : SLt n →* SLt n)) W ↔
      ∃ m ≤ n, W = (flagSpace n (ZMod 2) m).map (mulVecLin (mat g)) := by
  constructor
  · intro h
    have hinv : ∀ u ∈ unitriangular n (ZMod 2),
        ∀ v ∈ W.map (mulVecLin (mat g⁻¹)), mat u *ᵥ v ∈ W.map (mulVecLin (mat g⁻¹)) := by
      rintro u hu _ ⟨w, hw, rfl⟩
      have hq : g * u * g⁻¹ ∈ (unitriangular n (ZMod 2)).map (MulAut.conj g : SLt n →* SLt n) :=
        ⟨u, hu, by simp [MulAut.conj_apply]⟩
      refine ⟨mat (g * u * g⁻¹) *ᵥ w, h _ hq w hw, ?_⟩
      simp only [mulVecLin_apply, mulVec_mulVec, mat_inv_conj_mul]
    obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant hinv
    refine ⟨m, hm, ?_⟩
    have : W = (W.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat g)) := by
      rw [← Submodule.map_comp, ← mulVecLin_mul, mat_mul_inv, mulVecLin_one, Submodule.map_id]
    rw [this, hW]
  · rintro ⟨m, hm, rfl⟩ q ⟨u, hu, hq⟩ _ ⟨f, hf, rfl⟩
    have hq' : q = g * u * g⁻¹ := by rw [← hq]; rfl
    refine ⟨mat u *ᵥ f,
      flagSpace_invariant m (unitriangular_le_upperTriangular n (ZMod 2) hu) hf, ?_⟩
    simp only [mulVecLin_apply, mulVec_mulVec, hq', mat_conj_mul]

theorem finrank_map_mulVecLin {n : ℕ} (g : SLt n) (W : Submodule (ZMod 2) (Vt n)) :
    finrank (ZMod 2) (W.map (mulVecLin (mat g))) = finrank (ZMod 2) W :=
  LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) W

theorem exists_unique_flag {n : ℕ} (hn : 1 ≤ n) (Q : Sylow 2 (SLt n)) :
    ∃ W : ℕ → Submodule (ZMod 2) (Vt n),
      (∀ k ≤ n, finrank (ZMod 2) (W k) = k) ∧ (∀ k ≤ n, SInv (Q : Subgroup (SLt n)) (W k)) ∧
      (∀ k, W k ≤ W (k + 1)) ∧
      ∀ X : Submodule (ZMod 2) (Vt n), SInv (Q : Subgroup (SLt n)) X → ∀ k ≤ n,
        finrank (ZMod 2) X = k → X = W k := by
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  refine ⟨fun k => (flagSpace n (ZMod 2) k).map (mulVecLin (mat g)), fun k hk => ?_,
    fun k hk => ?_, fun k => ?_, fun X hX k hk hXk => ?_⟩
  · rw [finrank_map_mulVecLin, finrank_flagSpace hk]
  · rw [hg]
    exact (sInv_conj_iff g _).2 ⟨k, hk, rfl⟩
  · exact Submodule.map_mono (flagSpace_mono (Nat.le_succ k))
  · rw [hg] at hX
    obtain ⟨m, hm, rfl⟩ := (sInv_conj_iff g X).1 hX
    rw [finrank_map_mulVecLin, finrank_flagSpace hm] at hXk
    rw [hXk]

@[expose] def subgroupOfSpace {n : ℕ} (W : Submodule (ZMod 2) (Vt n)) :
    Subgroup (Multiplicative (Vt n)) where
  carrier := {x | Multiplicative.toAdd x ∈ W}
  mul_mem' := fun {_ _} ha hb => W.add_mem ha hb
  one_mem' := W.zero_mem
  inv_mem' := fun {_} ha => W.neg_mem ha

@[expose] def spaceOfSubgroup {n : ℕ} (Y : Subgroup (Multiplicative (Vt n))) :
    Submodule (ZMod 2) (Vt n) where
  carrier := {v | Multiplicative.ofAdd v ∈ Y}
  add_mem' := fun {_ _} ha hb => Y.mul_mem ha hb
  zero_mem' := Y.one_mem
  smul_mem' := by
    intro c v hv
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp
    · simpa using hv

theorem mem_subgroupOfSpace {n : ℕ} {W : Submodule (ZMod 2) (Vt n)} {x : Multiplicative (Vt n)} :
    x ∈ subgroupOfSpace W ↔ Multiplicative.toAdd x ∈ W := Iff.rfl

theorem mem_spaceOfSubgroup {n : ℕ} {Y : Subgroup (Multiplicative (Vt n))} {v : Vt n} :
    v ∈ spaceOfSubgroup Y ↔ Multiplicative.ofAdd v ∈ Y := Iff.rfl

theorem spaceOfSubgroup_subgroupOfSpace {n : ℕ} (W : Submodule (ZMod 2) (Vt n)) :
    spaceOfSubgroup (subgroupOfSpace W) = W := by
  ext v
  rfl

theorem subgroupOfSpace_spaceOfSubgroup {n : ℕ} (Y : Subgroup (Multiplicative (Vt n))) :
    subgroupOfSpace (spaceOfSubgroup Y) = Y := by
  ext x
  rfl

theorem card_subgroupOfSpace {n : ℕ} (W : Submodule (ZMod 2) (Vt n)) :
    Nat.card (subgroupOfSpace W) = 2 ^ finrank (ZMod 2) W := by
  have h1 : Nat.card (subgroupOfSpace W) = Nat.card W :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩
        left_inv := fun x => rfl
        right_inv := fun v => rfl }
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

@[expose] def SInvG {n : ℕ} (Q : Subgroup (SLt n)) (X : Subgroup (Multiplicative (Vt n))) : Prop :=
  ∀ q ∈ Q, ∀ x ∈ X, Multiplicative.ofAdd (mat q *ᵥ Multiplicative.toAdd x) ∈ X

theorem exists_unique_flag_subgroup {n : ℕ} (hn : 1 ≤ n) (Q : Sylow 2 (SLt n)) :
    ∃ Y : ℕ → Subgroup (Multiplicative (Vt n)),
      (∀ k ≤ n, Nat.card (Y k) = 2 ^ k) ∧ (∀ k ≤ n, SInvG (Q : Subgroup (SLt n)) (Y k)) ∧
      (∀ k, Y k ≤ Y (k + 1)) ∧
      ∀ X : Subgroup (Multiplicative (Vt n)), SInvG (Q : Subgroup (SLt n)) X → ∀ k ≤ n,
        Nat.card X = 2 ^ k → X = Y k := by
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := exists_unique_flag hn Q
  refine ⟨fun k => subgroupOfSpace (W k), fun k hk => ?_, fun k hk => hW2 k hk,
    fun k x hx => hW3 k hx, fun X hX k hk hXk => ?_⟩
  · rw [card_subgroupOfSpace, hW1 k hk]
  · have h1 : SInv (Q : Subgroup (SLt n)) (spaceOfSubgroup X) := fun q hq v hv =>
      hX q hq (Multiplicative.ofAdd v) hv
    have h2 : finrank (ZMod 2) (spaceOfSubgroup X) = k := by
      have h3 := card_subgroupOfSpace (spaceOfSubgroup X)
      rw [subgroupOfSpace_spaceOfSubgroup, hXk] at h3
      exact (Nat.pow_right_injective le_rfl h3).symm
    have h4 := hW4 _ h1 k hk h2
    rw [← subgroupOfSpace_spaceOfSubgroup X, h4]

end CFSG.Quasithin.FLc
