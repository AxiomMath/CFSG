module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H8

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

@[expose] def fixN (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    AddSubgroup (Fin n → ZMod 2) where
  carrier := {v | ∀ a ∈ A, a • v = v}
  add_mem' := fun ha hb a hA => by rw [smul_add, ha a hA, hb a hA]
  zero_mem' := fun a _ => smul_zero a
  neg_mem' := fun ha a hA => by rw [smul_neg, ha a hA]

theorem mem_fixN {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))} {v : Fin n → ZMod 2} :
    v ∈ fixN A ↔ ∀ a ∈ A, a • v = v := Iff.rfl

theorem smul_mem_fixN {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}
    {x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ Subgroup.normalizer (A : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))))
    {v : Fin n → ZMod 2} (hv : v ∈ fixN A) : x • v ∈ fixN A := by
  intro a ha
  have h : x⁻¹ * a * x ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) a).mp ha
    simpa using this
  calc a • x • v = x • (x⁻¹ * a * x) • v := by rw [← mul_smul, ← mul_smul]; group
    _ = x • v := by rw [hv _ h]

theorem exists_ne_zero_fixN {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : IsPGroup 2 A) (hn : 1 ≤ n) : ∃ v ∈ fixN A, v ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hA.card_modEq_card_fixedPoints (Fin n → ZMod 2)
  have he : MulAction.fixedPoints A (Fin n → ZMod 2) = (fixN A : Set (Fin n → ZMod 2)) := by
    ext v
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixN, Subtype.forall]
    rfl
  rw [he] at h1
  have hcard : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard] at h1
  by_contra hc
  have hbot : Nat.card ↥(fixN A) = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨⟨0, (fixN A).zero_mem⟩⟩⟩
    have ha : (a : Fin n → ZMod 2) = 0 := by
      by_contra h
      exact hc ⟨a, a.2, h⟩
    have hb : (b : Fin n → ZMod 2) = 0 := by
      by_contra h
      exact hc ⟨b, b.2, h⟩
    exact Subtype.ext (ha.trans hb.symm)
  have hbot' : Nat.card ↑(fixN A : Set (Fin n → ZMod 2)) = 1 := hbot
  have h1' : 2 ^ n ≡ 1 [MOD 2] := by
    have := h1
    rwa [hbot'] at this
  unfold Nat.ModEq at h1'
  rw [Nat.pow_mod] at h1'
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [pow_succ] at h1'

theorem exists_not_mem_fixN {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA1 : A ≠ ⊥) : ∃ v, v ∉ fixN A := by
  by_contra hc
  apply hA1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply ext_mulVec
  intro x
  have hx : x ∈ fixN A := by
    by_contra h
    exact hc ⟨x, h⟩
  rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
  exact hx a ha

theorem eq_zero_of_fixed (hn : 2 ≤ n) {v : Fin n → ZMod 2}
    (hv : ∀ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), g • v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨w, hw0, hwv⟩ : ∃ w : Fin n → ZMod 2, w ≠ 0 ∧ w ≠ v := by
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    by_cases h : v = Pi.single i0 1
    · refine ⟨Pi.single i1 1, fun h' => ?_, fun h' => ?_⟩
      · have := congrFun h' i1
        simp at this
      · rw [h] at h'
        have := congrFun h' i1
        simp [i0, i1] at this
    · refine ⟨Pi.single i0 1, fun h' => ?_, fun h' => h h'.symm⟩
      have := congrFun h' i0
      simp at this
  obtain ⟨g, hg⟩ := exists_mulVec_eq hv0 hw0
  exact hwv (hg.symm.trans (hv g))

theorem eq_bot_of_normal_two (hn : 2 ≤ n)
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N = ⊥ := by
  by_contra h1
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_fixN hp (by omega)
  obtain ⟨w, hw⟩ := exists_not_mem_fixN h1
  by_cases hw0 : w = 0
  · exact hw (hw0 ▸ (fixN N).zero_mem)
  obtain ⟨g, hg⟩ := exists_mulVec_eq hv0 hw0
  apply hw
  have hgN : g ∈ Subgroup.normalizer (N : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    trivial
  have := smul_mem_fixN hgN hv
  rwa [smul_eq_mulVec', hg] at this

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
