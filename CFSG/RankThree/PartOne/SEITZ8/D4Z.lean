module

public import CFSG.RankThree.PartOne.SEITZ8.D4Entry

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

@[expose] def Zsub (K : Type) [Field K] : Submodule K (RootModule d4 K) where
  carrier := {z | (∀ γ : Fin d4.rank → ℤ, coordAt γ z = 0) ∧ z (Sum.inl (nd 2)) = 0 ∧
    z (Sum.inl (nd 0)) + z (Sum.inl (nd 1)) + z (Sum.inl (nd 3)) = 0}
  add_mem' := fun {x y} hx hy =>
    ⟨fun γ => by rw [coordAt_add, hx.1 γ, hy.1 γ, add_zero],
      by rw [Finsupp.add_apply, hx.2.1, hy.2.1, add_zero],
      by
        simp only [Finsupp.add_apply]
        calc _ = (x (Sum.inl (nd 0)) + x (Sum.inl (nd 1)) + x (Sum.inl (nd 3))) +
              (y (Sum.inl (nd 0)) + y (Sum.inl (nd 1)) + y (Sum.inl (nd 3))) := by ring
          _ = 0 := by rw [hx.2.2, hy.2.2, add_zero]⟩
  zero_mem' := ⟨fun γ => by simp [coordAt], by simp, by simp⟩
  smul_mem' := fun c x hx =>
    ⟨fun γ => by rw [coordAt_smul, hx.1 γ, mul_zero],
      by rw [Finsupp.smul_apply, hx.2.1, smul_zero],
      by
        simp only [Finsupp.smul_apply, smul_eq_mul]
        calc _ = c * (x (Sum.inl (nd 0)) + x (Sum.inl (nd 1)) + x (Sum.inl (nd 3))) := by ring
          _ = 0 := by rw [hx.2.2, mul_zero]⟩

section ZFix

variable [CharP K 2]

omit [CharP K 2] in
theorem hVec_apply_inl (j j' : Fin d4.rank) :
    (hVec d4 K j') (Sum.inl j) = if j' = j then 1 else 0 := by
  show (Finsupp.single (Sum.inl j') (1 : K) : RootModule d4 K) (Sum.inl j) = _
  rw [Finsupp.single_apply]
  simp

omit [CharP K 2] in
theorem hVec_apply_inr (j : Fin d4.rank) (β : {v // IsRoot d4 v}) :
    (hVec d4 K j) (Sum.inr β) = 0 := by
  show (Finsupp.single (Sum.inl j) (1 : K) : RootModule d4 K) (Sum.inr β) = 0
  rw [Finsupp.single_apply]
  simp

omit [CharP K 2] in
theorem Zsub_eq_four {z : RootModule d4 K} (hz : z ∈ Zsub K) :
    z = z (Sum.inl (nd 0)) • hVec d4 K (nd 0) + z (Sum.inl (nd 1)) • hVec d4 K (nd 1) +
      z (Sum.inl (nd 2)) • hVec d4 K (nd 2) + z (Sum.inl (nd 3)) • hVec d4 K (nd 3) := by
  refine Finsupp.ext fun b => ?_
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rcases b with j | ⟨β, hβ⟩
  · have hj : j.val < 4 := j.2
    have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases this with h | h | h | h
    · have e : j = (nd 0) := Fin.ext h
      subst e
      simp [hVec_apply_inl, nd, Fin.ext_iff]
    · have e : j = (nd 1) := Fin.ext h
      subst e
      simp [hVec_apply_inl, nd, Fin.ext_iff]
    · have e : j = (nd 2) := Fin.ext h
      subst e
      simp [hVec_apply_inl, nd, Fin.ext_iff]
    · have e : j = (nd 3) := Fin.ext h
      subst e
      simp [hVec_apply_inl, nd, Fin.ext_iff]
  · have h0 := hz.1 β
    rw [coordAt_eq hβ] at h0
    simp [h0, hVec_apply_inr]

omit [CharP K 2] in
theorem cartan_abs_check : ∀ i j : Fin d4.rank, (d4.cartan j i).natAbs =
    if i = j then 2 else if (i.val = 2) ≠ (j.val = 2) then 1 else 0 := by decide

theorem Z_scalar {z : RootModule d4 K} (hz : z ∈ Zsub K) (i : Fin d4.rank) :
    z (Sum.inl (nd 0)) * ((d4.cartan (nd 0) i).natAbs : K) +
      z (Sum.inl (nd 1)) * ((d4.cartan (nd 1) i).natAbs : K) +
      z (Sum.inl (nd 2)) * ((d4.cartan (nd 2) i).natAbs : K) +
      z (Sum.inl (nd 3)) * ((d4.cartan (nd 3) i).natAbs : K) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, hz2, hz013⟩ := hz
  have hi : i.val < 4 := i.2
  have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases this with h | h | h | h
  · have e : i = (nd 0) := Fin.ext h
    subst e
    simp only [cartan_abs_check]
    simp [hz2, h2, nd, Fin.ext_iff]
  · have e : i = (nd 1) := Fin.ext h
    subst e
    simp only [cartan_abs_check]
    simp [hz2, h2, nd, Fin.ext_iff]
  · have e : i = (nd 2) := Fin.ext h
    subst e
    simp only [cartan_abs_check]
    simp [h2, nd, Fin.ext_iff]
    linear_combination hz013
  · have e : i = (nd 3) := Fin.ext h
    subst e
    simp only [cartan_abs_check]
    simp [hz2, h2, nd, Fin.ext_iff]

theorem xCoeff_Z {z : RootModule d4 K} (hz : z ∈ Zsub K) (i : Fin d4.rank) {k : ℕ} (hk : 1 ≤ k) :
    xCoeff d4 K i k z = 0 := by
  have hs := Z_scalar (K := K) hz i
  rw [Zsub_eq_four hz]
  simp only [map_add, map_smul]
  simp only [xCoeff_hVec]
  by_cases h1 : k = 1
  · subst h1
    simp only [one_ne_zero, ite_false, ite_true, smul_smul, ← add_smul]
    rw [hs, zero_smul]
  · have h0 : k ≠ 0 := by omega
    simp [h0, h1]

theorem yCoeff_Z {z : RootModule d4 K} (hz : z ∈ Zsub K) (i : Fin d4.rank) {k : ℕ} (hk : 1 ≤ k) :
    yCoeff d4 K i k z = 0 := by
  have hs := Z_scalar (K := K) hz i
  rw [Zsub_eq_four hz]
  simp only [map_add, map_smul]
  simp only [yCoeff_hVec]
  by_cases h1 : k = 1
  · subst h1
    simp only [one_ne_zero, ite_false, ite_true, smul_smul, ← add_smul]
    rw [hs, zero_smul]
  · have h0 : k ≠ 0 := by omega
    simp [h0, h1]

theorem xOp_Z {z : RootModule d4 K} (hz : z ∈ Zsub K) (i : Fin d4.rank) (c : K) :
    xOp d4 K i c z = z := by
  rw [xOp_eq_sum_xCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
    LinearMap.smul_apply, xCoeff_zero, Module.End.one_apply, pow_zero, one_smul]
  rw [xCoeff_Z hz i (by norm_num : 1 ≤ 1), xCoeff_Z hz i (by norm_num : 1 ≤ 2),
    xCoeff_Z hz i (by norm_num : 1 ≤ 3)]
  simp

theorem yOp_Z {z : RootModule d4 K} (hz : z ∈ Zsub K) (i : Fin d4.rank) (c : K) :
    yOp d4 K i c z = z := by
  rw [yOp_eq_sum_yCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
    LinearMap.smul_apply, yCoeff_zero, Module.End.one_apply, pow_zero, one_smul]
  rw [yCoeff_Z hz i (by norm_num : 1 ≤ 1), yCoeff_Z hz i (by norm_num : 1 ≤ 2),
    yCoeff_Z hz i (by norm_num : 1 ≤ 3)]
  simp

theorem adjointGroup_fix_Z (g : adjointGroup d4 K) {z : RootModule d4 K} (hz : z ∈ Zsub K) :
    g • z = z := by
  obtain ⟨g, hg⟩ := g
  show ((g : ModGL d4 K) : Module.End K (RootModule d4 K)) z = z
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, h | h⟩ := hx
    · rw [h]
      exact xOp_Z hz i c
    · rw [h]
      exact yOp_Z hz i c
  | one => rfl
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Module.End.mul_apply, hy, hx]
  | inv x _ hx =>
    calc ((x⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) z
        = ((x⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K))
            ((x : Module.End K (RootModule d4 K)) z) := by rw [hx]
      _ = z := by
        rw [← Module.End.mul_apply, Units.inv_mul]
        rfl

end ZFix

section Rat

variable [CharP K 2] {σ : K →+* K} {k : Subfield K}
  {R : Subgroup (adjointGroup d4 K)}

omit [CharP K 2] in
theorem ratMod_add_Z {y w : RootModule d4 K} (hy : RatMod k y) (hw : w ∈ Zsub K) :
    RatMod k (y + w) := by
  refine ⟨fun γ => ?_, ?_, ?_⟩
  · rw [coordAt_add, hw.1 γ, add_zero]
    exact hy.1 γ
  · rw [Finsupp.add_apply, hw.2.1, add_zero]
    exact hy.2.1
  · have h1 := hy.2.2
    simp only [Finsupp.add_apply]
    have e : y (Sum.inl (nd 0)) + w (Sum.inl (nd 0)) + (y (Sum.inl (nd 1)) + w (Sum.inl (nd 1))) +
        (y (Sum.inl (nd 3)) + w (Sum.inl (nd 3))) =
          (y (Sum.inl (nd 0)) + y (Sum.inl (nd 1)) + y (Sum.inl (nd 3))) +
            (w (Sum.inl (nd 0)) + w (Sum.inl (nd 1)) + w (Sum.inl (nd 3))) := by ring
    rw [e, hw.2.2, add_zero]
    exact h1

theorem hVec_add_mem_Z_13 : hVec d4 K (nd 1) + hVec d4 K (nd 3) ∈ Zsub K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun γ => by rw [coordAt_add, coordAt_hVec, coordAt_hVec, add_zero], ?_, ?_⟩
  · simp [hVec_apply_inl, nd, Fin.ext_iff]
  · simp only [Finsupp.add_apply, hVec_apply_inl, nd, Fin.ext_iff]
    norm_num
    linear_combination h2

theorem hVec_add_mem_Z_03 : hVec d4 K (nd 0) + hVec d4 K (nd 3) ∈ Zsub K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun γ => by rw [coordAt_add, coordAt_hVec, coordAt_hVec, add_zero], ?_, ?_⟩
  · simp [hVec_apply_inl, nd, Fin.ext_iff]
  · simp only [Finsupp.add_apply, hVec_apply_inl, nd, Fin.ext_iff]
    norm_num
    linear_combination h2

theorem hVec_add_mem_Z_01 : hVec d4 K (nd 0) + hVec d4 K (nd 1) ∈ Zsub K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun γ => by rw [coordAt_add, coordAt_hVec, coordAt_hVec, add_zero], ?_, ?_⟩
  · simp [hVec_apply_inl, nd, Fin.ext_iff]
  · simp only [Finsupp.add_apply, hVec_apply_inl, nd, Fin.ext_iff]
    norm_num
    linear_combination h2

omit [CharP K 2] in
theorem hVec_split (i j l : Fin d4.rank) (hl : ∀ x : RootModule d4 K, x + x = 0) :
    hVec d4 K i = (hVec d4 K i + hVec d4 K j + hVec d4 K l) + (hVec d4 K j + hVec d4 K l) := by
  have : (hVec d4 K i + hVec d4 K j + hVec d4 K l) + (hVec d4 K j + hVec d4 K l) =
      hVec d4 K i + (hVec d4 K j + hVec d4 K j) + (hVec d4 K l + hVec d4 K l) := by abel
  rw [this, hl, hl, add_zero, add_zero]

theorem ratMod_basis (h : SpanHyp σ k R) {g : adjointGroup d4 K}
    (hrat : ∀ x ∈ Submodule.span k (longOrbit R), RatMod k (g • x)) (b : Label d4) :
    RatMod k (g • (Finsupp.single b (1 : K) : RootModule d4 K)) := by
  rcases b with j | ⟨β, hβ⟩
  · have hj : j.val < 4 := j.2
    have hcase : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    have hsingle : ∀ i : Fin d4.rank,
        (Finsupp.single (Sum.inl i) (1 : K) : RootModule d4 K) = hVec d4 K i := fun i => rfl
    rcases hcase with hj | hj | hj | hj
    · have e : j = nd 0 := Fin.ext hj
      subst e
      rw [hsingle, hVec_split (nd 0) (nd 1) (nd 3) vec_add_self, smul_add,
        adjointGroup_fix_Z g hVec_add_mem_Z_13]
      exact ratMod_add_Z (hrat _ (t2_mem_span h)) hVec_add_mem_Z_13
    · have e : j = nd 1 := Fin.ext hj
      subst e
      rw [hsingle, hVec_split (nd 1) (nd 0) (nd 3) vec_add_self, smul_add,
        adjointGroup_fix_Z g hVec_add_mem_Z_03]
      have ht : hVec d4 K (nd 1) + hVec d4 K (nd 0) + hVec d4 K (nd 3) ∈
          Submodule.span k (longOrbit R) := by
        have e : hVec d4 K (nd 1) + hVec d4 K (nd 0) + hVec d4 K (nd 3) =
            hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3) := by abel
        rw [e]
        exact t2_mem_span h
      exact ratMod_add_Z (hrat _ ht) hVec_add_mem_Z_03
    · have e : j = nd 2 := Fin.ext hj
      subst e
      rw [hsingle]
      exact hrat _ (h2_mem_span h)
    · have e : j = nd 3 := Fin.ext hj
      subst e
      rw [hsingle, hVec_split (nd 3) (nd 0) (nd 1) vec_add_self, smul_add,
        adjointGroup_fix_Z g hVec_add_mem_Z_01]
      have ht : hVec d4 K (nd 3) + hVec d4 K (nd 0) + hVec d4 K (nd 1) ∈
          Submodule.span k (longOrbit R) := by
        have e : hVec d4 K (nd 3) + hVec d4 K (nd 0) + hVec d4 K (nd 1) =
            hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3) := by abel
        rw [e]
        exact t2_mem_span h
      exact ratMod_add_Z (hrat _ ht) hVec_add_mem_Z_01
  · obtain ⟨p, hp, hpβ⟩ := exists_pos_of_isRoot hβ
    have e : (Finsupp.single (Sum.inr ⟨β, hβ⟩) (1 : K) : RootModule d4 K) = rv p := by
      rw [rv, hpβ, rootVec_eq_single K hβ]
    rw [e]
    exact hrat _ (rv_mem_span h hp)

omit [CharP K 2] in
theorem mapRange_sub_mem_Z (δ : K →+* K) (hk : ∀ c ∈ k, δ c = c) {y : RootModule d4 K}
    (hy : RatMod k y) : Finsupp.mapRange δ δ.map_zero y - y ∈ Zsub K := by
  refine ⟨fun γ => ?_, ?_, ?_⟩
  · by_cases hγ : IsRoot d4 γ
    · have h1 := hy.1 γ
      rw [coordAt_eq hγ] at h1 ⊢
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
      rw [hk _ h1, sub_self]
    · simp [coordAt, hγ]
  · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    rw [hk _ hy.2.1, sub_self]
  · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    have h1 := hy.2.2
    have e := hk _ h1
    rw [map_add, map_add] at e
    linear_combination e

end Rat

end CFSG.RankThree.PartOne.SEITZ8
