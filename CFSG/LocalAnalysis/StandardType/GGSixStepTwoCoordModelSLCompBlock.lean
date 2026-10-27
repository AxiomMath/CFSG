module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBasic
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

namespace CoordSL

section Proj

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {s r p : ℕ}

theorem frame_ext {M : Type*} [AddCommGroup M] [Module K M]
    {f f' : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] M}
    (h1 : ∀ j x, f (Pi.single j x, 0) = f' (Pi.single j x, 0)) (h2 : ∀ w, f (0, w) = f' (0, w)) :
    f = f' := by
  refine LinearMap.prod_ext (LinearMap.pi_ext' fun j => LinearMap.ext fun x => ?_)
    (LinearMap.ext h2)
  exact h1 j x

@[expose] noncomputable def projN (β : Fin s → ZMod p) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) where
  toFun x := (fun i => if β i = 0 then 0 else x.1 i, 0)
  map_add' x y := Prod.ext (funext fun i => by
    simp only [Prod.fst_add, Pi.add_apply]; split_ifs <;> simp) (by simp)
  map_smul' c x := Prod.ext (funext fun i => by
    simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp) (by simp)

theorem projN_apply (β : Fin s → ZMod p) (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    projN β x = (fun i => if β i = 0 then 0 else x.1 i, 0) :=
  rfl

@[expose] noncomputable def projC (β : Fin s → ZMod p) (c : ZMod p) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) where
  toFun x := (fun i => if β i = c then x.1 i else 0, 0)
  map_add' x y := Prod.ext (funext fun i => by
    simp only [Prod.fst_add, Pi.add_apply]; split_ifs <;> simp) (by simp)
  map_smul' c' x := Prod.ext (funext fun i => by
    simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp) (by simp)

theorem projC_apply (β : Fin s → ZMod p) (c : ZMod p) (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    projC β c x = (fun i => if β i = c then x.1 i else 0, 0) :=
  rfl

theorem projN_eq_zero_iff {β : Fin s → ZMod p} {x : (Fin s → AdjoinRoot g) × (Fin r → K)} :
    projN β x = 0 ↔ ∀ i, β i ≠ 0 → x.1 i = 0 := by
  constructor
  · intro h i hi
    have h1 := congrFun (congrArg Prod.fst h) i
    simpa [projN_apply, hi] using h1
  · intro h
    refine Prod.ext (funext fun i => ?_) rfl
    by_cases hi : β i = 0
    · simp [projN_apply, hi]
    · simp [projN_apply, hi, h i hi]

theorem projN_eq_self_iff {β : Fin s → ZMod p} {x : (Fin s → AdjoinRoot g) × (Fin r → K)} :
    projN β x = x ↔ (∀ i, β i = 0 → x.1 i = 0) ∧ x.2 = 0 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 := congrFun (congrArg Prod.fst h) i
      simp only [projN_apply, hi, ↓reduceIte] at h1
      exact h1.symm
    · exact (congrArg Prod.snd h).symm
  · rintro ⟨h1, h2⟩
    refine Prod.ext (funext fun i => ?_) h2.symm
    by_cases hi : β i = 0
    · simp [projN_apply, hi, h1 i hi]
    · simp [projN_apply, hi]

theorem projC_eq_zero_iff {β : Fin s → ZMod p} {c : ZMod p}
    {x : (Fin s → AdjoinRoot g) × (Fin r → K)} :
    projC β c x = 0 ↔ ∀ i, β i = c → x.1 i = 0 := by
  constructor
  · intro h i hi
    have h1 := congrFun (congrArg Prod.fst h) i
    simpa [projC_apply, hi] using h1
  · intro h
    refine Prod.ext (funext fun i => ?_) rfl
    by_cases hi : β i = c
    · simp [projC_apply, hi, h i hi]
    · simp [projC_apply, hi]

theorem projC_eq_self_iff {β : Fin s → ZMod p} {c : ZMod p}
    {x : (Fin s → AdjoinRoot g) × (Fin r → K)} :
    projC β c x = x ↔ (∀ i, β i ≠ c → x.1 i = 0) ∧ x.2 = 0 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 := congrFun (congrArg Prod.fst h) i
      simp only [projC_apply, hi, ↓reduceIte] at h1
      exact h1.symm
    · exact (congrArg Prod.snd h).symm
  · rintro ⟨h1, h2⟩
    refine Prod.ext (funext fun i => ?_) h2.symm
    by_cases hi : β i = c
    · simp [projC_apply, hi]
    · simp [projC_apply, hi, h1 i hi]

variable [Finite K] [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1}
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {β : Fin s → ZMod p}
include hprim

theorem apply_single_eq_zero_of_ne (hal : Aligned hζ β)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x))
    {j : Fin s} (hj : β j ≠ 0) (x : AdjoinRoot g) {i : Fin s} (hi : β i ≠ β j) :
    (φ (Pi.single j x, 0)).1 i = 0 := by
  rw [apply_single_of_comm hprim hal hφ hj x]
  simp [hi]

omit [Finite K] in
theorem apply_fixed_of_comm
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x))
    {x : (Fin s → AdjoinRoot g) × (Fin r → K)} (hx : ∀ i, β i ≠ 0 → x.1 i = 0) {i : Fin s}
    (hi : β i ≠ 0) : (φ x).1 i = 0 := by
  have hfix : torusAct g (fun i => (β i).val) x = x := (torusAct_eq_self_iff hprim).mpr hx
  have h1 : torusAct g (fun i => (β i).val) (φ x) = φ x := by rw [← hφ, hfix]
  exact (torusAct_eq_self_iff hprim).mp h1 i hi

theorem projN_comp_comm (hal : Aligned hζ β)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x)) :
    projN β ∘ₗ φ = φ ∘ₗ projN β := by
  refine frame_ext (fun j x => ?_) (fun w => ?_)
  · simp only [LinearMap.comp_apply]
    by_cases hj : β j = 0
    · have h0 : projN β ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) = 0 :=
        projN_eq_zero_iff.mpr fun i hi => by
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          simp [hij]
      rw [h0, map_zero]
      exact projN_eq_zero_iff.mpr fun i hi => apply_fixed_of_comm hprim hφ (fun k hk => by
        have hkj : k ≠ j := fun h => hk (h ▸ hj)
        simp [hkj]) hi
    · have h0 : projN β ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
          ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) :=
        projN_eq_self_iff.mpr ⟨fun i hi => by
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          simp [hij], rfl⟩
      rw [h0]
      refine projN_eq_self_iff.mpr ⟨fun i hi => ?_, ?_⟩
      · exact apply_single_eq_zero_of_ne hprim hal hφ hj x (fun h => hj (h ▸ hi))
      · rw [apply_single_of_comm hprim hal hφ hj x]
  · simp only [LinearMap.comp_apply]
    have h0 : projN β ((0 : Fin s → AdjoinRoot g), w) = 0 :=
      projN_eq_zero_iff.mpr fun i _ => rfl
    rw [h0, map_zero]
    exact projN_eq_zero_iff.mpr fun i hi => apply_fixed_of_comm hprim hφ (fun k _ => rfl) hi


theorem projC_comp_comm (hal : Aligned hζ β) {c : ZMod p} (hc : c ≠ 0)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x)) :
    projC β c ∘ₗ φ = φ ∘ₗ projC β c := by
  refine frame_ext (fun j x => ?_) (fun w => ?_)
  · simp only [LinearMap.comp_apply]
    by_cases hj : β j = c
    · have h0 : projC β c ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
          ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) :=
        projC_eq_self_iff.mpr ⟨fun i hi => by
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          simp [hij], rfl⟩
      rw [h0]
      have hj0 : β j ≠ 0 := hj ▸ hc
      refine projC_eq_self_iff.mpr ⟨fun i hi => ?_, ?_⟩
      · exact apply_single_eq_zero_of_ne hprim hal hφ hj0 x (fun h => hi (h.trans hj))
      · rw [apply_single_of_comm hprim hal hφ hj0 x]
    · have h0 : projC β c ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) = 0 :=
        projC_eq_zero_iff.mpr fun i hi => by
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          simp [hij]
      rw [h0, map_zero]
      refine projC_eq_zero_iff.mpr fun i hi => ?_
      by_cases hj0 : β j = 0
      · exact apply_fixed_of_comm hprim hφ (fun k hk => by
          have hkj : k ≠ j := fun h => hk (h ▸ hj0)
          simp [hkj]) (hi ▸ hc)
      · exact apply_single_eq_zero_of_ne hprim hal hφ hj0 x (fun h => hj (h ▸ hi))
  · simp only [LinearMap.comp_apply]
    have h0 : projC β c ((0 : Fin s → AdjoinRoot g), w) = 0 :=
      projC_eq_zero_iff.mpr fun i _ => rfl
    rw [h0, map_zero]
    exact projC_eq_zero_iff.mpr fun i hi =>
      apply_fixed_of_comm hprim hφ (fun k _ => rfl) (hi ▸ hc)

end Proj

section ClassBlock

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {s r p : ℕ}

theorem mulVec_single_apply' {R : Type*} [CommRing R] (M : Matrix (Fin s) (Fin s) R) (j i : Fin s)
    (x : R) : (M *ᵥ Pi.single j x) i = M i j * x := by
  simp [Matrix.mulVec_single, Matrix.col_apply, mul_comm]

theorem mulVec_eq_self_of_cols {R : Type*} [CommRing R] {β : Fin s → ZMod p} {c : ZMod p}
    {M : Matrix (Fin s) (Fin s) R}
    (hM : ∀ i k, β k ≠ c → M i k = (1 : Matrix (Fin s) (Fin s) R) i k)
    {y : Fin s → R} (hy : ∀ k, β k = c → y k = 0) : M *ᵥ y = y := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : β i = c
    · rw [hy i hi, mul_zero]
    · rw [hM i i hi, Matrix.one_apply_eq, one_mul]
  · intro k _ hki
    by_cases hk : β k = c
    · rw [hy k hk, mul_zero]
    · rw [hM i k hk, Matrix.one_apply_ne (Ne.symm hki), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem mulVec_apply_eq_zero_of_rows {R : Type*} [CommRing R] {β : Fin s → ZMod p} {c : ZMod p}
    {M : Matrix (Fin s) (Fin s) R}
    (hM : ∀ i k, β i ≠ c → M i k = (1 : Matrix (Fin s) (Fin s) R) i k)
    {y : Fin s → R} (hy : ∀ k, β k ≠ c → y k = 0) {i : Fin s} (hi : β i ≠ c) :
    (M *ᵥ y) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hy i hi, mul_zero]
  · intro k _ hki
    rw [hM i k hi, Matrix.one_apply_ne (Ne.symm hki), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

@[expose] noncomputable def classMat (β : Fin s → ZMod p) (c : ZMod p)
    (φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))) :
    Matrix (Fin s) (Fin s) (AdjoinRoot g) :=
  fun i j => if β i = c ∧ β j = c then (φ (Pi.single j 1, 0)).1 i
    else (1 : Matrix (Fin s) (Fin s) (AdjoinRoot g)) i j

theorem classMat_rows {β : Fin s → ZMod p} {c : ZMod p}
    (φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)))
    (i k : Fin s) (hi : β i ≠ c) : classMat β c φ i k = (1 : Matrix _ _ (AdjoinRoot g)) i k := by
  simp [classMat, hi]

theorem classMat_cols {β : Fin s → ZMod p} {c : ZMod p}
    (φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)))
    (i k : Fin s) (hk : β k ≠ c) : classMat β c φ i k = (1 : Matrix _ _ (AdjoinRoot g)) i k := by
  simp [classMat, hk]

variable [Finite K] [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1}
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {β : Fin s → ZMod p}
include hprim

theorem apply_single_eq_classMat (hal : Aligned hζ β) {c : ZMod p} (hc : c ≠ 0)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x))
    {j : Fin s} (hj : β j = c) (x : AdjoinRoot g) :
    φ (Pi.single j x, 0) = (classMat β c φ *ᵥ Pi.single j x, 0) := by
  rw [apply_single_of_comm hprim hal hφ (hj ▸ hc) x]
  refine Prod.ext (funext fun i => ?_) rfl
  simp only
  rw [mulVec_single_apply']
  by_cases hi : β i = c
  · simp [classMat, hi, hj, mul_comm]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [classMat, hi, hj, Matrix.one_apply_ne hij]

theorem comp_projC_eq (hal : Aligned hζ β) {c : ZMod p} (hc : c ≠ 0)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x)) :
    φ ∘ₗ projC β c = blockAct g (classMat β c φ) ∘ₗ projC β c := by
  refine frame_ext (fun j x => ?_) (fun w => ?_)
  · simp only [LinearMap.comp_apply]
    by_cases hj : β j = c
    · have h0 : projC β c ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
          ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) :=
        projC_eq_self_iff.mpr ⟨fun i hi => by
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          simp [hij], rfl⟩
      rw [h0, apply_single_eq_classMat hprim hal hc hφ hj x, blockAct_apply]
    · have h0 : projC β c ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) = 0 :=
        projC_eq_zero_iff.mpr fun i hi => by
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          simp [hij]
      rw [h0, map_zero, map_zero]
  · simp only [LinearMap.comp_apply]
    have h0 : projC β c ((0 : Fin s → AdjoinRoot g), w) = 0 :=
      projC_eq_zero_iff.mpr fun i _ => rfl
    rw [h0, map_zero, map_zero]


theorem comp_blockAct_comp (hal : Aligned hζ β) {c : ZMod p} (hc : c ≠ 0)
    {φ φ' : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x))
    (hφ' : ∀ x, φ' (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ' x))
    (hφφ' : ∀ x, φ (φ' x) = x) {M : Matrix (Fin s) (Fin s) (AdjoinRoot g)}
    (hMr : ∀ i k, β i ≠ c → M i k = (1 : Matrix _ _ (AdjoinRoot g)) i k)
    (hMc : ∀ i k, β k ≠ c → M i k = (1 : Matrix _ _ (AdjoinRoot g)) i k) :
    φ ∘ₗ blockAct g M ∘ₗ φ' = blockAct g (classMat β c φ * M * classMat β c φ') := by
  refine frame_ext (fun j x => ?_) (fun w => ?_)
  · simp only [LinearMap.comp_apply]
    rw [blockAct_apply (g := g) (classMat β c φ * M * classMat β c φ'), ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    by_cases hj : β j = c
    · rw [apply_single_eq_classMat hprim hal hc hφ' hj x, blockAct_apply]
      set y := M *ᵥ (classMat β c φ' *ᵥ Pi.single j x) with hy
      have hyoff : ∀ i, β i ≠ c → y i = 0 := fun i hi =>
        mulVec_apply_eq_zero_of_rows hMr (fun k hk => mulVec_apply_eq_zero_of_rows
          (classMat_rows φ') (fun l hl => by
            have hlj : l ≠ j := fun h => hl (h ▸ hj)
            simp [hlj]) hk) hi
      have hP : projC β c (y, (0 : Fin r → K)) = (y, 0) :=
        projC_eq_self_iff.mpr ⟨hyoff, rfl⟩
      have h1 := congrArg (fun f => f (y, (0 : Fin r → K))) (comp_projC_eq hprim hal hc hφ)
      simp only [LinearMap.comp_apply, hP, blockAct_apply] at h1
      rw [h1]
    · set v := φ' ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) with hv
      have hvc : ∀ k, β k = c → v.1 k = 0 := by
        have h1 := congrArg (fun f => f ((Pi.single j x : Fin s → AdjoinRoot g),
          (0 : Fin r → K))) (projC_comp_comm hprim hal hc hφ')
        have h0 : projC β c ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) = 0 :=
          projC_eq_zero_iff.mpr fun i hi => by
            have hij : i ≠ j := fun h => hj (h ▸ hi)
            simp [hij]
        simp only [LinearMap.comp_apply, h0, map_zero] at h1
        exact projC_eq_zero_iff.mp h1
      have hsj : ∀ k, β k = c → (Pi.single j x : Fin s → AdjoinRoot g) k = 0 := fun k hk => by
        have hkj : k ≠ j := fun h => hj (h ▸ hk)
        simp [hkj]
      have hfix : blockAct g M v = v := by
        rw [blockAct_apply, mulVec_eq_self_of_cols hMc hvc]
      rw [hfix, hv, hφφ', mulVec_eq_self_of_cols (classMat_cols φ') hsj,
        mulVec_eq_self_of_cols hMc hsj, mulVec_eq_self_of_cols (classMat_cols φ) hsj]
  · simp only [LinearMap.comp_apply]
    set v := φ' ((0 : Fin s → AdjoinRoot g), w) with hv
    have hvc : ∀ k, β k = c → v.1 k = 0 := fun k hk =>
      apply_fixed_of_comm hprim hφ' (fun _ _ => rfl) (hk ▸ hc)
    have hfix : blockAct g M v = v := by
      rw [blockAct_apply, mulVec_eq_self_of_cols hMc hvc]
    rw [hfix, hv, hφφ', blockAct_apply, Matrix.mulVec_zero]

end ClassBlock

section Normal

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}
  [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1}
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {β : Fin s → ZMod p}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}

@[expose] def classSet (β : Fin s → ZMod p) (c : ZMod p) : Finset (Fin s) :=
  Finset.univ.filter fun i => β i = c

omit [Fact p.Prime] in
theorem mem_classSet {c : ZMod p} {i : Fin s} : i ∈ classSet β c ↔ β i = c := by
  simp [classSet]

omit [Finite K] [Fact p.Prime] in
theorem frameForm_comm_of_mem {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u) :
    (∀ x, frameForm g ε (u : Matrix (Fin n) (Fin n) K) (torusAct g (fun i => (β i).val) x) =
        torusAct g (fun i => (β i).val) (frameForm g ε (u : Matrix (Fin n) (Fin n) K) x)) ∧
      (∀ x, frameForm g ε ((u⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) (torusAct g (fun i => (β i).val) x) =
        torusAct g (fun i => (β i).val)
          (frameForm g ε ((u⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) x)) ∧
      ∀ x, frameForm g ε (u : Matrix (Fin n) (Fin n) K)
        (frameForm g ε ((u⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) x) = x := by
  have hu' : u⁻¹ * SLNS.nsSL ε hC (fun i => (β i).val) =
      SLNS.nsSL ε hC (fun i => (β i).val) * u⁻¹ :=
    (show Commute u (SLNS.nsSL ε hC (fun i => (β i).val)) from hu).inv_left.eq
  refine ⟨frameForm_torusAct_comm g ε (congrArg Subtype.val hu),
    frameForm_torusAct_comm g ε (congrArg Subtype.val hu'), fun x => ?_⟩
  have h1 := congrArg (fun v : Matrix.SpecialLinearGroup (Fin n) K =>
    frameForm g ε (v : Matrix (Fin n) (Fin n) K) x) (mul_inv_cancel u)
  simp only [Matrix.SpecialLinearGroup.coe_mul, frameForm_mul, LinearMap.comp_apply,
    Matrix.SpecialLinearGroup.coe_one, frameForm_one, LinearMap.id_apply] at h1
  exact h1

include hprim in
theorem conj_mem_classBlock (hal : Aligned hζ β) {c : ZMod p} (hc : c ≠ 0)
    {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u)
    {M : Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g)}
    (hM : M ∈ coordBlockSL (AdjoinRoot g) (classSet β c)) :
    u * theta g ε M * u⁻¹ ∈ (coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε) := by
  obtain ⟨hφ, hφ', hφφ'⟩ := frameForm_comm_of_mem (hC := hC) hu
  set φ := frameForm g ε (u : Matrix (Fin n) (Fin n) K) with hφdef
  set φ' := frameForm g ε ((u⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hφ'def
  have hM' := mem_coordBlockSL_iff.mp hM
  have hMr : ∀ i k, β i ≠ c → (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) i k =
      (1 : Matrix (Fin s) (Fin s) (AdjoinRoot g)) i k := fun i k hi => by
    rw [hM' i k (Or.inl (by rwa [mem_classSet])), Matrix.one_apply]
  have hMc : ∀ i k, β k ≠ c → (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) i k =
      (1 : Matrix (Fin s) (Fin s) (AdjoinRoot g)) i k := fun i k hk => by
    rw [hM' i k (Or.inr (by rwa [mem_classSet])), Matrix.one_apply]
  set Λ := classMat β c φ with hΛ
  set Λ' := classMat β c φ' with hΛ'
  have hΛΛ' : Λ * Λ' = 1 := by
    have h1 := comp_blockAct_comp hprim hal hc hφ hφ' hφφ' (M := 1)
      (fun i k _ => rfl) (fun i k _ => rfl)
    rw [Matrix.mul_one] at h1
    ext i j
    have h2 := congrArg (fun f => (f ((Pi.single j 1 : Fin s → AdjoinRoot g),
      (0 : Fin r → K))).1 i) h1
    simp only [LinearMap.comp_apply, blockAct_apply, Matrix.one_mulVec, hφφ'] at h2
    rw [mulVec_single_apply', mul_one] at h2
    rw [← h2, Matrix.one_apply, Pi.single_apply]
  set N := Λ * (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) * Λ' with hN
  have hdet : N.det = 1 := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, M.2, mul_one, ← Matrix.det_mul, hΛΛ', Matrix.det_one]
  have hNcol : ∀ j, β j ≠ c → N *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j hj
    have hsj : ∀ k, β k = c → (Pi.single j (1 : AdjoinRoot g) : Fin s → AdjoinRoot g) k = 0 :=
      fun k hk => by
        have hkj : k ≠ j := fun h => hj (h ▸ hk)
        simp [hkj]
    rw [hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      mulVec_eq_self_of_cols (classMat_cols φ') hsj, mulVec_eq_self_of_cols hMc hsj,
      mulVec_eq_self_of_cols (classMat_cols φ) hsj]
  set N' : Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g) := ⟨N, hdet⟩ with hN'
  have hNmem : N' ∈ coordBlockSL (AdjoinRoot g) (classSet β c) := by
    rw [mem_coordBlockSL_iff]
    intro i j hij
    change N i j = _
    have hcol : N i j = (N *ᵥ Pi.single j 1) i := by rw [mulVec_single_apply', mul_one]
    by_cases hj : β j = c
    · have hi : β i ≠ c := by
        rcases hij with h | h
        · rwa [mem_classSet] at h
        · exact absurd (mem_classSet.mpr hj) h
      have hij' : i ≠ j := fun h => hi (h ▸ hj)
      rw [hcol, hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [hij', ↓reduceIte]
      exact mulVec_apply_eq_zero_of_rows (classMat_rows φ) (fun k hk =>
        mulVec_apply_eq_zero_of_rows hMr (fun l hl => mulVec_apply_eq_zero_of_rows
          (classMat_rows φ') (fun m hm => by
            have hmj : m ≠ j := fun h => hm (h ▸ hj)
            simp [hmj]) hl) hk) hi
    · rw [hcol, hNcol j hj, Pi.single_apply]
  refine ⟨N', hNmem, ?_⟩
  apply Subtype.ext
  apply frameForm_injective g ε
  rw [coe_theta, frameForm_thetaMat, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, frameForm_mul, frameForm_mul, coe_theta,
    frameForm_thetaMat, ← hφdef, ← hφ'def]
  exact (comp_blockAct_comp hprim hal hc hφ hφ' hφφ' hMr hMc).symm

end Normal

section Zero

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}

@[expose] def zeroCoords (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (β : Fin s → ZMod p) : Finset (Fin n) :=
  Finset.univ.filter fun x => Sum.elim (fun ai => decide (β ai.2 = 0)) (fun _ => true) (ε x) = true

theorem mem_zeroCoords_inl {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {β : Fin s → ZMod p}
    {x : Fin n} {a : Fin (rootPB g).dim} {i : Fin s} (hx : ε x = Sum.inl (a, i)) :
    x ∈ zeroCoords ε β ↔ β i = 0 := by
  simp [zeroCoords, hx]

theorem mem_zeroCoords_inr {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {β : Fin s → ZMod p}
    {x : Fin n} {j : Fin r} (hx : ε x = Sum.inr j) : x ∈ zeroCoords ε β := by
  simp [zeroCoords, hx]

theorem frameCoords_apply (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) (y : Fin n) :
    frameCoords g ε x y =
      Sum.elim (fun ai => (rootPB g).basis.repr (x.1 ai.2) ai.1) (fun j => x.2 j) (ε y) :=
  rfl

theorem frameForm_compIndicator (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (β : Fin s → ZMod p) :
    frameForm g ε (compIndicator K (zeroCoords ε β)) = projN (r := r) β := by
  refine LinearMap.ext fun x => ?_
  rw [frameForm_apply]
  apply (frameCoords g ε).injective
  rw [LinearEquiv.apply_symm_apply]
  funext y
  rw [compIndicator, Matrix.mulVec_diagonal, frameCoords_apply, frameCoords_apply]
  rcases hy : ε y with ⟨a, i⟩ | j
  · have hmem := mem_zeroCoords_inl (β := β) hy
    by_cases hi : β i = 0
    · have h1 : y ∈ zeroCoords ε β := hmem.mpr hi
      simp [h1, hi, projN_apply]
    · have h1 : y ∉ zeroCoords ε β := fun h => hi (hmem.mp h)
      simp [h1, hi, projN_apply]
  · simp [mem_zeroCoords_inr (β := β) hy, projN_apply]

theorem frameCoords_single_basis (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (a : Fin (rootPB g).dim) (i : Fin s) :
    frameCoords g ε ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
      Pi.single (ε.symm (Sum.inl (a, i))) 1 := by
  funext y
  rw [frameCoords_apply]
  have h1 : y = ε.symm (Sum.inl (a, i)) ↔ ε y = Sum.inl (a, i) := Equiv.eq_symm_apply ε
  rcases hy : ε y with ⟨a', i'⟩ | j
  · rw [hy, Sum.inl.injEq] at h1
    simp only [Sum.elim_inl, Pi.single_apply (i := ε.symm (Sum.inl (a, i))), h1]
    by_cases hi : i' = i
    · subst hi
      rw [Pi.single_eq_same, Basis.repr_self, Finsupp.single_apply]
      by_cases ha : a' = a
      · subst ha
        simp
      · have hne : ¬ (a', i') = (a, i') := fun h => ha (Prod.mk.inj h).1
        simp [hne, Ne.symm ha]
    · have hne : ¬ (a', i') = (a, i) := fun h => hi (Prod.mk.inj h).2
      rw [Pi.single_eq_of_ne hi, map_zero, Finsupp.zero_apply]
      simp [hne]
  · rw [hy] at h1
    simp only [Sum.elim_inr, Pi.single_apply (i := ε.symm (Sum.inl (a, i))), h1]
    simp

variable [Finite K] [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1}
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {β : Fin s → ZMod p}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
include hprim

theorem compIndicator_comm_of_mem (hal : Aligned hζ β) {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u) :
    compIndicator K (zeroCoords ε β) * (u : Matrix (Fin n) (Fin n) K) =
      (u : Matrix (Fin n) (Fin n) K) * compIndicator K (zeroCoords ε β) := by
  obtain ⟨hφ, -, -⟩ := frameForm_comm_of_mem (hC := hC) hu
  apply frameForm_injective g ε
  rw [frameForm_mul, frameForm_mul, frameForm_compIndicator]
  exact projN_comp_comm hprim hal hφ

theorem conj_mem_zeroBlock (hal : Aligned hζ β) {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u)
    {M : Matrix.SpecialLinearGroup (Fin n) K} (hM : M ∈ coordBlockSL K (zeroCoords ε β)) :
    u * M * u⁻¹ ∈ coordBlockSL K (zeroCoords ε β) :=
  conj_mem_coordBlockSL (compIndicator_comm_of_mem hprim hal hu) hM

end Zero

end CoordSL

end CFSG.StandardType
