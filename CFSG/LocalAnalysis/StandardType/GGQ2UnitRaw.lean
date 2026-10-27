module

public import CFSG.Assembly.GL83LieDefs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

public section

namespace CFSG.StandardType.GGQ2Frame.UnitRaw

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

abbrev F : Type := ZMod 3

abbrev W (N : ℕ) : Type := Fin N → F

@[expose] def oneLine (N : ℕ) : Submodule F (W N) :=
  Submodule.span F {fun _ => (1 : F)}

theorem mem_oneLine {N : ℕ} (w : W N) : w ∈ oneLine N ↔ ∃ c : F, w = fun _ => c := by
  rw [oneLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ext i; simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ext i; simp⟩

abbrev Vfull (N : ℕ) : Type := W N ⧸ oneLine N

@[expose] def sumFun (N : ℕ) : W N →ₗ[F] F :=
  ∑ i : Fin N, LinearMap.proj (R := F) (φ := fun _ : Fin N => F) i

theorem sumFun_apply {N : ℕ} (w : W N) : sumFun N w = ∑ i, w i := by
  simp [sumFun]

@[expose] def heart (N : ℕ) : Submodule F (Vfull N) :=
  (LinearMap.ker (sumFun N)).map (oneLine N).mkQ

@[expose] def diffFun (N : ℕ) (i j : Fin N) : Vfull N →ₗ[F] F :=
  (oneLine N).liftQ
    (LinearMap.proj (R := F) (φ := fun _ : Fin N => F) i -
      LinearMap.proj (R := F) (φ := fun _ : Fin N => F) j)
    (by
      rw [oneLine, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      simp)

theorem diffFun_mk {N : ℕ} (i j : Fin N) (w : W N) :
    diffFun N i j ((oneLine N).mkQ w) = w i - w j := by
  simp [diffFun]

@[expose] def occurs {N : ℕ} (U : Submodule F (Vfull N)) (S : Finset (Fin N)) : Prop :=
  S.Nonempty ∧ ∀ i ∈ S, ∀ j : Fin N, j ∈ S ↔ ∀ u ∈ U, diffFun N i j u = 0

@[expose] def admissible {N : ℕ} (S : Finset (Fin N)) : Prop := 4 ≤ S.card

@[expose] def label {N : ℕ} (S : Finset (Fin N)) : LargeEvenLabel := ⟨.twA, S.card - 1, 1⟩

@[expose] def constOn {N : ℕ} (S : Finset (Fin N)) : Submodule F (W N) where
  carrier := {w | ∀ i ∈ S, ∀ j ∈ S, w i = w j}
  zero_mem' := by intro i _ j _; rfl
  add_mem' := by
    intro a b ha hb i hi j hj
    simp only [Pi.add_apply]
    rw [ha i hi j hj, hb i hi j hj]
  smul_mem' := by
    intro c a ha i hi j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha i hi j hj]

@[expose] def suppSumZero {N : ℕ} (S : Finset (Fin N)) : Submodule F (W N) where
  carrier := {w | (∀ i, i ∉ S → w i = 0) ∧ ∑ i, w i = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · simp [ha1 i hi, hb1 i hi]
    · simp [Finset.sum_add_distrib, ha2, hb2]
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · simp [ha1 i hi]
    · simp [← Finset.mul_sum, ha2]

@[expose] def cent {N : ℕ} (S : Finset (Fin N)) : Submodule F (Vfull N) :=
  (constOn S).map (oneLine N).mkQ

@[expose] def inside {N : ℕ} (S : Finset (Fin N)) : Submodule F (Vfull N) :=
  (suppSumZero S).map (oneLine N).mkQ

theorem mem_cent_iff {N : ℕ} (S : Finset (Fin N)) (v : Vfull N) :
    v ∈ cent S ↔ ∃ w : W N, (oneLine N).mkQ w = v ∧ ∀ i ∈ S, ∀ j ∈ S, w i = w j := by
  unfold cent
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨w, hw, rfl⟩

theorem mem_inside_iff {N : ℕ} (S : Finset (Fin N)) (v : Vfull N) :
    v ∈ inside S ↔
      ∃ w : W N, (oneLine N).mkQ w = v ∧ (∀ i, i ∉ S → w i = 0) ∧ ∑ i, w i = 0 := by
  unfold inside
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    exact ⟨w, rfl, h1, h2⟩
  · rintro ⟨w, rfl, h1, h2⟩
    exact ⟨w, ⟨h1, h2⟩, rfl⟩

@[expose] def occursH {N : ℕ} (U : Submodule F ↥(heart N)) (S : Finset (Fin N)) : Prop :=
  occurs (U.map (heart N).subtype) S

@[expose] def centH {N : ℕ} (S : Finset (Fin N)) : Submodule F ↥(heart N) :=
  (cent S).comap (heart N).subtype

@[expose] def insideH {N : ℕ} (S : Finset (Fin N)) : Submodule F ↥(heart N) :=
  (inside S).comap (heart N).subtype

theorem mem_centH_iff {N : ℕ} (S : Finset (Fin N)) (v : ↥(heart N)) :
    v ∈ centH S ↔ (v : Vfull N) ∈ cent S := Iff.rfl

theorem mem_insideH_iff {N : ℕ} (S : Finset (Fin N)) (v : ↥(heart N)) :
    v ∈ insideH S ↔ (v : Vfull N) ∈ inside S := Iff.rfl

end

end CFSG.StandardType.GGQ2Frame.UnitRaw
