module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ShultStronglyClosedTI

open Matrix CFSG.Open

section Linear

variable {G : Type*} [Group G]

@[expose] def ExplicitLinearModel (G : Type*) [Group G] : Prop :=
  ∃ (f : ℕ) (_ : 2 ≤ f) (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ f ∧ Nonempty (G ≃* GLAProj (GLASLGroup (Fin 2) K))

theorem explicitLinearModel_iff :
    ExplicitLinearModel G ↔
      ∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
  constructor
  · rintro ⟨f, hf, K, hfield, hfinite, hcard, ⟨e⟩⟩
    let := hfield
    let := hfinite
    exact ⟨f, hf, ⟨e.trans (glaSL2EquivNative f hf hcard)⟩⟩
  · rintro ⟨f, hf, ⟨e⟩⟩
    refine ⟨f, hf, GaloisField 2 f, inferInstance, inferInstance,
      GaloisField.card 2 f (by omega), ?_⟩
    exact ⟨e.trans glaSLQuotientEquivPSL.symm⟩

end Linear

section Unitary

noncomputable def glaSUCanonicalEquivNative (f : ℕ) :
    GLAProj (GLASUGroup (Fin 3) (GaloisField 2 (2 * f)) (2 ^ f)) ≃* PSU3 2 f := by
  have hnative : (unitaryAntidiagonalGroup (K := GaloisField 2 (2 * f)) f).map
      ProjGenLinGroup.mk = PSU3 2 f := by
    rfl
  exact (glaSUGramEquiv f).trans (MulEquiv.subgroupCongr hnative)

noncomputable def glaSU3EquivNative {K : Type} [Field K] [Finite K]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ (2 * f)) :
    GLAProj (GLASUGroup (Fin 3) K (2 ^ f)) ≃* PSU3 2 f :=
  (glaSUFieldEquiv (binaryFieldEquiv (2 * f) (by omega) hcard) (2 ^ f)).trans
    (glaSUCanonicalEquivNative f)

@[expose] def ExplicitUnitaryModel (G : Type*) [Group G] : Prop :=
  ∃ (f : ℕ) (_ : 2 ≤ f) (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ (2 * f) ∧
      Nonempty (G ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ f)))

theorem explicitUnitaryModel_iff {G : Type*} [Group G] :
    ExplicitUnitaryModel G ↔ ∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSU3 2 f) := by
  constructor
  · rintro ⟨f, hf, K, hfield, hfinite, hcard, ⟨e⟩⟩
    let := hfield
    let := hfinite
    exact ⟨f, hf, ⟨e.trans (glaSU3EquivNative f hf hcard)⟩⟩
  · rintro ⟨f, hf, ⟨e⟩⟩
    refine ⟨f, hf, GaloisField 2 (2 * f), inferInstance, inferInstance,
      GaloisField.card 2 (2 * f) (by omega), ?_⟩
    exact ⟨e.trans (glaSUCanonicalEquivNative f).symm⟩

end Unitary

section Suzuki

open scoped Pointwise

local notation "F" a => GaloisField 2 (2 * a + 1)

theorem transpose_glaSzGens_iff (a : ℕ) (M : Matrix (Fin 4) (Fin 4) (F a)) :
    M.transpose ∈ SzGenerators a ↔ M ∈ GLASzGens a (F a) := by
  constructor
  · rintro (⟨u, v, h⟩ | ⟨l, h⟩ | h)
    · left
      refine ⟨u, v, ?_⟩
      ext i j
      have hij := congrArg (fun A => A j i) h
      fin_cases i <;> fin_cases j <;> simpa [Nat.add_comm] using hij
    · right
      left
      refine ⟨l, ?_⟩
      ext i j
      have hij := congrArg (fun A => A j i) h
      fin_cases i <;> fin_cases j <;>
        simpa [Matrix.diagonal_apply, inv_pow] using hij
    · right
      right
      ext i j
      have hij := congrArg (fun A => A j i) h
      fin_cases i <;> fin_cases j <;> simpa using hij
  · rintro (⟨u, v, rfl⟩ | ⟨l, rfl⟩ | rfl)
    · left
      refine ⟨u, v, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Nat.add_comm]
    · right
      left
      refine ⟨l, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [inv_pow]
    · right
      right
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem map_inverseTranspose_glaSzGroup (a : ℕ) :
    (GLASzGroup a (F a)).map GeneralLinearGroup.inverseTranspose.toMonoidHom = Sz a := by
  let e : GL (Fin 4) (F a) ≃* GL (Fin 4) (F a) := GeneralLinearGroup.inverseTranspose
  let S : Set (GL (Fin 4) (F a)) := {A | (A : Matrix (Fin 4) (Fin 4) (F a)) ∈ GLASzGens a (F a)}
  let T : Set (GL (Fin 4) (F a)) := {A | (A : Matrix (Fin 4) (Fin 4) (F a)) ∈ SzGenerators a}
  have hsets : e '' S⁻¹ = T := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [Set.mem_inv] at hA
      change ((e A : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) ∈ SzGenerators a
      dsimp only [e]
      rw [GeneralLinearGroup.coe_inverseTranspose]
      exact (transpose_glaSzGens_iff a _).mpr hA
    · intro hB
      change (B : Matrix (Fin 4) (Fin 4) (F a)) ∈ SzGenerators a at hB
      refine ⟨e.symm B, ?_, e.apply_symm_apply B⟩
      rw [Set.mem_inv]
      apply (transpose_glaSzGens_iff a _).mp
      rw [← GeneralLinearGroup.coe_inverseTranspose]
      change (e (e.symm B) : Matrix (Fin 4) (Fin 4) (F a)) ∈ SzGenerators a
      simpa only [e.apply_symm_apply] using hB
  change (Subgroup.closure S).map e.toMonoidHom = Subgroup.closure T
  rw [← Subgroup.closure_inv S, MonoidHom.map_closure]
  exact congrArg Subgroup.closure hsets

noncomputable def glaSzCanonicalEquivNative (a : ℕ) : GLASzGroup a (F a) ≃* Sz a :=
  (GeneralLinearGroup.inverseTranspose.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_inverseTranspose_glaSzGroup a))

noncomputable def glaSzEquivNative {K : Type} [Field K] [Finite K]
    (a : ℕ) (ha : 1 ≤ a) (hcard : Nat.card K = 2 ^ (2 * a + 1)) :
    GLASzGroup a K ≃* Sz a :=
  (glaSzFieldEquiv (binaryFieldEquiv (2 * a + 1) (by omega) hcard) a).trans
    (glaSzCanonicalEquivNative a)

@[expose] def ExplicitSuzukiModel (G : Type*) [Group G] : Prop :=
  ∃ (a : ℕ) (_ : 1 ≤ a) (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (G ≃* GLASzGroup a K)

theorem explicitSuzukiModel_iff {G : Type*} [Group G] :
    ExplicitSuzukiModel G ↔ ∃ a : ℕ, 1 ≤ a ∧ Nonempty (G ≃* Sz a) := by
  constructor
  · rintro ⟨a, ha, K, hfield, hfinite, hcard, ⟨e⟩⟩
    let := hfield
    let := hfinite
    exact ⟨a, ha, ⟨e.trans (glaSzEquivNative a ha hcard)⟩⟩
  · rintro ⟨a, ha, ⟨e⟩⟩
    refine ⟨a, ha, F a, inferInstance, inferInstance,
      GaloisField.card 2 (2 * a + 1) (by omega), ?_⟩
    exact ⟨e.trans (glaSzCanonicalEquivNative a).symm⟩

end Suzuki

@[expose] def ExplicitRankOneModel (G : Type*) [Group G] : Prop :=
  ExplicitLinearModel G ∨ ExplicitUnitaryModel G ∨ ExplicitSuzukiModel G

theorem explicitRankOneModel_iff_fusionIsBenderGroup (G : Type*) [Group G] :
    ExplicitRankOneModel G ↔ fusionIsBenderGroup G := by
  unfold ExplicitRankOneModel fusionIsBenderGroup
  rw [explicitLinearModel_iff, explicitUnitaryModel_iff, explicitSuzukiModel_iff]

end CFSG.ShultStronglyClosedTI
