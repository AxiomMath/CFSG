module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryTransport
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Models.BenderSuzuki
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.Goldschmidt CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.RootCenter

variable {X : Type} [Group X]

theorem bender_of_isPSU {n : ℕ} (hn : 2 ≤ n) (hX : IsPSU 3 2 n X) : fusionIsBenderGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) := e
  exact Or.inr (Or.inl ⟨n, hn,
    ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)⟩⟩)

theorem nonempty_equiv_psu3_of_isPSU {n : ℕ} (hn : 2 ≤ n) (hX : IsPSU 3 2 n X) :
    Nonempty (X ≃* CFSG.Open.PSU3 2 n) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) := e
  exact ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)⟩

theorem isSimpleGroup_of_isPSU {n : ℕ} (hX : IsPSU 3 2 n X) : IsSimpleGroup X :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 2 n hX).2

theorem center_eq_bot_of_isPSU [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSU 3 2 n X) : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup X := isSimpleGroup_of_isPSU hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
    obtain ⟨D, hD⟩ := G3a.exists_borelSetup (bender_of_isPSU hn hX) T
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
    have hnorm : (T : Subgroup X).Normal := ⟨fun x _ g => by
      rwa [hcomm g x, mul_inv_cancel_right]⟩
    have hu : Unique (Sylow 2 X) := Sylow.unique_of_normal T hnorm
    have h1 : Nat.card (Sylow 2 X) = 1 := Nat.card_unique
    have h2 := hD.card
    have h3 : 0 < Nat.card (T : Subgroup X) := Nat.card_pos
    omega

theorem conj_injective_of_isPSU [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSU 3 2 n X) : Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx' : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut X => φ g) (MonoidHom.mem_ker.mp hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = (x * g * x⁻¹) * x := by rw [this]
      _ = x * g := by group
  rw [center_eq_bot_of_isPSU hn hX] at hx'
  exact hx'

@[expose] def omegaU (R : Subgroup X) : Subgroup X :=
  (CFSG.omega₁ (G := ↥R) (p := 2)).map R.subtype

structure RootCenterData (n : ℕ) (R U : Subgroup X) : Prop where
  center_iff : ∀ x, x ∈ U ↔ x ∈ R ∧ ∀ y ∈ R, x * y = y * x
  injOn : Set.InjOn (MulAut.conj : X →* MulAut X) (R : Set X)
  exists_D : ∃ D : Subgroup (MulAut X), R.map MulAut.conj ⊓ D = ⊥ ∧
    R.map MulAut.conj ⊔ D = rootCenterAut R U ∧
    ((R.map MulAut.conj).subgroupOf (rootCenterAut R U)).Normal ∧ Nat.card D = 2 * (2 ^ n + 1)
  fix_eq : ∀ γ ∈ rootCenterAut R U, (∀ x ∈ R, γ x = x) → ∃ z ∈ U, γ = MulAut.conj z

theorem rootCenterData_of_isPSU [Finite X] {n : ℕ} (hn : 2 ≤ n) (hX : IsPSU 3 2 n X)
    (R : Sylow 2 X) : RootCenterData n (R : Subgroup X) (omegaU (R : Subgroup X)) := by
  obtain ⟨e⟩ := nonempty_equiv_psu3_of_isPSU hn hX
  let k := GaloisField 2 n
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian n (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hKcard hfixed).some
  have hmodel : PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* CFSG.Open.PSU3 2 n :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  obtain ⟨-, hU, hinj, hD, -, hfix, -, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J n hn hKcard hfixed hJ e₃ R
      (omegaU (R : Subgroup X)) rfl
  refine ⟨hU, hinj, ?_, ?_⟩
  · obtain ⟨D, h1, h2, h3, h4, -⟩ := hD
    exact ⟨D, h1, h2, h3, h4⟩
  · intro γ hγ hfixR
    have hUR : omegaU (R : Subgroup X) ≤ (R : Subgroup X) := fun x hx => ((hU x).1 hx).1
    have h1 : γ ∈ {γ | γ ∈ rootCenterAut (R : Subgroup X) (omegaU (R : Subgroup X)) ∧
        ∀ x ∈ (R : Subgroup X), γ x = x} := ⟨hγ, hfixR⟩
    rw [hfix (R : Subgroup X) hUR le_rfl (by simp)] at h1
    obtain ⟨z, hz, rfl⟩ := h1
    exact ⟨z, hz, rfl⟩

end CFSG.Quasithin.U31521
