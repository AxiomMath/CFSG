module

public import CFSG.RankThree.PartOne.KE6.EqpOpp
public import CFSG.RankThree.PartOne.KE6.Phi6A2
public import CFSG.RankThree.PartOne.KE6.Phi3A2
public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_unitary)
open CFSG.RankThree.Classical2 (chainRoot13_mem_parabolicRoots)
open Matrix
open scoped Matrix MatrixGroups Pointwise

section Alg

theorem eqp_halg (K : Type) [Field K] [Finite K] [CharP K 2] (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra K Ω] [IsAlgClosure K Ω] :
    letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω := by
  let := ZMod.algebra Ω 2
  let := ZMod.algebra K 2
  have : IsScalarTower (ZMod 2) K Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      have h := RingHom.ext_zmod (algebraMap (ZMod 2) Ω)
        ((algebraMap K Ω).comp (algebraMap (ZMod 2) K))
      exact congrArg (fun g => g x) h)
  have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.trans (ZMod 2) K Ω

end Alg

section Weyl24

variable {Ω : Type} [Field Ω]

@[expose] def eqpV : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word [3, 2, 1, 3, 0, 2])

theorem eqpV_image :
    (eqpV • ·) '' parabolicRoots Tag.E6 (e6QpSupport 12) = parabolicRoots Tag.E6 support13 := by
  have hsupp : ∀ i, i ∈ support13 ↔ (i = 0 ∨ i = 2) := fun i => by
    simp only [support13, Set.mem_insert_iff, Set.mem_singleton_iff]
    rfl
  have hJ : ∀ i, i ∈ e6QpSupport 12 ↔ (i = 1 ∨ i = 3) := fun i => by
    show i ∈ e6QpSupportList 12 ↔ _
    fin_cases i <;> decide
  refine image_smul_parabolicRoots_eq (P := fun i => i = 1 ∨ i = 3) (P' := fun i => i = 0 ∨ i = 2)
    hJ hsupp ?_ ?_
  · simp only [eqpV, wordProd_e6Word_smul]
    decide +kernel
  · simp only [eqpV, wordProd_e6Word_smul]
    decide +kernel

theorem e6Delta_eq_foldr (m : Fin 15) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) x = -((e6QpWord m).foldr (reflect Tag.E6) (permLattice e6Rho x)) := by
  rw [e6Delta, e6Longest_qp, wordProd_smul]

theorem eqpV_delta_chain {m : Fin 15} (hm : m = 12 ∨ m = 13) (i j : Fin 3) (hij : i ≠ j) :
    eqpV • e6Delta (e6QpSupport m) (eqpV⁻¹ • chainRoot chain13 i j) =
      chainRoot chain13 (Equiv.swap 0 2 j) (Equiv.swap 0 2 i) := by
  have hinv : eqpV⁻¹ = (coxeterSystem Tag.E6).wordProd (e6Word [3, 2, 1, 3, 0, 2]).reverse := by
    rw [eqpV, CoxeterSystem.wordProd_reverse]
  have key12 : ∀ i j : Fin 3, i ≠ j →
      (e6Word [3, 2, 1, 3, 0, 2]).foldr (reflect Tag.E6)
        (-((e6Word [1, 3, 1]).foldr (reflect Tag.E6) (permLattice e6Rho
          ((e6Word [3, 2, 1, 3, 0, 2]).reverse.foldr (reflect Tag.E6) (chainRoot chain13 i j))))) =
        chainRoot chain13 (Equiv.swap 0 2 j) (Equiv.swap 0 2 i) := by
    decide +kernel
  have key13 : ∀ i j : Fin 3, i ≠ j →
      (e6Word [3, 2, 1, 3, 0, 2]).foldr (reflect Tag.E6)
        (-((e6Word [0, 1, 3, 1, 5]).foldr (reflect Tag.E6) (permLattice e6Rho
          ((e6Word [3, 2, 1, 3, 0, 2]).reverse.foldr (reflect Tag.E6) (chainRoot chain13 i j))))) =
        chainRoot chain13 (Equiv.swap 0 2 j) (Equiv.swap 0 2 i) := by
    decide +kernel
  have hw12 : e6QpWord 12 = e6Word [1, 3, 1] := by decide
  have hw13 : e6QpWord 13 = e6Word [0, 1, 3, 1, 5] := by decide
  rw [e6Delta_eq_foldr, hinv]
  simp only [eqpV, wordProd_e6Word_smul]
  rw [wordProd_smul]
  rcases hm with rfl | rfl
  · rw [hw12]
    exact key12 i j hij
  · rw [hw13]
    exact key13 i j hij

end Weyl24

section Main

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

omit [IsAlgClosed Ω] in
theorem e6Psi_injective (J : Set (Fin Tag.E6.rank)) (f : ℕ) :
    Function.Injective (e6Psi Ω J f) := fun _ _ h =>
  entrywiseFrobGL_injective (τ := Tag.E6) (k := Ω) (p := 2) f ((MulAut.conj _).injective h)

theorem e6P24_finite_isQuasisimple {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {J : Set (Fin Tag.E6.rank)} (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) :
    Finite ↥(e6P24 Ω J f) ∧ CFSG.IsQuasisimple ↥(e6P24 Ω J f) := by
  classical
  have hℓ : (2 : ℕ).Prime := Nat.prime_two
  have : Fact (2 : ℕ).Prime := ⟨hℓ⟩
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (show 0 < 2 by norm_num) f)
    exact ⟨z, by rw [hFr, hz]⟩
  set n := canonicalRep (coxeterSystem Tag.E6) Ω eqpV with hn
  have hm := CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul (τ := Tag.E6) (K := Ω)
  have hrep : canonicalRep (coxeterSystem Tag.E6) Ω eqpV⁻¹ = n⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hm, mul_inv_cancel, canonicalRep_one]
  have hQ : (rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 e6Supp24)).map
      (MulAut.conj n).toMonoidHom = subsystemGroup Tag.E6 Ω support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 eqpV _ (fun α hα => hα.1)]
    rw [show (eqpV • ·) '' parabolicRoots Tag.E6 e6Supp24 = parabolicRoots Tag.E6 support13 from
      eqpV_image]
    exact (subsystemGroup_eq_rootSpan _).symm
  let θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
    (MulAut.conj n).toMonoidHom.comp ((e6Psi Ω J f).comp (MulAut.conj n⁻¹).toMonoidHom)
  have hinj : Function.Injective θ' := by
    intro x y h
    simp only [θ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h2 := e6Psi_injective J f (mul_left_cancel (mul_right_cancel h))
    have h4 := mul_right_cancel h2
    exact mul_left_cancel h4
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (Equiv.swap 0 2 j) (Equiv.swap 0 2 i)) (e * Fr c) := by
    intro i j hij
    refine ⟨1, one_mul 1, fun c => ?_⟩
    have hβ : IsRoot Tag.E6 (chainRoot chain13 i j) := (chainRoot13_mem_parabolicRoots hij).1
    have hβ' : IsRoot Tag.E6 (eqpV⁻¹ • chainRoot chain13 i j) := IsRoot.smul hβ _
    have h1 := E6EvenFixedRootDatum.canonicalRep_conj_pinnedX eqpV⁻¹ hβ c
    rw [hrep, inv_inv] at h1
    have h2 : n * e6Psi Ω J f (n⁻¹ * pinnedX Tag.E6 Ω (chainRoot chain13 i j) c * n) * n⁻¹ =
        pinnedX Tag.E6 Ω (eqpV • e6Delta J (eqpV⁻¹ • chainRoot chain13 i j)) (c ^ 2 ^ f) := by
      rw [h1, e6Psi_pinnedX J f hβ']
      exact E6EvenFixedRootDatum.canonicalRep_conj_pinnedX eqpV
        (isRoot_e6Delta J hβ') _
    change n * e6Psi Ω J f (n⁻¹ * pinnedX Tag.E6 Ω (chainRoot chain13 i j) c * n⁻¹⁻¹) * n⁻¹ = _
    rw [inv_inv, h2, one_mul, hFr]
    congr 2
    rcases hJ with rfl | rfl
    · exact eqpV_delta_chain (Or.inl rfl) i j hij
    · exact eqpV_delta_chain (Or.inr rfl) i j hij
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs θ' hinj
    (Equiv.swap 0 2) hθ
  have h2f : 2 < 2 ^ f := by
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨-, ⟨H', hH'⟩, -, hfin, hq⟩ := sl3_root_permuting_frobenius_fixed_unitary hℓ
    (by omega) hK (Equiv.swap 0 2) Φ b (fun i j hij t => by rw [hΦt, hFr])
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup_gen (S := parabolicRoots Tag.E6 e6Supp24)
    (w := eqpV) (e6Psi Ω J f) θ' (fun y => by
      simp only [θ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hn]
      group) hQ hmaps Φ hΦ₀
  exact ⟨Finite.of_equiv _ e.symm.toEquiv,
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm (hq h2f).1⟩

end Main

end CFSG.RankThree.PartOne.KE6
