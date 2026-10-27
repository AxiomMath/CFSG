module

public import CFSG.RankThree.PartOne.KD4L.TauDatum
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Orbits


theorem gam_d4Support {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) : gam j ∈ d4Support := by
  obtain ⟨h0, h5⟩ : j ≠ 0 ∧ j ≠ 5 := hj
  change gam j ≠ 0 ∧ gam j ≠ 5
  revert h0 h5
  fin_cases j <;> decide

theorem d4Support_cases {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) :
    j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
  obtain ⟨h0, h5⟩ : j ≠ 0 ∧ j ≠ 5 := hj
  revert h0 h5
  fin_cases j <;> decide

theorem gam_gam (j : Fin Tag.E6.rank) : gam (gam j) = j := by
  fin_cases j <;> decide

theorem gam_one : gam (1 : Fin Tag.E6.rank) = 1 := by decide

theorem gam_two : gam (2 : Fin Tag.E6.rank) = 4 := by decide

theorem gam_three : gam (3 : Fin Tag.E6.rank) = 3 := by decide

theorem gam_four : gam (4 : Fin Tag.E6.rank) = 2 := by decide

theorem permLattice_gam_single (j : Fin Tag.E6.rank) :
    permLattice (τ := Tag.E6) gam (Pi.single j 1) = Pi.single (gam j) 1 :=
  permLattice_single (τ := Tag.E6) gam j

theorem theta_pow_single {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) (m : ℕ) :
    (d4Gen.θ ^ m) (toReal (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
      toReal (Pi.single (gam^[m] j) 1 : Fin Tag.E6.rank → ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hjm : gam^[m] j ∈ d4Support := by
      clear ih
      induction m with
      | zero => exact hj
      | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact gam_d4Support ihm
    have hK : (Pi.single (gam^[m] j) 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots d4Gen.χ := by
      rw [kernelRoots_d4Gen]
      exact single_mem_parabolicRoots hjm
    rw [pow_succ', Module.End.mul_apply, ih, d4Gen_theta_toReal hK, permLattice_gam_single,
      Function.iterate_succ_apply']

theorem thetaOrbit_single {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) :
    thetaOrbit d4Gen.θ (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      {Pi.single j 1, Pi.single (gam j) 1} := by
  have hg2 : gam^[2] = id := funext fun x => gam_gam x
  ext β
  simp only [thetaOrbit, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [theta_pow_single hj] at hm
    have hβ := toReal_injective hm.symm
    rcases Nat.even_or_odd m with he | ho
    · left
      rw [hβ]
      obtain ⟨n, rfl⟩ := he
      rw [← two_mul, Function.iterate_mul, hg2, Function.iterate_id]
      rfl
    · right
      rw [hβ]
      obtain ⟨n, rfl⟩ := ho
      rw [Function.iterate_add_apply, Function.iterate_mul, hg2, Function.iterate_id,
        Function.iterate_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [theta_pow_single hj]; rfl⟩

end Orbits

section Classification

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

theorem single_mem_simpleRootsJ {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ (tauDatum L ℓ f hf).simpleRootsJ := by
  rw [GenFixedRootDatum.simpleRootsJ_eq]
  exact d4Aux.mem_unionSimpleRoots_iff.2 ⟨j, d4Aux_support ▸ hj, rfl⟩

theorem thetaOrbit_mem_orbits {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) :
    thetaOrbit d4Gen.θ (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ (tauDatum L ℓ f hf).orbits :=
  ⟨_, single_mem_simpleRootsJ hf hj, rfl⟩

theorem orbit_cases {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ (tauDatum L ℓ f hf).orbits) :
    O = {Pi.single 1 1} ∨ O = {Pi.single 3 1} ∨ O = {Pi.single 2 1, Pi.single 4 1} := by
  obtain ⟨β, hβ, rfl⟩ := hO
  rw [GenFixedRootDatum.simpleRootsJ_eq] at hβ
  obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
  have hjS : j ∈ d4Support := d4Aux_support ▸ hj
  have hOrb : thetaOrbit (tauDatum L ℓ f hf).θ (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      {Pi.single j 1, Pi.single (gam j) 1} := thetaOrbit_single hjS
  rw [hOrb]
  rcases d4Support_cases hjS with rfl | rfl | rfl | rfl
  · left
    rw [gam_one]
    exact Set.pair_eq_singleton _
  · right; right
    rw [gam_two]
  · right; left
    rw [gam_three]
    exact Set.pair_eq_singleton _
  · right; right
    rw [gam_four]
    exact Set.pair_comm _ _

theorem orbitRoot_single {O : Set (Fin Tag.E6.rank → ℤ)} {j : Fin Tag.E6.rank}
    (hO : O ∈ (tauDatum L ℓ f hf).orbits) (hOj : O = {Pi.single j 1}) :
    GenFixedRootDatum.orbitRoot O = Pi.single j 1 := by
  have h := (tauDatum L ℓ f hf).orbitRoot_mem hO
  exact Set.mem_singleton_iff.1 ((Set.ext_iff.1 hOj _).1 h)

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem single_ne_single {i j : Fin Tag.E6.rank} (h : i ≠ j) :
    (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j 1 := fun e => by
  have := congrFun e i
  simp [h] at this

theorem orbit1_mem :
    ({Pi.single 1 1} : Set (Fin Tag.E6.rank → ℤ)) ∈ (tauDatum L ℓ f hf).orbits := by
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have := thetaOrbit_mem_orbits (L := L) (ℓ := ℓ) (f := f) hf h1S
  rwa [thetaOrbit_single h1S, gam_one, Set.pair_eq_singleton] at this

theorem orbit3_mem :
    ({Pi.single 3 1} : Set (Fin Tag.E6.rank → ℤ)) ∈ (tauDatum L ℓ f hf).orbits := by
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have := thetaOrbit_mem_orbits (L := L) (ℓ := ℓ) (f := f) hf h3S
  rwa [thetaOrbit_single h3S, gam_three, Set.pair_eq_singleton] at this

theorem orbit24_mem :
    ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) ∈
      (tauDatum L ℓ f hf).orbits := by
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have := thetaOrbit_mem_orbits (L := L) (ℓ := ℓ) (f := f) hf h2S
  rwa [thetaOrbit_single h2S, gam_two] at this

theorem q_ge_two : 2 ≤ (tauDatum L ℓ f hf).q := by
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  change 2 ≤ ℓ ^ f
  calc 2 ≤ ℓ := hℓ
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) hf

theorem tau_isPerfect : Group.IsPerfect (tauDatum L ℓ f hf).orbitGroup := by
  set D := tauDatum L ℓ f hf with hD
  have hO1 := orbit1_mem (L := L) (ℓ := ℓ) (f := f) hf
  have hO3 := orbit3_mem (L := L) (ℓ := ℓ) (f := f) hf
  have c13 : Tag.E6.cartan 1 3 = -1 := by decide
  have c31 : Tag.E6.cartan 3 1 = -1 := by decide
  refine D.isPerfect_orbitGroup_of_forall fun O hO c => ?_
  rcases orbit_cases hf hO with rfl | rfl | rfl
  · exact orbitXY_mem_commutator_of_adjacent D hO3 hO (Set.ncard_singleton _) (Set.ncard_singleton _)
      (orbitRoot_single hf hO3 rfl) (orbitRoot_single hf hO rfl) c31 c13 c
  · exact orbitXY_mem_commutator_of_adjacent D hO1 hO (Set.ncard_singleton _) (Set.ncard_singleton _)
      (orbitRoot_single hf hO1 rfl) (orbitRoot_single hf hO rfl) c13 c31 c
  · refine D.gens_mem_commutator_of_three_lt hO ?_ c
    have hcard : GenFixedRootDatum.orbitCard ({Pi.single 2 1, Pi.single 4 1} :
        Set (Fin Tag.E6.rank → ℤ)) = 2 := by
      rw [GenFixedRootDatum.orbitCard, Set.ncard_pair (single_ne_single (by decide))]
    rw [D.card_orbitField hO, hcard]
    have := q_ge_two (L := L) (ℓ := ℓ) (f := f) hf
    nlinarith

theorem tau_isQuasisimple : CFSG.IsQuasisimple (tauDatum L ℓ f hf).orbitGroup :=
  (tauDatum L ℓ f hf).isQuasisimple_orbitGroup_of_isPerfect (orbit3_mem (L := L) (ℓ := ℓ) (f := f) hf)
    (tau_isPerfect hf)

end Classification

end CFSG.RankThree.PartOne.KD4L
