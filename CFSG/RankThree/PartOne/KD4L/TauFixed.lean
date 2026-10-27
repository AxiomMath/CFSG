module

public import CFSG.RankThree.PartOne.KD4L.TauPerfect
public import CFSG.RankThree.Chevalley.SteinbergBID4Kernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups
open scoped commutatorElement Pointwise

section Torus

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

@[expose] def d4Sigma : Equiv.Perm (Fin 4) := Equiv.swap 1 3

omit [IsAlgClosed L] in
theorem frobTwist_torusElt (f : ℕ) (i : Fin Tag.E6.rank) (u : Lˣ) :
    frobTwistGL Tag.E6 L ℓ f (diagramMap TwistTag.E6 L) (torusElt Tag.E6 L i u) =
      torusElt Tag.E6 L (TwistTag.E6.perm i) (Units.map (iterateFrobenius L ℓ f).toMonoidHom u) :=
  twistHom_torusElt TwistTag.E6 L (iterateFrobenius L ℓ f) i u

omit [IsAlgClosed L] in
theorem frobTwist_d4TorusHom (f : ℕ) (a : Fin 4 → Lˣ) :
    frobTwistGL Tag.E6 L ℓ f (diagramMap TwistTag.E6 L) (d4TorusHom L a) =
      d4TorusHom L (fun k => Units.map (iterateFrobenius L ℓ f).toMonoidHom (a (d4Sigma k))) := by
  rw [d4TorusHom_apply, d4TorusHom_apply, map_mul, map_mul, map_mul, frobTwist_torusElt,
    frobTwist_torusElt, frobTwist_torusElt, frobTwist_torusElt]
  have p1 : TwistTag.E6.perm (1 : Fin Tag.E6.rank) = 1 := by decide
  have p2 : TwistTag.E6.perm (2 : Fin Tag.E6.rank) = 4 := by decide
  have p3 : TwistTag.E6.perm (3 : Fin Tag.E6.rank) = 3 := by decide
  have p4 : TwistTag.E6.perm (4 : Fin Tag.E6.rank) = 2 := by decide
  have s0 : d4Sigma 0 = 0 := by decide
  have s1 : d4Sigma 1 = 3 := by decide
  have s2 : d4Sigma 2 = 2 := by decide
  have s3 : d4Sigma 3 = 1 := by decide
  rw [p1, p2, p3, p4, s0, s1, s2, s3]
  set x0 := Units.map (iterateFrobenius L ℓ f).toMonoidHom (a 0)
  set x1 := Units.map (iterateFrobenius L ℓ f).toMonoidHom (a 1)
  set x2 := Units.map (iterateFrobenius L ℓ f).toMonoidHom (a 2)
  set x3 := Units.map (iterateFrobenius L ℓ f).toMonoidHom (a 3)
  have c42 : torusElt Tag.E6 L 4 x1 * torusElt Tag.E6 L 2 x3 =
      torusElt Tag.E6 L 2 x3 * torusElt Tag.E6 L 4 x1 := torusElt_mul_comm 4 2 _ _
  have c43 : torusElt Tag.E6 L 4 x1 * torusElt Tag.E6 L 3 x2 =
      torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 4 x1 := torusElt_mul_comm 4 3 _ _
  have c32 : torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 2 x3 =
      torusElt Tag.E6 L 2 x3 * torusElt Tag.E6 L 3 x2 := torusElt_mul_comm 3 2 _ _
  have key : torusElt Tag.E6 L 4 x1 * (torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 2 x3) =
      torusElt Tag.E6 L 2 x3 * (torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 4 x1) := by
    calc torusElt Tag.E6 L 4 x1 * (torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 2 x3)
        = (torusElt Tag.E6 L 4 x1 * torusElt Tag.E6 L 3 x2) * torusElt Tag.E6 L 2 x3 :=
          (mul_assoc _ _ _).symm
      _ = (torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 4 x1) * torusElt Tag.E6 L 2 x3 := by
          rw [c43]
      _ = torusElt Tag.E6 L 3 x2 * (torusElt Tag.E6 L 4 x1 * torusElt Tag.E6 L 2 x3) :=
          mul_assoc _ _ _
      _ = torusElt Tag.E6 L 3 x2 * (torusElt Tag.E6 L 2 x3 * torusElt Tag.E6 L 4 x1) := by
          rw [c42]
      _ = (torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 2 x3) * torusElt Tag.E6 L 4 x1 :=
          (mul_assoc _ _ _).symm
      _ = (torusElt Tag.E6 L 2 x3 * torusElt Tag.E6 L 3 x2) * torusElt Tag.E6 L 4 x1 := by
          rw [c32]
      _ = torusElt Tag.E6 L 2 x3 * (torusElt Tag.E6 L 3 x2 * torusElt Tag.E6 L 4 x1) :=
          mul_assoc _ _ _
  calc torusElt Tag.E6 L 1 x0 * torusElt Tag.E6 L 4 x1 * torusElt Tag.E6 L 3 x2 *
        torusElt Tag.E6 L 2 x3
      = torusElt Tag.E6 L 1 x0 * (torusElt Tag.E6 L 4 x1 * (torusElt Tag.E6 L 3 x2 *
          torusElt Tag.E6 L 2 x3)) := by group
    _ = torusElt Tag.E6 L 1 x0 * (torusElt Tag.E6 L 2 x3 * (torusElt Tag.E6 L 3 x2 *
          torusElt Tag.E6 L 4 x1)) := by rw [key]
    _ = _ := by group

end Torus

section Fixed

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

theorem unionRoots_tau :
    unionRoots d4Gen.χ d4Gen.J = parabolicRoots Tag.E6 d4Support := by
  rw [← kernelRoots_d4Gen]
  ext α
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, Set.mem_univ _⟩

theorem rootSpanJ_tau :
    (tauDatum L ℓ f hf).rootSpanJ = subsystemGroup Tag.E6 L d4Support := by
  change rootSpan Tag.E6 L (unionRoots d4Gen.χ d4Gen.J) = _
  rw [unionRoots_tau, subsystemGroup_eq_rootSpan]

theorem torusJ_tau :
    (tauDatum L ℓ f hf).torusJ = supportedTorus Tag.E6 L d4Support := by
  change unionRootSpan L d4Gen.χ d4Gen.J ⊓ torusGroup Tag.E6 L = _
  rw [show unionRootSpan L d4Gen.χ d4Gen.J = subsystemGroup Tag.E6 L d4Support from
    rootSpanJ_tau (L := L) (ℓ := ℓ) hf]
  exact subsystemGroup_inf_torusGroup_eq_supportedTorus d4Support

theorem exists_params_of_mem_fixedTorus {t : adjointGroup Tag.E6 L}
    (ht : t ∈ (tauDatum L ℓ f hf).fixedTorus) :
    ∃ a : Fin 4 → Lˣ, d4TorusHom L a = (t : ModGL Tag.E6 L) ∧
      (a 0 : L) ^ ℓ ^ f = a 0 ∧ (a 2 : L) ^ ℓ ^ f = a 2 ∧ (a 3 : L) = (a 1 : L) ^ ℓ ^ f ∧
        (a 1 : L) = (a 3 : L) ^ ℓ ^ f := by
  obtain ⟨htT, htF⟩ := (tauDatum L ℓ f hf).mem_fixedTorus.1 ht
  rw [torusJ_tau (L := L) (ℓ := ℓ) hf, ← range_d4TorusHom] at htT
  obtain ⟨a, ha⟩ := htT
  have hF : frobTwistGL Tag.E6 L ℓ f (diagramMap TwistTag.E6 L) (t : ModGL Tag.E6 L) =
      (t : ModGL Tag.E6 L) := by
    have h1 := congrArg Subtype.val htF
    have h2 : (((tauDatum L ℓ f hf).F t : adjointGroup Tag.E6 L) : ModGL Tag.E6 L) =
        frobTwistGL Tag.E6 L ℓ f (diagramMap TwistTag.E6 L) (t : ModGL Tag.E6 L) :=
      tauF_apply f hf t
    rw [h2] at h1
    exact h1
  rw [← ha, frobTwist_d4TorusHom] at hF
  have hinj := d4TorusHom_injective hF
  have key : ∀ k, ((Units.map (iterateFrobenius L ℓ f).toMonoidHom (a (d4Sigma k)) : Lˣ) : L) =
      (a k : L) := fun k => congrArg Units.val (congrFun hinj k)
  have e0 := key 0
  have e1 := key 1
  have e2 := key 2
  have e3 := key 3
  have s0 : d4Sigma 0 = 0 := by decide
  have s1 : d4Sigma 1 = 3 := by decide
  have s2 : d4Sigma 2 = 2 := by decide
  have s3 : d4Sigma 3 = 1 := by decide
  rw [s0] at e0
  rw [s1] at e1
  rw [s2] at e2
  rw [s3] at e3
  simp only [Units.coe_map] at e0 e1 e2 e3
  exact ⟨a, ha, e0, e2, e3.symm, e1.symm⟩

theorem pair_data {O : Set (Fin Tag.E6.rank → ℤ)} (hOe : O = {Pi.single 2 1, Pi.single 4 1})
    (hO : O ∈ (tauDatum L ℓ f hf).orbits) :
    (GenFixedRootDatum.orbitCard O = 2) ∧
      (((tauDatum L ℓ f hf).orbitVec O 0 = Pi.single 2 1 ∧
          (tauDatum L ℓ f hf).orbitVec O 1 = Pi.single 4 1) ∨
        ((tauDatum L ℓ f hf).orbitVec O 0 = Pi.single 4 1 ∧
          (tauDatum L ℓ f hf).orbitVec O 1 = Pi.single 2 1)) := by
  set D := tauDatum L ℓ f hf with hD
  subst hOe
  refine ⟨by rw [GenFixedRootDatum.orbitCard, Set.ncard_pair (single_ne_single (by decide))], ?_⟩
  have hroot := D.orbitRoot_mem hO
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  have step := D.theta_orbitVec hO 0
  rcases hroot with h | h
  · left
    have hi : D.orbitVec {Pi.single 2 1, Pi.single 4 1} 0 = Pi.single 2 1 := by
      rw [D.orbitVec_zero]; exact h
    refine ⟨hi, ?_⟩
    rw [hi] at step
    have hK : (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots d4Gen.χ := by
      rw [kernelRoots_d4Gen]; exact single_mem_parabolicRoots h2S
    have h' : D.θ (toReal (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) =
        toReal (permLattice (τ := Tag.E6) gam (Pi.single 2 1)) := d4Gen_theta_toReal hK
    rw [h', permLattice_gam_single, gam_two] at step
    exact (toReal_injective step).symm
  · right
    have h4 : GenFixedRootDatum.orbitRoot ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) = Pi.single 4 1 :=
      Set.mem_singleton_iff.1 h
    have hi : D.orbitVec {Pi.single 2 1, Pi.single 4 1} 0 = Pi.single 4 1 := by
      rw [D.orbitVec_zero]; exact h4
    refine ⟨hi, ?_⟩
    rw [hi] at step
    have hK : (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots d4Gen.χ := by
      rw [kernelRoots_d4Gen]; exact single_mem_parabolicRoots h4S
    have h' : D.θ (toReal (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) =
        toReal (permLattice (τ := Tag.E6) gam (Pi.single 4 1)) := d4Gen_theta_toReal hK
    rw [h', permLattice_gam_single, gam_four] at step
    exact (toReal_injective step).symm

theorem fixedTorus_le_orbitGroupC :
    (tauDatum L ℓ f hf).fixedTorus ≤ (tauDatum L ℓ f hf).orbitGroupC := by
  set D := tauDatum L ℓ f hf with hD
  intro t ht
  obtain ⟨a, ha, h0, h2, h13, h31⟩ := exists_params_of_mem_fixedTorus hf ht
  have hO1 := orbit1_mem (L := L) (ℓ := ℓ) (f := f) hf
  have hO3 := orbit3_mem (L := L) (ℓ := ℓ) (f := f) hf
  have hO24 := orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf
  have m1 : torusElt Tag.E6 L 1 (a 0) ∈ D.orbitGroup :=
    torusElt_mem_orbitGroup_of_single D hO1 (Set.ncard_singleton _)
      (orbitRoot_single hf hO1 rfl) (a 0) h0
  have m3 : torusElt Tag.E6 L 3 (a 2) ∈ D.orbitGroup :=
    torusElt_mem_orbitGroup_of_single D hO3 (Set.ncard_singleton _)
      (orbitRoot_single hf hO3 rfl) (a 2) h2
  have hq2 : ∀ s : Lˣ, (s : L) = ((s : L) ^ ℓ ^ f) ^ ℓ ^ f → (s : L) ^ (ℓ ^ f) ^ 2 = s := by
    intro s hs
    rw [sq, pow_mul]
    exact hs.symm
  have m24 : torusElt Tag.E6 L 2 (a 1) * torusElt Tag.E6 L 4 (a 3) ∈ D.orbitGroup := by
    obtain ⟨hc, hcase⟩ := pair_data hf rfl hO24
    rcases hcase with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · have := torusElt_pair_mem_orbitGroup D hO24 hc hi hi' (a 1) (hq2 (a 1) (by
        rw [← h13]; exact h31))
      have e : ((a 1 ^ D.q : Lˣ) : L) = (a 3 : L) := by
        rw [Units.val_pow_eq_pow_val]; exact h13.symm
      rwa [Units.ext e] at this
    · have := torusElt_pair_mem_orbitGroup D hO24 hc hi hi' (a 3) (hq2 (a 3) (by
        rw [← h31]; exact h13))
      have e : ((a 3 ^ D.q : Lˣ) : L) = (a 1 : L) := by
        rw [Units.val_pow_eq_pow_val]; exact h31.symm
      rw [Units.ext e] at this
      rwa [torusElt_mul_comm] at this
  show (t : ModGL Tag.E6 L) ∈ D.orbitGroup
  rw [← ha, d4TorusHom_apply]
  have e : torusElt Tag.E6 L 1 (a 0) * torusElt Tag.E6 L 2 (a 1) * torusElt Tag.E6 L 3 (a 2) *
      torusElt Tag.E6 L 4 (a 3) =
      torusElt Tag.E6 L 1 (a 0) * torusElt Tag.E6 L 3 (a 2) *
        (torusElt Tag.E6 L 2 (a 1) * torusElt Tag.E6 L 4 (a 3)) := by
    calc torusElt Tag.E6 L 1 (a 0) * torusElt Tag.E6 L 2 (a 1) * torusElt Tag.E6 L 3 (a 2) *
          torusElt Tag.E6 L 4 (a 3)
        = torusElt Tag.E6 L 1 (a 0) * (torusElt Tag.E6 L 2 (a 1) * torusElt Tag.E6 L 3 (a 2)) *
          torusElt Tag.E6 L 4 (a 3) := by group
      _ = torusElt Tag.E6 L 1 (a 0) * (torusElt Tag.E6 L 3 (a 2) * torusElt Tag.E6 L 2 (a 1)) *
          torusElt Tag.E6 L 4 (a 3) := by rw [torusElt_mul_comm 2 3]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem m1 m3) m24

theorem fixedGroup_eq_orbitGroupC :
    (tauDatum L ℓ f hf).fixedGroup = (tauDatum L ℓ f hf).orbitGroupC := by
  set D := tauDatum L ℓ f hf with hD
  refine le_antisymm (fun g hg => ?_) D.orbitGroupC_le_fixedGroup
  have hg' : g ∈ (D.fixedTorus : Set (adjointGroup Tag.E6 L)) *
      (D.orbitGroupC : Set (adjointGroup Tag.E6 L)) := by
    rw [← D.coe_fixedGroup_eq_mul]
    exact hg
  obtain ⟨t, ht, c, hc, rfl⟩ := hg'
  exact mul_mem (fixedTorus_le_orbitGroupC hf ht) hc

end Fixed

end CFSG.RankThree.PartOne.KD4L
