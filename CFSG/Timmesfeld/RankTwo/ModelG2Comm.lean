module

public import CFSG.Timmesfeld.RankTwo.ModelG2Words
public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Steinberg.Adjoint.Group

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Chevalley.RootWalk
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section RepCheck

variable {τ : Tag} {K : Type} [Field K]

theorem commutator_xPar_of_repCheck {a b : ℕ} {fs : List Factor} (h : repCheck τ a b fs = true)
    (s t : K) :
    ⁅xPar (rootOperatorFamily τ) (τ.rootCertificate.root a) s,
        xPar (rootOperatorFamily τ) (τ.rootCertificate.root b) t⁆ =
      (fs.map fun f => xPar (rootOperatorFamily τ) (τ.rootCertificate.root f.2.2.1)
        ((f.2.2.2 : K) * s ^ f.1 * t ^ f.2.1)).prod := by
  set F := rootOperatorFamily τ
  have hab : a < τ.rootCertificate.roots.length ∧ b < τ.rootCertificate.roots.length := by
    simp only [repCheck, Bool.and_eq_true, Nat.blt_eq] at h
    exact ⟨h.1.1.1, h.1.1.2⟩
  have hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length := fun f hf => by
    simp only [repCheck, Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.2 f hf
    simp only [coneOk, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.1.1
  have hop := elt_mul_elt_of_repCheck (R := K) (RootOps.dataChecks τ).valid h
    (rootAt τ a hab.1) (rootAt τ b hab.2) (rootPos_rootAt _) (rootPos_rootAt _) s t
  have hx : ∀ (g : ℕ) (hg : g < τ.rootCertificate.roots.length) (c : K),
      xPar F (τ.rootCertificate.root g) c = F.eltElement (rootAt τ g hg) c := fun g hg c =>
    xPar_of_isRoot (isRoot_rootCertificate_root hg) c
  have hprod : factorsElement K fs s t = (fs.map fun f => xPar F (τ.rootCertificate.root f.2.2.1)
      ((f.2.2.2 : K) * s ^ f.1 * t ^ f.2.1)).prod := by
    rw [factorsElement]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    rw [dite_eq_left (hfs f hf), hx _ (hfs f hf)]
  have hmul : F.eltElement (rootAt τ a hab.1) s * F.eltElement (rootAt τ b hab.2) t =
      factorsElement K fs s t * F.eltElement (rootAt τ b hab.2) t *
        F.eltElement (rootAt τ a hab.1) s := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, RootOperatorFamily.coe_eltElement,
      RootOperatorFamily.coe_eltUnit, coe_factorsElement]
    exact hop
  rw [hx a hab.1, hx b hab.2, commutatorElement_def, hmul, ← hprod]
  group

end RepCheck


@[expose] def g2Pos : Fin 6 → ℕ := ![1, 3, 8, 7, 4, 0]

theorem hexRoot_eq_g2 (i : Fin 6) : hexRoot i = (Tag.rootCertificate .G2).root (g2Pos i) := by
  fin_cases i <;> funext k <;> fin_cases k <;> decide

@[expose] def g2HexReps : List (ℕ × ℕ × List Factor) := [
  (1, 3, []), (1, 8, [(1, 1, 3, 3)]), (1, 7, []),
  (1, 4, [(2, 1, 3, -3), (1, 1, 8, -2), (1, 2, 7, -3)]),
  (1, 0, [(3, 1, 3, 1), (2, 1, 8, 1), (3, 2, 7, -1), (1, 1, 4, -1)]),
  (3, 8, []), (3, 7, []), (3, 4, []), (3, 0, [(1, 1, 7, -1)]),
  (8, 7, []), (8, 4, [(1, 1, 7, -3)]), (8, 0, []),
  (7, 4, []), (7, 0, []), (4, 0, [])]

theorem g2HexReps_check : repsCheck .G2 g2HexReps = true := by decide +kernel

theorem repCheck_of_mem_g2HexReps {a b : ℕ} {fs : List Factor} (h : (a, b, fs) ∈ g2HexReps) :
    repCheck .G2 a b fs = true := by
  have := g2HexReps_check
  simp only [repsCheck, List.all_eq_true] at this
  exact this _ h

section G2

variable {K : Type} [Field K]

@[expose] noncomputable def g2X (i : Fin 6) (c : K) : adjointGroup .G2 K :=
  xPar (rootOperatorFamily .G2) (hexRoot i) c

theorem g2X_eq (i : Fin 6) (c : K) :
    g2X i c = xPar (rootOperatorFamily .G2) ((Tag.rootCertificate .G2).root (g2Pos i)) c := by
  rw [g2X, hexRoot_eq_g2]

theorem g2X_add (i : Fin 6) (c d : K) : g2X i (c + d) = g2X i c * g2X i d :=
  xPar_add _ c d

theorem g2X_zero (i : Fin 6) : g2X i (0 : K) = 1 :=
  xPar_zero _

theorem commutator_g2X {i j : Fin 6} {fs : List Factor} (h : (g2Pos i, g2Pos j, fs) ∈ g2HexReps)
    (s t : K) :
    ⁅g2X i s, g2X j t⁆ = (fs.map fun f => xPar (rootOperatorFamily .G2)
      ((Tag.rootCertificate .G2).root f.2.2.1) ((f.2.2.2 : K) * s ^ f.1 * t ^ f.2.1)).prod := by
  rw [g2X_eq, g2X_eq]
  exact commutator_xPar_of_repCheck (repCheck_of_mem_g2HexReps h) s t

theorem commute_g2X {i j : Fin 6} (h : (g2Pos i, g2Pos j, []) ∈ g2HexReps) (s t : K) :
    Commute (g2X i s) (g2X j t) := by
  rw [← commutatorElement_eq_one_iff_commute, commutator_g2X h, List.map_nil, List.prod_nil]

variable [CharP K 2]

theorem cast_odd_eq_one {C : ℤ} (hC : Odd C) : (C : K) = 1 := by
  obtain ⟨k, rfl⟩ := hC
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  push_cast
  rw [h2, zero_mul, zero_add]

theorem cast_even_eq_zero {C : ℤ} (hC : Even C) : (C : K) = 0 := by
  obtain ⟨k, rfl⟩ := hC
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  push_cast
  rw [← two_mul, h2, zero_mul]

theorem xPar_inv_eq {τ : Tag} (γ : Fin τ.rank → ℤ) (c : K) :
    (xPar (rootOperatorFamily τ) γ c)⁻¹ = xPar (rootOperatorFamily τ) γ c := by
  rw [xPar_neg, CharTwo.neg_eq]

theorem g2X_inv (i : Fin 6) (c : K) : (g2X i c)⁻¹ = g2X i c :=
  xPar_inv_eq _ c

theorem charTwo_three : (3 : K) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h2

theorem g2X_comm02 (s t : K) : ⁅g2X 0 s, g2X 2 t⁆ = g2X 1 (s * t) := by
  rw [commutator_g2X (fs := [(1, 1, 3, 3)]) (by decide)]
  simp [charTwo_three, g2X_eq, g2Pos]

theorem g2X_comm24 (s t : K) : ⁅g2X 2 s, g2X 4 t⁆ = g2X 3 (s * t) := by
  rw [commutator_g2X (fs := [(1, 1, 7, -3)]) (by decide)]
  simp [charTwo_three, CharTwo.neg_eq, g2X_eq, g2Pos]

theorem g2X_comm15 (s t : K) : ⁅g2X 1 s, g2X 5 t⁆ = g2X 3 (s * t) := by
  rw [commutator_g2X (fs := [(1, 1, 7, -1)]) (by decide)]
  simp [CharTwo.neg_eq, g2X_eq, g2Pos]

theorem g2X_comm04 (s t : K) :
    ⁅g2X 0 s, g2X 4 t⁆ = g2X 1 (s ^ 2 * t) * g2X 3 (s * t ^ 2) := by
  rw [commutator_g2X (fs := [(2, 1, 3, -3), (1, 1, 8, -2), (1, 2, 7, -3)]) (by decide)]
  simp [charTwo_three, CharTwo.neg_eq, CharTwo.two_eq_zero, xPar_zero, g2X_eq, g2Pos]

theorem g2X_comm05 (s t : K) : ⁅g2X 0 s, g2X 5 t⁆ =
    g2X 1 (t * s ^ 3) * g2X 2 (t * s ^ 2) * g2X 3 (t ^ 2 * s ^ 3) * g2X 4 (t * s) := by
  rw [commutator_g2X (fs := [(3, 1, 3, 1), (2, 1, 8, 1), (3, 2, 7, -1), (1, 1, 4, -1)])
    (by decide)]
  simp [CharTwo.neg_eq, g2X_eq, g2Pos, mul_assoc, mul_comm]

theorem g2X_rels :
    ∀ r ∈ GradedPresentation.rels (g2Cm (K := K)),
      FreeGroup.lift (fun g : Σ _ : Fin 6, K => g2X g.1 g.2) r = 1 :=
  rels_g2Cm_of (fun i c d => g2X_add i c d) g2X_comm02 g2X_comm24 g2X_comm15 g2X_comm04
    g2X_comm05 (commute_g2X (by decide)) (commute_g2X (by decide)) (commute_g2X (by decide))
    (commute_g2X (by decide)) (commute_g2X (by decide)) (commute_g2X (by decide))
    (commute_g2X (by decide)) (commute_g2X (by decide)) (commute_g2X (by decide))
    (commute_g2X (by decide))

end G2

end CFSG.Timmesfeld.RankTwo
