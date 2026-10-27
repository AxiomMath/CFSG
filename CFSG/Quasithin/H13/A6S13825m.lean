module

public import CFSG.Quasithin.Background.P4GLAut
public import CFSG.Quasithin.EmptyFaithful.SBd8FlagL4

public section

namespace CFSG.Quasithin.H13.A6.L13825

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.SBd8.Flag

variable {n : ℕ}

@[expose] def revCuts (n : ℕ) (C : Set ℕ) : Set ℕ := {c | c ≤ n ∧ n - c ∈ C}

theorem mem_revCuts {C : Set ℕ} {c : ℕ} : c ∈ revCuts n C ↔ c ≤ n ∧ n - c ∈ C := Iff.rfl

theorem isCuts_revCuts {C : Set ℕ} (hC : IsCuts n C) : IsCuts n (revCuts n C) := by
  rintro c ⟨hcn, hc⟩
  have := hC _ hc
  omega

theorem revCuts_revCuts {C : Set ℕ} (hC : IsCuts n C) : revCuts n (revCuts n C) = C := by
  ext c
  rw [mem_revCuts, mem_revCuts]
  constructor
  · rintro ⟨hcn, -, h⟩
    rwa [Nat.sub_sub_self hcn] at h
  · intro hc
    have := hC c hc
    refine ⟨by omega, by omega, ?_⟩
    rwa [Nat.sub_sub_self (by omega)]

theorem revCuts_full : revCuts n {i | 1 ≤ i ∧ i < n} = {i | 1 ≤ i ∧ i < n} := by
  ext c
  rw [mem_revCuts, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  omega

theorem det_revJ :
    ((Fin.revPerm : Equiv.Perm (Fin n)).permMatrix (ZMod 2)).det = 1 := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
    rw [h] <;> decide

@[expose] def revJ (n : ℕ) : SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨(Fin.revPerm : Equiv.Perm (Fin n)).permMatrix (ZMod 2), det_revJ⟩

theorem revJ_apply (i j : Fin n) :
    (revJ n : Matrix (Fin n) (Fin n) (ZMod 2)) i j = if j = Fin.rev i then 1 else 0 := by
  change (Fin.revPerm : Equiv.Perm (Fin n)).toPEquiv.toMatrix i j = _
  rw [PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
  by_cases h : j = Fin.rev i
  · simp [h]
  · simp [h, Ne.symm h]

theorem revJ_apply' (i j : Fin n) :
    (revJ n : Matrix (Fin n) (Fin n) (ZMod 2)) i j = if i = Fin.rev j then 1 else 0 := by
  rw [revJ_apply]
  by_cases h : i = Fin.rev j
  · simp [h]
  · have h' : j ≠ Fin.rev i := fun h' => h (by rw [h', Fin.rev_rev])
    simp [h, h']

theorem revJ_mul_apply (A : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    ((revJ n : Matrix (Fin n) (Fin n) (ZMod 2)) * A) i j = A (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [revJ_apply]
  · intro k _ hk
    simp [revJ_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_revJ_apply (A : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    (A * (revJ n : Matrix (Fin n) (Fin n) (ZMod 2))) i j = A i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [revJ_apply']
  · intro k _ hk
    simp [revJ_apply', hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem revJ_mul_self : revJ n * revJ n = 1 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  rw [revJ_mul_apply, revJ_apply, Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

@[expose] noncomputable def revGraph (n : ℕ) :
    MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  MulAut.conj (revJ n) * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)

theorem revGraph_apply (g : SpecialLinearGroup (Fin n) (ZMod 2)) (i j : Fin n) :
    (revGraph n g : Matrix (Fin n) (Fin n) (ZMod 2)) i j =
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
        (Fin.rev j) (Fin.rev i) := by
  have hJ : (revJ n)⁻¹ = revJ n := inv_eq_of_mul_eq_one_right revJ_mul_self
  have e : revGraph n g = revJ n * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n
      (ZMod 2) g * revJ n := by
    rw [revGraph, MulAut.mul_apply, MulAut.conj_apply, hJ]
  rw [e]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [mul_revJ_apply, revJ_mul_apply,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, Matrix.transpose_apply]

theorem revGraph_revGraph (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    revGraph n (revGraph n g) = g := by
  ext i j
  rw [revGraph_apply, ← map_inv, revGraph_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem revGraph_mem_flagStabilizer {C : Set ℕ} {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) C) :
    revGraph n g ∈ flagStabilizer n (ZMod 2) (revCuts n C) := by
  have hg' := (flagStabilizer n (ZMod 2) C).inv_mem hg
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  obtain ⟨hcn, hc'⟩ := hc
  rw [revGraph_apply]
  refine stabilizer_entries (mem_flagStabilizer.mp hg' (n - c) hc') ?_ ?_
  · rw [Fin.val_rev]
    omega
  · rw [Fin.val_rev]
    omega

theorem map_revGraph_flagStabilizer {C : Set ℕ} (hC : IsCuts n C) :
    (flagStabilizer n (ZMod 2) C).map (revGraph n).toMonoidHom =
      flagStabilizer n (ZMod 2) (revCuts n C) := by
  refine le_antisymm ?_ fun h hh => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact revGraph_mem_flagStabilizer hg
  · refine ⟨revGraph n h, ?_, revGraph_revGraph h⟩
    have := revGraph_mem_flagStabilizer hh
    rwa [revCuts_revCuts hC] at this

theorem map_revGraph_unitriangular :
    (unitriangular n (ZMod 2)).map (revGraph n).toMonoidHom = unitriangular n (ZMod 2) := by
  have hfull : IsCuts n {i | 1 ≤ i ∧ i < n} := fun i hi => hi
  rw [← upperTriangular_eq_unitriangular (Nat.card_zmod 2),
    CFSG.Quasithin.SBd8.Flag.upperTriangular_eq_flagStabilizer_full,
    map_revGraph_flagStabilizer hfull, revCuts_full]

theorem slConjugation_eq_conj (A : GL (Fin n) (ZMod 2)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A =
      MulAut.conj ((G11.P4GL.slEquiv n).symm A) := by
  refine MulEquiv.ext fun g => ?_
  apply SpecialLinearGroup.toGL_injective
  have hA : SpecialLinearGroup.toGL ((G11.P4GL.slEquiv n).symm A) = A :=
    (G11.P4GL.slEquiv n).apply_symm_apply A
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    MulAut.conj_apply, map_mul, map_mul, map_inv, hA]

theorem map_conj_of_mem {G : Type} [Group G] {H : Subgroup G} {b : G} (hb : b ∈ H) :
    H.map (MulAut.conj b).toMonoidHom = H :=
  CFSG.Quasithin.A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hb)

theorem map_flagStabilizer_of_ne_conj (hn : 3 ≤ n)
    {α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hα : (unitriangular n (ZMod 2)).map α.toMonoidHom = unitriangular n (ZMod 2))
    (hout : ∀ s, α ≠ MulAut.conj s) {C : Set ℕ} (hC : IsCuts n C) :
    (flagStabilizer n (ZMod 2) C).map α.toMonoidHom =
      flagStabilizer n (ZMod 2) (revCuts n C) := by
  rcases G11.P4GL.aut_SL_cases hn α with ⟨A, hA⟩ | ⟨A, hA⟩
  · exact absurd (hA.trans (slConjugation_eq_conj A)) (hout _)
  set J := revJ n with hJdef
  set s := (G11.P4GL.slEquiv n).symm A with hs
  set b := s * J⁻¹ with hb
  have hαb : α = MulAut.conj b * revGraph n := by
    rw [hA, slConjugation_eq_conj, revGraph, ← mul_assoc, hb, map_mul, mul_assoc (MulAut.conj s),
      ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hmap : ∀ P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)),
      P.map α.toMonoidHom = (P.map (revGraph n).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
    intro P
    rw [Subgroup.map_map, hαb]
    rfl
  have hbU : b ∈ unitriangular n (ZMod 2) := by
    have h1 := hmap (unitriangular n (ZMod 2))
    rw [hα, map_revGraph_unitriangular] at h1
    have h2 := CFSG.Quasithin.A38.map_conj_eq_iff.mp h1.symm
    rw [normalizer_unitriangular, upperTriangular_eq_unitriangular (Nat.card_zmod 2)] at h2
    exact h2
  have hbQ : b ∈ flagStabilizer n (ZMod 2) (revCuts n C) :=
    upperTriangular_le_flagStabilizer _
      ((upperTriangular_eq_unitriangular (Nat.card_zmod 2)).symm ▸ hbU)
  rw [hmap, map_revGraph_flagStabilizer hC, map_conj_of_mem hbQ]

theorem revCuts_eq_of_map_eq (hn : 3 ≤ n) {α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hα : (unitriangular n (ZMod 2)).map α.toMonoidHom = unitriangular n (ZMod 2))
    (hout : ∀ s, α ≠ MulAut.conj s) {C : Set ℕ} (hC : IsCuts n C)
    (hfix : (flagStabilizer n (ZMod 2) C).map α.toMonoidHom = flagStabilizer n (ZMod 2) C) :
    revCuts n C = C := by
  rw [map_flagStabilizer_of_ne_conj hn hα hout hC] at hfix
  exact flagStabilizer_injOn (isCuts_revCuts hC) hC hfix

end CFSG.Quasithin.H13.A6.L13825
