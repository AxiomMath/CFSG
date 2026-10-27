module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c13bc_commute_of_perfect {Γ : Type*} [Group Γ] {L Z : Subgroup Γ} {p : ℕ}
    (hp : p.Prime) (hL : _root_.commutator ↥L = ⊤) (hZc : Nat.card Z = p)
    (hZn : ∀ m ∈ L, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z) : ∀ m ∈ L, ∀ x ∈ Z, m * x = x * m := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic Z := isCyclic_of_prime_card hZc
  have hLN : L ≤ Subgroup.normalizer (Z : Set Γ) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hZn m hm x hx, fun hx => ?_⟩
    have h := hZn m⁻¹ (L.inv_mem hm) _ hx
    simpa [mul_assoc] using h
  let φ : ↥L →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hcommAut : ∀ a b : MulAut ↥Z, a * b = b * a := fun a b =>
    (IsCyclic.mulAutMulEquiv (G := ↥Z)).injective (by rw [map_mul, map_mul, mul_comm])
  have hker : (⊤ : Subgroup ↥L) ≤ φ.ker := by
    rw [← hL, _root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcommAut _ _)
  intro m hm x hx
  have h1 : φ ⟨m, hm⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
  have h2 : ((φ ⟨m, hm⟩ ⟨x, hx⟩ : ↥Z) : Γ) = m * x * m⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe Z (Subgroup.inclusion hLN ⟨m, hm⟩) ⟨x, hx⟩
  rw [h1, MulAut.one_apply] at h2
  exact mul_inv_eq_iff_eq_mul.1 h2.symm

theorem s16c13bc_map_conj_mul {Γ : Type*} [Group Γ] (A : Subgroup Γ) (x y : Γ) :
    A.map (MulAut.conj (x * y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

theorem s16c13bc_map_conj_one {Γ : Type*} [Group Γ] (A : Subgroup Γ) :
    A.map (MulAut.conj (1 : Γ)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem s16c13bc_map_conj_cancel {Γ : Type*} [Group Γ] (A : Subgroup Γ) (x : Γ) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = A := by
  rw [← s16c13bc_map_conj_mul, inv_mul_cancel, s16c13bc_map_conj_one]

theorem s16c13bc_map_conj_inj {Γ : Type*} [Group Γ] {A B : Subgroup Γ} (x : Γ)
    (h : A.map (MulAut.conj x).toMonoidHom = B.map (MulAut.conj x).toMonoidHom) : A = B := by
  rw [← s16c13bc_map_conj_cancel A x, ← s16c13bc_map_conj_cancel B x, h]

theorem s16c13bc_conj_mem_pair {Γ : Type*} [Group Γ] {M A : Subgroup Γ} {t : Γ} (htM : t ∈ M)
    (htne : A.map (MulAut.conj t).toMonoidHom ≠ A)
    (hcls : Set.ncard {Y : Subgroup Γ | ∃ φ ∈ M, Y = A.map (MulAut.conj φ).toMonoidHom} = 2) :
    ∀ g ∈ M, A.map (MulAut.conj g).toMonoidHom = A ∨
      A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj t).toMonoidHom := by
  classical
  set C : Set (Subgroup Γ) := {Y | ∃ φ ∈ M, Y = A.map (MulAut.conj φ).toMonoidHom} with hC
  have hsub : ({A, A.map (MulAut.conj t).toMonoidHom} : Set (Subgroup Γ)) ⊆ C := by
    intro Y hY
    rcases hY with rfl | rfl
    · exact ⟨1, M.one_mem, (s16c13bc_map_conj_one _).symm⟩
    · exact ⟨t, htM, rfl⟩
  have hpair : ({A, A.map (MulAut.conj t).toMonoidHom} : Set (Subgroup Γ)).ncard = 2 :=
    Set.ncard_pair htne.symm
  have hfin : C.Finite := Set.finite_of_ncard_ne_zero (by rw [hcls]; norm_num)
  have heq : ({A, A.map (MulAut.conj t).toMonoidHom} : Set (Subgroup Γ)) = C :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcls, hpair]) hfin
  intro g hg
  have hmem : A.map (MulAut.conj g).toMonoidHom ∈ C := ⟨g, hg, rfl⟩
  rw [← heq] at hmem
  exact hmem

theorem s16c13bc_conj_pair_stable {Γ : Type*} [Group Γ] {M A : Subgroup Γ} {t : Γ}
    (htM : t ∈ M) (htne : A.map (MulAut.conj t).toMonoidHom ≠ A)
    (hcls : Set.ncard {Y : Subgroup Γ | ∃ φ ∈ M, Y = A.map (MulAut.conj φ).toMonoidHom} = 2)
    {w : Γ} (hwM : w ∈ M) (hw : A.map (MulAut.conj w).toMonoidHom = A) :
    (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj w).toMonoidHom =
      A.map (MulAut.conj t).toMonoidHom := by
  have h1 : (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj w).toMonoidHom =
      A.map (MulAut.conj (w * t)).toMonoidHom := (s16c13bc_map_conj_mul A w t).symm
  rcases s16c13bc_conj_mem_pair htM htne hcls (w * t) (M.mul_mem hwM htM) with h | h
  · exfalso
    apply htne
    have h2 : (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj w).toMonoidHom =
        A.map (MulAut.conj w).toMonoidHom := h1.trans (h.trans hw.symm)
    exact s16c13bc_map_conj_inj w h2
  · rw [h1]
    exact h

theorem s16c13bc_conj_sq {Γ : Type*} [Group Γ] {M A : Subgroup Γ} {t : Γ} (htM : t ∈ M)
    (htne : A.map (MulAut.conj t).toMonoidHom ≠ A)
    (hcls : Set.ncard {Y : Subgroup Γ | ∃ φ ∈ M, Y = A.map (MulAut.conj φ).toMonoidHom} = 2) :
    A.map (MulAut.conj (t * t)).toMonoidHom = A := by
  rcases s16c13bc_conj_mem_pair htM htne hcls (t * t) (M.mul_mem htM htM) with h | h
  · exact h
  · exfalso
    apply htne
    have h2 : (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        A.map (MulAut.conj t).toMonoidHom := (s16c13bc_map_conj_mul A t t).symm.trans h
    exact s16c13bc_map_conj_inj t h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
