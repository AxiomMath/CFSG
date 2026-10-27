module

public import CFSG.ClassicalGroups.Symplectic.StatedSpTransport

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Alternating CFSG.Open
open Matrix

theorem stroth_2_1_fixed_of_hom {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {X : Type*} [Group X] {M : Type*} [AddCommGroup M] [Finite M]
    (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) (hm : 1 ≤ m)
    (h2 : ∀ a : M, a + a = 0) [DistribMulAction X M]
    (hker : ∀ x ∈ φ.ker, ∀ a : M, x • a = a) {u u' : Fin m ⊕ Fin m → K}
    (huu' : spForm m K u u' ≠ 0) {L₁ L₂ : Subgroup X}
    (hL₁ : L₁.map φ = LspGL m K u) (hL₂ : L₂.map φ = LspGL m K u')
    (hdec : IsCompl (fixedSub M (L₁ : Set X)) (fixedSub M (L₂ : Set X)))
    {x : X} (hx : φ x ∈ LspGL m K u)
    (hn : ∃ y : Fin m ⊕ Fin m → K,
      spForm m K y ((φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0) :
    (comm M x).range = fixedSub M (L₁ : Set X) ∧
      Nat.card M = Nat.card (fixedSub M (L₁ : Set X)) ^ 2 := by
  have hk : ∀ g ∈ (toGsp φ hφ).ker, ∀ a : M, g • a = a := by
    intro g hg a
    rw [ker_toGsp] at hg
    exact hker g hg a
  have hΦ := toGsp_surjective φ hφ
  letI : DistribMulAction (Gsp (spForm m K)) M := descendAction (toGsp φ hφ) hΦ hk
  have hsm : ∀ (g : X) (a : M), toGsp φ hφ g • a = g • a := fun g a =>
    descendAction_smul (toGsp φ hφ) hΦ hk g a
  have e1 : fixedSub M ((Lsp (spForm m K) spForm_isAlt u : Subgroup (Gsp (spForm m K))) :
      Set (Gsp (spForm m K))) = fixedSub M (L₁ : Set X) :=
    (fixedSub_descend (toGsp φ hφ) hΦ hk _).trans (fixedSub_viaMatrix_eq φ hφ hker hL₁)
  have e2 : fixedSub M ((Lsp (spForm m K) spForm_isAlt u' : Subgroup (Gsp (spForm m K))) :
      Set (Gsp (spForm m K))) = fixedSub M (L₂ : Set X) :=
    (fixedSub_descend (toGsp φ hφ) hΦ hk _).trans (fixedSub_viaMatrix_eq φ hφ hker hL₂)
  have hx₀ : toGsp φ hφ x ∈ Lsp (spForm m K) spForm_isAlt u := by
    rw [LspGL_eq_matrixOf] at hx
    obtain ⟨_, h⟩ := mem_matrixOf_iff.mp hx
    exact h
  have hn₀ : (toGsp φ hφ x).NonA2 := by
    obtain ⟨y, hy⟩ := hn
    unfold Gsp.NonA2
    exact ⟨y, by rw [toGsp_app]; exact hy⟩
  have hu'u : spForm m K u' u ≠ 0 := by
    rw [← spForm_isAlt.neg_eq u u']
    exact neg_ne_zero.mpr huu'
  have hdec' : IsCompl
      (fixedSub M ((Lsp (spForm m K) spForm_isAlt u' : Subgroup (Gsp (spForm m K))) :
        Set (Gsp (spForm m K))))
      (fixedSub M ((Lsp (spForm m K) spForm_isAlt u : Subgroup (Gsp (spForm m K))) :
        Set (Gsp (spForm m K)))) := by
    rw [e1, e2]
    exact hdec.symm
  have key := stroth_2_1_ii_sp_fixed spForm_isAlt spForm_nondegenerate hu'u h2 hdec' hx₀ hn₀
  have hcomm : comm M (toGsp φ hφ x) = comm M x :=
    AddMonoidHom.ext fun a => by rw [comm_apply, comm_apply, hsm]
  refine ⟨?_, ?_⟩
  · rw [← hcomm, key.2.1, e1]
  · rw [key.2.2, e1]

end CFSG.ClassicalGroups.Symplectic
