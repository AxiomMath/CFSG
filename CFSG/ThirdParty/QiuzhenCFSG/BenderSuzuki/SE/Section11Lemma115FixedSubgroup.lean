module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Subgroup

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the fixed subgroup in `C_X(tu)`

The source identifies the Peterfalvi fixed factor of `C_X(tu)` with the
already selected subgroup `V = C_D(t) = C_D(u)`.  This is an elementary
centralizer calculation, using only strong embedding for the inclusion into
`M` and the `Lemma83Data.centralizer_eq` identity for the reverse inclusion.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- `C_{C_X(tu)}(t)` is the selected Peterfalvi fixed subgroup `V`. -/
public theorem lemma115_peterfalviV_centralizer_tu_eq
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t)
    (d83 : Lemma83Data M t) :
    peterfalviV (Subgroup.centralizer ({t * d83.u} : Set X)) t =
      peterfalviV (M ⊓ rightConjugate M t) t := by
  apply le_antisymm
  · intro x hx
    have hxt : Commute x t :=
      Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxtu : Commute x (t * d83.u) :=
      Subgroup.mem_centralizer_singleton_iff.mp hx.1
    have hxu : Commute x d83.u := by
      have htu : Commute x (t⁻¹ * (t * d83.u)) :=
        hxt.inv_right.mul_right hxtu
      simpa [mul_assoc] using htu
    have hxuM : x ∈ M :=
      hM.centralizer_le d83.u_mem_M d83.u_involution
        (Subgroup.mem_centralizer_singleton_iff.mpr hxu)
    have hxtM : x ∈ rightConjugate M t := by
      have hxconj := rightConjugateElem_mem_rightConjugate
        (g := t) hxuM
      have hconj : rightConjugateElem x t = x := by
        change t⁻¹ * x * t = x
        rw [ht.inv_eq_self, ← hxt.eq]
        calc
          x * t * t = x * (t * t) := by group
          _ = x := by
            rw [show t * t = 1 by simpa [pow_two] using ht.sq_eq_one]
            simp
      simpa [hconj] using hxconj
    exact ⟨⟨hxuM, hxtM⟩, hx.2⟩
  · intro x hx
    have hxD : x ∈ M ⊓ rightConjugate M t := hx.1
    have hxt : x ∈ Subgroup.centralizer ({t} : Set X) := hx.2
    have hxU : x ∈ Subgroup.centralizer ({d83.u} : Set X) := by
      have hxEq : x ∈
          (M ⊓ rightConjugate M t) ⊓
            Subgroup.centralizer ({t} : Set X) := ⟨hxD, hxt⟩
      have hxEq' := d83.centralizer_eq ▸ hxEq
      exact hxEq'.2
    have hxtu : x ∈ Subgroup.centralizer ({t * d83.u} : Set X) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hxt' := Subgroup.mem_centralizer_singleton_iff.mp hxt
      have hxu' := Subgroup.mem_centralizer_singleton_iff.mp hxU
      calc
        x * (t * d83.u) = (x * t) * d83.u := by group
        _ = (t * x) * d83.u := by rw [hxt']
        _ = t * (x * d83.u) := by group
        _ = t * (d83.u * x) := by rw [hxu']
        _ = (t * d83.u) * x := by group
    exact ⟨hxtu, hxt⟩

end CFSG.BenderSuzuki
