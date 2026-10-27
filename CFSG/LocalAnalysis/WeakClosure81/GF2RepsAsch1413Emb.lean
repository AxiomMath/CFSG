module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.ConjNormalFaithful

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem a1413_embedding {Q : Type} [Group Q] {L : Subgroup Q} (hLn : L.Normal)
    (hc : centralizer (L : Set Q) ≤ L) {P : Type} [Group P] (e : ↥L ≃* P)
    (hP : Subgroup.center P = ⊥) :
    ∃ θ : Q →* MulAut P, Function.Injective θ ∧
      (∀ l : ↥L, θ (l : Q) = MulAut.conj (e l)) ∧
      (∀ (q : Q) (l : ↥L), θ q (e l) = e ⟨q * l * q⁻¹, hLn.conj_mem _ l.2 q⟩) ∧
      (∀ q : Q, q ∈ L ↔ θ q ∈ inner P) ∧ inner P ≤ θ.range := by
  haveI := hLn
  let θ₁ : Q →* MulAut ↥L := MulAut.conjNormal
  let θ : Q →* MulAut P := (MulAut.congr e).toMonoidHom.comp θ₁
  have hZL : Subgroup.center ↥L = ⊥ := by
    have hmap : (Subgroup.center ↥L).map e.toMonoidHom = ⊥ := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e, hP]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) e.injective).mp hmap
  have hconj : ∀ l : ↥L, θ (l : Q) = MulAut.conj (e l) := by
    intro l
    change (MulAut.congr e) (MulAut.conjNormal (l : Q)) = MulAut.conj (e l)
    rw [MulAut.conjNormal_val,
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have happ : ∀ (q : Q) (l : ↥L),
      θ q (e l) = e ⟨q * l * q⁻¹, hLn.conj_mem _ l.2 q⟩ := by
    intro q l
    change e (MulAut.conjNormal q (e.symm (e l))) = e ⟨q * l * q⁻¹, _⟩
    rw [e.symm_apply_apply]
    exact congrArg e (Subtype.ext (MulAut.conjNormal_apply q l))
  have hinj : Function.Injective θ :=
    (MulAut.congr e).injective.comp
      (Subgroup.conjNormal_injective_of_centralizer_le (N := L) hc hZL)
  have hinner : ∀ q : Q, q ∈ L ↔
      θ q ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P := by
    intro q
    constructor
    · intro hq
      exact ⟨e ⟨q, hq⟩, (hconj ⟨q, hq⟩).symm⟩
    · rintro ⟨g, hg⟩
      have hgl : (e.symm g : Q) = q := by
        apply hinj
        rw [hconj (e.symm g), e.apply_symm_apply, hg]
      exact hgl ▸ (e.symm g).2
  have hle : CFSG.ComponentClassification.OuterAutomorphisms.inner P ≤ θ.range := by
    rintro x ⟨g, hg⟩
    rw [← hg]
    exact ⟨(e.symm g : ↥L), by rw [hconj (e.symm g), e.apply_symm_apply]⟩
  exact ⟨θ, hinj, hconj, happ, hinner, hle⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
