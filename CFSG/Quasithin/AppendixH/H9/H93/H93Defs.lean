module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] noncomputable def imgPermOf (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    (A : Subgroup (MulAut (PairN 4))) : Subgroup (Equiv.Perm (Fin 8)) :=
  (A.subgroupOf (Mg 4)).map ψ.toMonoidHom

@[expose] noncomputable def psiExt (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    (t : MulAut (PairN 4)) : Equiv.Perm (Fin 8) :=
  open Classical in if h : t ∈ Mg 4 then ψ ⟨t, h⟩ else 1

theorem psiExt_of_mem (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {t : MulAut (PairN 4)} (ht : t ∈ Mg 4) :
    psiExt ψ t = ψ ⟨t, ht⟩ := by
  unfold psiExt
  rw [dif_pos ht]

theorem mem_imgPermOf (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {A : Subgroup (MulAut (PairN 4))}
    {x : Equiv.Perm (Fin 8)} :
    x ∈ imgPermOf ψ A ↔ ∃ (g : MulAut (PairN 4)) (hg : g ∈ Mg 4), g ∈ A ∧ ψ ⟨g, hg⟩ = x := by
  unfold imgPermOf
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨⟨g, hg⟩, hgA, rfl⟩
    exact ⟨g, hg, hgA, rfl⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨⟨g, hg⟩, hgA, rfl⟩

theorem imgPermOf_mono (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {A B : Subgroup (MulAut (PairN 4))}
    (h : A ≤ B) : imgPermOf ψ A ≤ imgPermOf ψ B := by
  intro x hx
  obtain ⟨g, hg, hgA, rfl⟩ := (mem_imgPermOf ψ).1 hx
  exact (mem_imgPermOf ψ).2 ⟨g, hg, h hgA, rfl⟩

@[expose] def IsTvElt (g : MulAut (PairN 4)) : Prop :=
  g ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers g)) = 1

end CFSG.ASVolI.ChH
