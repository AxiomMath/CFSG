module

public import CFSG.Quasithin.AppendixH.H9.H93.H93Defs
public import CFSG.Quasithin.AppendixH.H9.H93.S8Defs

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem isElemAbelian_two_iff_isElemAb2 {G : Type*} [Group G] {E : Subgroup G} :
    IsElemAbelian 2 E ↔ IsElemAb2 E := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨fun a ha b hb => ?_, h⟩
    have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rintro ⟨hc, h⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h⟩

theorem le_of_imgPermOf_le (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A B : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4)
    (h : imgPermOf ψ A ≤ imgPermOf ψ B) : A ≤ B := by
  intro x hx
  have hxM : x ∈ Mg 4 := hA hx
  have hxE : ψ ⟨x, hxM⟩ ∈ imgPermOf ψ A :=
    (mem_imgPermOf ψ).2 ⟨x, hxM, hx, rfl⟩
  obtain ⟨g, hg, hgB, hgx⟩ := (mem_imgPermOf ψ).1 (h hxE)
  have hgm : (⟨g, hg⟩ : ↥(Mg 4)) = ⟨x, hxM⟩ := ψ.injective hgx
  have hgx' : g = x := congrArg Subtype.val hgm
  exact hgx' ▸ hgB

theorem eq_of_imgPermOf_eq (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A B : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) (hB : B ≤ Mg 4)
    (h : imgPermOf ψ A = imgPermOf ψ B) : A = B := by
  exact le_antisymm (le_of_imgPermOf_le ψ hA h.le) (le_of_imgPermOf_le ψ hB h.ge)

theorem exists_le_Mg_imgPermOf_eq (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    (E : Subgroup (Equiv.Perm (Fin 8))) :
    ∃ J : Subgroup (MulAut (PairN 4)), J ≤ Mg 4 ∧ imgPermOf ψ J = E := by
  refine ⟨(E.comap ψ.toMonoidHom).map (Mg 4).subtype,
    Subgroup.map_subtype_le (E.comap ψ.toMonoidHom), ?_⟩
  ext x
  rw [mem_imgPermOf]
  constructor
  · rintro ⟨g, hg, hgJ, hgx⟩
    obtain ⟨m, hm, hgm⟩ := hgJ
    have hcong : (⟨g, hg⟩ : ↥(Mg 4)) = m := Subtype.ext hgm.symm
    have hxm : ψ m = x := (congrArg ψ hcong).symm.trans hgx
    exact hxm ▸ hm
  · intro hx
    refine ⟨↑(ψ.symm x), (ψ.symm x).2, ?_, ?_⟩
    · exact ⟨ψ.symm x, (Subgroup.mem_comap).2 (by simpa using hx), rfl⟩
    · have hcong : (⟨↑(ψ.symm x), (ψ.symm x).2⟩ : ↥(Mg 4)) = ψ.symm x := Subtype.ext rfl
      exact (congrArg ψ hcong).trans (ψ.apply_symm_apply x)

end CFSG.ASVolI.ChH
