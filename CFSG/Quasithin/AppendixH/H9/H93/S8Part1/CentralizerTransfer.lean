module

public import CFSG.Quasithin.AppendixH.H9.H93.PsiSign

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem imgPermOf_Lg_inf_centralizer (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {t : MulAut (PairN 4)} (ht : t ∈ Mg 4) :
    imgPermOf ψ (Lg 4 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 4)))) =
      alternatingGroup (Fin 8) ⊓
        Subgroup.centralizer ({psiExt ψ t} : Set (Equiv.Perm (Fin 8))) := by
  ext σ
  rw [mem_imgPermOf]
  constructor
  · rintro ⟨g, hg, hgK, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      have h := (mem_Lg_iff_sign ψ hg).1 (Subgroup.mem_inf.1 hgK).1
      rwa [psiExt_of_mem ψ hg] at h
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hgK).2 t rfl
      rw [psiExt_of_mem ψ ht, ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hc)
  · intro hσ
    obtain ⟨hσA, hσC⟩ := Subgroup.mem_inf.1 hσ
    refine ⟨(ψ.symm σ : MulAut (PairN 4)), (ψ.symm σ).2, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [mem_Lg_iff_sign ψ (ψ.symm σ).2, psiExt_coe, MulEquiv.apply_symm_apply]
      exact Equiv.Perm.mem_alternatingGroup.1 hσA
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hc := Subgroup.mem_centralizer_iff.1 hσC (psiExt ψ t) rfl
      rw [psiExt_of_mem ψ ht] at hc
      have h3 : (⟨t, ht⟩ : ↥(Mg 4)) * ψ.symm σ = ψ.symm σ * ⟨t, ht⟩ := by
        have h4 := congrArg ψ.symm hc
        rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h4
      exact congrArg Subtype.val h3
    · exact MulEquiv.apply_symm_apply ψ σ

theorem nonempty_mulEquiv_Lg_centralizer (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {t : MulAut (PairN 4)} (ht : t ∈ Mg 4) :
    Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 4)))) ≃*
      ↥(alternatingGroup (Fin 8) ⊓
        Subgroup.centralizer ({psiExt ψ t} : Set (Equiv.Perm (Fin 8))))) := by
  have hK : Lg 4 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 4))) ≤ Mg 4 :=
    inf_le_left.trans Lg_le_Mg
  exact ⟨((Subgroup.subgroupOfEquivOfLe hK).symm.trans (MulEquiv.subgroupMap ψ _)).trans
    (MulEquiv.subgroupCongr (imgPermOf_Lg_inf_centralizer ψ ht))⟩

end CFSG.ASVolI.ChH
