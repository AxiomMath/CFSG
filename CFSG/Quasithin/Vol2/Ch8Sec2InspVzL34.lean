module

public import CFSG.Quasithin.Vol2.Ch8Sec2InspDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2InspVzL34Std

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.ZTrans
  CFSG.Quasithin.H13.VzL34 CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.H.L3W9
  CFSG.Quasithin.H13.Ch9.Herm9 Equiv

theorem vzModL34_holds : VzModL34 := by
  intro V _ _ H z hBN hz1 hS
  obtain ⟨S, hSH, hSc, hzS⟩ := hS
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 hBN hz1 hSH hSc hzS
  have hP : (parz82 H z).map (congrHom e) = L34 := by
    have h : (parZ H z).map (congrHom e) = parZ img9 z0 := by
      rw [← he, ← hez]
      exact parZ_map e H z
    rw [parZ_std] at h
    exact h
  have hR : (radz82 H z).map (congrHom e) = Rbar := by
    have h : (radZ H z).map (congrHom e) = radZ img9 z0 := by
      rw [← he, ← hez]
      exact radZ_map e H z
    rw [radZ_std] at h
    exact h
  have hW : (vz82 H z).map e.toMonoidHom = W0 := by
    have h : (vZ H z).map e.toMonoidHom = vZ img9 z0 := by
      rw [← he, ← hez]
      exact vZ_map e H z
    rw [vZ_std] at h
    exact h
  have hmem : ∀ p : ↥(parz82 H z), congrHom e (p : MulAut V) ∈ L34 := fun p => by
    rw [← hP]
    exact Subgroup.mem_map_of_mem _ p.2
  let φV : ↥(parz82 H z) →* ↥L34 :=
    MonoidHom.codRestrict ((congrHom e).comp (parz82 H z).subtype) L34 hmem
  have hφV : ∀ p : ↥(parz82 H z), ((φV p : ↥L34) : MulAut W9) = congrHom e (p : MulAut V) :=
    fun p => rfl
  refine ⟨vzL34Alpha.comp φV, vzL34Hom.comp e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    obtain ⟨φ, hφ⟩ := vzL34Alpha_surj x
    have hφ' : (φ : MulAut W9) ∈ (parz82 H z).map (congrHom e) := by
      rw [hP]; exact φ.2
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.1 hφ'
    refine ⟨⟨p, hp⟩, ?_⟩
    have : φV ⟨p, hp⟩ = φ := Subtype.ext hpe
    simp only [MonoidHom.comp_apply, this, hφ]
  ·
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      vzL34Alpha_eq_one_iff, hφV, ← hR]
    exact Subgroup.mem_map_iff_mem (congrHom_injective e)
  ·
    intro y
    obtain ⟨w, hw⟩ := vzL34Hom_surj y
    exact ⟨e.symm w, by simpa using hw⟩
  ·
    ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, vzL34Hom_eq_one_iff, ← hW]
    exact Subgroup.mem_map_iff_mem e.injective
  ·
    intro p v i
    have key := vzL34Alpha_acts (φV p) (e v)
    have hev : ((φV p : ↥L34) : MulAut W9) (e v) = e ((p : MulAut V) v) := by
      rw [hφV]
      show e ((p : MulAut V) (e.symm (e v))) = e ((p : MulAut V) v)
      rw [MulEquiv.symm_apply_apply]
    show vzL34Val (e ((p : MulAut V) v)) i = vzL34Val (e v) _
    rw [← hev, key]
    rfl

end CFSG.Quasithin.H13
