module

public import CFSG.Quasithin.AppendixH.Common.OctadPtStab

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem mem_iff_of_mem_octStab {O : Finset (Fin 24)} {g : S24} (hg : g ∈ octStab O)
    (i : Fin 24) : g i ∈ O ↔ i ∈ O := by
  have hfix : g • O = O := (mem_octStab_iff.mp hg).2
  have h := Finset.smul_mem_smul_finset_iff (s := O) g (b := i)
  rw [hfix] at h
  exact h

@[expose] def octAct (O : Finset (Fin 24)) : ↥(octStab O) →* Equiv.Perm ↥O where
  toFun g := (g : S24).subtypePerm fun i => mem_iff_of_mem_octStab g.2 i
  map_one' := by
    ext
    rfl
  map_mul' := by
    intro g h
    ext
    rfl

theorem octAct_apply {O : Finset (Fin 24)} (g : ↥(octStab O)) (i : ↥O) :
    ((octAct O g i : ↥O) : Fin 24) = (g : S24) i := rfl

theorem ker_octAct (O : Finset (Fin 24)) :
    (octAct O).ker = (octFix O).subgroupOf (octStab O) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_octFix_iff]
  constructor
  · intro h
    refine ⟨(mem_octStab_iff.mp g.2).1, fun i hi => ?_⟩
    show (g : S24) i = i
    have h1 := congrArg (fun f : Equiv.Perm ↥O => ((f ⟨i, hi⟩ : ↥O) : Fin 24)) h
    exact h1
  · rintro ⟨_, hfix⟩
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show (g : S24) x.1 = x.1
    exact hfix x.1 x.2

end CFSG.ASVolI.AppH
