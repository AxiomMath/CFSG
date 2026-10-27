module

public import CFSG.Quasithin.AppendixH.H12.ModelAct
public import CFSG.Quasithin.AppendixH.H12.GroupStructure

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsExtOf IsIntDirect cenIn ptStab)

theorem card_vecStab_five : Nat.card (vecStab 5) = 1920 := by
  rw [vecStab_five]
  exact H12Cert.card_S0

theorem card_ptStab_five :
    Nat.card (ptStab glHom G0 (ptSub 5)) = 5760 := by
  rw [card_ptStab (c := 5) (by norm_num) (by norm_num), card_vecStab_five]

@[expose] def planes5Gen (i : ℕ) : List ℕ := planes5.getD i []

theorem planes5Gen_valid : ∀ i < 5, ∀ c ∈ planes5Gen i, c < 4096 := by
  intro i hi c hc
  have hmem : planes5Gen i ∈ planes5 := by
    rw [planes5Gen, List.getD_eq_getElem planes5 [] (by simpa [planes5_length] using hi)]
    exact List.getElem_mem _
  exact planes_valid _ (planes5_mem_planes _ hmem).1 c hc

theorem planes5Gen_inj :
    ∀ i < 5, ∀ j < 5, spanSub (planes5Gen i) = spanSub (planes5Gen j) → i = j := by
  intro i hi j hj h
  have h' : (⟨i, hi⟩ : Fin 5) = ⟨j, hj⟩ := planes5_inj h
  exact Fin.ext_iff.mp h'

theorem exists_p5 : ∃ π : ↥(vecStab 5) →* Equiv.Perm (Fin 5), ∀ (g : ↥(vecStab 5)) (i : Fin 5),
    smulSub (g : Γ12) (spanSub (planes5Gen i)) = spanSub (planes5Gen (π g i)) := by
  refine exists_actHom (n := 5) (vecStab 5) planes5Gen planes5Gen_inj ?_
  intro g hg i hi
  have hgG0 : (g : Γ12) ∈ G0 := vecStab_le_G0 5 hg
  have hg5 : gmv (g : Γ12) 5 = 5 :=
    ((mem_vecStab_iff (by norm_num) (g : Γ12)).mp hg).2
  have hbmem5 : planes5Gen i ∈ planes5 := by
    rw [planes5Gen, List.getD_eq_getElem planes5 [] (by simpa [planes5_length] using hi)]
    exact List.getElem_mem _
  have hbplanes : planes5Gen i ∈ planes := (planes5_mem_planes _ hbmem5).1
  have h5b : 5 ∈ spanN (planes5Gen i) := (planes5_mem_planes _ hbmem5).2
  obtain ⟨b', hb'planes, hb'eq⟩ := planes_closed hgG0 hbplanes
  have h5b' : 5 ∈ spanN b' := by
    have hdc : dc 5 ∈ spanSub (planes5Gen i) :=
      (dc_mem_spanSub_iff (planes_valid _ hbplanes) (by norm_num)).mpr h5b
    have himg : glHom (g : Γ12) (dc 5) ∈ smulSub (g : Γ12) (spanSub (planes5Gen i)) :=
      Subgroup.mem_map_of_mem (glHom (g : Γ12)).toMonoidHom hdc
    rw [hb'eq] at himg
    have hgl : glHom (g : Γ12) (dc 5) = dc 5 := by
      rw [glHom_dc]
      exact congrArg dc hg5
    rw [hgl] at himg
    exact (dc_mem_spanSub_iff (planes_valid b' hb'planes) (by norm_num)).mp himg
  obtain ⟨b'', hb''5, hb''eq⟩ := planes5_complete hb'planes h5b'
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb''5
  have hj5 : j < 5 := by simpa [planes5_length] using hj
  refine ⟨j, hj5, ?_⟩
  calc smulSub (g : Γ12) (spanSub (planes5Gen i))
      = spanSub b' := hb'eq
    _ = spanSub b'' := hb''eq
    _ = spanSub (planes5Gen j) := by
        rw [planes5Gen, List.getD_eq_getElem planes5 []
          (by simpa [planes5_length] using hj5), ← hjb]

noncomputable def p5 : ↥(vecStab 5) →* Equiv.Perm (Fin 5) := Classical.choose exists_p5

theorem p5_spec (g : ↥(vecStab 5)) (i : Fin 5) :
    smulSub (g : Γ12) (spanSub (planes5Gen i)) = spanSub (planes5Gen (p5 g i)) :=
  Classical.choose_spec exists_p5 g i

@[expose] def s120 : List (List ℕ) := [
    [],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0,
     1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
     1], [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0,
     1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
     1, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
     0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1,
     1], [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0,
     1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
     0, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
     1], [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
     0, 1], [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
     0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0,
     1, 1, 1], [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
     1],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1,
     0, 1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
     1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
     0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0,
     1], [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
     1], [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1,
     0, 1], [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1,
     1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
     1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
     0, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
     1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0,
     1], [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
     1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
     1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
     1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
     1], [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
     0, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0,
     1], [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0,
     1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0,
     1], [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]]

theorem s120_length : s120.length = 120 := by
  decide

set_option maxRecDepth 200000 in
theorem tU_s120_mem : ∀ w ∈ s120, tU w ∈ vecStab 5 := by
  have h : s120.all (fun w => mvN (tW w) 5 == 5) = true := by decide +kernel
  intro w hw
  rw [tU_mem_vecStab_iff (by norm_num)]
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

set_option maxRecDepth 200000 in
theorem s120_sig_nodup : (s120.map (sigOf planes5Gen 5)).Nodup := by
  decide +kernel

theorem p5_range : 120 ≤ Nat.card p5.range := by
  have h := length_le_card_range_of_sig p5 planes5Gen planes5Gen_valid p5_spec
    s120 tU_s120_mem s120_sig_nodup
  rw [s120_length] at h
  exact h

@[expose] def sker : List (List ℕ) := [
    [], [0], [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
     1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
     1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,
     1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,
     1, 0, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
     1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
     1, 0, 1, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
     0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
     1, 1, 1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
     0, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
     1, 1, 1, 0, 1, 1, 1, 0]]

theorem sker_length : sker.length = 16 := by
  decide

set_option maxRecDepth 200000 in
theorem sker_tW_nodup : (sker.map tW).Nodup := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem tU_sker_ker : ∀ w ∈ sker, ∃ h : tU w ∈ vecStab 5, p5 ⟨tU w, h⟩ = 1 := by
  have h5 : sker.all (fun w => mvN (tW w) 5 == 5) = true := by decide +kernel
  have hfix : sker.all (fun w => (List.range 5).all (fun i =>
      spanMask ((planes5Gen i).map (mvN (tW w))) == spanMask (planes5Gen i))) = true := by
    decide +kernel
  intro w hw
  have hw5 : mvN (tW w) 5 = 5 := beq_iff_eq.mp (List.all_eq_true.mp h5 w hw)
  have h : tU w ∈ vecStab 5 := (tU_mem_vecStab_iff (by norm_num) w).mpr hw5
  refine ⟨h, ?_⟩
  refine actHom_tU_eq_one p5 planes5Gen planes5Gen_valid planes5Gen_inj p5_spec h ?_
  intro i hi
  have hwi := List.all_eq_true.mp hfix w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp hwi i (List.mem_range.mpr hi))

noncomputable abbrev R5 : Subgroup Γ12 := p5.ker.map (vecStab 5).subtype

theorem R5_le : R5 ≤ vecStab 5 := by
  exact Subgroup.map_subtype_le p5.ker

theorem card_R5_ge : 16 ≤ Nat.card R5 := by
  have hcard : Nat.card R5 = Nat.card p5.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (vecStab 5))
  rw [hcard]
  have h := length_le_card_ker_of_words p5 sker sker_tW_nodup tU_sker_ker
  rw [sker_length] at h
  exact h

theorem p5_R5 : ∀ r (hr : r ∈ R5), p5 ⟨r, R5_le hr⟩ = 1 := by
  intro r hr
  obtain ⟨x, hxker, hxr⟩ := Subgroup.mem_map.mp hr
  have heq : (⟨r, R5_le hr⟩ : ↥(vecStab 5)) = x := Subtype.ext hxr.symm
  rw [heq]
  exact hxker

theorem structure_X5 :
    Nat.card R5 = 16 ∧ IsPGroup 2 R5 ∧ pCoreOf 2 (vecStab 5) = R5 ∧
      IsExtOf (vecStab 5) (pCoreOf 2 (vecStab 5)) (Equiv.Perm (Fin 5)) := by
  exact structure_S5 (X := vecStab 5) (R := R5) (by rw [card_vecStab_five]) R5_le
    card_R5_ge p5 p5_R5 p5_range

theorem R5_mem_words : ∀ q ∈ R5, q ∈ sker.map tU := by
  have hnd : (sker.map tU).Nodup := by
    refine List.Nodup.of_map (f := fun u : Γ12 =>
      colsN ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) ?_
    have heq : (sker.map tU).map (fun u : Γ12 =>
        colsN ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) = sker.map tW := by
      rw [List.map_map]
      exact List.map_congr_left (fun w _ => colsN_tU w)
    rw [heq]
    exact sker_tW_nodup
  have hmem : ∀ x ∈ sker.map tU, x ∈ R5 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h, hp⟩ := tU_sker_ker w hw
    exact Subgroup.mem_map.mpr ⟨⟨tU w, h⟩, hp, rfl⟩
  have hc : Nat.card R5 ≤ (sker.map tU).length := by
    rw [structure_X5.1, List.length_map, sker_length]
  exact mem_of_card_le_length R5 (sker.map tU) hnd hmem hc

private theorem tU_append (w w' : List ℕ) : tU (w ++ w') = tU w * tU w' := by
  simp only [tU, List.map_append, List.prod_append]

private theorem tU_nil : tU ([] : List ℕ) = 1 := by
  simp only [tU, List.map_nil, List.prod_nil]

private theorem tW_append (w w' : List ℕ) : tW (w ++ w') = mulN (tW w) (tW w') := by
  have h := congrArg (fun u : Γ12 =>
    colsN ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) (tU_append w w')
  simpa only [colsN_tU, Units.val_mul, colsN_mul] using h

private def skerT : List (List ℕ) := sker.map tW

set_option maxRecDepth 200000 in
theorem R5_isElemAbelian : IsElemAbelian 2 R5 := by
  have hcommall : skerT.all (fun a => skerT.all (fun b =>
      mulN a b == mulN b a)) = true := by
    decide +kernel
  have hsqall : skerT.all (fun a => mulN a a == tW []) = true := by
    decide +kernel
  have hcomm : ∀ a ∈ sker.map tU, ∀ b ∈ sker.map tU, a * b = b * a := by
    intro a ha b hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hb
    have hm : tW (w ++ w') = tW (w' ++ w) := by
      rw [tW_append, tW_append]
      exact beq_iff_eq.mp (List.all_eq_true.mp
        (List.all_eq_true.mp hcommall (tW w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
        (tW w') (List.mem_map.mpr ⟨w', hw', rfl⟩))
    rw [← tU_append, ← tU_append]
    exact tU_eq_of_tW_eq hm
  have hsq : ∀ a ∈ sker.map tU, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    have hm : tW (w ++ w) = tW [] := by
      rw [tW_append]
      exact beq_iff_eq.mp (List.all_eq_true.mp hsqall (tW w)
        (List.mem_map.mpr ⟨w, hw, rfl⟩))
    rw [pow_two, ← tU_append, tU_eq_of_tW_eq hm, tU_nil]
  exact isElemAbelian_of_list R5 (sker.map tU) R5_mem_words hcomm hsq

theorem clause4_N_part
    (hZ : (Subgroup.center ↥G0).map G0.subtype = Subgroup.zpowers zU) :
    ∃ X : Subgroup Γ12, IsIntDirect (ptStab glHom G0 (ptSub 5)) X
        ((Subgroup.center ↥G0).map G0.subtype) ∧
      IsElemAbelian 2 (pCoreOf 2 X) ∧ Nat.card ↥(pCoreOf 2 X) = 16 ∧
      IsExtOf X (pCoreOf 2 X) (Equiv.Perm (Fin 5)) := by
  refine ⟨vecStab 5, ?_, ?_, ?_, ?_⟩
  · rw [hZ]
    exact isIntDirect_ptStab (c := 5) (by norm_num) (by norm_num)
  · rw [structure_X5.2.2.1]
    exact R5_isElemAbelian
  · rw [structure_X5.2.2.1]
    exact structure_X5.1
  · exact structure_X5.2.2.2

end CFSG.Quasithin.AppendixH.H12.Model
