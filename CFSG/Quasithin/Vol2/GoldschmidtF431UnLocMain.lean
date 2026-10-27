module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocCore
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutGenC
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo

public section

namespace CFSG.Quasithin.H13.F431.Un

set_option linter.unusedSectionVars false

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.Loc442Q

section Main


variable {D C G : Type} [Group D] [Finite D] [Group C] [Group G] [Finite G] {M1 M2 : Subgroup G}
  {m f : ℕ} (E : LieExt D M1 M2) (ε : D ≃* C)

open scoped Classical in
theorem f431Local_un_of_std {U P P' : Subgroup C} {z t : C} {V4 V Uc R K : Subgroup C}
    (S1 : StdTwo C U P P' z t) (SV : UnStdV C U P P' z t V4) (SL : UnStdLoc C U z t V Uc R K)
    {Q Q' : Subgroup D} (hQ : (Q = E.P1 ∧ Q' = E.P2) ∨ (Q = E.P2 ∧ Q' = E.P1))
    (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P')
    (hU : E.TD.map ε.toMonoidHom = U) (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ E.K)
    (hodd : ¬ 2 ∣ (iK E.toLieAmalgamExt hgen).range.index)
    (hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
      Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨ Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2)
    (hyps : F431Hyps M1 M2 .PSU m f) :
    ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
  set A := E.toLieAmalgamExt with hA
  have H := twoClassD_of_std A ε S1 hQ hQP hQP' hU
  have LK := f431LieK_of_twoClassD A hgen hcen hodd H hag
  have hLie := unLoc442Lie_of_std (A := A) (hgen := hgen) hcen SL hU
  have hnc : ¬ IsConj (lamK A hgen ε z) (lamK A hgen ε t) :=
    not_isConj_iK A hgen hcen H.noconj
  have hzt : lamK A hgen ε z * lamK A hgen ε t = lamK A hgen ε t * lamK A hgen ε z := by
    rw [← map_mul, ← map_mul, SL.comm]
  have hTD : A.TD = U.map ε.symm.toMonoidHom := (map_symm_eq_of_map_eq ε hU).symm
  have hcent : (Subgroup.centralizer ({t} : Set C)).map ε.symm.toMonoidHom =
      Subgroup.centralizer ({ε.symm t} : Set D) := map_centralizer_singleton ε.symm t
  have hsyl0 : IsSylowTwoOf (A.TD ⊓ Subgroup.centralizer ({ε.symm t} : Set D))
      (Subgroup.centralizer ({ε.symm t} : Set D)) := by
    have := isSylowTwoOf_map_inj ε.symm.toMonoidHom ε.symm.injective SL.sylow_t
    rwa [Subgroup.map_inf _ _ _ ε.symm.injective, ← hTD, hcent] at this
  have hSylt := sylow_cent_K A hgen hcen hodd hsyl0
  have hV4T := lamK_V4_le A hgen ε SV hU
  have hV4ab := lamK_V4_ab A hgen ε SV
  have hV4sq := lamK_V4_sq A hgen ε SV
  have hV4u := lamK_V4_unique A hgen hcen ε SV hU
  have hzV4 : lamK A hgen ε z ∈ V4.map (lamK A hgen ε) := ⟨z, SV.V4_zt.1, rfl⟩
  have htV4 : lamK A hgen ε t ∈ V4.map (lamK A hgen ε) := ⟨t, SV.V4_zt.2, rfl⟩
  have hmemI : ∀ i ∈ ({iK A hgen (ε.symm z), iK A hgen (ε.symm t)} : Finset ↥A.K),
      i = iK A hgen (ε.symm z) ∨ i = iK A hgen (ε.symm t) := by
    intro i hi
    rwa [Finset.mem_insert, Finset.mem_singleton] at hi
  have hI : ({iK A hgen (ε.symm z), iK A hgen (ε.symm t)} : Finset ↥A.K) =
      {lamK A hgen ε z, lamK A hgen ε t} := rfl
  refine ⟨A.TD.map (iK A hgen), {iK A hgen (ε.symm z), iK A hgen (ε.symm t)},
    iK A hgen (ε.symm z), LK, ?_⟩
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hzZ := lamK_z_mem_centerOf_perfectCore A hgen hcen ε hodd (Mb1_inf_range A hgen) SV hQP
    have hV4e := lamK_V4_eq A hgen hcen ε hodd SV (Mb2_inf_range A hgen) hQP'
    have cz := cent_le_Mb1 A hgen hcen ((centralizer_le_transport ε hQP z).mpr SV.cz) H.aut_z
    have ct := cent_le_Mb2 A hgen hcen ((centralizer_le_transport ε hQP' t).mpr SV.ct) H.aut_t
    obtain ⟨hnf, hb1, hbt⟩ := un_local_core LK (UnGSetup.of_hyps hyps E) hI hzt cz ct hSylt hzZ
      hV4T hV4ab hV4sq hV4e hV4u hzV4 htV4 hnc hLie
    refine ⟨hnfI_of_hnf hnf, ?_, ?_⟩
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact hb1
      · exact absurd ((centralizer_le_transport ε hQP t).mp (cent_le_P1_of_Mb1 A hgen hc)) SV.nt
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact absurd ((centralizer_le_transport ε hQP' z).mp (cent_le_P2_of_Mb2 A hgen hc)) SV.nz
      · exact hbt
  · have hzZ := lamK_z_mem_centerOf_perfectCore A hgen hcen ε hodd (Mb2_inf_range A hgen) SV hQP
    have hV4e := lamK_V4_eq A hgen hcen ε hodd SV (Mb1_inf_range A hgen) hQP'
    have cz := cent_le_Mb2 A hgen hcen ((centralizer_le_transport ε hQP z).mpr SV.cz) H.aut_z
    have ct := cent_le_Mb1 A hgen hcen ((centralizer_le_transport ε hQP' t).mpr SV.ct) H.aut_t
    obtain ⟨hnf, hb1, hbt⟩ := un_local_core (swapLieK LK) (UnGSetup.of_hyps_symm hyps E) hI hzt
      cz ct hSylt hzZ hV4T hV4ab hV4sq hV4e hV4u hzV4 htV4 hnc hLie
    rw [amalgamMap_swap E.comp] at hnf hb1 hbt
    refine ⟨hnfI_of_hnf hnf, ?_, ?_⟩
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact absurd ((centralizer_le_transport ε hQP' z).mp (cent_le_P1_of_Mb1 A hgen hc)) SV.nz
      · exact hbt
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact hb1
      · exact absurd ((centralizer_le_transport ε hQP t).mp (cent_le_P2_of_Mb2 A hgen hc)) SV.nt

end Main

end CFSG.Quasithin.H13.F431.Un
