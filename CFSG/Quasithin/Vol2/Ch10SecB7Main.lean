module

public import CFSG.Quasithin.Vol2.Ch10SecB7Aux
public import CFSG.Quasithin.Vol2.Ch10SecD213
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem four_lt_rParam (hF : Fact10_2_7Six) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1026 : Stmt10_2_6) (h63 : ASInputs.AS_E_6_3)
    (h612 : ASInputs.AS_E_6_12) (hyp : Hyp10 G T L I) (h6 : Case10_1_1Six T L I) :
    (4 : ℕ∞) < E3.rParam (fsuVM T L I) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hNV := SecA.normalizer_fsuVM_eq hyp (fsuM_isMaxTwoLocal h331 hyp)
  obtain ⟨e1, e2, -, -, e5, -⟩ := six_facts hF h37 h38 h1011 hyp h6 hV ht htn
  have h61 := hypE61_of h331 h1012 hyp h6
  have hr4 : (4 : ℕ∞) ≤ E3.rParam (fsuVM T L I) := by
    have := (h63 G T (fsuM T L) (fsuVM T L I) hV h61 (by rw [e2]; norm_num)).1
    rw [e2] at this
    exact_mod_cast this
  refine lt_of_le_of_ne hr4 fun h4 => ?_
  have hex : ∃ U : Subgroup G, U ≤ fsuVM T L I ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (fsuVM T L I : Set G) ∧
      E3.mQuot (fsuVM T L I) U = 4 := by
    by_contra hne
    have h5 : (5 : ℕ∞) ≤ E3.rParam (fsuVM T L I) := by
      unfold E3.rParam
      refine le_iInf₂ fun U hU => ?_
      have h1 := E3.rParam_le_mQuot hU.1 hU.2
      rw [← h4] at h1
      have h1' : 4 ≤ E3.mQuot (fsuVM T L I) U := by exact_mod_cast h1
      have h2 : E3.mQuot (fsuVM T L I) U ≠ 4 := fun h => hne ⟨U, hU.1, hU.2, h⟩
      exact_mod_cast (show 5 ≤ E3.mQuot (fsuVM T L I) U by omega)
    rw [← h4] at h5
    exact absurd h5 (by norm_num)
  obtain ⟨U, hUV, hUC, hU4⟩ := hex
  have hUC' : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := by rwa [hNV] at hUC
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    rw [E3.mQuot_bot_eq_rk] at hU4
    have e1' : rk ↥(fsuVM T L I) = 24 := e1
    omega
  by_cases hCM : fsuM T L ⊓ Subgroup.centralizer (U : Set G) =
      fsuM T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G)
  · have h1 := (h612 G T (fsuM T L) (fsuVM T L I) U h61 hU0 hUV hCM hUC').2
    rw [h1] at h4
    exact absurd h4 (by norm_num)
  have hle : fsuM T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤
      fsuM T L ⊓ Subgroup.centralizer (U : Set G) :=
    inf_le_inf_left _ fun x hx => Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp hx u (hUV hu)
  obtain ⟨x, ⟨hxM, hxU⟩, hxV⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hle (Ne.symm hCM))
  have hxC : x ∉ Subgroup.centralizer (fsuVM T L I : Set G) := fun h => hxV ⟨hxM, h⟩
  have hxN : x ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I hxM
  have hxbM : convI hV ⟨x, hxN⟩ ∈ autI hV (fsuM T L) := convI_mem_autI hV hxM hxN
  have hxb1 : convI hV ⟨x, hxN⟩ ≠ 1 := fun h => hxC ((convI_eq_one_iff hV _).mp h)
  have hUfix : modSub hV U ≤ fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩)) := by
    intro w hw φ hφ
    have hst : convI hV ⟨x, hxN⟩ ∈ MulAction.stabilizer (MulAut (IntMod (fsuVM T L I) hV)) w := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact convI_fix hV hxU hw
    have h2 := Subgroup.zpowers_le.mpr hst hφ
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
  have hrkU : rkIdx (modSub hV U) = 4 := by
    rw [E3.rkIdx_eq_mQuot_map hV, Subgroup.map_comap_eq, range_valHom, inf_eq_right.mpr hUV, hU4]
  have hfix4 : rkIdx (fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩))) ≤ 4 :=
    (rkIdx_anti hUfix).trans hrkU.le
  obtain ⟨hord, hWi⟩ := e5 _ hxbM hxb1 hfix4
  have hm4 : 4 ≤ rkIdx (fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩))) := by
    rw [← e2]
    refine E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.mpr hxbM) ?_
      (fun h => hxb1 (Subgroup.zpowers_eq_bot.mp h))
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hUeq : modSub hV U = fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩)) := by
    refine eq_of_le_of_rk_le (fun w => IntMod.sq_eq_one w) hUfix ?_
    have h1 := rk_add_rkIdx (modSub hV U)
    have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩)))
    omega
  rw [← hUeq] at hWi
  have hLM : L ≤ fsuM T L := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
  have hLtM : CFSG.conjugate L t ≤ fsuM T L :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)
  obtain ⟨K, hK, hKM, hKU⟩ : ∃ K : Subgroup G, IsLi T L K ∧ K ≤ fsuM T L ∧
      ⁅fsuVM T L I, K⁆ ≤ U := by
    rcases hWi with h | h
    · exact ⟨L, Or.inl rfl, hLM, le_of_modSub_le hV (commutator_le_fsuVM hLM) h⟩
    · exact ⟨_, Or.inr ⟨t, ht, htn, rfl⟩, hLtM, le_of_modSub_le hV (commutator_le_fsuVM hLtM) h⟩
  apply hUC'
  refine le_trans (fun y hy => Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_iff.mp hy v (hKU hv)) ?_
  exact (Subgroup.centralizer_le_normalizer _).trans ((h1026 G T L I hyp).2.1 K hK)

theorem commutator_le_normalizer_conj {V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVK : ⁅V, K⁆ ≤ V) {g : G} (hr : (4 : ℕ∞) < E3.rParam V)
    (hmA : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) = 2)
    (hq : E3.mQuot (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))
      (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ⊓
        fixingSubgroup (MulAut (IntMod V hV)) (modSub hV ⁅V, K⁆ : Set (IntMod V hV))) ≤ 2) :
    ⁅V, K⁆ ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hAN : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (V : Set G) := inf_le_right
  rw [E3.mQuot_autI_preI hV hAN inf_le_left, preI_inf_fixingSubgroup hV hAN hVK] at hq
  have hBA : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer ((⁅V, K⁆ : Subgroup G) : Set G) ≤
        conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) :=
    inf_le_left
  have hm := E3.mQuot_add hBA inf_le_left
  rw [hmA] at hm
  have hlt : (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer ((⁅V, K⁆ : Subgroup G) : Set G)) : ℕ∞) <
        E3.rParam (conjSubgroup V g) := by
    rw [E3.rParam_conj]
    refine lt_of_le_of_lt ?_ hr
    exact_mod_cast (show _ ≤ 4 by omega)
  have hC : Subgroup.centralizer ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer ((⁅V, K⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (conjSubgroup V g : Set G) := by
    by_contra hc
    exact absurd (E3.rParam_le_mQuot (hBA.trans inf_le_left) hc) (not_le.mpr hlt)
  exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans hC

theorem not_case_six (hF : Fact10_2_7Six) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3) (h1026 : Stmt10_2_6) (h4413 : TmpL6_4_4_13)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12)
    (hyp : Hyp10 G T L I) : ¬ Case10_1_1Six T L I := by
  intro h6
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hNV := SecA.normalizer_fsuVM_eq hyp (fsuM_isMaxTwoLocal h331 hyp)
  obtain ⟨-, e2, e3, -, -, e6⟩ := six_facts hF h37 h38 h1011 hyp h6 hV ht htn
  have htop : autI hV ⊤ = autI hV (fsuM T L) := autI_top_eq hV hNV.le
  have h61 := hypE61_of h331 h1012 hyp h6
  have hs := (h63 G T (fsuM T L) (fsuVM T L I) hV h61 (by rw [e2]; norm_num)).2
  rw [e2] at hs
  have hr := four_lt_rParam hF h37 h38 h331 h1011 h1012 h1026 h63 h612 hyp h6
  have h336 := SecD.hypE336_of h331 h1012 h1023 h4413 hyp
  obtain ⟨H, hH⟩ := exists_isHStar h331 hyp
  have hn2 : E1.nParam H ≤ 2 := by
    by_cases h1 : 1 < E1.nParam H
    · exact ((h1023 G T L I hyp H hH h1).1).le
    · exact (not_lt.mp h1).trans (by norm_num)
  have hmin := ASInputs.min_le_nParam_of_le hV (SecA.fsuVM_ne_bot hyp.fsu) h336 hH
    fun x hx => hNV ▸ Subgroup.centralizer_le_normalizer _ hx.2
  have hwn : E3.wParam T (fsuVM T L I) ≤ E1.nParam H := by
    rcases le_total (E3.wParam T (fsuVM T L I)) (E3.rParam (fsuVM T L I)) with hle | hle
    · rwa [min_eq_left hle] at hmin
    · rw [min_eq_right hle] at hmin
      exact absurd (hr.trans_le (hmin.trans hn2)) (by norm_num)
  have has' := (E3.e3_34_one hV h336.hyp322 (by rw [htop, e3, hs]; norm_num)).1
  rw [htop, e3, hs] at has'
  have h2w : (2 : ℕ∞) ≤ E3.wParam T (fsuVM T L I) := by exact_mod_cast has'
  have hw2 : E3.wParam T (fsuVM T L I) = 2 := le_antisymm (hwn.trans hn2) h2w
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV h336.hyp322 (k := 2) (by rw [hw2]; rfl)
  have hws : E3.wParam T (fsuVM T L I) < (E3.sParam hV : ℕ∞) := by
    rw [hw2, hs]
    norm_num
  have hmA : E3.mQuot (conjSubgroup (fsuVM T L I) g)
      (conjSubgroup (fsuVM T L I) g ⊓ Subgroup.normalizer (fsuVM T L I : Set G)) = 2 := by
    have h1 := hg.2
    rw [hw2] at h1
    exact_mod_cast h1.symm
  have hA2 := (E3.e3_33_four hV hg hws).1
  rw [hmA, hs, htop] at hA2
  obtain ⟨hq1, hq2⟩ := e6 _ hA2
  have hLM : L ≤ fsuM T L := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
  have hLtM : CFSG.conjugate L t ≤ fsuM T L :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)
  have hVN : fsuVM T L I ≤ Subgroup.normalizer (conjSubgroup (fsuVM T L I) g : Set G) :=
    (SecA.fsuVM_eq_sup h37 h38 hyp ht htn).le.trans (sup_le
      (commutator_le_normalizer_conj hV (commutator_le_fsuVM hLM) hr hmA hq1)
      (commutator_le_normalizer_conj hV (commutator_le_fsuVM hLtM) hr hmA hq2))
  have hw0 : 0 < E3.wParam T (fsuVM T L I) := by
    rw [hw2]
    norm_num
  exact hg.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((E3.e3_25_centralizer_iff_normalizer hV h336.hyp322 hw0 g).mpr hVN))

theorem stmt10_2_7_of (hF : Fact10_2_7Six) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3) (h1026 : Stmt10_2_6) (h4413 : TmpL6_4_4_13)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) :
    Stmt10_2_7 := by
  intro G _ _ T L I hyp
  have h6 := not_case_six hF h37 h38 h331 h1011 h1012 h1023 h1026 h4413 h63 h612 hyp
  exact ⟨h6, (h1012 G T L I hyp).2.2.1 h6⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
