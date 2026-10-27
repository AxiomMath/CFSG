module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822B
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsQPf
public import CFSG.Quasithin.Vol2.Ch8Sec2L822L33
public import CFSG.Quasithin.Vol2.E2NineTI

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L822C

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem one_lt_of_isPSL_822 {X : Type} [Group X] {k : ℕ} (hP : IsPSL 2 2 k X) : 1 < k := by
  obtain ⟨⟨-, hk1, -, h22, -⟩, -⟩ := hP
  rcases Nat.lt_or_ge 1 k with h | h
  · exact h
  · have hk : k = 1 := by omega
    subst hk
    exact absurd rfl h22

theorem concl822_of_822 (hE213 : AS_E_2_13_I)
    (hE214 : AS_E_2_14) (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (hw : 0 < wParam T (fsuV T I)) {H : Subgroup G} (h1 : ¬ fsuV T I ≤ pCoreOf 2 H)
    (h28 : E2.Hyp28 H T (H ⊓ fsuM T L) (fsuV T I)) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn (fsuV T I) (H ⊓ fsuM T L)) {h : G}
    (hIC : IsInIHTVC H T (H ⊓ fsuM T L) (fsuV T I) (ch82I (fsuV T I) h))
    (hhI : h ∈ ch82I (fsuV T I) h) : ∃ k : ℕ, Concl822 T L I H h k := by
  have hFF := not_isFFModule_of_hyp702 hyp hV hNM
  obtain ⟨h6, h257⟩ := hE213 G H T (H ⊓ fsuM T L) (fsuV T I) (ch82I (fsuV T I) h) h h28
    hchar hIC hhI rfl
  have hSp : ∀ j : ℕ, ¬ IsSp4C j
      (E2.StarQuot (H ⊓ fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) :=
    h6 fun i _ hiT => conj_le_centralizer_822 hyp hV hN hw i hiT
  obtain ⟨k, hkn, hcases, hBor⟩ := cases_822 hIC hSp
  have hDLSz : IsDihL2Sz
      (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    rcases hcases with ⟨-, hD⟩ | hP | hS
    · exact Or.inl hD
    · exact Or.inr (Or.inl ⟨k, hP⟩)
    · exact Or.inr (Or.inr ⟨k, hS⟩)
  have hMI0 := inf_inf_eq_82 (M := fsuM T L) hIC.1
  obtain ⟨h2a, h5, h7⟩ := h257 (isDihL2Sz_of_eq hMI0.symm hDLSz)
  have hZ1 : ch82ZI (fsuV T I) h ≠ ⊥ := fun hZ =>
    absurd (h5 hZ) (not_le.mpr (one_lt_qOf_82 hV H hFF))
  obtain ⟨hMI, hVZ⟩ := e214_822 hE214 hhI hIC hZ1 h28 hchar hTI hDLSz
  have hker : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h) := by
    have := h7.2
    rw [inf_inf_eq_82 hIC.1] at this
    exact this.symm
  have hSyl := hIC.2.2.1
  have hTM : T ⊓ ch82I (fsuV T I) h ≤ fsuM T L ⊓ ch82I (fsuV T I) h :=
    inf_le_inf_right _ (le_normalizer_conjClosure L T)
  have := E2P.finite_starQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
  have hMN : E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (fsuM T L ⊓ ch82I (fsuV T I) h) =
      Subgroup.normalizer (E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (T ⊓ ch82I (fsuV T I) h) :
          Set (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h))) := by
    rcases hcases with ⟨-, m, hm, -, ⟨e⟩⟩ | hP | hS
    · exact star_eq_normalizer_of_dihedral_822 hTM hSyl hm e
    · exact star_eq_normalizer_of_borel_822 hTM hSyl (hBor (one_lt_of_isPSL_822 hP))
    · obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hS
      exact star_eq_normalizer_of_borel_822 hTM hSyl (hBor (by omega))
  have hidx : (pCoreOf 2 (ch82I (fsuV T I) h)).relIndex (fsuV T I) = 2 ^ k := by
    rcases hcases with ⟨rfl, m, hm, -, ⟨e⟩⟩ | hP | hS
    · have hcl := hIC.2.2.2.1
      rw [inf_inf_eq_82 hIC.1] at hcl
      have hpair := pair_82 hV (fsuV_le_T hyp.fsu hV hN) (le_sup_right.trans hN) hSyl hMI hhI hcl
      have h2 := hpair.relIndex_eq_two_of_dihedral hm e
      rw [Subgroup.inf_relIndex_right, hker] at h2
      rw [h2, pow_one]
    · have hc := card_star_822 (M' := fsuM T L ⊓ ch82I (fsuV T I) h)
        (I := ch82I (fsuV T I) h) (V := fsuV T I) le_sup_left
      rw [hVZ, card_center_822 (E2.isSylowTwoOf_star_inf hSyl) (one_lt_of_isPSL_822 hP)
        (Or.inl hP), hker] at hc
      exact hc.symm
    · have hk2 : 2 ≤ k := by
        obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hS
        omega
      have hc := card_star_822 (M' := fsuM T L ⊓ ch82I (fsuV T I) h)
        (I := ch82I (fsuV T I) h) (V := fsuV T I) le_sup_left
      rw [hVZ, card_center_822 (E2.isSylowTwoOf_star_inf hSyl) hk2 (Or.inr hS), hker] at hc
      exact hc.symm
  have hhP : h ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hhI
  have hm7 := mQuot_add_eq_822 hhP hidx h2a.2.2.2
  exact ⟨k, h1, hhI, hIC, hZ1, ch82ZI_le_centralizer_822 hV, hSyl, hMI, hker, hkn, hcases, hVZ,
    hMN, h2a.1, h2a.2.2.2, h2a.2.1, h2a.2.2.1, hm7, ch82U_le_ch82B_822 hV h7.1, h28, hchar, hTI⟩

theorem stmt8_2_2_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (hin : Input8_1_2)
    (h711n : Stmt7_1_1_normal) (h756 : Stmt7_5_6_two) (h813 : Stmt8_1_3) (h755 : Input7_5_5)
    (hcard : Mathieu.StmtH13Card) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h316 : Theorem316Statement) (hE29 : AS_E_2_9CTI)
    (hE213 : AS_E_2_13_I) (hE214 : AS_E_2_14) (hM22 : Step822M22) : Stmt8_2_2 := by
  have hL33 : Res822L33 := res822L33_holds h37 h38 h39 h3228 h325 h331 hC58 h317 h711n
  have htab : HTab82 := hTab82_holds
  have hcode : HCode82 := hCode82_holds
  have hQ : HQ82 := hQ82_holds
  intro G _ _ T L I hyp h731 h821 hc hrow
  have hmod := stmtFSUModule_of_eight h3228
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hw := wParam_pos_822 h37 h38 h39 hmod h325 hin h711n h756 h813 h755 htab hcode hcard hyp
    h731 hrow
  refine ⟨((h331 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow).2 L
      hyp.fsu.maximal hyp.fsu.quasisimple).2.2.1, fun H hH => ?_⟩
  have h1 := not_le_pCoreOf_822 h37 h38 h39 h3228 h316 hQ hM22 hyp h731 h821 hrow hTL hH
  obtain ⟨h28, hchar, hTI, -⟩ := hyp28_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH h1
  refine ⟨?_, fun h _ hIC hhI =>
    concl822_of_822 hE213 hE214 hyp hV hN hNM hw h1 h28 hchar hTI hIC hhI⟩
  obtain ⟨I₁, hI₁⟩ := (hE29 G H T (H ⊓ fsuM T L) (fsuV T I) h28 hTI).1
    (hL33 G T L I hyp h731 h821 hc hrow H hH)
  obtain ⟨g, hg, hgen⟩ := hI₁.2.1
  have hI : ch82I (fsuV T I) g = I₁ := hgen.symm
  refine ⟨g, hI₁.1 hg, ?_, ?_⟩
  · rw [hI]
    exact hI₁
  · rw [hI]
    exact hg

end L822C

end CFSG.Quasithin.H13
