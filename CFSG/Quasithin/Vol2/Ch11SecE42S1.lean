module

public import CFSG.Quasithin.Vol2.Ch11SecE42S1f
public import CFSG.Quasithin.Vol2.Ch11SecE42S1c
public import CFSG.Quasithin.Vol2.Ch11SecE42Obl
public import CFSG.Quasithin.Vol2.Ch11SecE42S2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem obl11_4_2S1_of (hF : Facts42) (hS : Facts42S1) (hF43 : Facts43) (hP : SecB.PointFacts)
    (hN : SecA.NatFacts) (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (h312 : QuasithinUnique.Vol2Native.A312ForSQTKCat) (h3214 : TmpL6_3_2_14)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h701 : Stmt7_0_1) (hFSU : Ch10.StmtFSUChoice)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) :
    Obl11_4_2S1 := by
  intro G _ _ T L I n V₁ z hc Kp hKp hle
  have h := hc.hyp
  have := h.fsu.simple
  have hLocal := (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF43 h1102 h hcV hc.vi hc.mem.1 hc.mem.2
  obtain ⟨hK, hNK, -⟩ := kz_spec hF43 h1102 h1110 h1111 h hcV hc.vi hc.mem hc.ne_one
  have hTz := le_centralizer_of_mem hc.mem.2
  have hTK : T ≤ Subgroup.normalizer (kz L V₁ z : Set G) := hTz.trans hNK
  have hLK : LOf L V₁ ≤ kz L V₁ z := le_conjClosure _ _
  have hKz : kz L V₁ z ≤ Subgroup.centralizer ({z} : Set G) := le_of_mem_cComp hK
  have hlocK : quasithinIsLocal T (kz L V₁ z) :=
    isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz)
      (pCoreOf_centralizer_ne_bot h hc.mem hc.ne_one) hK
  have hKl : kz L V₁ z ∈ lFamily T := mem_lFamily_iff'.mpr hlocK.2.1
  obtain ⟨Km, hKpKm, hKm⟩ := Finite.exists_le_maximal (p := quasithinIsLocal T) hKp
  have hmax : quasithinIsMaximalLocal T Km :=
    ⟨hKm.1, fun Y hY hle' => (hKm.eq_of_le hY hle').symm⟩
  have hKKm : kz L V₁ z ≤ Km := hle.trans hKpKm
  suffices hKeq : Km = kz L V₁ z from le_antisymm (hKpKm.trans hKeq.le) hle
  by_contra hneq
  have hlt : kz L V₁ z < Km := lt_of_le_of_ne hKKm (Ne.symm hneq)
  have hTKm := T_le_normalizer_of_le hLocal h37 hmax.1 hKl hTK hKKm
  have hnz := not_le_of_lt_of_mem_cComp hK hTz hmax.1 hlt
  have hHne : pCoreOf 2 (Km ⊔ T) ≠ ⊥ := hmax.1.2.2.2
  have hSyl : QuasithinUnique.IsSylowTwoOf T (Km ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  have hKH : kz L V₁ z ≤ Km ⊔ T := hKKm.trans le_sup_left
  have hKmc : Km ∈ cComp (Km ⊔ T) := hmax.1.2.1
  rcases QuasithinUnique.Vol2Native.lemma_1_2_4_list hLocal h312 hHne hSyl hKH hKl hKmc hKKm
    with heq | hcase
  · exact (ne_of_lt hlt) (SecA.eq_of_modO2Image_eq hSyl le_sup_left hKKm
      (perfect_of_mem_cComp hKmc) hTK heq)
  obtain ⟨eK⟩ := nonempty_modO2_modO2Image_equiv hKH
  obtain ⟨hn2, hM | hJ | ⟨p, hp, hp11, hL⟩ | h21⟩ :=
    hS.list11 _ _ _ _ n h.one_lt ⟨eK⟩ hc.list hc.not_a36 hc.not_sl2pE hcase
  rotate_left 2
  ·
    have hL₁l : LOf L V₁ ∈ lFamily T := SecA.lOf_mem_lFamily hN h1102 h hc.vi (Or.inl rfl) le_rfl
    have hL₁H : LOf L V₁ ≤ Km ⊔ T := hLK.trans hKH
    obtain ⟨F, _, _, hF4, ⟨e₁⟩⟩ := exists_lOf_iso h1110 h hc.vi hn2
    obtain ⟨φ', hφ's, hφ'k⟩ := exists_modO2Image_lOf_map hL₁H e₁
    have hlist1 := QuasithinUnique.Vol2Native.lemma_1_2_4_list hLocal h312 hHne hSyl hL₁H hL₁l
      hKmc (hLK.trans hKKm)
    obtain ⟨h1, h2, h3, h4, h5⟩ := hF.a5 _ _ _ F hF4 ⟨φ', hφ's, hφ'k⟩ hlist1 p hp (by omega)
    rcases hL with hL | hL | hL | hL | hL
    exacts [h1 hL, h2 hL, h3 hL, h4 hL, h5 hL]
  ·
    exact hnz (le_centralizer_of_case21 h3214 h hc.mem hmax.1 hKKm hKz h21)
  all_goals
    obtain ⟨eKm⟩ := modO2_mulEquiv hKmc
    have hX' : IsSporadic .M23 (↥Km ⧸ CFSG.pCore 2 ↥Km) ∨
        IsSporadic .J4 (↥Km ⧸ CFSG.pCore 2 ↥Km) := by
      first
        | exact Or.inl (Nonempty.intro (eKm.trans (Nonempty.some hM)))
        | exact Or.inr (Nonempty.intro (eKm.trans (Nonempty.some hJ)))
    have hsimple := (hS.m23j4 _ hX').1
    have : (CFSG.pCore 2 ↥Km).Normal := CFSG.pCore_normal
    have : Group.IsPerfect ↥Km := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKmc)
    have hQ : CFSG.IsQuasisimple (↥Km ⧸ CFSG.pCore 2 ↥Km) :=
      isQuasisimple_of_isSimpleGroup_of_perfect
    have hzO := le_omegaOneCenterOf hP h1102 h hc.vi (hLK.trans hKKm) hHne hzV₁
    have hne : ⁅omegaOneCenterOf (pCoreOf 2 (Km ⊔ T)), Km⁆ ≠ ⊥ := by
      intro h0
      apply hnz
      intro k hk
      have hzC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0 hzO
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzC k hk)
    have hfl := isFaithfulLocal_of h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h39 h.fsu.sylow
      hmax hTKm hne
    obtain ⟨I', hfsu'⟩ := hFSU G T Km h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow hmax
      hfl hQ
    exact false_of_fsu_sporadic hS hM24 h701 h325 h328 hfsu' hTKm hX'

end CFSG.Quasithin.Vol2.Ch11.SecE
