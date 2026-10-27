module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10D
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10C

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem i12_facts : i1.comp i1 = B6.id ∧ i1 ≠ B6.id ∧ i2.comp i2 = B6.id ∧ i2 ≠ B6.id ∧
    fixCount i1 = 8 ∧ fixCount i2 = 8 ∧ 16 ∈ oVecL ∧ presv (ptOf 16) i2 = true := by decide

theorem i1_acts_none : ∀ p ∈ oPts, presv (ptOf p) i1 = false := by decide

theorem i1_comm : ∀ D ∈ l1 ++ s0p, i1.comp D = D.comp i1 := by decide

theorem i2_comm : ∀ D ∈ l2 ++ s0p, i2.comp D = D.comp i2 := by decide

theorem s0p_valid : ∀ s ∈ s0p, s.Valid := by decide

theorem id_mem_s0p : B6.id ∈ s0p := by decide

theorem id_mem_l1s0p : B6.id ∈ l1s0p := by decide

theorem id_mem_l2s0p : B6.id ∈ l2s0p := by decide

theorem mem_l1s0p_of_l1 {a : B6} (ha : a ∈ l1) : a ∈ l1s0p :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨B6.id, id_mem_s0p, B6.comp_id⟩⟩

theorem mem_l1s0p_of_s0p {s : B6} (hs : s ∈ s0p) : s ∈ l1s0p :=
  List.mem_flatMap.2 ⟨B6.id, id_mem_l1, List.mem_map.2 ⟨s, hs, B6.id_comp (s0p_valid s hs)⟩⟩

theorem mem_l2s0p_of_l2 {a : B6} (ha : a ∈ l2) : a ∈ l2s0p :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨B6.id, id_mem_s0p, B6.comp_id⟩⟩

theorem mem_l2s0p_of_s0p {s : B6} (hs : s ∈ s0p) : s ∈ l2s0p :=
  List.mem_flatMap.2 ⟨B6.id, id_mem_l2, List.mem_map.2 ⟨s, hs, B6.id_comp (s0p_valid s hs)⟩⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem autOn_sup {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hB : B ≤ Subgroup.normalizer (V : Set G)) : autOn (A ⊔ B) V = autOn A V ⊔ autOn B V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hA hB

theorem center_of_codes {C : Coding ↥V}
    {A B : Subgroup (MulAut ↥V)} {la lp : List B6} {i : B6} {x : MulAut ↥V}
    (hAcode : ∀ a ∈ A, C.cB a ∈ la) (hBcode : ∀ b ∈ B, C.cB b ∈ lp)
    (hAs : ∀ D ∈ la, ∃ a ∈ A, C.cB a = D) (hBs : ∀ D ∈ lp, ∃ b ∈ B, C.cB b = D)
    (hla : ∀ a ∈ la, a ∈ la.flatMap fun a => lp.map fun s => a.comp s)
    (hlp : ∀ s ∈ lp, s ∈ la.flatMap fun a => lp.map fun s => a.comp s)
    (h1 : B6.id ∈ la.flatMap fun a => lp.map fun s => a.comp s)
    (hcl : ∀ y ∈ la.flatMap (fun a => lp.map fun s => a.comp s),
      ∀ z ∈ la.flatMap (fun a => lp.map fun s => a.comp s),
        y.comp z ∈ la.flatMap fun a => lp.map fun s => a.comp s)
    (hcen : ∀ D ∈ la.flatMap (fun a => lp.map fun s => a.comp s),
      (∀ E ∈ la ++ lp, D.comp E = E.comp D) → D = B6.id ∨ D = i)
    (hi : i ∈ la.flatMap fun a => lp.map fun s => a.comp s)
    (hicomm : ∀ E ∈ la ++ lp, i.comp E = E.comp i) (hx : C.cB x = i) :
    (A ⊔ B) ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) =
      Subgroup.zpowers x := by
  set P := la.flatMap fun a => lp.map fun s => a.comp s with hPd
  have hle : A ⊔ B ≤ C.subOf P h1 hcl := sup_le (fun a ha => hla _ (hAcode a ha))
    (fun b hb => hlp _ (hBcode b hb))
  have hcommx : ∀ y ∈ A ⊔ B, y * x = x * y := by
    intro y hy
    have hcent : A ⊔ B ≤ Subgroup.centralizer ({x} : Set (MulAut ↥V)) := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply C.cB_injective
        rw [C.cB_mul, C.cB_mul, hx]
        exact (hicomm _ (List.mem_append_left _ (hAcode a ha))).symm
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply C.cB_injective
        rw [C.cB_mul, C.cB_mul, hx]
        exact (hicomm _ (List.mem_append_right _ (hBcode b hb))).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hy)
  have hxAB : x ∈ A ⊔ B := by
    obtain ⟨a', ha', hs'⟩ := List.mem_flatMap.1 hi
    obtain ⟨s', hs'', he⟩ := List.mem_map.1 hs'
    obtain ⟨a, ha, hac⟩ := hAs a' ha'
    obtain ⟨b, hb, hbc⟩ := hBs s' hs''
    have : x = a * b := C.cB_injective (by rw [hx, C.cB_mul, hac, hbc, he])
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  apply le_antisymm
  · rintro y ⟨hyAB, hyc⟩
    have hyP : C.cB y ∈ P := hle hyAB
    have hcomm : ∀ E ∈ la ++ lp, (C.cB y).comp E = E.comp (C.cB y) := by
      intro E hE
      have hE' : ∃ e ∈ A ⊔ B, C.cB e = E := by
        rcases List.mem_append.1 hE with hE | hE
        · obtain ⟨a, ha, rfl⟩ := hAs E hE
          exact ⟨a, Subgroup.mem_sup_left ha, rfl⟩
        · obtain ⟨b, hb, rfl⟩ := hBs E hE
          exact ⟨b, Subgroup.mem_sup_right hb, rfl⟩
      obtain ⟨e, he, rfl⟩ := hE'
      have := Subgroup.mem_centralizer_iff.1 hyc e he
      rw [← C.cB_mul, ← C.cB_mul, this]
    rcases hcen _ hyP hcomm with e | e
    · rw [C.cB_eq_one.1 e]
      exact Subgroup.one_mem _
    · rw [show y = x from C.cB_injective (by rw [e, hx])]
      exact Subgroup.mem_zpowers x
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨hxAB, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact (hcommx y hy)

theorem lemma12_7_10_three
    (h1222 : Stmt12_2_2) {t : G} (hS : Setting1273 G T L V t) :
    autOn L V < hS.hyp.hyp.MVbar →
      ∃ i₁ ∈ hS.hyp.hyp.MVbar, ∃ i₂ ∈ hS.hyp.hyp.MVbar,
        i₁ ∉ autOn L V ∧ i₂ ∉ autOn L V ∧ orderOf i₁ = 2 ∧ orderOf i₂ = 2 ∧
        (∀ y ∈ hS.hyp.hyp.MVbar, y ∉ autOn L V → orderOf y = 2 →
          (∃ m ∈ hS.hyp.hyp.MVbar, y = m * i₁ * m⁻¹) ∨
            (∃ m ∈ hS.hyp.hyp.MVbar, y = m * i₂ * m⁻¹)) ∧
        (¬ ∃ m ∈ hS.hyp.hyp.MVbar, i₂ = m * i₁ * m⁻¹) ∧
        autOn (L1 T L V ⊔ T) V ⊓
            Subgroup.centralizer (autOn (L1 T L V ⊔ T) V : Set (MulAut ↥V)) =
          Subgroup.zpowers i₁ ∧
        autOn (L2 T L V ⊔ T) V ⊓
            Subgroup.centralizer (autOn (L2 T L V ⊔ T) V : Set (MulAut ↥V)) =
          Subgroup.zpowers i₂ ∧
        Nat.card ↥(fixV (Subgroup.zpowers i₁)) = 8 ∧
        Nat.card ↥(fixV (Subgroup.zpowers i₂)) = 8 ∧
        (∃ l ∈ L, Acts i₂ ((Vt L t).map (MulAut.conj l).toMonoidHom)) ∧
        ∀ l ∈ L, ¬ Acts i₁ ((Vt L t).map (MulAut.conj l).toMonoidHom) := by
  intro hlt
  have h := hS.hyp
  have hne : h.hyp.MVbar ≠ autOn L V := (ne_of_lt hlt).symm
  obtain ⟨C, hC, hT⟩ := exists_coding_T h1222 h hne
  have hsurj := MVbar_surj h hC.1 hne
  obtain ⟨hi1n, hi1g, hi2n, hi2g⟩ := cert4_i12_mem
  obtain ⟨e11, n1, e22, n2, f1, f2, h16o, hp16⟩ := i12_facts
  obtain ⟨x₁, hx₁M, hx₁c⟩ := hsurj i1 hi1n
  obtain ⟨x₂, hx₂M, hx₂c⟩ := hsurj i2 hi2n
  have hnotL : ∀ {x : MulAut ↥V} {B : B6}, C.cB x = B → B ∉ gm6 → x ∉ autOn L V :=
    fun hx hB hxL => hB (hx ▸ (hC.1.1 _).1 hxL)
  have hord : ∀ {x : MulAut ↥V} {B : B6}, C.cB x = B → B.comp B = B6.id → B ≠ B6.id →
      orderOf x = 2 := by
    intro x B hx hBB hB1
    apply orderOf_eq_prime
    · apply C.cB_injective
      rw [pow_two, C.cB_mul, C.cB_one, hx, hBB]
    · intro e
      apply hB1
      rw [← hx, e, C.cB_one]
  have hL1N : L1 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (oTwoUpper_le' _).trans (inf_le_left.trans (L_le_normalizer h))
  have hL2N : L2 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (oTwoUpper_le' _).trans fun x hx => L_le_normalizer h hx.1
  have hTN := T_le_normalizer h1222 h
  have hTs := T_surj h1222 h hC hne hT
  have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
  have hct := cd_t_mem_oVecL h1222 h hC hS.t_mem hS.orbit_t
  refine ⟨x₁, hx₁M, x₂, hx₂M, hnotL hx₁c hi1g, hnotL hx₂c hi2g, hord hx₁c e11 n1,
    hord hx₂c e22 n2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y hyM hyL hy2
    have hB := (MVbar_code h hC.1 hyM).1
    have hyg : C.cB y ∉ gm6 := fun hg => hyL ((hC.1.1 y).2 hg)
    have hyy : (C.cB y).comp (C.cB y) = B6.id := by
      rw [← C.cB_mul, ← pow_two, ← hy2, pow_orderOf_eq_one, C.cB_one]
    obtain ⟨m, hm, hm12⟩ := cert4_classes _ hB hyg hyy
    obtain ⟨n, hnM, rfl⟩ := hsurj m hm
    rcases hm12 with e | e
    · left
      have e' : y * n = n * x₁ := C.cB_injective (by rw [C.cB_mul, C.cB_mul, hx₁c, e])
      exact ⟨n, hnM, by rw [← e', mul_inv_cancel_right]⟩
    · right
      have e' : y * n = n * x₂ := C.cB_injective (by rw [C.cB_mul, C.cB_mul, hx₂c, e])
      exact ⟨n, hnM, by rw [← e', mul_inv_cancel_right]⟩
  ·
    rintro ⟨m, hmM, e⟩
    have e' : x₂ * m = m * x₁ := by rw [e, inv_mul_cancel_right]
    have := congrArg C.cB e'
    rw [C.cB_mul, C.cB_mul, hx₁c, hx₂c] at this
    exact cert4_noncong _ (MVbar_code h hC.1 hmM).1 this
  · rw [autOn_sup hL1N hTN]
    refine center_of_codes (C := C) (la := l1) (lp := s0p) (fun a ha => (mem_autOn_L1 h hC a).1 ha)
      hT (fun D hD => ?_) hTs (fun a ha => mem_l1s0p_of_l1 ha) (fun s hs => mem_l1s0p_of_s0p hs)
      id_mem_l1s0p cert4_l1s0p_closed cert4_center1 cert4_i12_prod.1 i1_comm hx₁c
    obtain ⟨a, rfl⟩ := hC.1.2 D (l1_sub_gm6 D hD)
    exact ⟨a, (mem_autOn_L1 h hC a).2 hD, rfl⟩
  · rw [autOn_sup hL2N hTN]
    refine center_of_codes (C := C) (la := l2) (lp := s0p) (fun a ha => (mem_autOn_L2 h hC a).1 ha)
      hT (fun D hD => ?_) hTs (fun a ha => mem_l2s0p_of_l2 ha) (fun s hs => mem_l2s0p_of_s0p hs)
      id_mem_l2s0p cert4_l2s0p_closed cert4_center2 cert4_i12_prod.2 i2_comm hx₂c
    obtain ⟨a, rfl⟩ := hC.1.2 D (l2_sub_gm6 D hD)
    exact ⟨a, (mem_autOn_L2 h hC a).2 hD, rfl⟩
  · rw [card_fixV_zpowers_code (C := C), hx₁c, f1]
  · rw [card_fixV_zpowers_code (C := C), hx₂c, f2]
  ·
    obtain ⟨g₁, hg₁, hg₁t⟩ := cert4_hyp_trans _ hct
    obtain ⟨g₂, hg₂, hg₂16⟩ := cert4_hyp_trans _ h16o
    obtain ⟨a₁, rfl⟩ := hC.1.2 g₁ hg₁
    obtain ⟨y₁, hy₁N, hy₁L, rfl⟩ := mem_autOn'.1 ((hC.1.1 _).2 hg₁)
    obtain ⟨y₂, hy₂L, hy₂N, hy₂c⟩ := exists_L_map_to hC.1 hg₂ (by decide) hg₂16
    have hlL : y₂ * y₁ ∈ L := L.mul_mem hy₂L hy₁L
    have hlN : y₂ * y₁ ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hy₂N hy₁N
    have hl16 : (C.cB (conjAct V ⟨y₂ * y₁, hlN⟩)).app (C.cd ⟨t, hS.t_mem⟩) = 16 := by
      rw [conjAct_mul_code hy₂N hy₁N, hg₁t, hy₂c]
    refine ⟨y₂ * y₁, hlL, ?_⟩
    rw [Vt_eq_ptOf h1222 h hC.1 hS.t_mem, map_subG_ptOf hC.1 hlN hlL (C.cd_lt _)]
    intro v hv
    have hcv := (C.mem_subG v).1 hv
    rw [hl16] at hcv
    refine (C.mem_subG _).2 ?_
    rw [hl16, C.cd_apply, hx₂c]
    exact (presv_iff _ _).1 hp16 _ hcv
  ·
    intro l hlL hact
    have hlN := L_le_normalizer h hlL
    rw [Vt_eq_ptOf h1222 h hC.1 hS.t_mem, map_subG_ptOf hC.1 hlN hlL (C.cd_lt _)] at hact
    set d := (C.cB (conjAct V ⟨l, hlN⟩)).app (C.cd ⟨t, hS.t_mem⟩) with hdd
    have hd : d ∈ oVecL := (MVbar_code h hC.1 (hLM (conjAct_mem_autOn hlL hlN))).2.1 _ hct
    have hd64 := oVecL_lt d hd
    obtain ⟨hpd, hpeq⟩ := oVecL_pn d hd
    have hpres : presv (ptOf (pn d)) (C.cB x₁) = true := by
      rw [presv_iff]
      intro c hc
      have hc' := (mem_iff_of_ptSetEq hpeq c).2 hc
      have hc64 := ptOf_lt_all d hd64 c hc'
      have hv : ((C.dc c : ↥V) : G) ∈ C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd64) :=
        (C.mem_subG _).2 (by rw [C.cd_dc c hc64]; exact hc')
      have himg := (C.mem_subG _).1 (hact _ hv)
      rw [C.cd_apply, C.cd_dc c hc64] at himg
      exact (mem_iff_of_ptSetEq hpeq _).1 himg
    rw [hx₁c, i1_acts_none _ hpd] at hpres
    exact Bool.false_ne_true hpres

theorem lemma12_7_10_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight) (hE612 : ASInputs.AS_E_6_12) : Lemma12_7_10 := by
  intro G _ _ T L V _ t hS
  exact ⟨mParam_MVbar h1222 hS.hyp, ⟨two_lt_rParam h331 h1222 h3228 hE612 hS,
    fun hV => sParam_eq_two h331 h1222 h3228 hE612 hS hV⟩, lemma12_7_10_three h1222 hS,
    lemma12_7_10_four h1222 hS, fun U hUV hU3 hno =>
      lemma12_7_10_five h331 h1222 h3228 hE612 hS U hUV hU3 hno⟩

end CFSG.Quasithin.H13.S127.Mod

end
