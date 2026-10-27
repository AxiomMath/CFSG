module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G5
public import CFSG.Quasithin.Vol2.Ch10SecC9C12
public import CFSG.Quasithin.Vol2.Ch4Sec2W4213

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace C10P4F

omit [Finite G] in
theorem not_case_six_of_case_one {n : ℕ} (h1 : Case10_1_1One T L I n) :
    ¬ Case10_1_1Six T L I := by
  rintro ⟨⟨e3⟩, -⟩
  obtain ⟨hn, ⟨K, _, _, hK, ⟨e1⟩⟩, -⟩ := h1
  classical
  have := Fintype.ofFinite K
  have hc := (Nat.card_congr e1.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  rw [h3, Matrix.card_SL_field, Fin.prod_univ_two] at hc
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at hc
  rw [Nat.card_eq_fintype_card] at hK
  rw [hK] at hc
  set q := 2 ^ n with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 0 < q - 1 := by omega
  have hsq : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, pow_two]
  rw [hsq, ← mul_assoc, Nat.mul_div_cancel _ hpos] at hc
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    rw [hq, hn2] at hc
    norm_num at hc
  · have hq8 : 8 ≤ q := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 63 ≤ q ^ 2 - 1 := by
      have : 64 ≤ q ^ 2 := by nlinarith
      omega
    have : 504 ≤ (q ^ 2 - 1) * q := by nlinarith
    omega

theorem centralizer_le_of_not_le_T1 (h4213 : Stmt4_2_13FF) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : G}
    (hwC : w ∈ fsuCVM T L I) (hw1 : w ≠ 1)
    (hTw : ¬ T ⊓ Subgroup.centralizer ({w} : Set G) ≤ T1 T L) :
    Subgroup.centralizer ({w} : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTwdef
  set I0 := fsuL0 T L ⊔ Tw with hI0
  have hwV : w ∈ fsuVM T L I := hwC.1
  have hw2 : w ^ 2 = 1 := (SecA.isElemAbelian_fsuVM hyp).2 w hwV
  have hL0C : fsuL0 T L ≤ Subgroup.centralizer ({w} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwC.2 l hl)
  have hIC : I0 ≤ Subgroup.centralizer ({w} : Set G) := sup_le hL0C inf_le_right
  have hIM : I0 ≤ fsuM T L :=
    sup_le (SecA.fsuL0_le_fsuM T L) (inf_le_left.trans (SecA.le_fsuM T L))
  obtain ⟨s, hsTw, hsT1⟩ := Set.not_subset.mp hTw
  have hsn : s ∉ Subgroup.normalizer (L : Set G) := fun h => hsT1 ⟨hsTw.1, h⟩
  have hLs : CFSG.conjugate L s = CFSG.conjugate L t := by
    rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hsTw.1) with h | h
    · exact absurd (SecA.conjugate_eq_self_iff.mp h) hsn
    · exact h
  have hVTw : fsuVM T L I ≤ Tw := by
    refine le_inf (SecA.fsuVM_le_T hyp) fun x hx => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (B2F.isElemAbelian_comm (SecA.isElemAbelian_fsuVM hyp) hx hwV)
  have hVO : fsuVM T L I ≤ pCoreOf 2 I0 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVTw.trans le_sup_right)
      (hIM.trans (SecA.fsuM_le_normalizer_fsuVM T L I)) (SecA.isPGroup_fsuVM hyp)
  have hO2 : pCoreOf 2 I0 ≠ ⊥ := fun h =>
    SecA.fsuVM_ne_bot hyp.fsu (le_bot_iff.mp (h ▸ hVO))
  have hLM : L ≤ fsuM T L := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
  rcases h4213 G T (fsuM T L) L I0 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      (SecB.fsuM_isMaxTwoLocal h331 hyp) (SecA.le_fsuM T L) hyp.fsu.maximal hyp.fsu.faithful hLM
      hyp.fsu.quasisimple hIM
      (fun x hx => ⟨x, Subgroup.mem_sup_left (SecA.le_fsuL0 T L hx), 1,
        (pCoreOf 2 (L ⊔ T)).one_mem, mul_one x⟩)
      (fun r hr => by
        rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hr) with h | h
        · exact ⟨1, I0.one_mem, h.trans (SecA.conjugate_one L).symm⟩
        · exact ⟨s, Subgroup.mem_sup_right hsTw, h.trans hLs.symm⟩)
      (fun i hi => by
        rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (hIM hi) with h | h
        · exact ⟨1, T.one_mem, h.trans (SecA.conjugate_one L).symm⟩
        · exact ⟨t, ht, h⟩)
      hO2 with hU | hN | hO
  · obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot (pCoreOf_centralizer_ne_bot hw1 hw2)
    have h := hU.2 M' ⟨hM'.1, hIC.trans hM'.2⟩
    rw [← h]
    exact hM'.2
  · exact absurd ((SecA.le_fsuM T L).trans hN.1.1) hyp.not_normal
  · exact absurd ((SecA.le_fsuM T L).trans hO.1) hyp.not_normal

end C10P4F

theorem gap10_2_9V1capV2_of
    (h4213 : Stmt4_2_13FF) (hF1 : SecB.Fact10_2_6Pair) (hF2 : SecB.Fact10_2_6Rank)
    (hC27 : C27NoL2pJ1)
    (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1021 : Stmt10_2_1)
    (he23 : E2.E23Statement) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : TmpL6_3_2_2_eight) (h3210n : TmpL6_3_2_10_nine) : Gap10_2_9V1capV2 := by
  intro G _ _ T L I hyp n h1 t ht htn v hv hT1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hvM
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hT1 fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by group)
  have hvC : v ∈ fsuCVM T L I := inf_V2_le_fsuCVM hyp h1011 ht htn hv
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro hJ
    have h0 := fsuCVM_eq_bot_of_thompsonJ h3210n hyp hJ
    rw [h0, Subgroup.mem_bot] at hvC
    exact hv1 hvC
  have hTM : IsSylowTwoOf T (fsuM T L) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (SecA.le_fsuM T L)
  obtain ⟨m, hm, hSyl, -⟩ := exists_isSylowTwoOf_centralizer hTM v
  set w := m * v * m⁻¹ with hw
  have ew : m⁻¹ * w * m = v := by rw [hw]; group
  have hwV12 : w ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rcases conj_V_pair h37 h38 hyp ht htn hm with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨(h1' w).mpr (by rw [ew]; exact hv.1), (h2' w).mpr (by rw [ew]; exact hv.2)⟩
    · exact ⟨(h1' w).mpr (by rw [ew]; exact hv.2), (h2' w).mpr (by rw [ew]; exact hv.1)⟩
  have hwC : w ∈ fsuCVM T L I := inf_V2_le_fsuCVM hyp h1011 ht htn hwV12
  have hw1 : w ≠ 1 := fun h => hv1 (by rw [← ew, h]; group)
  have hwM : ¬ Subgroup.centralizer ({w} : Set G) ≤ fsuM T L := by
    rw [centralizer_conj_le_iff hm]
    exact hvM
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTwdef
  obtain ⟨-, hbaum, -⟩ := SecE.e23_case1 he23 h37 h38 h322 hshape h3228 hyp h1 hJ
  have hT0V : T0 T L ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ≤ Tw := by
    refine sup_le (le_inf inf_le_left fun x hx => ?_) (le_inf inf_le_left fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hwC.2 x hx.2)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 w hwC.1).symm
  have hbeq : baum T = baum Tw := baum_eq_of_le (hbaum.trans hT0V) inf_le_left
  have hN : Subgroup.normalizer (Tw : Set G) ≤ fsuM T L :=
    (normalizer_le_normalizer_baum _).trans
      (hbeq ▸ h1021 G T L I hyp (not_case_three_of_case_one h1))
  have hSylG : IsSylowTwoOf Tw (Subgroup.centralizer ({w} : Set G)) :=
    isSylowTwoOf_of_normalizer_le hSyl (inf_le_right.trans hN)
  by_cases hTwT1 : Tw ≤ T1 T L
  ·
    have hQ := (h1012 G T L I hyp).2.2.1 (C10P4F.not_case_six_of_case_one h1)
    have hL0C : fsuL0 T L ≤ Subgroup.centralizer ({w} : Set G) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hwC.2 l hl)
    have c : C10P4F.RCtx T L I Tw (Subgroup.centralizer ({w} : Set G)) :=
      ⟨hyp, pCoreOf_centralizer_ne_bot hw1 ((SecA.isElemAbelian_fsuVM hyp).2 w hwC.1),
        sup_le hL0C inf_le_right, hSylG, hTwT1, hQ ▸ (le_sup_right.trans hT0V), hwM⟩
    exact c.false_main hF1 hF2 hC27 hList hSL2 h36 h37 h38 h39 h331 h1011
  · exact hwM (C10P4F.centralizer_le_of_not_le_T1 h4213 h331 h37 h38 hyp ht htn hwC hw1 hTwT1)

end CFSG.Quasithin.Vol2.Ch10.SecC
