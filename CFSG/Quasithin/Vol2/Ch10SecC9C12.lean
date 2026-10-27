module

public import CFSG.Quasithin.Vol2.Ch10SecAT1Trans
public import CFSG.Quasithin.Vol2.Ch10SecE21A
public import CFSG.Quasithin.Vol2.Ch10SecEN3d
public import CFSG.Quasithin.Vol2.Ch10SecC9B
public import CFSG.Quasithin.Vol2.Ch10SecC9Comp
public import CFSG.Quasithin.Vol2.Ch10SecC9Out
public import CFSG.Quasithin.Vol2.Ch10SecC9U

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Gap10_2_9V1capV2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I → ∀ n : ℕ,
    Case10_1_1One T L I n → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      ∀ v ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆,
        ¬ T1 T L ≤ Subgroup.centralizer ({v} : Set G) →
          Subgroup.centralizer ({v} : Set G) ≤ fsuM T L

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem not_case_three_of_case_one {n : ℕ} (h1 : Case10_1_1One T L I n) :
    ¬ Case10_1_1Three T L I := by
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

theorem claim_of_baum (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1021 : Stmt10_2_1)
    (hn3 : ¬ Case10_1_1Three T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (huV1 : u ∉ fsuUL T L I)
    (huM : ¬ Subgroup.centralizer ({u} : Set G) ≤ fsuM T L)
    (hJu : thompsonJ T ≤ Subgroup.centralizer ({u} : Set G)) : ∃ w, ClaimOut T L I t w := by
  obtain ⟨m, hm, hwW, hwV1, hSyl, hcon⟩ := exists_conj_in_V2 h37 h38 hyp ht htn hu huV1
  set w := m * u * m⁻¹ with hw
  have hJT : thompsonJ T ≤ T ⊓ Subgroup.centralizer ({u} : Set G) :=
    le_inf (B6.thompsonJ_le T) hJu
  have hJc : B6.conjSub m (thompsonJ T) ≤ T := by
    rintro y ⟨x, hx, rfl⟩
    exact (hcon x (hJT hx)).1
  have hJeq := conjSub_thompsonJ_eq hJc
  have hJw : thompsonJ T ≤ Subgroup.centralizer ({w} : Set G) := by
    intro j hj
    rw [← hJeq] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    exact (hcon x (hJT hx)).2
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hwJ : w ∈ Subgroup.centralizer (thompsonJ T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJw hj))
  have hSw : baum T ≤ T ⊓ Subgroup.centralizer ({w} : Set G) :=
    le_inf inf_le_left (baum_le_centralizer_of_mem (SecA.isElemAbelian_fsuVM hyp)
      (SecA.fsuVM_le_T hyp) (hV2V hwW) hwJ)
  have hbeq : baum T = baum (T ⊓ Subgroup.centralizer ({w} : Set G)) :=
    baum_eq_of_le hSw inf_le_left
  have hN : Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) ≤
      fsuM T L :=
    (normalizer_le_normalizer_baum _).trans (hbeq ▸ h1021 G T L I hyp hn3)
  refine ⟨w, hwW, hwV1, ?_, isSylowTwoOf_of_normalizer_le hSyl (inf_le_right.trans hN), hJw,
    fun h3 => absurd h3 hn3⟩
  rw [centralizer_conj_le_iff hm]
  exact huM

theorem claim_case1
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1021 : Stmt10_2_1) (h1026 : Stmt10_2_6) (he23 : E2.E23Statement) (h322 : TmpL6_3_2_2_two)
    (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight) (hGap : Gap10_2_9V1capV2) {n : ℕ}
    (h1 : Case10_1_1One T L I n) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) : ∃ w, ClaimOut T L I t w := by
  have hn3 := not_case_three_of_case_one h1
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2L, -⟩ := hdec t ht htn
  have hJ0 := (SecE.e23_case1 he23 h37 h38 h322 hshape h3228 hyp h1 hJ).2.2
  by_cases hvV1 : v ∈ fsuUL T L I
  · exfalso
    have hvC : v ∈ fsuCVM T L I := inf_V2_le_fsuCVM hyp h1011 ht htn ⟨hvV1, hv⟩
    by_cases hT1 : T1 T L ≤ Subgroup.centralizer ({v} : Set G)
    · apply hvM
      refine le_fsuM_of_le hyp h1026 (sup_le (fun x hx => ?_) hT1)
        (pCoreOf_centralizer_ne_bot hv1 ((SecA.isElemAbelian_fsuVM hyp).2 v (hV2V hv)))
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hvC.2 x hx)
    · exact hvM (hGap G T L I hyp n h1 t ht htn v ⟨hvV1, hv⟩ hT1)
  have key : ∀ u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, u ∉ fsuUL T L I →
      ¬ Subgroup.centralizer ({u} : Set G) ≤ fsuM T L →
      u ∈ Subgroup.centralizer ((T ⊓ L ⊔ T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) →
      ∃ w, ClaimOut T L I t w := by
    intro u hu huV1 huM huC
    have hT0 : T0 T L ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp
        (SecA.T0_le_centralizer h37 h38 h322 hyp ht htn hx) u ⟨hV2V hu, huC⟩).symm
    have hQu : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤
        Subgroup.centralizer ({u} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 u (hV2V hu)).symm
    exact claim_of_baum h37 h38 hyp h1021 hn3 ht htn hu huV1 huM (hJ0.trans (sup_le hT0 hQu))
  by_cases hvC : v ∈ fsuCVM T L I
  · refine key v hv hvV1 hvM (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (sup_le (inf_le_right.trans (SecA.le_fsuL0 T L))
        (inf_le_right.trans (SecA.conjugate_le_fsuL0 ht)))) hvC.2)
  · obtain ⟨l, hl, hlC⟩ := SecA.exists_conj_mem_centralizer_of_case_one' hyp h1 ht hv hvC
    have hlM : l ∈ fsuM T L := SecA.fsuL0_le_fsuM T L (SecA.conjugate_le_fsuL0 ht hl)
    have hlVN : l ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.conjugate_le_fsuL0 ht hl)
    have hlV2 : l * v * l⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
      (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator
        (fun _ hx => SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.conjugate_le_fsuL0 ht hx))
        (fun _ hx => Subgroup.le_normalizer hx) hl) v).mp hv
    have hlN : l ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
      SecA.le_normalizer_commutator (fun _ hx => SecA.fsuL0_le_normalizer_fsuVM T L I
        (SecA.conjugate_le_fsuL0 ht hx)) (conjugate_le_normalizer hyp ht) hl
    have hlV1 : l * v * l⁻¹ ∉ fsuUL T L I := fun h =>
      hvV1 ((Subgroup.mem_normalizer_iff.mp hlN v).mpr h)
    refine key _ hlV2 hlV1 ?_ (mem_centralizer_sup ?_ hlC)
    · rw [centralizer_conj_le_iff hlM]
      exact hvM
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hV2L hlV2) x hx.2)

omit [Finite G] in
theorem not_case_three_of_case_two (h2 : Case10_1_1Two T L I) : ¬ Case10_1_1Three T L I := by
  rintro ⟨⟨e3⟩, -⟩
  obtain ⟨⟨e2⟩, -⟩ := h2
  have hc := (Nat.card_congr e2.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  have h5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]; decide
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  rw [h5, h3] at hc
  omega

theorem claim_case2
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1021 : Stmt10_2_1) (he23 : E2.E23Statement)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight)
    (hn1 : ¬ ∃ n, Case10_1_1One T L I n) (h2 : Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) : ∃ w, ClaimOut T L I t w := by
  have hn3 := not_case_three_of_case_two h2
  have hcv : fsuCVM T L I = ⊥ := (h1012 G T L I hyp).2.2.2.2.2.2.1 (not_or.mpr ⟨hn1, hn3⟩)
  have hvV1 : v ∉ fsuUL T L I := fun h => by
    have := inf_V2_le_fsuCVM hyp h1011 ht htn ⟨h, hv⟩
    rw [hcv, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨x, hx, y, hy, -, -, hJx, hJy, -, -, -, horb⟩ :=
    SecE.fix_pair_orbit_case2 he23 h37 h38 h322 hshape h3228 hyp h2 ht htn hJ
  obtain ⟨k, hk, hkv⟩ := horb v hv hv1
  have hkM : k ∈ fsuM T L := SecA.fsuL0_le_fsuM T L (SecA.conjugate_le_fsuL0 ht hk)
  have hkV2 : k * v * k⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator
      (fun _ hz => SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.conjugate_le_fsuL0 ht hz))
      (fun _ hz => Subgroup.le_normalizer hz) hk) v).mp hv
  have hkN : k ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (fun _ hz => SecA.fsuL0_le_normalizer_fsuVM T L I
      (SecA.conjugate_le_fsuL0 ht hz)) (conjugate_le_normalizer hyp ht) hk
  have hkV1 : k * v * k⁻¹ ∉ fsuUL T L I := fun h =>
    hvV1 ((Subgroup.mem_normalizer_iff.mp hkN v).mpr h)
  have hJu : thompsonJ T ≤ Subgroup.centralizer ({k * v * k⁻¹} : Set G) := by
    rcases hkv with h | h <;> rw [h]
    · exact hJx
    · exact hJy
  refine claim_of_baum h37 h38 hyp h1021 hn3 ht htn hkV2 hkV1 ?_ hJu
  rw [centralizer_conj_le_iff hkM]
  exact hvM

end CFSG.Quasithin.Vol2.Ch10.SecC
