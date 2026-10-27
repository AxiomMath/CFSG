module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Cfg
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowRankTwo
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL52
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVG23
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU54
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowR27

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.GorensteinWalter
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27)


theorem noCfgS431_projSL_two {F : Type} [Field F] [Finite F]
    (h : ringChar F ≠ 3 ∨ Nat.card F ≤ 9) {S : Type} [Group S] [Finite S]
    (e : S ≃* projSL 2 F) : NoCfgS431 S := by
  have e' : S ≃* PSL2 F := e.trans (projSLEquivPSL F)
  by_cases h4 : 4 ≤ Nat.card F ∧ ringChar F ≠ 3
  · exact noCfgS431_of_autNoE27 ((RonanK429.autNoE27_psl2 h4.2 h4.1).of_mulEquiv e')
  · apply noCfgS431_of_card_lt
    have hc := RonanK432.card_psl2_mul_gcd F
    rw [← Nat.card_congr e'.toEquiv] at hc
    have hF : Nat.card F ≤ 9 := by
      rcases h with h | h
      · have : ¬ 4 ≤ Nat.card F := fun h4' => h4 ⟨h4', h⟩
        omega
      · exact h
    have hq : 1 < Nat.card F := Finite.one_lt_card
    generalize Nat.card F = q at hc hF hq
    interval_cases q <;> norm_num at hc <;> omega

theorem rowSOf431_one (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (h : p ≠ 3 ∨ e ≤ 2) :
    RowSOf431 (projSL 2 (GaloisField p e)) := by
  refine rowSOf431_of_noCfg fun _ _ _ _ _ ⟨eS⟩ => noCfgS431_projSL_two ?_ eS
  have hchar : ringChar (GaloisField p e) = p := ringChar.eq (GaloisField p e) p
  rcases h with h | h
  · exact Or.inl (by rw [hchar]; exact h)
  · by_cases hp3 : p = 3
    · subst hp3
      refine Or.inr ?_
      rw [GaloisField.card 3 e (by omega)]
      calc 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
        _ = 9 := by norm_num
    · exact Or.inl (by rw [hchar]; exact hp3)

theorem rowSOf431_seven_SL2 (n : ℕ) (hn : 1 ≤ n) : RowSOf431 (projSL 2 (GaloisField 2 n)) :=
  rowSOf431_one 2 n hn (Or.inl (by norm_num))

theorem rowSOf431_two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2) :
    RowSOf431 (projSL 3 (GaloisField p e)) :=
  rowSOf431_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => noCfgS431_of_autNoE27
    ((RonanK429.autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (by omega) he (by omega))).of_mulEquiv φ)

theorem rowSOf431_two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2) :
    RowSOf431 (projSU 3 p e) := by
  have hq : 2 < p ^ e := by
    calc 2 < p := by omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  exact rowSOf431_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => noCfgS431_of_autNoE27
    ((RonanK429.autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (by omega) he hq
        (by omega))).of_mulEquiv φ)

theorem rowSOf431_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowSOf431 (projSp 2 (GaloisField p 1)) := by
  refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨Fact.out, le_rfl, le_rfl, fun h => by simp at h; omega⟩
  haveI : Finite (projSp 2 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSp 2 (GaloisField p 1)) .PSp 2 p 1 :=
    Or.inl ⟨by decide,
      CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSp 2 (GaloisField p 1)) = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv φ.symm (RonanK429.center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgS431_of_autNoE27 ((RonanK429.autNoE27_of_forall_inner (fun α hα =>
    RonanK429.mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (RonanK429.noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSp_four_le_two hp))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSp 2 p ∣ 2 := Nat.gcd_dvd_left 2 _
  have := (h3.trans h2)
  omega

theorem rowSOf431_four_SL_of_mod_two (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 2) :
    RowSOf431 (projSL 4 (GaloisField p 1)) := by
  refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSL 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  haveI : Finite (projSL 4 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSL 4 (GaloisField p 1)) .PSL 4 p 1 :=
    Or.inl ⟨by decide,
      CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSL 4 (GaloisField p 1)) = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv φ.symm (RonanK429.center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgS431_of_autNoE27 ((RonanK429.autNoE27_of_forall_inner (fun α hα =>
    RonanK429.mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (RonanK429.noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSL 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSOf431_four_SU_of_mod_one (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 1) :
    RowSOf431 (projSU 4 p 1) := by
  refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSU 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩
  haveI : Finite (projSU 4 p 1) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSU 4 p 1) .PSU 4 p 1 :=
    Or.inl ⟨by decide,
      CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSU 4 p 1) = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv φ.symm (RonanK429.center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgS431_of_autNoE27 ((RonanK429.autNoE27_of_forall_inner (fun α hα =>
    RonanK429.mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (RonanK429.noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSU_four_le_two (by omega) le_rfl
        (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSU 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSOf431_four_G2 :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
      ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
        RowSOf431 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro p _ hp3 q hqp hqe hq
  refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hM : ChevalleyExceptionalModel S .G2 p 1 := by
    have h := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv φ
      (Census.chevalleyExceptionalModel_G2_of_odd q hq (by omega))
    rwa [hqp, hqe] at h
  have hX : LieModel S .G2 0 p 1 := Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  have hcen : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
  refine noCfgS431_of_autNoE27 (RonanK429.autNoE27_of_forall_inner (fun α hα =>
    RonanK429.mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 hM.1 hX
      (by decide) (by decide) (by decide)
      (by rw [show lieOrderDivisor .G2 0 p = 1 from rfl]; norm_num) hα) hcen
    (RonanK429.noE27_of_forall (Item434Spor.noE27_of_pRank_le_two
      (Res417Four.pRank_g2_le_two hp3 S hM))))

theorem rowSOf431_three :
    ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      RowSOf431 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  intro hr
  obtain ⟨f⟩ := CFSG.AGLEmbedding.ReeModel.nonempty_reeGamma_equiv 1 le_rfl hr
  have hcard : Nat.card RonanK432.Ree27 = 10073444472 := by
    rw [CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq RonanK432.card_ree27Field]
    norm_num
  have hno : NoCfgS431 RonanK432.Ree27 :=
    noCfgS431_of_not_five_dvd (by rw [hcard]; norm_num)
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := Finite.of_equiv _ f.toEquiv
  exact rowSOf431_of_noCfgS431 (hno.of_mulEquiv f.symm)

theorem rowSOf431_alternating_le_eight {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) :
    RowSOf431 (alternatingGroup (Fin n)) :=
  rowSOf431_of_noCfg fun _ _ _ hs hna ⟨e⟩ => noCfgS431_of_autNoE27
    (RonanK429.autNoE27_of_mulEquiv_of_noE27 e hs hna
      (RonanK429.not_three_dvd_outer_alternatingGroup hn5)
      (RonanK429.noE27_of_not_dvd (RonanK429.not_dvd_card_alternatingGroup_le_eight hn5 hn8)))

theorem rowSOf431_of_noE27 {s : TauCeti.SporadicName}
    (h : ¬ 3 ∣ Nat.card (Outer (Spor s)) ∧ NoE27 (Spor s)) : RowSOf431 (Spor s) :=
  rowSOf431_of_noCfg fun _ _ _ hs hna ⟨e⟩ =>
    noCfgS431_of_autNoE27 (RonanK429.autNoE27_of_mulEquiv_of_noE27 e hs hna h.1 h.2)

theorem rowSOf431_m11 :
    RowSOf431 (Spor .M11) :=
  rowSOf431_of_noE27 RonanK429.spor_m11

theorem rowSOf431_m12 :
    RowSOf431 (Spor .M12) :=
  rowSOf431_of_noE27 RonanK429.spor_m12

theorem rowSOf431_m22 :
    RowSOf431 (Spor .M22) :=
  rowSOf431_of_noE27 RonanK429.spor_m22

theorem rowSOf431_m23 :
    RowSOf431 (Spor .M23) :=
  rowSOf431_of_noE27 RonanK429.spor_m23

theorem rowSOf431_m24 :
    RowSOf431 (Spor .M24) :=
  rowSOf431_of_noE27 RonanK429.spor_m24

theorem rowSOf431_j1 :
    RowSOf431 (Spor .J1) :=
  rowSOf431_of_noE27 RonanK429.spor_j1

theorem rowSOf431_j2 :
    RowSOf431 (Spor .J2) :=
  rowSOf431_of_noE27 RonanK429.spor_j2

theorem rowSOf431_j4 :
    RowSOf431 (Spor .J4) :=
  rowSOf431_of_noE27 RonanK429.spor_j4

theorem rowSOf431_hs :
    RowSOf431 (Spor .HS) :=
  rowSOf431_of_noE27 RonanK429.spor_hs

theorem rowSOf431_he :
    RowSOf431 (Spor .He) :=
  rowSOf431_of_noE27 RonanK429.spor_he

theorem rowSOf431_ru :
    RowSOf431 (Spor .Ru) :=
  rowSOf431_of_noE27 RonanK429.spor_ru

theorem rowSOf431_j3 :
    RowSOf431 (Spor .J3) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  exact rowSOf431_of_concl (Or.inr (Or.inl ⟨b.symm⟩))

theorem rowSOf431_seven_Sz :
    ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
      RowSOf431 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro m hm
  refine rowSOf431_of_noCfg fun S _ _ _ _ ⟨e⟩ => ?_
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact not_three_dvd_card_suzukiGroup hK
  exact noCfgS431_of_not_three_dvd h3

theorem rowSOf431_seven_Tits :
    ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
      RowSOf431 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro ht
  refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨e⟩ => ?_
  have hm : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e (Census.bridgeExceptional46.tits ht)
  have hout : ¬ 3 ∣ Nat.card (Outer S) :=
    CFSG.Quasithin.A318P.not_dvd_outer_tits hm Nat.prime_three (by norm_num)
  have hE : NoE27 S := fun D hD => by
    have hD' := hD.map e
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits ht
      (E := D.map e.toMonoidHom) hD'.1 hD'.2
  exact noCfgS431_of_autNoE27
    (RonanK429.autNoE27_of_noE27 hout (RonanK429.center_eq_bot_of_isSimpleGroup hs hna) hE)

theorem rowSOf431_eight_SL5 : RowSOf431 (projSL 5 (GaloisField 2 1)) :=
  rowSOf431_of_noCfg fun _ _ _ hs hna ⟨e⟩ => noCfgS431_of_autNoE27
    (RonanK429.autNoE27_of_mulEquiv_of_noE27 e hs hna
      (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))
      RonanK429.noE27_projSL_five_two)

theorem rowSOf431_eight_SU5_4 : RowSOf431 (projSU 5 2 2) := by
  haveI : Finite (projSU 5 2 2) := Item434SmallTwoOther.UTools.finite_projSU_gf16 5
  exact rowSOf431_of_noCfg fun _ _ _ hs hna ⟨e⟩ => noCfgS431_of_autNoE27
    (RonanK429.autNoE27_of_mulEquiv_of_noE27 e hs hna outU54_holds
      (RonanK429.noE27_of_not_dvd RonanK432.not_27_dvd_card_u54))

theorem rowSOf431_nine_SL3_odd (e : ℕ) (he : e = 1 ∨ e = 3) :
    RowSOf431 (projSL 3 (GaloisField 3 e)) := by
  refine rowSOf431_of_noCfg fun S _ _ _ _ ⟨φ⟩ => ?_
  have hS : Nat.card S = (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 - 1)) :=
    (Nat.card_congr φ.toEquiv).trans
      (RonanK429.RowV.card_projSL_three_char_three (e := e) (by omega))
  refine noCfgS431_of_not_five_dvd ?_
  rw [hS]
  rcases he with rfl | rfl <;> norm_num

theorem rowSOf431_nine_SU3_odd (e : ℕ) (he : e = 1 ∨ e = 3) :
    RowSOf431 (projSU 3 3 e) := by
  refine rowSOf431_of_noCfg fun S _ _ _ _ ⟨φ⟩ => ?_
  have hS : Nat.card S = (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)) :=
    (Nat.card_congr φ.toEquiv).trans
      (RonanK429.RowV.card_projSU_three_char_three (e := e) (by omega))
  refine noCfgS431_of_not_five_dvd ?_
  rw [hS]
  rcases he with rfl | rfl <;> norm_num

theorem rowSOf431_nine_G2 :
    RowSOf431 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group := by
  refine rowSOf431_of_noCfg fun S _ _ _ _ ⟨φ⟩ => ?_
  have hS : Nat.card S ∣ CFSG.Open.ordG2 3 := by
    rw [Nat.card_congr φ.toEquiv]
    exact RonanK429.RowV.card_g2_three_dvd
  exact noCfgS431_of_not_five_dvd fun h5 => by
    have h := h5.trans hS
    norm_num [CFSG.Open.ordG2] at h

end CFSG.RankThree.PartTwo.Sec4.Ronan431
