module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL52
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.GorensteinWalter (PSL2)

theorem noCfgSEps_projSL_two {F : Type} [Field F] [Finite F]
    (h : ringChar F ≠ 3 ∨ Nat.card F ≤ 9) {S : Type} [Group S] [Finite S]
    (e : S ≃* projSL 2 F) : NoCfgSEps S := by
  have e' : S ≃* PSL2 F := e.trans (projSLEquivPSL F)
  by_cases h4 : 4 ≤ Nat.card F ∧ ringChar F ≠ 3
  · exact noCfgSEps_of_autNoE27 ((autNoE27_psl2 h4.2 h4.1).of_mulEquiv e')
  · apply noCfgSEps_of_card_lt
    have hc := RonanK432.card_psl2_mul_gcd F
    rw [← Nat.card_congr e'.toEquiv] at hc
    have hF : Nat.card F ≤ 9 := by
      rcases h with h | h
      · have : ¬ 4 ≤ Nat.card F := fun h4' => h4 ⟨h4', h⟩
        omega
      · exact h
    have hg : 0 < Nat.gcd 2 (Nat.card F - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : Nat.card S ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
      hc ▸ Nat.le_mul_of_pos_right _ hg
    have h2 : Nat.card F ^ 2 ≤ 81 := by
      calc Nat.card F ^ 2 ≤ 9 ^ 2 := Nat.pow_le_pow_left hF 2
        _ = 81 := by norm_num
    have h3 : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 9 * 80 :=
      Nat.mul_le_mul hF (by omega)
    omega

theorem rowSEpsOf_one (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (h : p ≠ 3 ∨ e ≤ 2) :
    RowSEpsOf (projSL 2 (GaloisField p e)) := by
  refine fun _ _ _ _ _ ⟨eS⟩ => noCfgSEps_projSL_two ?_ eS
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

theorem rowSEpsOf_seven_SL2 (n : ℕ) (hn : 1 ≤ n) : RowSEpsOf (projSL 2 (GaloisField 2 n)) :=
  rowSEpsOf_one 2 n hn (Or.inl (by norm_num))

theorem rowSEpsOf_two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2) :
    RowSEpsOf (projSL 3 (GaloisField p e)) :=
  fun _ _ _ _ _ ⟨φ⟩ => noCfgSEps_of_autNoE27
    ((autNoE27_of_card_le_nine (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (by omega) he
      (by omega))).of_mulEquiv φ)

theorem rowSEpsOf_two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2) :
    RowSEpsOf (projSU 3 p e) := by
  have hq : 2 < p ^ e := by
    calc 2 < p := by omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  exact fun _ _ _ _ _ ⟨φ⟩ => noCfgSEps_of_autNoE27
    ((autNoE27_of_card_le_nine (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (by omega) he hq
      (by omega))).of_mulEquiv φ)

theorem rowSEpsOf_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowSEpsOf (projSp 2 (GaloisField p 1)) := by
  refine fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨Fact.out, le_rfl, le_rfl, fun h => by simp at h; omega⟩
  haveI : Finite (projSp 2 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSp 2 (GaloisField p 1)) .PSp 2 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSp 2 (GaloisField p 1)) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgSEps_of_autNoE27 ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen (HeringUnitary.pRank_projSp_four_le_two hp))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSp 2 p ∣ 2 := Nat.gcd_dvd_left 2 _
  have := (h3.trans h2)
  omega

theorem rowSEpsOf_four_SL_of_mod_two (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 2) :
    RowSEpsOf (projSL 4 (GaloisField p 1)) := by
  refine fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSL 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  haveI : Finite (projSL 4 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSL 4 (GaloisField p 1)) .PSL 4 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSL 4 (GaloisField p 1)) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgSEps_of_autNoE27 ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSL 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSEpsOf_four_SU_of_mod_one (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 1) :
    RowSEpsOf (projSU 4 p 1) := by
  refine fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSU 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩
  haveI : Finite (projSU 4 p 1) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSU 4 p 1) .PSU 4 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSU 4 p 1) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgSEps_of_autNoE27 ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSU_four_le_two (by omega) le_rfl
        (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSU 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSEpsOf_four_G2 :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
      ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
        RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro p _ hp3 q hqp hqe hq
  refine fun S _ _ hs hna ⟨φ⟩ => ?_
  have hM : ChevalleyExceptionalModel S .G2 p 1 := by
    have h := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv φ
      (Census.chevalleyExceptionalModel_G2_of_odd q hq (by omega))
    rwa [hqp, hqe] at h
  have hX : LieModel S .G2 0 p 1 := Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hs hna
  exact noCfgSEps_of_autNoE27 (autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 hM.1 hX
      (by decide) (by decide) (by decide)
      (by rw [show lieOrderDivisor .G2 0 p = 1 from rfl]; norm_num) hα) hcen
    (noE27_of_forall (Item434Spor.noE27_of_pRank_le_two
      (Res417Four.pRank_g2_le_two hp3 S hM))))

theorem rowSEpsOf_alternating_le_eight {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) :
    RowSEpsOf (alternatingGroup (Fin n)) :=
  fun _ _ _ hs hna ⟨e⟩ => noCfgSEps_of_autNoE27 (autNoE27_of_mulEquiv_of_noE27 e hs hna
    (not_three_dvd_outer_alternatingGroup hn5)
    (noE27_of_not_dvd (not_dvd_card_alternatingGroup_le_eight hn5 hn8)))

theorem rowSEpsOf_eight_SL5 : RowSEpsOf (projSL 5 (GaloisField 2 1)) :=
  fun _ _ _ hs hna ⟨e⟩ => noCfgSEps_of_autNoE27
    (autNoE27_of_mulEquiv_of_noE27 e hs hna
      (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))
      noE27_projSL_five_two)

section Rows

theorem rowSEpsOf_of_noE27 {T : Type} [Group T] (h : ¬ 3 ∣ Nat.card (Outer T) ∧ NoE27 T) :
    RowSEpsOf T :=
  fun _ _ _ hs hna ⟨e⟩ => noCfgSEps_of_autNoE27 (autNoE27_of_mulEquiv_of_noE27 e hs hna h.1 h.2)

theorem rowSEpsOf_m11 :
    RowSEpsOf (Spor .M11) :=
  rowSEpsOf_of_noE27 spor_m11

theorem rowSEpsOf_m12 :
    RowSEpsOf (Spor .M12) :=
  rowSEpsOf_of_noE27 spor_m12

theorem rowSEpsOf_m22 :
    RowSEpsOf (Spor .M22) :=
  rowSEpsOf_of_noE27 spor_m22

theorem rowSEpsOf_m23 :
    RowSEpsOf (Spor .M23) :=
  rowSEpsOf_of_noE27 spor_m23

theorem rowSEpsOf_m24 :
    RowSEpsOf (Spor .M24) :=
  rowSEpsOf_of_noE27 spor_m24

theorem rowSEpsOf_j1 :
    RowSEpsOf (Spor .J1) :=
  rowSEpsOf_of_noE27 spor_j1

theorem rowSEpsOf_j2 :
    RowSEpsOf (Spor .J2) :=
  rowSEpsOf_of_noE27 spor_j2

theorem rowSEpsOf_j4 :
    RowSEpsOf (Spor .J4) :=
  rowSEpsOf_of_noE27 spor_j4

theorem rowSEpsOf_hs :
    RowSEpsOf (Spor .HS) :=
  rowSEpsOf_of_noE27 spor_hs

theorem rowSEpsOf_he :
    RowSEpsOf (Spor .He) :=
  rowSEpsOf_of_noE27 spor_he

theorem rowSEpsOf_ru :
    RowSEpsOf (Spor .Ru) :=
  rowSEpsOf_of_noE27 spor_ru

end Rows

theorem three_dvd_card_of_isTypeEpsCube {X : Type} [Group X] (h : IsTypeEpsCube X) :
    3 ∣ Nat.card X := by
  obtain ⟨r, hr, ⟨hr3, hc⟩ | ⟨hr3, hc⟩⟩ := card_of_isTypeEpsCube h <;> rw [hc] <;>
  · have h6 : r ^ 6 % 3 = 1 := by
      rw [Nat.pow_mod, hr3]
    have h1 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (by omega) _) _

theorem rowSEpsOf_seven_Sz :
    ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
      RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro m hm S _ _ _ _ ⟨e⟩ A σ K hc
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact not_three_dvd_card_suzukiGroup hK
  apply h3
  exact (three_dvd_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)).trans
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K))

section Tits


theorem rowSEpsOf_seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro ht S _ _ hs hna ⟨e⟩
  have hm : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e (Census.bridgeExceptional46.tits ht)
  refine noCfgSEps_of_autNoE27 (autNoE27_of_noE27
    (CFSG.Quasithin.A318P.not_dvd_outer_tits hm Nat.prime_three (by norm_num))
    (center_eq_bot_of_isSimpleGroup hs hna) fun D hD => ?_)
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits ht
    (E := D.map e.toMonoidHom) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩ ?_
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e (congrArg Subtype.val (hD.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hD.1.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hD.2]

end Tits

end CFSG.RankThree.PartTwo.Sec4.RonanEps
