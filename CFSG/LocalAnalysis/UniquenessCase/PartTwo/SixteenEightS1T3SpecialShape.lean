module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

@[simp] private theorem s16t3_special_card_multiplicative_zmod (x : ℕ) :
    Nat.card (Multiplicative (ZMod x)) = x :=
  (Nat.card_congr (Multiplicative.toAdd (α := ZMod x))).trans (Nat.card_zmod x)

private theorem s16t3_special_statedClassicalModel_two {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2) :
    StatedClassicalModel (StatedSL n K) .PSL n 2 1 := by
  have hbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
    have hc1 : c = 1 := by
      have hsub : Subsingleton Kˣ :=
        (Nat.card_eq_one_iff_unique.mp (by simp [Nat.card_units, hK])).1
      exact hsub.allEq c 1
    exact Subtype.ext (by rw [← hc, hc1, map_one]; rfl)
  have hproj : StatedProj (StatedSL n K) ≃* StatedSL n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, le_refl 1, by omega, ?_, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  · rintro h; exact absurd (congrArg Prod.fst h) (by omega)
  · rintro h; exact absurd (congrArg Prod.snd h) (by norm_num)

private theorem s16t3_special_statedSL_three_zmod_two_eq_top :
    StatedSL 3 (ZMod 2) = ⊤ := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  haveI : Subsingleton (ZMod 2)ˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  refine eq_top_iff.mpr fun A _ => CFSG.Open.StatedAPI.mem_statedSL_iff.mpr ?_
  have h : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  simpa [Units.ext_iff] using h

private theorem s16t3_special_griessHopfMultiplier_gl3_card
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) = 2 := by
  have hclassSL : StatedClassicalModel (StatedSL 3 (ZMod 2)) .PSL 3 2 1 :=
    s16t3_special_statedClassicalModel_two (n := 3) (by norm_num) (by simp)
  let e : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) ≃* StatedSL 3 (ZMod 2) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
      s16t3_special_statedSL_three_zmod_two_eq_top.symm)
  have hclass : StatedClassicalModel (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) .PSL 3 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hclassSL
  have hmodel : CFSG.Models.LieModel (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) .PSL 3 2 1 :=
    ⟨hclass.1, Or.inl hclass⟩
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 3 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 1) = 2 := by
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
      Nat.card_prod]
  obtain ⟨-, ⟨m⟩⟩ := hGA _ .PSL 3 2 1 hmodel
  rw [Nat.card_congr m.toEquiv, hcard]

theorem s16t3_special_kBar_normal {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T) :
    ((s1t3KBar A L).subgroupOf A).Normal := by
  refine (Subgroup.normal_subgroupOf_iff inf_le_left).2 ?_
  intro k a hk ha
  refine ⟨A.mul_mem (A.mul_mem ha hk.1) (A.inv_mem ha), ?_⟩
  change a * k * a⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut W))
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hal : a⁻¹ * l * a ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (h.normal (A.inv_mem ha)) l).1 hl
  have hc : k * (a⁻¹ * l * a) = (a⁻¹ * l * a) * k :=
    ((Subgroup.mem_centralizer_iff.1 hk.2) (a⁻¹ * l * a) hal).symm
  have hm : a * (k * (a⁻¹ * l * a)) * a⁻¹ = (a * k * a⁻¹) * l := by group
  rw [← hm, hc]
  group

theorem s16t3_kBar_mulEquiv_gl3 {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (hK : Nat.card ↥(s1t3KBar A L) = 168) :
    Nonempty (↥(s1t3KBar A L) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  obtain ⟨r, hr1, -⟩ := h.exists_fano_rep h7
  let Kb := s1t3KBar A L
  let rK : ↥Kb →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    r.comp (Subgroup.inclusion (inf_le_left : Kb ≤ A))
  have hinj : Function.Injective rK := by
    intro x y hxy
    have h1 : rK (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hfix : ∀ J ∈ irrSet L, J.map ((x * y⁻¹ : ↥Kb) : MulAut W).toMonoidHom = J :=
      (hr1 (Subgroup.inclusion (inf_le_left : Kb ≤ A) (x * y⁻¹))).1 h1
    have hk : ((x * y⁻¹ : ↥Kb) : MulAut W) = 1 := h.eq_one_of_kBar_fix (x * y⁻¹).2 hfix
    exact mul_inv_eq_one.mp (Subtype.ext (by simpa using hk))
  have hcard_range : Nat.card ↥(rK.range) = 168 := by
    rw [← hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
    norm_num
  have htop : rK.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard_range, hGL])
  exact ⟨(MonoidHom.ofInjective hinj).trans
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

private theorem s16t3_special_kBar_mult_two_pow {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (hK : Nat.card ↥(s1t3KBar A L) = 168) :
    ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(s1t3KBar A L)) = 2 ^ k := by
  obtain ⟨e⟩ := s16t3_kBar_mulEquiv_gl3 h h7 hK
  refine ⟨1, ?_⟩
  rw [Nat.card_congr
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]
  simpa using s16t3_special_griessHopfMultiplier_gl3_card hGA

private theorem s16t3_special_not_isMulCommutative_of_card_168 {X : Type} [Group X] [Finite X]
    (hs : IsSimpleGroup X) (hcard : Nat.card X = 168) : ¬ IsMulCommutative X := by
  intro hc
  haveI : IsMulCommutative X := hc
  have hp : (Nat.card X).Prime := (Group.is_simple_iff_prime_card).1 hs
  rw [hcard] at hp
  norm_num at hp

private theorem s16t3_special_false_of_parabolic_three (h : S16gRowCtx D V₀ V L hV)
    (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    (hKs : IsSimpleGroup ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)))
    (hKnc : ¬ IsMulCommutative ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)))
    (hKmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier
      ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) = 2 ^ k)
    (hLK : lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) = ⊥)
    {a₀ : ℕ} (hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) a₀) (ha₀ : 2 ≤ a₀) :
    False := by
  have hPK : T3ParabK (lBar V₀ V hV L) (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))
      (barSub V₀ V hV D.T) (a₀ + 1) := T3ParabK.of_kBar hT h7 hK hP
  obtain ⟨J, hTJ, hJL, hJcard, hJexp⟩ := hPK
  refine h.false_of_parabolic_two h3 (h.mBarGT_two hT) hsimple hmult inf_le_left
    (s16t3_special_kBar_normal hT) hKs hKnc hKmult hLK hTJ hJL hJcard hJexp
    (by omega) (Or.inr (Or.inl (by omega)))

theorem S16gRowCtx.false_of_special_shape (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hsum : SumOfNatShape (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3 : 3 ∈ D.sig) (hS : T3SpecialShape (lBar V₀ V hV L)) : False := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  rcases hT.card_irrSet_eq with hIrr3 | hIrr7
  · exact h.false_of_card_irr_three_special hT hIrr3 hS
  · obtain ⟨N, hNA, hLN, -, hNcomm, hNKbot, hNKsup, hKord⟩ := hT.structure_of_seven hIrr7
    have hLK : lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) = ⊥ := by
      refine le_bot_iff.1 fun x hx => ?_
      have hxN : x ∈ N ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := ⟨hLN hx.1, hx.2⟩
      rw [hNKbot] at hxN
      simpa using hxN
    rcases hKord with hK7 | hK21 | ⟨hK168, hKsimple⟩
    · rcases hS with hL3 | hL4 | hOm4 | hOm6 | hA5 | hA6 | hA7
      · exact h.false_of_count h3 hT hIrr7 (Or.inl ⟨Or.inl hL3, Or.inl hK7⟩)
      · exact h.false_of_count h3 hT hIrr7 (Or.inr ⟨Or.inl hL4, hK7⟩)
      · exact h.false_of_count h3 hT hIrr7
          (Or.inl ⟨Or.inr (Or.inr hOm4), Or.inl hK7⟩)
      · exact h.false_of_omegaMinus6_Z7 hGA hSchur h3 hT hIrr7 hOm6 hK7
      · exact h.false_of_count h3 hT hIrr7 (Or.inl ⟨Or.inr (Or.inl hA5), Or.inl hK7⟩)
      · exact h.false_of_count h3 hT hIrr7 (Or.inr ⟨Or.inr (Or.inl hA6), hK7⟩)
      · exact h.false_of_count h3 hT hIrr7 (Or.inr ⟨Or.inr (Or.inr hA7), hK7⟩)
    · exact h.false_of_kBar_order_21 h3 hT hIrr7 hK21
    · have hKnc : ¬ IsMulCommutative
          ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) :=
        s16t3_special_not_isMulCommutative_of_card_168 hKsimple hK168
      have hKmult := s16t3_special_kBar_mult_two_pow hGA hT hIrr7 hK168
      rcases hS with hL3 | hL4 | hOm4 | hOm6 | hA5 | hA6 | hA7
      · exact h.false_of_count h3 hT hIrr7 (Or.inl ⟨Or.inl hL3, Or.inr hK168⟩)
      ·
        obtain ⟨hsimple, hmult⟩ :=
          s16t3_simple_and_mult hGA hSchur (Or.inl ⟨hL4, by norm_num⟩)
        obtain ⟨I, -, hTI, hInat⟩ := hT.exists_stable_natural
        rcases hInat with ⟨n', hSL | hSp | hOp | hOm | hAlt⟩
        · obtain ⟨hSLn, hSsum⟩ := hSL
          by_cases hn : 4 ≤ n'
          · exact s16t3_special_false_of_parabolic_three h h3 hT hIrr7 hK168 hsimple hmult
              hKsimple hKnc hKmult hLK (hT.parab_sl hn hSLn hTI hSsum) (by omega)
          · have h3n : 3 ≤ n' := s16k_three_le_of_isSLn hT.quasi hSLn
            have hn3 : n' = 3 := by omega
            exact h.false_of_count h3 hT hIrr7
              (Or.inl ⟨Or.inl (by simpa [hn3] using hSLn), Or.inr hK168⟩)
        · obtain ⟨hSpn, hSsum⟩ := hSp
          have hn : 6 ≤ n' := s16k_six_le_of_isSpn hT.quasi hSpn
          exact s16t3_special_false_of_parabolic_three h h3 hT hIrr7 hK168 hsimple hmult
            hKsimple hKnc hKmult hLK (hT.parab_sp hn hSpn hTI hSsum) (by omega)
        · obtain ⟨hOpn, hSsum⟩ := hOp
          have hn : 6 ≤ n' := s16k_six_le_of_isOmegaPlus hT.quasi hOpn
          exact s16t3_special_false_of_parabolic_three h h3 hT hIrr7 hK168 hsimple hmult
            hKsimple hKnc hKmult hLK (hT.parab_omegaPlus hn hOpn hTI hSsum) (by omega)
        · obtain ⟨hOmn, hSsum⟩ := hOm
          have h4n : 4 ≤ n' := s16k_four_le_of_isOmegaMinus hT.quasi hOmn
          by_cases hn : 6 ≤ n'
          · exact s16t3_special_false_of_parabolic_three h h3 hT hIrr7 hK168 hsimple hmult
              hKsimple hKnc hKmult hLK (hT.parab_omegaMinus hn hOmn hTI hSsum) (by omega)
          · have hn4 : n' = 4 := by
              obtain ⟨hev, -⟩ := hOmn
              obtain ⟨r, hr⟩ := hev
              omega
            exact h.false_of_count h3 hT hIrr7
              (Or.inl ⟨Or.inr (Or.inr (by simpa [hn4] using hOmn)), Or.inr hK168⟩)
        · obtain ⟨hAltn, hSsum⟩ := hAlt
          have h5n : 5 ≤ n' := s16k_five_le_of_isAlt hT.quasi hAltn
          by_cases hn : 8 ≤ n'
          · exact s16t3_special_false_of_parabolic_three h h3 hT hIrr7 hK168 hsimple hmult
              hKsimple hKnc hKmult hLK (hT.parab_alt hn hAltn hTI hSsum) (by omega)
          · have hcardSL : Nat.card ↥(lBar V₀ V hV L) = 20160 := by
              obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := hL4
              rw [Nat.card_congr e.toEquiv,
                CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two (by simpa using hKcard)]
            have hcardAlt := s15k_six_alt_card hAltn (by omega)
            rw [hcardSL] at hcardAlt
            have hn567 : n' = 5 ∨ n' = 6 ∨ n' = 7 := by omega
            rcases hn567 with rfl | rfl | rfl <;> norm_num at hcardAlt
      · exact h.false_of_count h3 hT hIrr7
          (Or.inl ⟨Or.inr (Or.inr hOm4), Or.inr hK168⟩)
      ·
        obtain ⟨hsimple, hmult⟩ :=
          s16t3_simple_and_mult hGA hSchur
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOm6, by norm_num⟩))))
        obtain ⟨I, -, hTI, hInat⟩ := hT.exists_stable_natural
        have hnat : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) (lBar V₀ V hV L) I
            (I ⊓ fixV (lBar V₀ V hV L)) 1 := s16t3_shape_branch_omegaMinus hInat hOm6
        have hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) 2 := by
          simpa using hT.parab_omegaMinus (n := 6) (by norm_num) hOm6 hTI hnat
        exact s16t3_special_false_of_parabolic_three h h3 hT hIrr7 hK168 hsimple hmult
          hKsimple hKnc hKmult hLK hP (by norm_num)
      · exact h.false_of_count h3 hT hIrr7 (Or.inl ⟨Or.inr (Or.inl hA5), Or.inr hK168⟩)
      · exact h.false_of_alt_six_seven_L3 h3 hT hIrr7 (Or.inl hA6) hK168
      · exact h.false_of_alt_six_seven_L3 h3 hT hIrr7 (Or.inr hA7) hK168

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
