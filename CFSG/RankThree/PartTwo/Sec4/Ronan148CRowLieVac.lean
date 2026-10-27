module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowRankTwo
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL52
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Background.A318POutCheap

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.GorensteinWalter (PSL2)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem autNoE27_of_not_dvd_factorial {S : Type} [Group S] [Finite S]
    (h : ¬ 27 ∣ (Nat.card S).factorial) : AutNoE27 S := by
  intro A hA
  have hinj : Function.Injective (MulAut.toPerm S) := fun a b hab =>
    MulEquiv.ext fun x => congrArg (fun σ : Equiv.Perm S => σ x) hab
  apply h
  have h1 : Nat.card (A.map (MulAut.toPerm S)) = 27 := by
    rw [Subgroup.card_map_of_injective hinj, hA.2]
  have h2 := Subgroup.card_subgroup_dvd_card (A.map (MulAut.toPerm S))
  rw [h1, Nat.card_perm] at h2
  exact h2

theorem rowSOf148_one_of_ne_three (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (he : 1 ≤ e) : RowSOf148 (projSL 2 (GaloisField p e)) := by
  refine rowSOf148_of_autNoE27 fun S _ _ _ _ ⟨eS⟩ => ?_
  have hchar : ringChar (GaloisField p e) = p := ringChar.eq (GaloisField p e) p
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hp5 : 5 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ (Fact.out : p.Prime)) (by decide)
    · exact h
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [hcard]
    calc 4 ≤ p := by omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  exact (autNoE27_psl2 (by rw [hchar]; exact hp3) h4).of_mulEquiv (eS.trans (projSLEquivPSL _))

theorem rowSOf148_seven_SL2 (n : ℕ) (hn : 1 ≤ n) : RowSOf148 (projSL 2 (GaloisField 2 n)) := by
  refine rowSOf148_of_autNoE27 fun S _ _ _ _ ⟨eS⟩ => ?_
  have hchar : ringChar (GaloisField 2 n) = 2 := ringChar.eq (GaloisField 2 n) 2
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  by_cases hn2 : 2 ≤ n
  · have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact (autNoE27_psl2 (by rw [hchar]; norm_num) h4).of_mulEquiv (eS.trans (projSLEquivPSL _))
  · have hn1 : n = 1 := by omega
    subst hn1
    refine autNoE27_of_not_dvd_factorial ?_
    have hc := RonanK432.card_psl2_mul_gcd (GaloisField 2 1)
    rw [hcard] at hc
    norm_num at hc
    rw [Nat.card_congr (eS.trans (projSLEquivPSL _)).toEquiv, hc]
    decide

theorem rowSOf148_projSL_three (p e : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ e) : RowSOf148 (projSL 3 (GaloisField p e)) :=
  rowSOf148_of_autNoE27 fun _ _ _ _ _ ⟨φ⟩ =>
    (autNoE27_of_card_le_nine (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL hp3 he h3)).of_mulEquiv
      φ

theorem rowSOf148_projSU_three (p e : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (he : 1 ≤ e)
    (hq : 2 < p ^ e) (h3 : ¬ 3 ∣ e) : RowSOf148 (projSU 3 p e) :=
  rowSOf148_of_autNoE27 fun _ _ _ _ _ ⟨φ⟩ =>
    (autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU hp3 he hq h3)).of_mulEquiv φ

theorem rowSOf148_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowSOf148 (projSp 2 (GaloisField p 1)) := by
  refine rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨Fact.out, le_rfl, le_rfl, fun h => by simp at h; omega⟩
  haveI : Finite (projSp 2 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSp 2 (GaloisField p 1)) .PSp 2 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSp 2 (GaloisField p 1)) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen (HeringUnitary.pRank_projSp_four_le_two hp))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSp 2 p ∣ 2 := Nat.gcd_dvd_left 2 _
  have := (h3.trans h2)
  omega

theorem rowSOf148_four_SL_of_mod_two (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 2) :
    RowSOf148 (projSL 4 (GaloisField p 1)) := by
  refine rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSL 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  haveI : Finite (projSL 4 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSL 4 (GaloisField p 1)) .PSL 4 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSL 4 (GaloisField p 1)) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSL 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSOf148_four_SU_of_mod_one (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 1) :
    RowSOf148 (projSU 4 p 1) := by
  refine rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSU 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩
  haveI : Finite (projSU 4 p 1) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSU 4 p 1) .PSU 4 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSU 4 p 1) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine ((autNoE27_of_forall_inner (fun α hα =>
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

theorem rowSOf148_four_G2 :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
      ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
        RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro p _ hp3 q hqp hqe hq
  refine rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨φ⟩ => ?_
  have hM : ChevalleyExceptionalModel S .G2 p 1 := by
    have h := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv φ
      (Census.chevalleyExceptionalModel_G2_of_odd q hq (by omega))
    rwa [hqp, hqe] at h
  have hX : LieModel S .G2 0 p 1 := Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hs hna
  refine (autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 hM.1 hX
      (by decide) (by decide) (by decide)
      (by rw [show lieOrderDivisor .G2 0 p = 1 from rfl]; norm_num) hα) hcen
    (noE27_of_forall (Item434Spor.noE27_of_pRank_le_two
      (Res417Four.pRank_g2_le_two hp3 S hM))))

section Sz


theorem rowSOf148_seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro m hm
  refine rowSOf148_of_autNoE27 fun S _ _ _ _ ⟨e⟩ => ?_
  have hM := Census.suzukiModel_of_index m hm
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := hM
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact KFacts.not_three_dvd_card_suzukiGroup hK
  have hcyc : IsCyclic (Outer S) := by
    have h := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2
      (2 * m + 1) (Census.suzukiModel_of_index m hm)).1.1
    exact isCyclic_of_surjective (equivalence e).symm.toMonoidHom (equivalence e).symm.surjective
  intro A hA
  haveI : IsCyclic (Outer (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group) := by
    obtain ⟨h, -⟩ := CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2
      (2 * m + 1) (Census.suzukiModel_of_index m hm)
    exact h.1
  haveI hcyc : IsCyclic (Outer S) :=
    isCyclic_of_surjective (equivalence e).symm.toMonoidHom (equivalence e).symm.surjective
  haveI : (inner S).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  have hInn : Nat.card (inner S) ∣ Nat.card S := by
    have h1 := Subgroup.card_map_dvd (⊤ : Subgroup S) (MulAut.conj : S →* MulAut S)
    rw [← MonoidHom.range_eq_map, Subgroup.card_top] at h1
    exact h1
  have hAI : A ⊓ inner S = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hA.2, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right hInn
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
  have hinj : Function.Injective ((QuotientGroup.mk' (inner S)).comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : MulAut S) ∈ inner S := (QuotientGroup.eq_one_iff _).mp ha
    have h2 : (a : MulAut S) ∈ A ⊓ inner S := ⟨a.2, h1⟩
    rw [hAI, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  haveI hcycA : IsCyclic A :=
    isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
      (MonoidHom.ofInjective hinj).symm.surjective
  obtain ⟨g, hg⟩ := hcycA.exists_generator
  have hord : orderOf g = 27 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hA.2]
  have hg3 : g ^ 3 = 1 := Subtype.ext (hA.1.2 _ g.2)
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hord] at this
  norm_num at this

end Sz

theorem rowSOf148_eight_SL5 : RowSOf148 (projSL 5 (GaloisField 2 1)) :=
  rowSOf148_of_noE27 ⟨Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num),
    noE27_projSL_five_two⟩

section Tits


theorem rowSOf148_seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := fun ht =>
  rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨e⟩ => by
    have hm : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv e (Census.bridgeExceptional46.tits ht)
    exact autNoE27_of_noE27 (CFSG.Quasithin.A318P.not_dvd_outer_tits hm Nat.prime_three
      (by norm_num)) (center_eq_bot_of_isSimpleGroup hs hna)
      (NoE27.of_mulEquiv e fun D hD =>
        CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits ht hD.1 hD.2)

end Tits

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
