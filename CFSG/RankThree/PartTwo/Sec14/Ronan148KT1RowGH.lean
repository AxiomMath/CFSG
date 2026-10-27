module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowSpor1
public import CFSG.GH74.GLS.Stage2.Local.GHSchMain
public import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVG23
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ree
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec6.BThreeCensus (suzukiOrder)

theorem row_three_pow_ne_two {e : ℕ} (he : 1 ≤ e) : 3 ^ e ≠ 2 := by
  intro h
  have h3 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
  rw [h] at h3
  norm_num at h3

theorem le_inner_of_perfect_outSolvable {S : Type} [Group S]
    (hOut : Group.IsSolvable (Outer S)) (P : Subgroup (MulAut S)) (hPp : Group.IsPerfect ↥P) :
    P ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  intro x hx
  by_contra hxS
  haveI := hPp
  haveI := hOut
  let φ : ↥P →* Outer S :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S)).comp P.subtype
  haveI : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) (MonoidHom.rangeRestrict_surjective φ)
  have hne : φ ⟨x, hx⟩ ≠ 1 := fun h => hxS ((QuotientGroup.eq_one_iff x).mp h)
  haveI : Nontrivial φ.range :=
    ⟨⟨⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable φ.range inferInstance

section KPSz


theorem noSzSection_of_dvd_two_pow_ten_suzuki {M : Type} [Group M] {N : ℕ}
    (hMN : Nat.card M ∣ N) (h10 : ¬ 2 ^ 10 ∣ N) (h1 : ¬ suzukiOrder 1 ∣ N) :
    CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection M := by
  intro X Y _ p f hS
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder_gen hS
  have hdvd : suzukiOrder a ∣ N := by
    rw [← hcard]
    exact (Subgroup.card_quotient_dvd_card Y).trans ((Subgroup.card_subgroup_dvd_card X).trans hMN)
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · obtain rfl : a = 1 := by omega
    exact h1 hdvd
  · refine h10 (dvd_trans ?_ hdvd)
    have hX : 2 ^ 10 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    unfold suzukiOrder
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hX _) _

theorem row143_of_outSolvable {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (hOut : Group.IsSolvable (Outer S))
    (hNo : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection S) : Row143 S := by
  unfold Row143
  intro β hβ3 _ D hDfix hDnorm hDpow P hPK hPcent hPnorm hPperf hP3
  have hPle : P ≤ (MulAut.conj : S →* MulAut S).range :=
    le_inner_of_perfect_outSolvable hOut P hPperf
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_isSimpleGroup hS hnc
  set Y : Subgroup S := P.comap (MulAut.conj : S →* MulAut S) with hYdef
  have hYmap : Y.map (MulAut.conj : S →* MulAut S) = P := by
    rw [hYdef, Subgroup.map_comap_eq, inf_eq_right.mpr hPle]
  let e : Y ≃* P :=
    (Y.equivMapOfInjective (MulAut.conj : S →* MulAut S) hinj).trans (MulEquiv.subgroupCongr hYmap)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [Nat.card_congr e.toEquiv]
    exact hP3
  have hYperf : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hYK : IsKGroup Y := IsKGroup.of_mulEquiv hPK e
  by_contra hP
  have hYne : Y ≠ ⊥ := by
    intro h
    apply hP
    rw [← hYmap, h, Subgroup.map_bot]
  haveI : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  obtain ⟨N, hN, f, hf⟩ := exists_suzuki_section_of_isPerfect hYK hYperf hY3 inferInstance
  haveI := hN
  exact hNo Y N 2 f hf

section Rows


theorem row143_of_ghList_card {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (hGH : CFSG.GH74.GHList S) {N : ℕ}
    (hN : Nat.card S ∣ N) (h10 : ¬ 2 ^ 10 ∣ N) (h1 : ¬ suzukiOrder 1 ∣ N) : Row143 S := by
  haveI := hS
  exact row143_of_outSolvable hS hnc
    (CFSG.GH74.GLS.Stage2.Local.GHSch.ghSchreier_thm S hnc hGH)
    (noSzSection_of_dvd_two_pow_ten_suzuki hN h10 h1)

theorem row143_projSL_three_of {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) {e : ℕ} (he : 1 ≤ e)
    (φ : S ≃* projSL 3 (GaloisField 3 e))
    (h10 : ¬ 2 ^ 10 ∣ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 - 1)))
    (h1 : ¬ suzukiOrder 1 ∣ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 - 1))) :
    Row143 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 3 e :=
    ⟨Nat.prime_three, he, by norm_num,
      fun h => by have := (Prod.mk.inj h).1; norm_num at this,
      fun h => by have := (Prod.mk.inj h).1; norm_num at this⟩
  have hL : CFSG.Blueprint.LieModel S .PSL 3 3 e :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ⟩
  have hGH : CFSG.GH74.GHList S :=
    Or.inr (Or.inr ⟨3, e, Nat.prime_three, he, Or.inl ⟨by norm_num, Or.inr (Or.inl hL)⟩⟩)
  exact row143_of_ghList_card hS hnc hGH
    ((Nat.card_congr φ.toEquiv).trans
      (CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_projSL_three_char_three he)).dvd h10 h1

theorem row143_projSU_three_of {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) {e : ℕ} (he : 1 ≤ e)
    (φ : S ≃* projSU 3 3 e)
    (h10 : ¬ 2 ^ 10 ∣ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)))
    (h1 : ¬ suzukiOrder 1 ∣ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1))) :
    Row143 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 3 e :=
    ⟨Nat.prime_three, he, by norm_num, fun h => row_three_pow_ne_two he (Prod.mk.inj h).2⟩
  have hL : CFSG.Blueprint.LieModel S .PSU 3 3 e :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ⟩
  have hGH : CFSG.GH74.GHList S :=
    Or.inr (Or.inr ⟨3, e, Nat.prime_three, he, Or.inl ⟨by norm_num, Or.inr (Or.inr (Or.inl hL))⟩⟩)
  exact row143_of_ghList_card hS hnc hGH
    ((Nat.card_congr φ.toEquiv).trans
      (CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_projSU_three_char_three he)).dvd h10 h1

theorem rowOf143_l3_three (e : ℕ) (he : 1 ≤ e) (he3 : e ≤ 3) (he2 : e ≠ 2) :
    RowOf143 (projSL 3 (GaloisField 3 e)) := by
  unfold RowOf143
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  obtain rfl | rfl : e = 1 ∨ e = 3 := by omega
  all_goals refine row143_projSL_three_of hS hnc (by norm_num) φ ?_ ?_
  all_goals norm_num [suzukiOrder, Nat.dvd_iff_mod_eq_zero]

theorem rowOf143_u3_three (e : ℕ) (he : 1 ≤ e) (he3 : e ≤ 3) : RowOf143 (projSU 3 3 e) := by
  unfold RowOf143
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  all_goals refine row143_projSU_three_of hS hnc (by norm_num) φ ?_ ?_
  all_goals norm_num [suzukiOrder, Nat.dvd_iff_mod_eq_zero]

theorem rowOf143_g2_three : RowOf143 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group := by
  unfold RowOf143
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  obtain ⟨hadm, K, hF, hFin, hK, ⟨ψ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_three
      (⟨3, 1, Nat.prime_three, Nat.one_pos⟩ : TauCeti.PrimePower) g2ThreeIndex.2 rfl rfl
  have hCEM : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 3 1 :=
    ⟨hadm, K, hF, hFin, hK, ⟨φ.trans ψ⟩⟩
  have hL : CFSG.Blueprint.LieModel S .G2 0 3 1 := Or.inr (Or.inl ⟨rfl, by decide, hCEM⟩)
  have hGH : CFSG.GH74.GHList S :=
    Or.inr (Or.inr ⟨3, 1, Nat.prime_three, le_rfl,
      Or.inl ⟨by norm_num, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))⟩⟩)
  have hN : Nat.card S ∣ CFSG.Open.ordG2 3 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_g2_three_dvd
  exact row143_of_ghList_card hS hnc hGH hN
    (by norm_num [CFSG.Open.ordG2, Nat.dvd_iff_mod_eq_zero])
    (by norm_num [CFSG.Open.ordG2, suzukiOrder, Nat.dvd_iff_mod_eq_zero])

theorem rowOf143_l4_three : RowOf143 (projSL 4 (GaloisField 3 1)) := by
  unfold RowOf143
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num,
      fun h => by have := (Prod.mk.inj h).1; norm_num at this,
      fun h => by have := (Prod.mk.inj h).1; norm_num at this⟩
  have hL : CFSG.Blueprint.LieModel S .PSL 4 3 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ⟩
  have hGH : CFSG.GH74.GHList S :=
    Or.inr (Or.inr ⟨3, 1, Nat.prime_three, le_rfl,
      Or.inr (Or.inl ⟨by norm_num, by norm_num, hL⟩)⟩)
  have hN : Nat.card S ∣ 3 ^ 6 * 16640 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_projSL_four_three_dvd
  exact row143_of_ghList_card hS hnc hGH hN (by norm_num [Nat.dvd_iff_mod_eq_zero])
    (by norm_num [suzukiOrder, Nat.dvd_iff_mod_eq_zero])

theorem rowOf143_u4_three : RowOf143 (projSU 4 3 1) := by
  unfold RowOf143
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by have := (Prod.mk.inj h).1; norm_num at this⟩
  have hL : CFSG.Blueprint.LieModel S .PSU 4 3 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ⟩
  have hGH : CFSG.GH74.GHList S :=
    Or.inr (Or.inr ⟨3, 1, Nat.prime_three, le_rfl,
      Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, hL⟩))⟩)
  have hO : Nat.card (projSU 4 3 1) = 3265920 := by
    have h := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSU_four_mul 3 1 le_rfl
    have h4 : Nat.gcd 4 (3 ^ 1 + 1) = 4 := by norm_num
    rw [h4] at h
    norm_num at h
    omega
  have hN : Nat.card S ∣ 3265920 := ((Nat.card_congr φ.toEquiv).trans hO).dvd
  exact row143_of_ghList_card hS hnc hGH hN (by norm_num [Nat.dvd_iff_mod_eq_zero])
    (by norm_num [suzukiOrder, Nat.dvd_iff_mod_eq_zero])

theorem rowOf143_ree27 (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  unfold RowOf143
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  have hK : Nat.card (GaloisField 3 (2 * 1 + 1)) = 3 ^ (2 * 1 + 1) :=
    GaloisField.card 3 (2 * 1 + 1) (by norm_num)
  haveI : CharP (GaloisField 3 (2 * 1 + 1)) CFSG.LieType.Ree.ReeTag.G2.prime :=
    inferInstanceAs (CharP (GaloisField 3 (2 * 1 + 1)) 3)
  obtain ⟨ψ⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.nonempty_reeGamma_equiv hr hK
  have hN : Nat.card S =
      (3 ^ (2 * 1 + 1)) ^ 3 * ((3 ^ (2 * 1 + 1)) ^ 3 + 1) * (3 ^ (2 * 1 + 1) - 1) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv,
      CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq hK]
  have hREE : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 (2 * 1 + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 1 ⟨hr, ⟨φ⟩⟩
  have hL : CFSG.Blueprint.LieModel S .twistedG2 0 3 3 :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hREE⟩))
  have hGH : CFSG.GH74.GHList S :=
    Or.inr (Or.inr ⟨3, 3, Nat.prime_three, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))⟩)
  exact row143_of_ghList_card hS hnc hGH hN.dvd (by norm_num [Nat.dvd_iff_mod_eq_zero])
    (by norm_num [suzukiOrder, Nat.dvd_iff_mod_eq_zero])

end Rows

end KPSz

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
