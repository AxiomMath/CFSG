module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SH1
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo
public import CFSG.RankThree.PartTwo.Sec4.Item49OddChar
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.HeisSmallModel
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

@[expose] def Row427Cent (S : Type) [Group S] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, Late.IsE27 A →
    partTwoE G = partTwoF G → aschbacherSolvableCore 3 G = ⊥ → ∀ L : Subgroup G, IsComponent L →
    Nonempty (L ⧸ Subgroup.center L ≃* S) →
    ∀ d ∈ A, d ≠ 1 →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
    ¬ L ≤ Subgroup.centralizer {d} →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {d} : Subgroup G), IsComponent K →
      (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5)) ∨
        (d ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype ∧
          IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3)))) →
      A ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → False

@[expose] def RowOf427Cent (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → Row427Cent S

@[expose] def AutRankLeTwo (S : Type) [Group S] : Prop :=
  ∀ B : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9

theorem AutRankLeTwo.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutRankLeTwo Y) : AutRankLeTwo X := by
  intro B hB
  have h1 := h (B.map (MulAut.congr e).toMonoidHom) (isElemAbelian_map _ hB)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h1

theorem autRankLeTwo_of_card {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (h27 : ¬ 27 ∣ Nat.card S) : AutRankLeTwo S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro B hB
  have hBp : IsPGroup 3 B := by
    refine IsPGroup.iff_orderOf.mpr fun x => ?_
    have hx : (x : MulAut S) ^ 3 = 1 := hB.2 x x.2
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx))
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  set π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  have hBi : B ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
    have hmp : IsPGroup 3 (B.map π) := hBp.map π
    have h1 : Nat.card (B.map π) = 1 := by
      rcases hmp.card_eq_or_dvd with h | h
      · exact h
      · exact absurd (h.trans (Subgroup.card_subgroup_dvd_card _)) hout
    intro b hb
    have hbm : π b ∈ B.map π := ⟨b, hb, rfl⟩
    rw [Subgroup.card_eq_one] at h1
    rw [h1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hbm
    exact hbm
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun α : MulAut S => α g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = x * g * x⁻¹ * x := by rw [h]
        _ = x * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hBS : Nat.card B ∣ Nat.card S := by
    refine (Subgroup.card_dvd_of_le hBi).trans ?_
    change Nat.card (MulAut.conj : S →* MulAut S).range ∣ _
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  rw [hk] at hBS ⊢
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> norm_num at hlt
  exact h27 ((pow_dvd_pow 3 hk3).trans hBS)

section Row

theorem row427_of_cent
    {S : Type} [Group S] (hC : Row427Cent S) (hR : AutRankLeTwo S) :
    Row427 S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK hKt
  by_cases hCA : A ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
      rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
        (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
        (mem_thetaComponents_of_isComponent3 hL)
    let ψ : A →* MulAut S :=
      (MulAut.congr e).toMonoidHom.comp ((RonanK429.descAut L).comp (Subgroup.inclusion hAN))
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : RonanK429.descAut L (Subgroup.inclusion hAN a) = 1 :=
        (map_eq_one_iff (MulAut.congr e) (MulAut.congr e).injective).mp ha
      have h2 := (RonanK429.descAut_eq_one_iff hL.1.1 _).mp h1
      have hmem : (a : G) ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨a.2, h2⟩
      rw [hCA, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hAtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup A) := by
      have h := isElemAbelian_comap A.subtype A.subtype_injective hA.1
      rwa [← Subgroup.subgroupOf, Subgroup.subgroupOf_self] at h
    have hB := hR ψ.range (by
      rw [MonoidHom.range_eq_map]
      exact isElemAbelian_map ψ hAtop)
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hA.2] at hB
    norm_num at hB
  · exact hC G hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK hKt hCA

theorem rowOf427_of_cent_card
    {X : Type} [Group X] (hC : RowOf427Cent X)
    (hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X))
    (h27 : ¬ 27 ∣ Nat.card X) : RowOf427 X := fun S _ _ hs hna ⟨e⟩ => by
  haveI := hs
  refine row427_of_cent (hC S hs hna ⟨e⟩) (autRankLeTwo_of_card
    (RonanK429H.center_eq_bot_of_simple_nonab hna) ?_ (by rwa [Nat.card_congr e.toEquiv]))
  rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]

theorem kH1_four_SL_five_of_cent
    (hC : RowOf427Cent (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1))) :
    RowOf427 (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine rowOf427_of_cent_card hC ?_ ?_
  · have hd := higher_linear_outer_order_divides_field_gcd_bound
      (k := GaloisField 5 1) (p := 5) (f := 1) (n := 4) (by norm_num) le_rfl (by norm_num)
      (GaloisField.card 5 1 (by norm_num))
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (projSLEquivProjectiveSL 4 (GaloisField 5 1))).toEquiv] at hd
    intro h3
    have h3' := h3.trans hd
    norm_num at h3'
  · have hc := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_four_mul (GaloisField 5 1)
    rw [GaloisField.card 5 1 (by norm_num)] at hc
    norm_num at hc
    have h : Nat.card (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1)) = 7254000000 := by
      omega
    rw [h]
    norm_num

theorem kH1_four_Sp_five_of_cent
    (hC : RowOf427Cent (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1))) :
    RowOf427 (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 (by norm_num)]; norm_num
  have h2 : (2 : GaloisField 5 1) ≠ 0 := by
    intro h
    have h5 : (5 : GaloisField 5 1) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaloisField 5 1) 5
    have : (1 : GaloisField 5 1) = 0 := by linear_combination h5 - 2 * h
    exact one_ne_zero this
  refine rowOf427_of_cent_card hC ?_ ?_
  · have e₀ : CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (GaloisField 5 1)) :=
      ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
        (MulEquiv.subgroupCongr
          (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 (GaloisField 5 1)))).symm
    have hodd : ringChar (GaloisField 5 1) ≠ 2 := by
      rw [ringChar.eq (GaloisField 5 1) 5]
      norm_num
    have h := Item49OddChar.not_three_dvd_card_outer_psp4 hodd
      (Item49OddChar.subsingleton_ringAut_of_card_prime (by norm_num) hK)
    rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      e₀).toEquiv] at h
  · have hc := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSp_two_mul (GaloisField 5 1) h2
    rw [hK] at hc
    norm_num at hc
    have h : Nat.card (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1)) = 4680000 := by
      omega
    rw [h]
    norm_num

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
