module

public import CFSG.Quasithin.EmptyFaithful.S153D52
public import CFSG.Quasithin.EmptyFaithful.S153D43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def Input15343NotA4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → ¬ IsAlt 4 ↥Yp

namespace S153D

section Generic

theorem card_eq_three_of_exponent_three {P : Type*} [Group P] [Finite P] (hP : ∀ x : P, x ^ 3 = 1)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup P) = 1) : Nat.card P = 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := fun x => ⟨1, by simpa using hP x⟩
  obtain ⟨a, ha⟩ := hPp.exists_card_eq
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup P)
  rw [hr, pow_one] at hEc
  have h3 : 3 ∣ Nat.card P := hEc ▸ Subgroup.card_subgroup_dvd_card E
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero] at ha
      rw [ha] at h3
      omega
    · exact h0
  by_contra hne
  have ha2 : 2 ≤ a := by
    rcases (by omega : a = 1 ∨ 2 ≤ a) with h1 | h2
    · exact absurd (by rw [ha, h1]; norm_num) hne
    · exact h2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 3
    (show 3 ^ 2 ∣ Nat.card P from ha ▸ pow_dvd_pow 3 ha2)
  have hKcomm : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hK
  have hKel : IsElemAbelian 3 K := ⟨hKcomm, fun x _ => hP x⟩
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : K ≤ ⊤) hKel hK
  omega

theorem isElemAbelianOfRank_of_card_153 {p n : ℕ} [hp : Fact p.Prime] {A : Type*} [CommGroup A]
    [Finite A] (hA : ∀ x : A, x ^ p = 1) (hcard : Nat.card A = p ^ n) :
    IsElemAbelianOfRank p n A := by
  classical
  let inst : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (x.toMul ^ p) = 0
    rw [hA]
    rfl
  have hfinite : Module.Finite (ZMod p) (Additive A) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) (Additive A) = n := by
    have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive A) _ _ inst hfinite
    rw [Nat.card_zmod, show Nat.card (Additive A) = Nat.card A from rfl, hcard] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  have hfree : @Module.Free (ZMod p) (Additive A) _ _ inst :=
    @Module.Free.of_divisionRing (ZMod p) (Additive A) _ _ inst
  let b : Module.Basis (Fin n) (ZMod p) (Additive A) :=
    @Module.finBasisOfFinrankEq (ZMod p) (Additive A) _ _ inst hfree _ hfinite n hfin
  exact ⟨MulEquiv.toAdditiveLeft.symm
    (LinearEquiv.toAddEquiv (@Module.Basis.equivFun _ _ _ _ _ inst _ b))⟩

end Generic

end S153D

namespace Hyp153

open S153D

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem card_OTwoQuot_of_pRank_one (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {X : Subgroup G}
    (hXY : X ≤ Y153 Mc M) (hr : CFSG.Open.pRank 3 X = 1) : Nat.card (OTwoQuot X) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, -⟩ := h.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hXY
  obtain ⟨⟨-, -, hexp⟩, -⟩ := h.Ystar_structure h113
  set Ys := imageOTwoQuot M (Y153 Mc M) with hYs
  set Q := imageOTwoQuot M X with hQ
  have hQY : Q ≤ Ys := imageOTwoQuot_mono hXY
  have hQ3 : ∀ x : ↥Q, x ^ 3 = 1 := fun x =>
    Subtype.ext (by simpa using congrArg Subtype.val (hexp ⟨(x : OTwoQuot M), hQY x.2⟩))
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Q) = 1 := by
    have hp1 : 1 < 3 := by norm_num
    have e1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ
    have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥X) := by
      intro hd
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
      rw [hk] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have e2 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥X) hnd
    have e3 := pRank_top_subtype (p := 3) X
    rw [← e1]
    calc CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot X))
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) := e2
      _ = CFSG.Open.pRank 3 X := e3
      _ = 1 := hr
  rw [Nat.card_congr φ.toEquiv]
  exact card_eq_three_of_exponent_three hQ3 hrank

end Hyp153

namespace S153D

variable {G : Type} [Group G] [Finite G]

theorem input15343Open_of_notA4 (h113 : StageLemma14113) (hA4 : Input15343NotA4) :
    Input15343Open := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have h2 := c.facts25.case_two
  have h3 := hh.lemma_15_3_11_three h113 h2 c.inH
  have hYC : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
    rw [h2.2]
    exact (oTwoUpper_le _).trans inf_le_right
  have hb1 : ⁅V₁, Yp⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
  have hV₁C : V₁ ≤ Subgroup.centralizer (Yp : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb1
  have hc : ⁅V₁, L⁆ ≠ ⊥ := by
    intro hbot
    apply c.c33.not_le
    rw [Subgroup.commutator_comm] at hbot
    exact (Subgroup.centralizer_le_normalizer (V₁ : Set G) |>.trans' (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)).trans h3.2.1
  refine ⟨c.facts25.yp_eq, hh.hyp.card_OTwoQuot_of_pRank_one h113 hh.Yp_le_Y153 c.rank, hb1,
    ⟨?_, ?_⟩, hc, ?_, hA4 G T Mc M V₁ V₂ Yp I L t c⟩
  · rw [h2.2]
    exact hh.hyp.commutator_V₂_Yplus h113 hh.decomp
  · have hel : IsElemAbelian 2 V₂ := isElemAbelian_mono_152 hh.hyp.elemAbelian hh.decomp.le₂
    let _ : CommGroup ↥V₂ := commGroupOfElemAbelian hel
    exact isElemAbelianOfRank_of_card_153 (p := 2) (n := 2)
      (fun x => Subtype.ext (by simpa using hel.2 (x : G) x.2))
      (by rw [hh.decomp.card₂]; norm_num)
  · intro heq
    have hV₁S : V₁ ≤ Sgp153 T V₁ ⊓ Subgroup.centralizer (Yp : Set G) :=
      le_inf (le_inf (fun x hx => hh.hyp.VZ_le_T (hh.decomp.le₁ hx)) Subgroup.le_normalizer)
        hV₁C
    rw [heq] at hV₁S
    exact hc (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => (hV₁S hx).2)

end S153D

end CFSG.Quasithin
