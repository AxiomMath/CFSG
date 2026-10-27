module

public import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
public import CFSG.RankThree.GF2n.Tim77.Sec21

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.Timmesfeld.Bridge

theorem sec414ash_isOddTransp_image {U : Type} [Group U] (W : Subgroup U) [W.Normal] {E : Set U}
    (hsq : ∀ x ∈ E, x * x = 1) (hnotW : ∀ x ∈ E, x ∉ W)
    (hprod : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) ∨
      ∃ n : ℕ, Odd n ∧ orderOf (x * y) = 2 * n ∧ (x * y) ^ n ∈ W) :
    Asc72.IsOddTransp (QuotientGroup.mk' W '' E) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, hsq x hx, map_one]
    · intro h1
      exact hnotW x hx ((QuotientGroup.eq_one_iff x).mp h1)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have hdvd : orderOf (QuotientGroup.mk' W (x * y)) ∣ orderOf (x * y) := orderOf_map_dvd _ _
    rcases hprod x hx y hy with h | h | ⟨n, hn, -, hnW⟩
    · exact Or.inl (hdvd.trans h)
    · exact Or.inr (h.of_dvd_nat hdvd)
    · refine Or.inr (hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_))
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hnW

theorem sec414ash_image_eq_conj {U : Type} [Group U] (W : Subgroup U) [W.Normal] {E : Set U}
    (hinv : ∀ (g x : U), x ∈ E → g * x * g⁻¹ ∈ E)
    (hone : ∀ x ∈ E, ∀ y ∈ E, ∃ g : U, g * x * g⁻¹ * y⁻¹ ∈ W) {x₀ : U} (hx₀ : x₀ ∈ E) :
    QuotientGroup.mk' W '' E = {r | IsConj (QuotientGroup.mk' W x₀) r} := by
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨g, hg⟩ := hone x₀ hx₀ y hy
    have h1 : QuotientGroup.mk' W (g * x₀ * g⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact isConj_iff.mpr ⟨QuotientGroup.mk' W g, by simpa using h1⟩
  · intro hr
    have hr' : IsConj (QuotientGroup.mk' W x₀) r := hr
    obtain ⟨c, hc⟩ := isConj_iff.mp hr'
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective W c
    exact ⟨u * x₀ * u⁻¹, hinv u x₀ hx₀, by rw [← hc]; simp⟩

theorem sec414ash_commute_of_commute_mk {U : Type} [Group U] (W : Subgroup U) [W.Normal]
    {x y : U} (hx : x * x = 1) (hy : y * y = 1) (hcomm : (x * y) ^ 2 ∈ W → x * y = y * x)
    (h : Commute (QuotientGroup.mk' W x) (QuotientGroup.mk' W y)) : x * y = y * x := by
  apply hcomm
  have h1 : QuotientGroup.mk' W (x * y) = QuotientGroup.mk' W (y * x) := by
    rw [map_mul, map_mul]
    exact h.eq
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h2 : (x * y) ^ 2 = (x * y) * (y * x)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi, sq]
  rw [h2]
  have h3 : QuotientGroup.mk' W ((x * y) * (y * x)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).mp h3

theorem sec414ash_isElemAbelian_image {U : Type} [Group U] (W : Subgroup U) [W.Normal]
    {E : Set U} (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, (x * y) ^ 2 ∈ W → x * y = y * x)
    (helem : ∀ d ∈ E, IsElemAbelian 2 (Subgroup.closure {e | e ∈ E ∧ e * d = d * e})) :
    ∀ dh ∈ QuotientGroup.mk' W '' E,
      IsElemAbelian 2 (Subgroup.closure {e | e ∈ QuotientGroup.mk' W '' E ∧ Commute e dh}) := by
  rintro _ ⟨d, hd, rfl⟩
  have hset : {e | e ∈ QuotientGroup.mk' W '' E ∧ Commute e (QuotientGroup.mk' W d)} =
      QuotientGroup.mk' W '' {e | e ∈ E ∧ e * d = d * e} := by
    ext r
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hc⟩
      exact ⟨e, ⟨he, sec414ash_commute_of_commute_mk W (hsq e he) (hsq d hd)
        (hcomm e he d hd) hc⟩, rfl⟩
    · rintro ⟨e, ⟨he, hc⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, (show Commute e d from hc).map _⟩
  rw [hset, ← MonoidHom.map_closure]
  exact Asc72.otg2_isElemAbelian_map _ (helem d hd)

theorem sec414ash_isRootInvolutionSet {R : Type} [Group R] {D : Set R}
    (hD : Asc72.IsOddTransp D) : CFSG.Timmesfeld.IsRootInvolutionSet D := by
  refine ⟨hD.1, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rcases hD.2 d hd e he with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
      · exact Or.inr (Or.inr (h1 ▸ odd_one))
      · exact Or.inl h2
    · exact Or.inr (Or.inr h)
  · exfalso
    rcases hD.2 d hd e he with h | h
    · rw [h4] at h
      omega
    · rw [h4] at h
      exact absurd h (by decide)

theorem sec414ash_not_isSolvable {R : Type} [Group R] [Finite R] {D : Set R}
    (hS : Asc72.Setup R D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    (hO2 : CFSG.pCore 2 R = ⊥) (hA : ∃ a ∈ D, ∃ b ∈ D, a * b = b * a ∧ a * b ≠ 1) :
    ¬ Group.IsSolvable R := by
  intro hsolv
  obtain ⟨d₀, hd₀⟩ := hS.isClass
  have hH : Tim77Lemma21.Hyp R D d₀ :=
    ⟨sec414ash_isRootInvolutionSet hS.oddT, hd₀, hsolv, fun d hd => (hE d hd).1⟩
  have hZ : ZStarCase R := Tim77Lemma21.zStarCase_of_pCore_eq_bot hH hO2 hS.gen
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hA
  obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj ha hb)
  have hcZ : c ∈ fusionZStar R := by
    rw [show fusionZStar R = ⊤ from hZ]
    exact Subgroup.mem_top c
  have hcc : QuotientGroup.mk' (fusionOddCore R) c ∈ Subgroup.center (R ⧸ fusionOddCore R) :=
    hcZ
  have hcenter := Subgroup.mem_center_iff.mp hcc (QuotientGroup.mk' (fusionOddCore R) a)
  have hba : QuotientGroup.mk' (fusionOddCore R) b = QuotientGroup.mk' (fusionOddCore R) a := by
    rw [← hc, map_mul, map_mul, map_inv, ← hcenter, mul_assoc, mul_inv_cancel, mul_one]
  have haa : a * a = 1 := hS.oddT.mul_self_eq_one ha
  have hbb : b * b = 1 := hS.oddT.mul_self_eq_one hb
  have hab1 : QuotientGroup.mk' (fusionOddCore R) (a * b) = 1 := by
    rw [map_mul, hba, ← map_mul, haa, map_one]
  have hmem : a * b ∈ fusionOddCore R := (QuotientGroup.eq_one_iff _).mp hab1
  have hsq : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hodd : Odd (Nat.card (fusionOddCore R)) := Tim77Lemma21.odd_card_oddCore R
  exact hne (Asc72.otg2_eq_one_of_odd_sq hodd hmem hsq)

theorem sec414_bender_quotient
    {U : Type} [Group U] [Finite U] (E : Set U)
    (hinv : ∀ (g x : U), x ∈ E → g * x * g⁻¹ ∈ E)
    (hgen : Subgroup.closure E = ⊤)
    (hsq : ∀ x ∈ E, x * x = 1)
    (hnotW : ∀ x ∈ E, x ∉ CFSG.pCore 2 U)
    (hprod : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) ∨
      ∃ n : ℕ, Odd n ∧ orderOf (x * y) = 2 * n ∧ (x * y) ^ n ∈ CFSG.pCore 2 U)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, (x * y) ^ 2 ∈ CFSG.pCore 2 U → x * y = y * x)
    (helem : ∀ d ∈ E, IsElemAbelian 2 (Subgroup.closure {e | e ∈ E ∧ e * d = d * e}))
    (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x)
    (hone : ∀ x ∈ E, ∀ y ∈ E, ∃ g : U, g * x * g⁻¹ * y⁻¹ ∈ CFSG.pCore 2 U)
    (hA : ∃ x ∈ E, ∃ y ∈ E, x * y = y * x ∧ x * y ∉ CFSG.pCore 2 U) :
    CFSG.BenderSuzuki.IsBenderGroup
        ((U ⧸ CFSG.pCore 2 U) ⧸ Subgroup.center (U ⧸ CFSG.pCore 2 U)) ∧
    ∀ x : U, IsPGroup 2 (Subgroup.zpowers x) →
      (QuotientGroup.mk' (Subgroup.center (U ⧸ CFSG.pCore 2 U))
        (QuotientGroup.mk' (CFSG.pCore 2 U) x) = 1) → x ∈ CFSG.pCore 2 U := by
  obtain ⟨x₀, hx₀, -, -, -⟩ := hnc
  have hodd := sec414ash_isOddTransp_image (CFSG.pCore 2 U) hsq hnotW hprod
  have hcls := sec414ash_image_eq_conj (CFSG.pCore 2 U) hinv hone hx₀
  have hgen' : Subgroup.closure (QuotientGroup.mk' (CFSG.pCore 2 U) '' E) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have hS : Asc72.Setup (U ⧸ CFSG.pCore 2 U) (QuotientGroup.mk' (CFSG.pCore 2 U) '' E) :=
    ⟨⟨_, hcls⟩, hodd, hgen'⟩
  have hE := sec414ash_isElemAbelian_image (CFSG.pCore 2 U) hsq hcomm helem
  have hbot : CFSG.pCore 2 (U ⧸ CFSG.pCore 2 U) = ⊥ := Tim77Lemma21.pCore_quot_bot U
  have hA' : ∃ a ∈ QuotientGroup.mk' (CFSG.pCore 2 U) '' E,
      ∃ b ∈ QuotientGroup.mk' (CFSG.pCore 2 U) '' E, a * b = b * a ∧ a * b ≠ 1 := by
    obtain ⟨x, hx, y, hy, hxy, hxyW⟩ := hA
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 U) x, ⟨x, hx, rfl⟩,
      QuotientGroup.mk' (CFSG.pCore 2 U) y, ⟨y, hy, rfl⟩, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, hxy]
    · rw [← map_mul]
      intro h1
      exact hxyW ((QuotientGroup.eq_one_iff _).mp h1)
  have hns := sec414ash_not_isSolvable hS hE hbot hA'
  have hO2 : CFSG.pCore 2 (U ⧸ CFSG.pCore 2 U) ≤ Subgroup.center (U ⧸ CFSG.pCore 2 U) := by
    rw [hbot]
    exact bot_le
  refine ⟨(Asc72.isBenderGroup_center_quot_of_elemComponents hS hE hO2 hns).2, ?_⟩
  intro x hx hx1
  have hz : QuotientGroup.mk' (CFSG.pCore 2 U) x ∈ Subgroup.center (U ⧸ CFSG.pCore 2 U) :=
    (QuotientGroup.eq_one_iff _).mp hx1
  have hle : Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 U) x) ≤
      Subgroup.center (U ⧸ CFSG.pCore 2 U) := Subgroup.zpowers_le.mpr hz
  haveI hnorm := Subgroup.normal_of_le_center hle
  have hp : IsPGroup 2 (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 U) x)) := by
    have := hx.map (QuotientGroup.mk' (CFSG.pCore 2 U))
    rwa [MonoidHom.map_zpowers] at this
  have hle2 : Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 U) x) ≤
      CFSG.pCore 2 (U ⧸ CFSG.pCore 2 U) := le_sSup ⟨hnorm, hp⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 U) x = 1 := by
    have := hle2 (Subgroup.mem_zpowers (QuotientGroup.mk' (CFSG.pCore 2 U) x))
    rwa [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).mp h1

end CFSG.RankThree.GF2n.Tim77

end
