module

public import CFSG.Quasithin.Background.KGSchurMult2b
public import CFSG.Quasithin.Background.KGSchurMult2Pf
public import CFSG.GH74.Generic.GKFSporadic
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.Sporadic.Recognition.HSMultiplierCert
public import CFSG.Sporadic.Recognition.RuMultiplier
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHopf
public import Certificates.Certificate15024
public import Certificates.Certificate15026

public section

namespace CFSG.Quasithin

open SchurMult2
open scoped IsMulCommutative

namespace SchurMult2

theorem card_dvd_two_of_le_two' {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 2 ↥(Subgroup.center K)) (h : Nat.card ↥(Subgroup.center K) ≤ 2) :
    Nat.card ↥(Subgroup.center K) ∣ 2 := by
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at h ⊢
  rcases k with _ | _ | k
  · simp
  · simp
  · exfalso
    have : 0 < 2 ^ k := by positivity
    rw [pow_add] at h
    omega

theorem index_range_sq {B : Type*} [CommGroup B] [Finite B] :
    (powMonoidHom 2 : B →* B).range.index = Nat.card (powMonoidHom 2 : B →* B).ker := by
  have h1 := (powMonoidHom 2 : B →* B).range.index_mul_card
  have h2 : Nat.card B = Nat.card (powMonoidHom 2 : B →* B).range *
      Nat.card (powMonoidHom 2 : B →* B).ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hpos : 0 < Nat.card (powMonoidHom 2 : B →* B).range := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem card_ker_sq_le_of_surjective {A Z : Type*} [CommGroup A] [CommGroup Z] [Finite A]
    [Finite Z] (χ : A →* Z) (hχ : Function.Surjective χ) :
    Nat.card (powMonoidHom 2 : Z →* Z).ker ≤ Nat.card (powMonoidHom 2 : A →* A).ker := by
  have hmap : (powMonoidHom 2 : A →* A).range.map χ = (powMonoidHom 2 : Z →* Z).range := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨χ a, by simp⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨a, rfl⟩ := hχ w
      exact ⟨a ^ 2, ⟨a, rfl⟩, by simp⟩
  have h := Subgroup.index_map_dvd (powMonoidHom 2 : A →* A).range hχ
  rw [hmap, index_range_sq, index_range_sq] at h
  exact Nat.le_of_dvd Nat.card_pos h

end SchurMult2

theorem schurMult2A7_holds : SchurMult2A7 := by
  intro K _ _ hK hZ ⟨e⟩
  have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK) e
  rw [CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven.2] at h1
  exact card_dvd_of_dvd_mul_odd hZ (a := 1) (m := 3) (by decide) (by simpa using h1)

theorem schurMult2L2Odd_holds :
    SchurMult2L2Odd := by
  intro p f hp2 K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  obtain ⟨⟨hp, hf, -⟩, -⟩ := id h
  have hgen : (CFSG.Blueprint.Multiplier.genericOrders .PSL 2 p f).1 ∣ 2 := Nat.gcd_dvd_left _ _
  have hgen2 : (CFSG.Blueprint.Multiplier.genericOrders .PSL 2 p f).2 = 1 := rfl
  rw [hgen2, mul_one] at this
  rcases (show p = 3 ∨ 4 ≤ p by have := hp.two_le; omega) with rfl | h4
  · rcases (show f = 2 ∨ f = 1 ∨ 3 ≤ f by omega) with rfl | rfl | h3
    · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 3 2 = (3, 1) := rfl
      rw [he] at this
      exact card_dvd_of_dvd_mul_odd hZ (a := 1) (m := 3) (by decide)
        (this.trans (by simpa using Nat.mul_dvd_mul_right hgen 3))
    · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 3 1 = (1, 1) := rfl
      rw [he] at this
      exact this.trans (by simpa using hgen)
    · obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
      have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 3 (k + 3) = (1, 1) := rfl
      rw [he] at this
      exact this.trans (by simpa using hgen)
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 4 := ⟨p - 4, by omega⟩
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 (k + 4) f = (1, 1) := rfl
    rw [he] at this
    exact this.trans (by simpa using hgen)

theorem schurMult2L35_holds :
    SchurMult2L35 := by
  intro K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 5 1 = (1, 1) := rfl
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 5 1 = (1, 1) := rfl
  rw [hg, he] at this
  exact eq_bot_of_dvd_odd hZ (m := 1) (by decide) (by simpa using this)

theorem schurMult2U35_holds :
    SchurMult2U35 := by
  intro K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row h (by decide))
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 5 1 = (3, 1) := rfl
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 5 1 = (1, 1) := rfl
  rw [hg, he] at this
  exact eq_bot_of_dvd_odd hZ (m := 3) (by decide) (by simpa using this)

theorem schurMult2J1_holds : SchurMult2J1 := fun K _ _ hK hZ hs =>
  CFSG.GH74.Generic.noTwoCover_J1_of_walter (K ⧸ Subgroup.center K) hs K
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK) hZ ⟨MulEquiv.refl _⟩

theorem schurMult2J2_holds :
    SchurMult2J2 := fun K _ _ hK hZ hs =>
  card_dvd_two_of_le_two' hZ
    (CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound K
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.1.1
        ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK)) hZ (Or.inr hs))

theorem schurMult2HS_holds :
    SchurMult2HS := by
  intro K _ _ hK hZ ⟨e⟩
  have e' : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.HS := e
  exact card_dvd_two_of_le_two' hZ
    (CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate (isPerfect hK) e')

section Ru

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Recognition.RuMultiplier

theorem schurMult2Ru_holds :
    SchurMult2Ru := by
  intro K _ _ hK hZ ⟨e⟩
  obtain ⟨hpos, hle⟩ := card_griessHopfMultiplier_J_le
    Certificates.certificate15024 Certificates.certificate15026
  have f := CFSG.Sporadic.Bridge.Ru.nativeEquiv
  have e' : K ⧸ Subgroup.center K ≃* J ruVec := e.trans f
  have h := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := J ruVec)
    (isPerfect hK) e'
  exact card_dvd_two_of_le_two' hZ ((Nat.le_of_dvd hpos h).trans hle)

end Ru

theorem card_ker_sq_l34 :
    Nat.card ↥(powMonoidHom 2 : (Multiplicative (ZMod 3) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →* _).ker = 4 := by
  have h : Nat.card ↥(powMonoidHom 2 : (Multiplicative (ZMod 3) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →* _).ker =
      Nat.card {a : (Multiplicative (ZMod 3) × Multiplicative (ZMod 1)) ×
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) // a ^ 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [MonoidHom.mem_ker, powMonoidHom_apply])
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem schurMult2L34Rank_holds :
    SchurMult2L34Rank := by
  intro K _ _ hK _ h E hEZ hE
  obtain ⟨-, ⟨m⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h
  obtain ⟨ψ, hψ⟩ := CFSG.EvenSporadicStandard.M24Std.exists_surjective_hopfMultiplier hK.1
    (QuotientGroup.mk' (Subgroup.center K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  let A : Type := (Multiplicative (ZMod 3) × Multiplicative (ZMod 1)) ×
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
  let m' : CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K) ≃* A := m
  let χ : A →* ↥(Subgroup.center K) :=
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (Subgroup.center K))).toMonoidHom.comp
      (ψ.comp m'.symm.toMonoidHom)
  have hχ : Function.Surjective χ :=
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (Subgroup.center K))).surjective.comp
      (hψ.comp m'.symm.surjective)
  have h1 := card_ker_sq_le_of_surjective χ hχ
  have h3 : Nat.card ↥(powMonoidHom 2 : A →* A).ker = 4 := card_ker_sq_l34
  replace h1 := h1.trans h3.le
  have h2 : Nat.card E ≤ Nat.card (powMonoidHom 2 : ↥(Subgroup.center K) →* _).ker := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEZ).toEquiv]
    refine Subgroup.card_le_of_le fun x hx => ?_
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact Subtype.ext (hE.2 _ (Subgroup.mem_subgroupOf.mp hx))
  omega

end CFSG.Quasithin
