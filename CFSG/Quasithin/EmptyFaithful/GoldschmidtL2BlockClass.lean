module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockDataSec
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockG2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockSecC

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace Bridge

namespace L2Block

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)} {n : ℕ}

namespace Ctx

variable (C : Ctx G L n)

include C

theorem natural {KP : ∀ (Y : Type) [Group Y], Prop} (h42 : AsB42With KP)
    (hS : ∀ s : S, s ^ 2 = 1) (hHyp : B4HypWith KP G L) {A : Subgroup (MulAut S)}
    (hA : IsFFStarOffender G A) : ∃ m : ℕ, BinaryNaturalSL L ⊤ ⊥ 2 m := by
  have hc := h42 S hS G L hHyp A hA
  have hq : CFSG.IsQuasisimple ↥L := hHyp.2.2.1
  unfold B42Conclusion at hc
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · obtain ⟨-, ⟨m, hm⟩, -, -⟩ := h1
    exact ⟨m, hm⟩
  · exact (C.case2_false h2).elim
  · exact (C.case3_false hq hA h3).elim
  · exact (C.case4_false hA h4).elim
  · exact (C.case5_false hq hA h5).elim
  · exact (C.case6_false h6).elim
  · exact (C.case7_false h7).elim
  · exact (C.case8_false h8).elim
  · exact (C.case9_false h9).elim
  · obtain ⟨⟨π, hπ⟩, -⟩ := h10
    exact (C.case_sl_false (m := 4) (Or.inl rfl) π hπ.1).elim
  · obtain ⟨-, -, -, -, π, hπ, -⟩ := h11
    exact (C.case_sl_false (m := 5) (Or.inr rfl) π hπ.1).elim

omit [Finite S] in
theorem exp_eq {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (e : ↥(StatedSL 2 K) ≃* ↥L) : m = n := by
  have hm : 1 ≤ m := TypeList.one_le_of_card_eq_pow hK
  have h1 : Nat.card ↥L = 2 ^ m * (4 ^ m - 1) := by
    rw [← Nat.card_congr e.toEquiv,
      Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv.symm,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, hK, ← pow_mul, mul_comm m 2,
      pow_mul]
    norm_num
  rw [C.card_eq] at h1
  exact (GoldL2.two_pow_mul_odd_eq (GoldL2.odd_four_pow_sub_one (by have := C.three_le; omega))
    (GoldL2.odd_four_pow_sub_one hm) h1).1.symm

end Ctx

end L2Block

end Bridge

namespace L246

variable {G : Type} [Group G] [Finite G] {X T L : Subgroup G}

omit [Finite G] in
theorem pRank_top_le_of_sq_mem {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hq : ∀ y : Y, y ^ 2 ∈ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup Y)
  have hEL : E ≤ L := by
    intro x hx
    have hxp : x ^ p = 1 := hE.2 x hx
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have hx' : x = (x ^ 2) ^ (k + 1) := by
      calc x = x ^ p * x := by rw [hxp, one_mul]
        _ = (x ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ]; congr 1; omega
    rw [hx']
    exact L.pow_mem (hq x) (k + 1)
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p L :=
    CFSG.SectionRank.le_pRank hp1 hEL hE hcard
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥L) = CFSG.Open.pRank p L :=
    CFSG.Quasithin.pRank_top_subtype (p := p) L
  omega

namespace BlockDataS

variable {n : ℕ} (D : BlockDataS X T L n)

include D

theorem isLin2Type {KP : ∀ (Y : Type) [Group Y], Prop} (hn : 3 ≤ n) (hK : Bridge.KClosed KP)
    (h42 : Bridge.AsB42With KP) (hKX : KP ↥X)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥X) ≤ 2) :
    IsLin2Type L n := by
  obtain ⟨A, hA, hAc⟩ := D.exists_offender
  have Hs := D.secHyp hA hAc
  have hFF := D.isFFStarOffender hA hAc
  have hV2 : ∀ v : IntMod (VZ T X) D.elem, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hKG : KP ↥(autI D.elem X) :=
    hK.of_hom_surjective hKX (rho1 D.elem D.XN) (rho1_surjective D.elem D.XN)
  have hLA : autI D.elem L ⊔ autI D.elem A ≤ autI D.elem X :=
    sup_le (autI_mono D.elem D.LX) (autI_mono D.elem (hA.1.trans D.TX))
  have hA2 : ∀ a ∈ autI D.elem A, a ^ 2 = 1 := hFF.2.2.1.2
  have hsq := Hs.sqG hA2
  obtain ⟨e₁⟩ := Hs.exists_equiv_autSec
  obtain ⟨e₂⟩ := D.autI_equiv_quot
  have hpsl : IsPSL 2 2 n ↥(autSec (autI D.elem L) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L))) := IsPSL.of_mulEquiv e₁ D.isPSL_autI
  have hSQ : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥(autSec (autI D.elem L ⊔ autI D.elem A)
      (intSub D.elem (blockU L)) (intSub D.elem (blockZ L))) := by
    intro p hp hp2
    refine (pRank_top_le_of_sq_mem (L := (autSec (autI D.elem L) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L))).subgroupOf (autSec (autI D.elem L ⊔ autI D.elem A)
        (intSub D.elem (blockU L)) (intSub D.elem (blockZ L))))
      (fun y => Subgroup.mem_subgroupOf.2 (hsq y y.2)) hp hp2).trans ?_
    have e₃ := Subgroup.subgroupOfEquivOfLe (Bridge.L2Block.SecHypS.le_autSec (A := autI D.elem A)
      (L := autI D.elem L) (U := intSub D.elem (blockU L)) (Z := intSub D.elem (blockZ L)))
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (e₃.trans (e₁.symm.trans e₂)),
      CFSG.SectionRank.pRank_quotient_two_group (CFSG.pCore 2 ↥L) CFSG.pCore_isPGroup hp hp2]
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (Subgroup.inclusion D.LX)
      (Subgroup.inclusion_injective D.LX)).trans (hrank p hp hp2)
  obtain ⟨hHyp, A₂, hA₂⟩ := Hs.b4Hyp hK hV2 hFF hKG hLA hSQ
  have C : Bridge.L2Block.Ctx (autSec (autI D.elem L ⊔ autI D.elem A) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L))) (autSec (autI D.elem L) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L))) n :=
    ⟨hn, hpsl, (Hs.genFitting_eq hA2 hV2).symm, hsq⟩
  obtain ⟨m, hm⟩ := C.natural h42 (Bridge.sec_sq_eq_one hV2 _ _) hHyp hA₂
  obtain ⟨K, hKf, hKfin, hKcard, π, hπ⟩ := hm
  have hπinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
  have hmn : m = n := C.exp_eq hKcard (MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩)
  subst hmn
  exact D.trData.isLin2Type_of_nat hKcard Hs.secRestrict_injective D.hpc hπ hπinj

end BlockDataS

end L246

end CFSG.QuasithinUnique
