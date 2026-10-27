module

public import CFSG.Quasithin.EmptyFaithful.SBc15312
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Quasithin.EmptyFaithful.S153GExtra

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family (GL32 center_GL32 slEquivGL)
open scoped commutatorElement

namespace SBc

section GL32

variable {Q : Type} [Group Q]

theorem eq_one_of_commute_of_equiv_GL32 (e : Q ≃* GL32) {q : Q} (hq : ∀ r : Q, r * q = q * r) :
    q = 1 := by
  have h : e q ∈ Subgroup.center GL32 := Subgroup.mem_center_iff.mpr fun g => by
    obtain ⟨r, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hq r]
  rw [center_GL32, Subgroup.mem_bot] at h
  exact e.injective (by rw [h, map_one])

private theorem congr_conj (e : Q ≃* GL32) (q : Q) :
    MulAut.congr e (MulAut.conj q) = MulAut.conj (e q) :=
  MulEquiv.ext fun x => by simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_conj_of_odd_of_equiv_GL32 (e : Q ≃* GL32) {α : MulAut Q} (hα : Odd (orderOf α)) :
    ∃ m : Q, α = MulAut.conj m := by
  obtain ⟨s, hs⟩ := Subgroup.mul_self_mem_of_index_two
    CFSG.LieType.SteinbergBR.AutGL32.index_inner (MulAut.congr e α)
  have h2 : α * α = MulAut.conj (e.symm s) := by
    apply (MulAut.congr e).injective
    rw [map_mul, congr_conj, MulEquiv.apply_symm_apply]
    exact hs.symm
  obtain ⟨k, hk⟩ := hα
  refine ⟨(e.symm s) ^ (k + 1), ?_⟩
  have h3 : α = (α * α) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf α + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h3, h2, ← map_pow]

end GL32

section Action

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inducesInner_of_equiv_GL32 {Yp L : Subgroup G} (hYN : Yp ≤ Subgroup.normalizer (L : Set G))
    (hYO : oTwoUpper Yp = Yp) (e : OTwoQuot L ≃* GL32) : InducesInnerModO2153 Yp L := by
  have : (CFSG.Open.pCore 2 ↥L).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
  set Φ : Subgroup.normalizer (L : Set G) →* MulAut (OTwoQuot L) :=
    SteinbergBS.conjQuotientHom L (CFSG.Open.pCore 2 ↥L) with hΦ
  set H : Subgroup G := ((MulAut.conj : OTwoQuot L →* MulAut (OTwoQuot L)).range.comap Φ).map
    (Subgroup.normalizer (L : Set G)).subtype with hH
  have hodd : ∀ y ∈ Yp, Odd (orderOf y) → y ∈ H := by
    intro y hy ho
    have hyN := hYN hy
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    have hord : orderOf (Φ ⟨y, hyN⟩) ∣ orderOf y := by
      refine (orderOf_map_dvd Φ ⟨y, hyN⟩).trans ?_
      rw [Subgroup.orderOf_mk]
    obtain ⟨m, hm⟩ := exists_conj_of_odd_of_equiv_GL32 e (Odd.of_dvd_nat ho hord)
    exact ⟨m, hm.symm⟩
  have hYH : Yp ≤ H := by
    conv_lhs => rw [← hYO]
    exact (Subgroup.closure_le H).mpr fun y hy => hodd y hy.1 hy.2
  intro y hy
  obtain ⟨g, hg, rfl⟩ := hYH hy
  obtain ⟨m, hm⟩ := hg
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective m
  refine ⟨(l : G), l.2, fun x hx => ?_⟩
  have h1 := DFunLike.congr_fun hm (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot L)
  have h2 : ((Subgroup.normalizerMonoidHom L g ⟨x, hx⟩ : ↥L) : OTwoQuot L) =
      ((l * ⟨x, hx⟩ * l⁻¹ : ↥L) : OTwoQuot L) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact h1.symm
  rw [QuotientGroup.eq_iff_div_mem, mem_pCore_iff'] at h2
  simpa [div_eq_mul_inv, Subgroup.normalizerMonoidHom_apply_apply_coe] using h2

end Action

section Main

theorem input15312TwoL3_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Input15312TwoL3 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL3
  obtain ⟨eS⟩ := hL3
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hLmem : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 hh c.ctx.inH hLmem
  let e : OTwoQuot L ≃* GL32 :=
    ((QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥L)).symm.trans eS).trans
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.trans
        (slEquivGL 3))
  have hcenterless : ∀ y ∈ L, (∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L) → y ∈ pCoreOf 2 L := by
    intro y hyL hy
    have h1 : (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : OTwoQuot L) = 1 := by
      refine eq_one_of_commute_of_equiv_GL32 e fun r => ?_
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective r
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
        mem_pCore_iff']
      simpa [div_eq_mul_inv, mul_assoc] using hy l l.2
    exact (mem_pCore_iff' _).mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hinner : InducesInnerModO2153 Yp L := inducesInner_of_equiv_GL32 hYN hh.oTwoUpper_eq e
  have hexp : ∀ y ∈ Yp, Odd (orderOf y) → y ^ 3 = 1 := fun y hy ho =>
    pow_three_of_odd_of_struct c.facts.struct_Yp hy ho
  have hr1 : CFSG.Open.pRank 3 L = 1 := by
    refine le_antisymm ?_ c.conc.2.2.1
    have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥L) := by
      intro hd
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).exists_card_eq
      rw [hk] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥L) hnd
    have h2 := pRank_top_subtype (p := 3) L
    have hcard : Nat.card (OTwoQuot L) = 168 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32
    have hle := CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd (X := OTwoQuot L)
      Nat.prime_three (by rw [hcard]; decide)
    rw [← h2, ← h1]
    exact hle
  have hne : oTwoUpper (Yp ⊓ L) ≠ ⊥ := c.c16.YL_ne
  have h3dvd : 3 ∣ Nat.card ↥(Yp ⊓ L) :=
    (three_dvd_card_oTwoUpper hexp (inf_le_left : Yp ⊓ L ≤ Yp) hne).trans
      (Subgroup.card_dvd_of_le (oTwoUpper_le _))
  exact core15312Two ⟨⟨hYN, hcenterless, hinner⟩, hexp, hr1, h3dvd⟩ hh.oTwoUpper_eq c.ctx.rank hne
    c.facts.struct_Yp

end Main

end SBc

end CFSG.Quasithin
