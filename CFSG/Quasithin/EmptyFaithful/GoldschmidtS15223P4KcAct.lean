module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KcAut
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GRank
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct
public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4.Kc

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

noncomputable def quotEquiv {X : Subgroup G} (hq : IsLnTwoQuot X 3) :
    OTwoQuot X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open (↥X) 2).symm).trans hq.some

omit [Finite G] in
theorem card_quot {X : Subgroup G} (hq : IsLnTwoQuot X 3) : Nat.card (OTwoQuot X) = 168 := by
  rw [Nat.card_congr (quotEquiv hq).toEquiv]
  exact S153E58.card_statedSL_three_two

omit [Finite G] in
theorem not_mem_pCoreOf_of_orderOf {X : Subgroup G} (hX2 : IsPGroup 2 ↥(pCoreOf 2 X)) {e : G}
    (he3 : orderOf e = 3) : e ∉ pCoreOf 2 X := fun h => by
  have he : e ^ 3 = 1 := he3 ▸ pow_orderOf_eq_one e
  have := S15223P4.G.eq_one_of_isPGroup_two_of_pow_three hX2 h he
  rw [this, orderOf_one] at he3
  omega

theorem false_of_perfect (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (hq : IsLnTwoQuot X 3) {Y : Subgroup G} (hYI : Y ≤ Mc ⊓ I) (hY : ⁅Y, Y⁆ = Y) {e : G}
    (heY : e ∈ Y) (heX : e ∈ X) (he3 : orderOf e = 3) : False := by
  have he3' : e ^ 3 = 1 := he3 ▸ pow_orderOf_eq_one e
  have hecore : e ∉ pCoreOf 2 X := not_mem_pCoreOf_of_orderOf (pCoreOf_isPGroup 2 X) he3
  set M0 : Subgroup G := X ⊓ (Mc ⊓ I) with hM0
  set A : Subgroup G := sOf152 T Mc M B₀ ⊓ X with hA
  have hAX : IsSylowTwoOf A X := hN.A_sylow
  have hAM0 : A ≤ M0 := le_inf inf_le_right (inf_le_left.trans (S_le_inf152 c.inputs))
  have hO2M0 : pCoreOf 2 X ≤ M0 := hAX.pCoreOf_le.trans hAM0
  have hM0X : M0 ≤ X := inf_le_left
  have hM0Mc : M0 ≤ Mc := inf_le_right.trans inf_le_left
  have heM0 : e ∈ M0 := ⟨heX, hYI heY⟩
  set ebar : OTwoQuot X := QuotientGroup.mk ⟨e, heX⟩ with hebar
  have hebar_mem : ebar ∈ imageOTwoQuot X M0 := mem_imageOTwoQuot_iff.mpr ⟨e, heX, heM0, rfl⟩
  have hebar3 : ebar ^ 3 = 1 := by
    rw [hebar, ← QuotientGroup.mk_pow]
    have : (⟨e, heX⟩ : ↥X) ^ 3 = 1 := Subtype.ext he3'
    rw [this]
    rfl
  have hebar1 : ebar ≠ 1 := fun h => hecore (by
    rw [hebar, QuotientGroup.eq_one_iff, SBc16.mem_pCore_iff_coe] at h
    exact h)
  have h3 : 3 ∣ Nat.card (imageOTwoQuot X M0) := by
    have hord : orderOf ebar = 3 := orderOf_eq_prime hebar3 hebar1
    have := orderOf_dvd_natCard (⟨ebar, hebar_mem⟩ : ↥(imageOTwoQuot X M0))
    rwa [Subgroup.orderOf_mk, hord] at this
  have h8 : 8 ∣ Nat.card (imageOTwoQuot X M0) := by
    have hle : imageOTwoQuot X A ≤ imageOTwoQuot X M0 := imageOTwoQuot_mono hAM0
    have hidx : (imageOTwoQuot X A).index ∣ (A.subgroupOf X).index :=
      Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
    have hodd : ¬ 2 ∣ (imageOTwoQuot X A).index := fun h => hAX.2.2 (h.trans hidx)
    have hmul := Subgroup.card_mul_index (imageOTwoQuot X A)
    rw [card_quot hq] at hmul
    have hcop : Nat.Coprime (2 ^ 3) (imageOTwoQuot X A).index :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).pow_left 3
    have h1 : 2 ^ 3 ∣ Nat.card (imageOTwoQuot X A) * (imageOTwoQuot X A).index := by
      rw [hmul]
      norm_num
    exact (hcop.dvd_of_dvd_mul_right h1).trans (Subgroup.card_dvd_of_le hle)
  have hM : imageOTwoQuot X M0 ≠ ⊤ := by
    intro htop
    apply hN.not_le_Mc
    intro x hx
    have hx' : (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot X) ∈ imageOTwoQuot X M0 :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨m, hmX, hmM0, hmk⟩ := mem_imageOTwoQuot_iff.mp hx'
    have h1 : (⟨m, hmX⟩ : ↥X)⁻¹ * ⟨x, hx⟩ ∈ CFSG.Open.pCore 2 ↥X := QuotientGroup.eq.mp hmk
    have h2 : m⁻¹ * x ∈ pCoreOf 2 X := (SBc16.mem_pCore_iff_coe X _).mp h1
    have h4 : x = m * (m⁻¹ * x) := by group
    rw [h4]
    exact Subgroup.mul_mem _ (hM0Mc hmM0) (hM0Mc (hO2M0 h2))
  have hYN : Y ≤ Subgroup.normalizer (X : Set G) := hYI.trans (inf_le_right.trans hN.normal)
  have hYM0 : Y ≤ Subgroup.normalizer (M0 : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hYN hg, Subgroup.le_normalizer (hYI hg)⟩
  let ρY : ↥Y →* MulAut (OTwoQuot X) := (SBc16.actHom X).comp (Subgroup.inclusion hYN)
  have hYtop : commutator ↥Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subtype_commutator, hY, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hRperf : ⁅ρY.range, ρY.range⁆ = ρY.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hYtop]
  have hstab : ∀ α ∈ ρY.range,
      (imageOTwoQuot X M0).map α.toMonoidHom = imageOTwoQuot X M0 := by
    rintro α ⟨y, rfl⟩
    have h := SBc16.map_actHom_imageOTwoQuot X (hYN y.2) hM0X
    have hc : conjSub (y : G) M0 = M0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYM0 y.2)
    rw [hc] at h
    exact h
  have hbot := eq_bot_of_perfect_stab (quotEquiv hq) h8 h3 hM hRperf hstab
  have hρe : SBc16.actHom X ⟨e, hYN heY⟩ = 1 := by
    have : ρY ⟨e, heY⟩ ∈ ρY.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have hcentral : ∀ t : OTwoQuot X, ebar * t = t * ebar := by
    intro t
    induction t using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, hk⟩ := x
    have h1 := DFunLike.congr_fun hρe (QuotientGroup.mk ⟨k, hk⟩ : OTwoQuot X)
    rw [SBc16.actHom_mk X (hYN heY) hk, MulAut.one_apply] at h1
    have h2 : (QuotientGroup.mk ⟨e * k * e⁻¹, (Subgroup.mem_normalizer_iff.mp (hYN heY) k).mp hk⟩ :
        OTwoQuot X) = ebar * QuotientGroup.mk ⟨k, hk⟩ * ebar⁻¹ := by
      rw [hebar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [h2] at h1
    calc ebar * QuotientGroup.mk ⟨k, hk⟩ = ebar * QuotientGroup.mk ⟨k, hk⟩ * ebar⁻¹ * ebar := by
          group
      _ = QuotientGroup.mk ⟨k, hk⟩ * ebar := by rw [h1]
  have hψ : (quotEquiv hq) ebar = 1 := by
    refine S153E58.statedSL_center fun t => ?_
    obtain ⟨t', rfl⟩ := (quotEquiv hq).surjective t
    rw [← map_mul, ← map_mul, hcentral t']
  exact hebar1 ((quotEquiv hq).injective (by rw [hψ, map_one]))

end S15223P4.Kc

end CFSG.Quasithin
