module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectBridge
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
import CFSG.RankThree.PartTwo.Sec6.Item65Two
import CFSG.GH74.GLS.C3.Layer1.Thm1L32Layer
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeC
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA6

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint
open CFSG.LieType.Ree

section AlmostSimple

theorem thirteen_dvd_card_of_sq {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y}
    (hsq : ∀ y : Y, y ^ 2 ∈ D) (h13 : 13 ∣ Nat.card Y) : 13 ∣ Nat.card D := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 13 h13
  have hx13 : x ^ (2 * 6 + 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hxD : x ∈ D :=
    HardMathSupport.Dickson.I271.TabCo1.mem_of_sq_mem_of_pow_eq_one (hsq x) hx13
  have : orderOf (⟨x, hxD⟩ : D) = 13 := by rw [Subgroup.orderOf_mk]; exact hx
  rw [← this]
  exact orderOf_dvd_natCard _

end AlmostSimple

section Ree


theorem thirteen_dvd_ordTwistedF4 (b : ℕ) : 13 ∣ ordTwistedF4 (2 ^ (2 * b + 1)) := by
  unfold ordTwistedF4
  have h : 13 ∣ (2 ^ (2 * b + 1)) ^ 6 + 1 := by
    have h1 : (2 ^ (2 * b + 1)) ^ 6 = 64 ^ (2 * b + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h1]
    have h2 := Odd.nat_add_dvd_pow_add_pow 64 1 (⟨b, rfl⟩ : Odd (2 * b + 1))
    rw [one_pow] at h2
    exact (show 13 ∣ 64 + 1 by norm_num).trans h2
  exact (((Dvd.dvd.mul_left h _).mul_right _).mul_right _).mul_right _

theorem simple_commutator_reeGamma {Y : Type} [Group Y] {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (e : Y ≃* ReeTag.F4.reeGamma k b) :
    IsSimpleGroup ↥(commutator Y) ∧ ∀ y : Y, y ^ 2 ∈ commutator Y := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card k = 2 := by simpa using hk
    have : CharP k 2 := ‹CharP k ReeTag.F4.prime›
    set R := reeFixed ReeTag.F4 k 0 with hR
    set eR : R ≃* ReeTag.F4.reeGamma k 0 := ReeTag.reeFixedEquivReeGamma k 0 with heR
    set D := commutator R with hD
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    have hDn : D.Normal := Subgroup.commutator_normal ⊤ ⊤
    have hsimple : ∀ N : Subgroup D, N.Normal → N = ⊥ ∨ N = ⊤ := by
      intro N hN
      rcases hT.eq_bot_or_eq_of_le hk2 (N.map D.subtype) (Subgroup.map_subtype_le N)
          (by
            rintro d hd _ ⟨m, hm, rfl⟩
            exact ⟨⟨d, hd⟩ * m * ⟨d, hd⟩⁻¹, hN.conj_mem m hm ⟨d, hd⟩, rfl⟩) with h | h
      · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h)
      · right
        rw [eq_top_iff]
        intro m _
        have hm : (m : R) ∈ N.map D.subtype := by rw [h]; exact m.2
        obtain ⟨m₁, hm₁, he⟩ := hm
        rwa [show m = m₁ from Subtype.ext he.symm]
    haveI : Nontrivial D :=
      ⟨⟨⟨hT.g₀, hT.g₀_mem⟩, 1, fun h => hT.g₀_ne_one (congrArg Subtype.val h)⟩⟩
    haveI hDs : IsSimpleGroup D := ⟨hsimple⟩
    have hsq : ∀ r : R, r ^ 2 ∈ D := by
      intro r
      have hr : r ∈ D ⊔ Subgroup.zpowers hT.g₁ := by
        rw [hT.commutator_sup_zpowers_eq_top hk2]
        exact Subgroup.mem_top r
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hr
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [hD, ← Abelianization.ker_of R, MonoidHom.mem_ker]
      have hy1 : Abelianization.of y = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hy
      have hg1 : Abelianization.of (hT.g₁ ^ 2) = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hT.g₁_sq_mem
      rw [map_pow, map_mul, hy1, one_mul, map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, ← map_pow, hg1, one_zpow]
    let f : Y ≃* R := e.trans eR.symm
    have hfD : (commutator Y).map f.toMonoidHom = D := by
      rw [_root_.map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective, hD]
      rfl
    refine ⟨((f.subgroupMap (commutator Y)).trans (MulEquiv.subgroupCongr hfD)).isSimpleGroup,
      fun y => ?_⟩
    have hmem : f (y ^ 2) ∈ (commutator Y).map f.toMonoidHom := by
      rw [hfD, map_pow]
      exact hsq (f y)
    obtain ⟨z, hz, hzy⟩ := hmem
    rw [← f.injective hzy]
    exact hz
  · haveI : IsSimpleGroup (ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    haveI : IsSimpleGroup Y := e.isSimpleGroup
    haveI : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    haveI : Group.IsPerfect Y :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hYtop : commutator Y = ⊤ := Group.IsPerfect.commutator_eq_top (G := Y)
    refine ⟨((MulEquiv.subgroupCongr hYtop).trans Subgroup.topEquiv).isSimpleGroup, fun y => ?_⟩
    rw [hYtop]
    exact Subgroup.mem_top _

theorem false_of_inner_largeRee {X : Type} [Group X] [Finite X] {a : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F LieType.Ree.ReeTag.F4.prime] (hF : Nat.card F = 2 ^ (2 * a + 1))
    (ψ : X ≃* LieType.Ree.ReeTag.F4.reeGamma F a) {P : Subgroup X} (hP : IsA6Sub P) {g : X}
    (hg3 : g ^ 3 = 1) (hgP : ∀ p ∈ P, p * g = g * p) (hg1 : g ≠ 1) : False := by
  obtain ⟨R, hRP, hR, hR9, -⟩ := hP.exists_elemAbelian_nine
  have hgR : g ∉ R := fun hgR =>
    hg1 (hP.eq_one_of_commute (hRP hgR) hgP
      (by rw [show 9 = 3 * 3 from rfl, pow_mul, hg3, one_pow]))
  obtain ⟨hF', hFcard⟩ := Sec6.isElemAbelian_sup_zpowers_three hR hgR hg3
    (fun k hk => hgP k (hRP hk))
  have hle := Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a F hF
    ((R ⊔ Subgroup.zpowers g).map ψ.toMonoidHom) (Sec4.isElemAbelian_map ψ.toMonoidHom hF')
  rw [Subgroup.card_map_of_injective ψ.injective, hFcard, hR9] at hle
  omega

theorem false_of_outer_largeRee {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G}
    (hc3 : c ^ 3 = 1) {n : ℕ}
    (h : ReeTitsModel (K ⧸ aschbacherSolvableCore 3 K) .twistedF4 2 n) (hA6 : HasA6Cent K c)
    (hout : InducesOuterTheta c K) : False := by
  obtain ⟨-, a', ha1, -, Kf, _, _, _, hKf, ⟨e⟩⟩ := exists_mulEquiv_reeGamma h
  obtain ⟨b, k', _, _, _, hk', -, ⟨eC⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha1 hKf e hc3 hout
  obtain ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩ := hA6
  have hPsub : IsA6Sub P := ⟨isPerfect_of_mem_thetaComponentsIn hP, ⟨e6⟩⟩
  set α := Item426.thetaAut K hcN with hα
  have hPC : P ≤ Item426.fixSub α := le_of_mem_thetaComponentsIn hP
  have hbar : Sec8.barCentralizer (Subgroup.zpowers c) K = Item426.fixSub α := by
    ext y
    rw [KFacts.mem_barCentralizer_zpowers_iff hcN y]
    exact Iff.rfl
  let eF : Item426.fixSub α ≃* ReeTag.F4.reeGamma k' b :=
    (MulEquiv.subgroupCongr hbar).symm.trans eC
  have hsn : (P.subgroupOf (Item426.fixSub α)).IsSubnormal :=
    (mem_thetaComponentsIn_iff.mp hP).2.2.1
  obtain ⟨hDs, hsq⟩ := simple_commutator_reeGamma hk' eF
  have h13 : 13 ∣ Nat.card (Item426.fixSub α) := by
    rw [Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b k' hk' eF]
    exact thirteen_dvd_ordTwistedF4 b
  have hP'perf : Group.IsPerfect (P.subgroupOf (Item426.fixSub α)) := by
    have := hPsub.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom) (MulEquiv.surjective _)
  have hP'ne : P.subgroupOf (Item426.fixSub α) ≠ ⊥ := fun hb =>
    hPsub.ne_bot ((Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hPC)
  have hD : P.subgroupOf (Item426.fixSub α) = commutator (Item426.fixSub α) :=
    GH74.GLS.C3.Layer1.Thm1L32.perfect_subnormal_eq_commutator hDs _ hP'ne
      (Subgroup.commutator_eq_self (H := P.subgroupOf (Item426.fixSub α))) hsn
  let ePD : P ≃* commutator (Item426.fixSub α) :=
    (Subgroup.subgroupOfEquivOfLe hPC).symm.trans (MulEquiv.subgroupCongr hD)
  haveI : IsSimpleGroup ↥P := ePD.isSimpleGroup
  have h360 : Nat.card P = 360 := hPsub.card_eq_of_isSimpleGroup
  have hD13 : 13 ∣ Nat.card (commutator (Item426.fixSub α)) := thirteen_dvd_card_of_sq hsq h13
  rw [← Nat.card_congr ePD.toEquiv, h360] at hD13
  omega

theorem largeRee611 {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    {n : ℕ} (hn : Odd n) (h : ReeTitsModel (K ⧸ aschbacherSolvableCore 3 K) .twistedF4 2 n)
    (hA6 : HasA6Cent K c) : False := by
  by_cases hin : KFacts.IsInnerAut (Item426.thetaAut K hA6.choose)
  · obtain ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩ := hA6
    have hPsub : IsA6Sub P := ⟨isPerfect_of_mem_thetaComponentsIn hP, ⟨e6⟩⟩
    obtain ⟨-, a, ha, hfa, F, _, _, _, hF, ⟨ψ⟩⟩ := exists_mulEquiv_reeGamma h
    set α := Item426.thetaAut K hcN with hα
    have hPC : P ≤ Item426.fixSub α := le_of_mem_thetaComponentsIn hP
    obtain ⟨g, hg⟩ := hin
    have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot ψ
        (LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a F hF)
    obtain ⟨hg3, hg1, hgP⟩ := inner_data hZ hα3 hα1 hg hPC
    exact false_of_inner_largeRee hF ψ hPsub hg3 hgP hg1
  · exact false_of_outer_largeRee hc3 h hA6 ⟨hA6.choose, hin⟩

end Ree

end CFSG.RankThree.PartTwo.Sec8.Hering611R
