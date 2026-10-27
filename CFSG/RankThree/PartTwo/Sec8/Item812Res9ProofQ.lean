module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofFinal
import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofKFacts
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofSp4
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open Item812Res3 (IsMaxPSub)

namespace Item812Res9

theorem cube_mul_eq {G : Type*} [Group G] {R : Subgroup G} {u : G}
    (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hR9 : ∀ x ∈ R, x ^ 9 = 1) (hu3 : u ^ 3 = 1)
    (huR : ∀ r ∈ R, u * r * u⁻¹ ∈ R) (huΩ : ∀ s ∈ R, s ^ 3 = 1 → u * s = s * u)
    {r : G} (hr : r ∈ R) : (u * r) ^ 3 = r ^ 3 := by
  have hr1R : u * r * u⁻¹ ∈ R := huR r hr
  have hr3 : u * r ^ 3 = r ^ 3 * u :=
    huΩ (r ^ 3) (R.pow_mem hr 3) (by rw [← pow_mul]; exact hR9 r hr)
  have hr13 : (u * r * u⁻¹) ^ 3 = r ^ 3 := by
    rw [conj_pow, hr3, mul_inv_cancel_right]
  set d := r⁻¹ * (u * r * u⁻¹) with hd
  have hdR : d ∈ R := R.mul_mem (R.inv_mem hr) hr1R
  have hcomm : Commute r⁻¹ (u * r * u⁻¹) := hRc _ (R.inv_mem hr) _ hr1R
  have hd3 : d ^ 3 = 1 := by
    rw [hd, hcomm.mul_pow, hr13, inv_pow, inv_mul_cancel]
  have hud : u * d = d * u := huΩ d hdR hd3
  have hr1 : u * r * u⁻¹ = r * d := by rw [hd, mul_inv_cancel_left]
  have h2 : u * (u * r * u⁻¹) * u⁻¹ = r * d * d := by
    rw [hr1, show u * (r * d) * u⁻¹ = (u * r * u⁻¹) * (u * d * u⁻¹) by group, hud,
      mul_inv_cancel_right, hr1]
  have hrd : Commute r d := hRc r hr d hdR
  calc (u * r) ^ 3 = (u * r * u⁻¹) * (u * (u * r * u⁻¹) * u⁻¹) * (u ^ 3 * r) := by
        rw [pow_succ, pow_succ, pow_one]
        group
    _ = (r * d) * (r * d * d) * r := by rw [h2, hu3, one_mul, hr1]
    _ = r ^ 3 * d ^ 3 := by
      rw [show (r * d) * (r * d * d) * r = (r * d) * (r * d) * (d * r) by group, ← hrd.eq,
        ← hrd.mul_pow, pow_succ, pow_succ, pow_one]
    _ = r ^ 3 := by rw [hd3, mul_one]

variable {G : Type} [Group G] [Finite G]


theorem q_struct (h45 : Sec4.Item4_5) (h84 : Pair84A) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n)
    {Q : Subgroup G} (hQ : IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)))
    (hAQN : A ≤ Subgroup.normalizer (Q : Set G)) :
    A ≤ Q ∧ a ∉ sec8R Q X ∧ Nat.card Q ≤ 3 * Nat.card (sec8R Q X) ∧
      (∀ q ∈ Q, ∀ r ∈ sec8R Q X, q * r * q⁻¹ ∈ sec8R Q X) ∧
      ∀ x ∈ Q, ∃ i : ℤ, a ^ i * x ∈ sec8R Q X := by
  classical
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hAB : A ≤ Subgroup.centralizer (sec8B A X : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y (Item812Res4.b_le_a hy) x hx
  have hQA := hQ.2.2 _ (Item812Res4.isPGroup_sup hQ.2.1
    (Item812Res4.isPGroup_of_isElemAbelian hAab) hAQN) le_sup_left (sup_le hQ.1 hAB)
  have hAQ : A ≤ Q := hQA ▸ le_sup_right
  have haQ : a ∈ Q := hAQ haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hbB : b ∈ sec8B A X :=
    ⟨hbA, Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXb)⟩
  have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hQ.1 hg) b hbB).symm)
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hQ.2.1
      hQb X hXb
  have haout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  have haR : a ∉ sec8R Q X := by
    rintro ⟨-, haXC⟩
    exact haout.2 ((Item812Res2.mem_sup_thetaQuotCentralizer_iff haout.1).mp haXC)
  set F := GaloisField 2 3 with hFdef
  set P := StatedProj (StatedSp 2 F) with hPdef
  set e : X ⧸ aschbacherSolvableCore 3 X ≃* P :=
    h.item89_X.some.trans (Sec4.projSpEquivStatedProj 2 F) with he
  set φ : Q →* CFSG.ComponentClassification.OuterAutomorphisms.Outer P :=
    (QuotientGroup.mk' (inner P)).comp ((KFacts.inducedAutHom X e).comp
      (Subgroup.inclusion hQN)) with hφ
  have hφker : ∀ g : Q, φ g = 1 ↔ (g : G) ∈ X ⊔ Sec4.thetaQuotCentralizer X := by
    intro g
    rw [Item812Res2.mem_sup_thetaQuotCentralizer_iff (hQN g.2), hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change IsInnerAut (MulAut.congr e (thetaQuotMulAut X (compAction X ⟨g, hQN g.2⟩))) ↔ _
    exact isInnerAut_congr e _
  have hRker : sec8R Q X = φ.ker.map Q.subtype := by
    ext x
    constructor
    · rintro ⟨hxQ, hxXC⟩
      exact ⟨⟨x, hxQ⟩, (hφker ⟨x, hxQ⟩).mpr hxXC, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.2, (hφker g).mp hg⟩
  have hRcard' : Nat.card (sec8R Q X) = Nat.card φ.ker := by
    rw [hRker, Subgroup.card_map_of_injective Q.subtype_injective]
  have hK : Nat.card F = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num) hK
  obtain ⟨-, -, -, -, -, hcardOut, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (by norm_num) hFr hord hzp
  have hrange3 : Nat.card φ.range ≤ 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 φ.range :=
      hQ.2.1.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have h6 : Nat.card φ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [hcardOut] at this
    rw [hk] at h6 ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · exfalso
      have h9 : 9 ∣ 3 ^ (k + 2) := ⟨3 ^ k, by ring⟩
      have := h9.trans h6
      norm_num at this
  have hQcard : Nat.card Q ≤ 3 * Nat.card (sec8R Q X) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    rw [hRcard', ← h1]
    nlinarith [Nat.card_pos (α := φ.ker)]
  have hnorm : ∀ q ∈ Q, ∀ r ∈ sec8R Q X, q * r * q⁻¹ ∈ sec8R Q X := by
    intro q hq r hr
    have hqrq : q * r * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hr.1) (Q.inv_mem hq)
    refine ⟨hqrq, (hφker ⟨_, hqrq⟩).mp ?_⟩
    have h1 : φ ⟨r, hr.1⟩ = 1 := (hφker ⟨r, hr.1⟩).mpr hr.2
    have h2 : (⟨q * r * q⁻¹, hqrq⟩ : Q) = ⟨q, hq⟩ * ⟨r, hr.1⟩ * ⟨q, hq⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  have hφa1 : φ ⟨a, haQ⟩ ≠ 1 := fun h1 => haR ⟨haQ, (hφker ⟨a, haQ⟩).mp h1⟩
  have hφa3 : φ ⟨a, haQ⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, haQ⟩ : Q) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hφaord : orderOf (φ ⟨a, haQ⟩) = 3 := orderOf_eq_prime hφa3 hφa1
  have hzle : Subgroup.zpowers (φ ⟨a, haQ⟩) ≤ φ.range :=
    (Subgroup.zpowers_le).mpr ⟨⟨a, haQ⟩, rfl⟩
  have hzeq : Subgroup.zpowers (φ ⟨a, haQ⟩) = φ.range :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [Nat.card_zpowers, hφaord]; exact hrange3)
  refine ⟨hAQ, haR, hQcard, hnorm, fun x hx => ?_⟩
  have hxr : φ ⟨x, hx⟩ ∈ Subgroup.zpowers (φ ⟨a, haQ⟩) := hzeq ▸ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxr
  refine ⟨-j, Q.mul_mem (Q.zpow_mem haQ _) hx, (hφker ⟨_, Q.mul_mem (Q.zpow_mem haQ _) hx⟩).mp ?_⟩
  have h2 : (⟨a ^ (-j) * x, Q.mul_mem (Q.zpow_mem haQ _) hx⟩ : Q) =
      (⟨a, haQ⟩ : Q) ^ (-j) * ⟨x, hx⟩ := rfl
  rw [h2, map_mul, map_zpow, ← hj, ← zpow_add, neg_add_cancel, zpow_zero]

theorem mem_b_of_mem_r_of_commute (hW : KF812WreathCent) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n)
    {Pa Q : Subgroup G} (hPa : IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)))
    (hpaeq : Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa) (hBeq : sec8B A X = A ⊓ Y)
    (hQ : IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)))
    (hPaQ : Pa ≤ Subgroup.normalizer (Q : Set G)) {r : G} (hr : r ∈ sec8R Q X)
    (hra : r * a = a * r) : r ∈ sec8B A X := by
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have hCN : Pa ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hPaQ (hPa.1.trans Subgroup.le_normalizer)
  have hS := Item812Res4.isPGroup_sup (hQ.2.1.to_le inf_le_left) hPa.2.1 hCN
  have hSeq := hPa.2.2 _ hS le_sup_right (sup_le inf_le_right hPa.1)
  have hrPa : r ∈ Pa := hSeq ▸ Subgroup.mem_sup_left
    ⟨hr.1, Subgroup.mem_centralizer_singleton_iff.mpr hra⟩
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left
      (show Commute a v from (Subgroup.mem_centralizer_singleton_iff.mp (hPa.1 hv.1)).symm)
        i).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hr' : r ∈ ((Subgroup.zpowers a ⊔ (Pa ⊓ Y) : Subgroup G) : Set G) := by
    rw [hpaeq]
    exact hrPa
  rw [hset] at hr'
  obtain ⟨u, hu, y, hy, huy⟩ := hr'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hyB : ∀ x ∈ sec8B A X, y * x = x * y := by
    intro x hx
    have h1 : r * x = x * r := (Subgroup.mem_centralizer_iff.mp (hQ.1 hr.1) x hx).symm
    have h2 : a ^ i * x = x * a ^ i := congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨a ^ i, A.zpow_mem haA i⟩ ⟨x, Item812Res4.b_le_a hx⟩)
    rw [← huy] at h1
    calc y * x = (a ^ i)⁻¹ * (a ^ i * y * x) := by group
      _ = (a ^ i)⁻¹ * (x * (a ^ i * y)) := by rw [h1]
      _ = (a ^ i)⁻¹ * (x * a ^ i) * y := by group
      _ = (a ^ i)⁻¹ * (a ^ i * x) * y := by rw [h2]
      _ = x * y := by group
  have hBY : sec8B A X ≤ Y := hBeq ▸ inf_le_right
  obtain ⟨k, hk⟩ := hPa.2.1 ⟨y, hy.1⟩
  have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyB' := Item812Res4.mem_of_forall_commute hW h.item89_Y hBY
    (Item812Res4.isElemAbelian_of_le hAab Item812Res4.b_le_a) (Item812Res8.card_sec8B h) hy.2
    hyk hyB
  refine ⟨?_, hr.2⟩
  rw [← huy]
  exact A.mul_mem (A.zpow_mem haA i) (Item812Res4.b_le_a hyB')

end Item812Res9

open Item812Res9


@[expose] def Fin812ROmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      ∀ x ∈ sec8R Q X, x ^ 3 = 1 → x ∈ A

theorem fin812RWeak_of (h45 : Sec4.Item4_5) (h84 : Pair84A)
    (hS : Fin812RStruct) : Fin812RWeak := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ g hg
  obtain ⟨hRc, hRcard, -⟩ := hS G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  obtain ⟨-, -, hQcard, hnorm, hdec⟩ := q_struct h45 h84 h hQ (hAPa.trans hPaQ)
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  set R := sec8R Q X with hRdef
  set Rg := R.map (MulAut.conj g).toMonoidHom with hRgdef
  have hRgcard : Nat.card Rg = 3 ^ 6 := by
    rw [hRgdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hRcard]
  by_contra hne
  have hnle : ¬ Rg ≤ R := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hRgcard, hRcard]))
  obtain ⟨x, hxRg, hxR⟩ := Set.not_subset.mp hnle
  obtain ⟨i, hi⟩ := hdec x (hg hxRg)
  have hRgc : ∀ u ∈ Rg, ∀ v ∈ Rg, u * v = v * u := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, hRc u hu v hv]
  set w := (a ^ i)⁻¹ with hw
  have hxw : x = w * (a ^ i * x) := by rw [hw]; group
  have hwR : w ∉ R := fun hwR => hxR (hxw ▸ R.mul_mem hwR hi)
  have hw1 : w ≠ 1 := fun h1 => hwR (h1 ▸ R.one_mem)
  have hwa : w ∈ Subgroup.zpowers a := Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers a i)
  have haw : a ∈ Subgroup.zpowers w := by
    have hle : Subgroup.zpowers w ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).mpr hwa
    have hw3 : w ^ 3 = 1 := by
      rw [hw, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3,
        one_zpow, inv_one]
    have heq : Subgroup.zpowers w = Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
      exact orderOf_le_of_pow_eq_one (by norm_num) ha3
    rw [heq]
    exact Subgroup.mem_zpowers a
  have hinfB : R ⊓ Rg ≤ sec8B A X := by
    intro s hs
    have hsx : s * x = x * s := hRgc s hs.2 x hxRg
    have hsr : s * (a ^ i * x) = (a ^ i * x) * s := hRc s hs.1 _ hi
    have hsw : s * w = w * s := by
      have h1 : w = x * (a ^ i * x)⁻¹ := by rw [hw]; group
      rw [h1]
      calc s * (x * (a ^ i * x)⁻¹) = (s * x) * (a ^ i * x)⁻¹ := by group
        _ = x * s * (a ^ i * x)⁻¹ := by rw [hsx]
        _ = x * (a ^ i * x)⁻¹ * ((a ^ i * x) * s * (a ^ i * x)⁻¹) := by group
        _ = x * (a ^ i * x)⁻¹ * (s * (a ^ i * x) * (a ^ i * x)⁻¹) := by rw [hsr]
        _ = x * (a ^ i * x)⁻¹ * s := by group
    have hsa : s * a = a * s := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haw
      rw [← hj]
      exact ((Commute.zpow_right (show Commute s w from hsw) j).eq)
    exact mem_b_of_mem_r_of_commute (kF812WreathCent_holds) h hPa hpaeq hBeq hQ hPaQ hs.1 hsa
  have hinf27 : Nat.card (R ⊓ Rg : Subgroup G) ≤ 27 :=
    (Subgroup.card_le_of_le hinfB).trans (Item812Res8.card_sec8B h).le
  have hRgN : Rg ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    Item812Res8.mem_normalizer_of_forall_conj_mem R fun r hr => hnorm u (hg hu) r hr
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hRgN
  have h2 : Nat.card (R ⊔ Rg : Subgroup G) ≤ Nat.card Q :=
    Subgroup.card_le_of_le (sup_le inf_le_left hg)
  rw [hRcard, hRgcard] at h1
  rw [hRcard] at hQcard
  nlinarith

theorem fin812QOmega_of (h45 : Sec4.Item4_5) (h84 : Pair84A) (hS : Fin812RStruct)
    (hO : Fin812ROmega) : Fin812QOmega := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ x hxQ hx3
  obtain ⟨hRc, -, hR9⟩ := hS G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hRO := hO G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  obtain ⟨hAQ, -, -, hnorm, hdec⟩ := q_struct h45 h84 h hQ (hAPa.trans hPaQ)
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  obtain ⟨i, hi⟩ := hdec x hxQ
  set u := (a ^ i)⁻¹ with hu
  have huA : u ∈ A := A.inv_mem (A.zpow_mem haA i)
  have hu3 : u ^ 3 = 1 := hAab.2 u huA
  have hcube := cube_mul_eq hRc hR9 hu3 (fun r hr => hnorm u (hAQ huA) r hr)
    (fun s hs hs3 => congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨u, huA⟩ ⟨s, hRO s hs hs3⟩)) hi
  have hxe : x = u * (a ^ i * x) := by rw [hu]; group
  have hr3 : (a ^ i * x) ^ 3 = 1 := by rw [← hcube, ← hxe, hx3]
  rw [hxe]
  exact A.mul_mem huA (hRO _ hi hr3)

theorem fin812QR_of_res9 (h45 : Sec4.Item4_5) (h84 : Pair84A)
    (hS : Fin812RStruct) (hO : Fin812ROmega) : Fin812QR :=
  fin812QR_of h45 h84 hS (fin812QOmega_of h45 h84 hS hO) (fin812RWeak_of h45 h84 hS)

end CFSG.RankThree.PartTwo.Sec8
