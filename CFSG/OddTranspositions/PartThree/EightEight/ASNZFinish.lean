module

public import CFSG.OddTranspositions.PartThree.EightEight.ASNZShape
public import CFSG.OddTranspositions.PartThree.EightEight.ASNZWreath
public import CFSG.OddTranspositions.PartThree.OddTranspClosure

import CFSG.OddTranspositions.BlockTransitive
import CFSG.OddTranspositions.PartThree.EightEight.ASFacts
import CFSG.OddTranspositions.PartThree.EightEight.ASNZTypes
import CFSG.OddTranspositions.PartThree.EightEight.KOneBender
import CFSG.OddTranspositions.PartThree.EightEight.StarConj
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourAut
import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem mk_center_ne_one_of_ne {X : Type} [Group X] {E : Set X}
    (hS : Setup X E) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) {e : X} (he : e ∈ E) :
    QuotientGroup.mk' (Subgroup.center X) e ≠ 1 := by
  intro h
  have hez : e ∈ Subgroup.center X := (QuotientGroup.eq_one_iff e).mp h
  have heq : ∀ c ∈ E, c = e := by
    intro c hc
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj he hc)
    rw [Subgroup.mem_center_iff.mp hez g, mul_inv_cancel_right]
  exact hab ((heq a ha).trans (heq b hb).symm)

private theorem StandingAS.setup_inClosure_starO (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y)
    (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) :
    Setup (Subgroup.closure (starO hC x w y n s)) (inClosure (starO hC x w y n s)) :=
  setup_inClosure hC.setup.oddT (fun _ ho => DalphaStar_subset hC.isBlock_alpha ho.1)
    (isClass_inClosure_of_conjOrbit_closure_eq ⟨hs.2, hs.1.1.2.mul_right (Commute.refl s)⟩
      (hSt.conjOrbit_closure_starO_eq h86 h87 hT hn hord hs))

theorem StandingAS.commSet_starO_eq (h86 : Lemma8_6) (h87 : Theorem8_7) {hC : HypothesisC D}
    (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) :
    commSet (starO hC x w y n s) s = conjOrbit (localGroup D ((x * y * w) ^ n)) x := by
  classical
  obtain ⟨ht, -, hx, hw, hy, -⟩ := id hT
  have hxcent : x ∈ centSet D ((x * y * w) ^ n) :=
    ⟨ht.1, (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm⟩
  have hsΔ : ∀ a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x, Commute s a := by
    have h : s ∈ {d | d ∈ centSet D ((x * y * w) ^ n) ∧
        d ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x} := hs.1
    rw [setOf_centSet_notMem_eq hC.setup ht hn hord] at h
    exact h.2
  ext a
  constructor
  ·
    rintro ⟨haO, has, hane⟩
    by_contra haΔ
    have haz : Commute a ((x * y * w) ^ n) := by
      have h := haO.2.mul_right has.inv_right
      rwa [mul_inv_cancel_right] at h
    have haN : a ∈ starN D hC.alpha (starSigma D x w y n) :=
      ⟨⟨⟨DalphaStar_subset hC.isBlock_alpha haO.1, haz⟩, haΔ⟩, haO.1⟩
    exact hSt.not_commute_of_mem_starN_of_ne h86 h87 hT hn hord haN hs hane has
  · intro ha
    have haD : a ∈ DalphaStar D hC.alpha :=
      conjOrbit_subset_DalphaStar hC hSt.derivedSeries_ne ht hx hw hy hn hord ha
    have haz : Commute a ((x * y * w) ^ n) :=
      (conjOrbit_subset_centSet hC.setup.normal hxcent ha).2
    have has : Commute a s := (hsΔ a ha).symm
    refine ⟨⟨haD, haz.mul_right has⟩, has, ?_⟩
    rintro rfl
    exact hs.1.2 ha

theorem StandingAS.disconnected_starO (h86 : Lemma8_6) (h87 : Theorem8_7) {hC : HypothesisC D}
    (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) :
    Disconnected (inClosure (starO hC x w y n s)) := by
  classical
  obtain ⟨ht, -, hx, -, -, -⟩ := id hT
  have hsO : s ∈ starO hC x w y n s := ⟨hs.2, hs.1.1.2.mul_right (Commute.refl s)⟩
  obtain ⟨c, hc⟩ := hSt.starGamma_nonempty h86 h87 hT hn hord hs
  have hcO : c ∈ starO hC x w y n s := ⟨hc.1, hc.2.2⟩
  have hsx : Commute s x := by
    have h : s ∈ {d | d ∈ centSet D ((x * y * w) ^ n) ∧
        d ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x} := hs.1
    rw [setOf_centSet_notMem_eq hC.setup ht hn hord] at h
    exact h.2 x (self_mem_conjOrbit _ x)
  have hJ : ∀ {p q : G}, p ∈ DalphaStar D hC.alpha → q ∈ DalphaStar D hC.alpha → Commute p q →
      (starBar D hC.alpha p)⁻¹ * starBar D hC.alpha q ∈ starSocle D hC.alpha := fun hp hq hpq =>
    hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hp)
      (starBar_mem_imageClass hC hq)
      (starBar_commute (mem_Halpha_of_mem_DalphaStar hp) (mem_Halpha_of_mem_DalphaStar hq) hpq)
  let S : Set (Subgroup.closure (starO hC x w y n s)) :=
    {p | (p : G) ∈ starO hC x w y n s ∧
      (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha (p : G) ∈ starSocle D hC.alpha}
  have hclosed : ∀ p ∈ S, ∀ q ∈ inClosure (starO hC x w y n s), Commute p q → q ∈ S := by
    rintro p ⟨hpO, hpx⟩ q hq hpq
    refine ⟨hq, ?_⟩
    have h := (starSocle D hC.alpha).mul_mem hpx (hJ hpO.1 hq.1 (hpq.map (Subgroup.subtype _)))
    rwa [mul_assoc, mul_inv_cancel_left] at h
  refine ⟨⟨s, Subgroup.subset_closure hsO⟩, hsO, ⟨c, Subgroup.subset_closure hcO⟩, hcO,
    fun h => ?_⟩
  exact hc.2.1 (mem_of_reach hclosed ⟨hsO, hJ hx hs.2 hsx.symm⟩ h).2

theorem StandingAS.exists_mulEquiv_l2Wreath_three_closure_starO (h1 : TheoremOne)
    (h86 : Lemma8_6) (h87 : Theorem8_7) (h91 : Theorem9_1) {hC : HypothesisC D}
    (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) :
    ∃ f : ℕ, 2 ≤ f ∧ Nonempty (Subgroup.closure (starO hC x w y n s) ⧸
      Subgroup.center (Subgroup.closure (starO hC x w y n s)) ≃* L2Wreath f 3) := by
  classical
  obtain ⟨ht, -, -, -, -, -⟩ := id hT
  set O := starO hC x w y n s with hO
  set Y := Subgroup.closure O with hY
  have hsO : s ∈ O := ⟨hs.2, hs.1.1.2.mul_right (Commute.refl s)⟩
  have hcomm : commSet O s = conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    hSt.commSet_starO_eq h86 h87 hT hn hord hs
  have hΔO : conjOrbit (localGroup D ((x * y * w) ^ n)) x ⊆ O := fun a ha =>
    (show a ∈ commSet O s by rw [hcomm]; exact ha).1
  let sY : Y := ⟨s, Subgroup.subset_closure hsO⟩
  have himage : Y.subtype '' commSet (inClosure O) sY = commSet O s := by
    ext a
    constructor
    · rintro ⟨b, ⟨hbO, hbs, hbne⟩, rfl⟩
      exact ⟨hbO, hbs.map Y.subtype, fun h => hbne (Subtype.ext h)⟩
    · rintro ⟨haO, has, hane⟩
      exact ⟨⟨a, Subgroup.subset_closure haO⟩,
        ⟨haO, Subtype.ext has.eq, fun h => hane (congrArg Subtype.val h)⟩, rfl⟩
  have hmemΔ : ∀ b : Y, b ∈ commSet (inClosure O) sY ↔
      (b : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := by
    intro b
    rw [← hcomm, ← himage]
    constructor
    · intro hb
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b', hb', hbb'⟩
      rwa [← Subtype.ext hbb']
  have hmemC : ∀ {g : Y}, (g : G) ∈ Subgroup.closure (commSet O s) →
      g ∈ Subgroup.closure (commSet (inClosure O) sY) := by
    intro g hg
    rw [← himage, ← MonoidHom.map_closure] at hg
    exact (Subgroup.mem_map_iff_mem Y.subtype_injective).mp hg
  have hLG : LocalBender O s := by
    refine ⟨?_, ?_⟩
    · rw [hcomm]
      intro a ha b hb
      have horb := conjOrbit_closure_conjOrbit_eq hC.setup ht hn hord
      rw [← horb] at ha hb
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨k, hk, rfl⟩ := hb
      exact ⟨k * g⁻¹, Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hg), by group⟩
    · rw [hcomm]
      exact isBenderGroup_closure_conjOrbit_quotient_center h1 h86 h87 hC hSt.rad hSt.not_o4
        hSt.faithful hSt.derivedSeries_ne ht hn hord
  have hL : LocalBender (inClosure O) sY :=
    LocalBender.of_injective Y.subtype Y.subtype_injective himage hLG
  have hzΔ := (pow_mem_closure_conjOrbit hC.setup ht hn hord).1
  let zY : Y := ⟨(x * y * w) ^ n, Subgroup.closure_mono hΔO hzΔ⟩
  have hz : zY ∈ Subgroup.closure (commSet (inClosure O) sY) := hmemC (by rw [hcomm]; exact hzΔ)
  have hzs : zY * sY ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hle : Subgroup.closure O ≤ Subgroup.centralizer {(x * y * w) ^ n * s} :=
      (Subgroup.closure_le _).mpr fun o ho => Subgroup.mem_centralizer_singleton_iff.mpr ho.2.eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle g.2)
  have h31 : ∀ a ∈ commSet (inClosure O) sY, ∃ a' ∈ commSet (inClosure O) sY, a' ≠ a ∧
      Commute a a' ∧ {r | r ∈ commSet (inClosure O) sY ∧ Commute r a} = {a, a', a * a' * zY} := by
    intro a ha
    obtain ⟨a', ha', hne', hcomm', hset⟩ :=
      exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hSt.rad hSt.not_o4 hSt.faithful
        hSt.derivedSeries_ne ht hn hord ((hmemΔ a).mp ha)
    let a'Y : Y := ⟨a', Subgroup.subset_closure (hΔO ha')⟩
    refine ⟨a'Y, (hmemΔ a'Y).mpr ha', fun h => hne' (congrArg Subtype.val h),
      Subtype.ext hcomm'.eq, ?_⟩
    ext r
    have key := Set.ext_iff.mp hset (r : G)
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at key ⊢
    rw [hmemΔ r, show Commute r a ↔ Commute (r : G) (a : G) from
      ⟨fun h => h.map Y.subtype, fun h => Subtype.ext h.eq⟩, key]
    simp only [Subtype.ext_iff, Subgroup.coe_mul]
    rfl
  exact exists_mulEquiv_l2Wreath_three_of_commSet h1 h91
    (hSt.setup_inClosure_starO h86 h87 hT hn hord hs)
    (hSt.disconnected_starO h86 h87 hT hn hord hs) hsO hzs h31 hL

theorem StandingAS.not_isStarTriangle (h1 : TheoremOne) (h86 : Lemma8_6) (h87 : Theorem8_7)
    (h91 : Theorem9_1) {hC : HypothesisC D} (hSt : StandingAS hC) (x w y : G) :
    ¬ IsStarTriangle hC x w y := by
  intro hT
  classical
  obtain ⟨n, hn, -, hord⟩ := hT.2.1
  obtain ⟨ht, -, hx, -, -, -⟩ := id hT
  have hz2 : (x * y * w) ^ n * (x * y * w) ^ n = 1 := by
    rw [← pow_add, ← two_mul, ← hord, pow_orderOf_eq_one]
  obtain ⟨s, hs⟩ := hSt.starN_nonempty h86 h87 hT hn hord
  have hsO : s ∈ starO hC x w y n s := ⟨hs.2, hs.1.1.2.mul_right (Commute.refl s)⟩
  have hsD : s ∈ D := DalphaStar_subset hC.isBlock_alpha hs.2
  have hs2 : s * s = 1 := hC.setup.oddT.mul_self_eq_one hsD
  have hzs : Commute ((x * y * w) ^ n) s := hs.1.1.2.symm
  set Y := Subgroup.closure (starO hC x w y n s) with hY
  obtain ⟨f, hf, ⟨φ⟩⟩ :=
    hSt.exists_mulEquiv_l2Wreath_three_closure_starO h1 h86 h87 h91 hT hn hord hs
  let sY : Y := ⟨s, Subgroup.subset_closure hsO⟩
  obtain ⟨P, hPperf, hZP, hPcent⟩ := exists_perfect_of_mulEquiv_l2Wreath_three
    (hSt.setup_inClosure_starO h86 h87 hT hn hord hs) hf φ (s := sY) hsO
  have hΔO : conjOrbit (localGroup D ((x * y * w) ^ n)) x ⊆ starO hC x w y n s := fun a ha =>
    (show a ∈ commSet (starO hC x w y n s) s by
      rw [hSt.commSet_starO_eq h86 h87 hT hn hord hs]; exact ha).1
  let zY : Y := ⟨(x * y * w) ^ n,
    Subgroup.closure_mono hΔO (pow_mem_closure_conjOrbit hC.setup ht hn hord).1⟩
  have hYτ : Y ≤ Subgroup.centralizer {(x * y * w) ^ n * s} :=
    (Subgroup.closure_le _).mpr fun o ho => Subgroup.mem_centralizer_singleton_iff.mpr ho.2.eq
  have hτ : zY * sY ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hYτ g.2))
  let R : Subgroup G := P.map Y.subtype
  have hτR : (x * y * w) ^ n * s ∈ R := ⟨zY * sY, hZP hτ, rfl⟩
  have hR : ⁅R, R⁆ = R := by rw [← Subgroup.map_commutator, hPperf]
  obtain ⟨ρ, hρ, hsρ⟩ := exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hsD
  obtain ⟨u, hu⟩ := hC.isBlock_alpha.nonempty
  have huN : u ∈ starN D ρ (starSigma D x w y n) :=
    alpha_subset_starN hC hSt.derivedSeries_ne hT hn hord hs hρ hsρ hu
  have huD : u ∈ D := huN.1.1.1
  have hu2 : u * u = 1 := hC.setup.oddT.mul_self_eq_one huD
  have huz : Commute u ((x * y * w) ^ n) := huN.1.1.2
  have hRcomm : ∀ r ∈ R, Commute r s ∧ Commute r ((x * y * w) ^ n) ∧ Commute r u := by
    rintro _ ⟨p, hp, rfl⟩
    have hps : Commute (p : G) s := (hPcent p hp sY hsO (Commute.refl sY)).map Y.subtype
    have hpτ : Commute (p : G) ((x * y * w) ^ n * s) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYτ p.2)
    have hpz : Commute (p : G) ((x * y * w) ^ n) := by
      have h := hpτ.mul_right hps.inv_right
      rwa [mul_inv_cancel_right] at h
    have hYu : Y ≤ Subgroup.centralizer {u} := (Subgroup.closure_le _).mpr fun o ho =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hSt.commute_of_mem_starO_of_mem_starN h86 h87 hT hn hord hs hρ hsρ ho huN).eq
    exact ⟨hps, hpz, Subgroup.mem_centralizer_singleton_iff.mp (hYu p.2)⟩
  obtain ⟨g, hgα, hTg⟩ := hSt.exists_conj_alpha_eq_of_mem_starSigma h86 h87 hT hn hord hs.1 hρ hsρ
  have hSt' : StandingAS (hC.conj g) := hSt.conj g
  have huN' : u ∈ starN D (hC.conj g).alpha (starSigma D x w y n) := by rw [hgα]; exact huN
  obtain ⟨f', hf', ⟨φ'⟩⟩ :=
    hSt'.exists_mulEquiv_l2Wreath_three_closure_starO h1 h86 h87 h91 hTg hn hord huN'
  set K := Subgroup.closure (starO (hC.conj g) x w y n u) with hK
  have huO : u ∈ starO (hC.conj g) x w y n u := ⟨huN'.2, huz.mul_right (Commute.refl u)⟩
  let uK : K := ⟨u, Subgroup.subset_closure huO⟩
  have hSK := hSt'.setup_inClosure_starO h86 h87 hTg hn hord huN'
  have hux : Commute u x := by
    have h : u ∈ {d | d ∈ centSet D ((x * y * w) ^ n) ∧
        d ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x} := huN.1
    rw [setOf_centSet_notMem_eq hC.setup ht hn hord] at h
    exact h.2 x (self_mem_conjOrbit _ x)
  have hxz : Commute x ((x * y * w) ^ n) :=
    (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm
  have hxO : x ∈ starO (hC.conj g) x w y n u := ⟨hTg.2.2.1, hxz.mul_right hux.symm⟩
  have hxu : x ≠ u := fun h => huN.1.2 (h ▸ self_mem_conjOrbit _ x)
  have hSQ : Setup (K ⧸ Subgroup.center K)
      (QuotientGroup.mk' (Subgroup.center K) '' inClosure (starO (hC.conj g) x w y n u)) :=
    hSK.map _ (QuotientGroup.mk'_surjective _) fun e he =>
      mk_center_ne_one_of_ne hSK (a := ⟨x, Subgroup.subset_closure hxO⟩) (b := uK) hxO huO
        (fun h => hxu (congrArg Subtype.val h)) he
  have hswap : φ' (QuotientGroup.mk' (Subgroup.center K) uK) ∈ WreathEndgame.swapSet f' 3 := by
    have h : QuotientGroup.mk' (Subgroup.center K) uK ∈
        QuotientGroup.mk' (Subgroup.center K) '' inClosure (starO (hC.conj g) x w y n u) :=
      ⟨uK, huO, rfl⟩
    rw [eq_preimage_swapSet_of_mulEquiv hSQ hf' (Or.inl rfl) φ'] at h
    exact h
  have hblock : ∀ r : G, Commute r s → (fun q => r * q * r⁻¹) '' ρ = ρ := by
    intro r hr
    refine eq_of_mem_of_mem_blockClass hC.isBlock_alpha (conj_image_mem_blockClass hρ r) hρ
      ⟨s, ⟨s, hsρ, ?_⟩, hsρ⟩
    show r * s * r⁻¹ = s
    rw [hr.eq, mul_inv_cancel_right]
  have hconjO : ∀ r : G, Commute r s → Commute r ((x * y * w) ^ n) → Commute r u →
      ∀ o ∈ starO (hC.conj g) x w y n u, r * o * r⁻¹ ∈ starO (hC.conj g) x w y n u := by
    intro r hrs hrz hru o ho
    have hoρ : o ∈ DalphaStar D ρ := hgα ▸ ho.1
    have h := DalphaStar.conj hC.setup.normal hoρ r
    rw [hblock r hrs] at h
    refine ⟨hgα ▸ h, ?_⟩
    have hrzu : Commute r ((x * y * w) ^ n * u) := hrz.mul_right hru
    have h' := (Commute.conj_iff r).mpr ho.2
    rwa [hrzu.eq, mul_inv_cancel_right] at h'
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    obtain ⟨hrs, hrz, hru⟩ := hRcomm r hr
    apply Subgroup.normalizer_le_normalizer_closure
    rw [Subgroup.mem_set_normalizer_iff]
    intro o
    constructor
    · exact hconjO r hrs hrz hru o
    · intro ho
      have h := hconjO r⁻¹ hrs.inv_left hrz.inv_left hru.inv_left _ ho
      rwa [inv_inv, show r⁻¹ * (r * o * r⁻¹) * r = o by group] at h
  have hd : ∀ k ∈ K, Commute ((x * y * w) ^ n * u * s) k := by
    intro k hk
    have hle : K ≤ Subgroup.centralizer {(x * y * w) ^ n * u * s} := by
      refine (Subgroup.closure_le _).mpr fun o ho => ?_
      have hos : Commute o s := by
        have h := mem_centralizer_Halpha_of_mem (D := D) hsρ
        exact Subgroup.mem_centralizer_iff.mp h o (Subgroup.subset_closure (hgα ▸ ho.1))
      exact Subgroup.mem_centralizer_singleton_iff.mpr (ho.2.mul_right hos).eq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm
  apply inv_mul_notMem_of_mem_swapSet hf' (Or.inl rfl) φ' hRK hR hd hswap
    (fun r hr => (hRcomm r hr).2.2)
  have hdu : ((x * y * w) ^ n * u * s)⁻¹ * u = (x * y * w) ^ n * s := by
    have hzinv : ((x * y * w) ^ n)⁻¹ = (x * y * w) ^ n := inv_eq_of_mul_eq_one_right hz2
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    calc ((x * y * w) ^ n * u * s)⁻¹ * u = s⁻¹ * (u⁻¹ * ((x * y * w) ^ n)⁻¹ * u) := by group
      _ = s * ((x * y * w) ^ n * (u * u)) := by
          rw [hsinv, huinv, hzinv, huz.eq, mul_assoc]
      _ = (x * y * w) ^ n * s := by rw [hu2, mul_one, hzs.symm.eq]
  rw [hdu]
  exact hτR

theorem starAlmostSimple_of (h1 : TheoremOne) (h86 : Lemma8_6) (h87 : Theorem8_7)
    (h91 : Theorem9_1) : StarAlmostSimple :=
  fun _ _ _ _ _ hrad h3 hns hF hO4 hne hAS x w y =>
    StandingAS.not_isStarTriangle h1 h86 h87 h91 ⟨hrad, h3, hns, hF, hO4, hne, hAS⟩ x w y

end CFSG.OddTranspositions.PartThree.EightEight

end
