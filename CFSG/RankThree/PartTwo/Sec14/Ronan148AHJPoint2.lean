module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148AHJPoint
import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelveRes
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VHJ4

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_img148_deltaZero_of_point_le (h142 : Concl142S14) {A L : Subgroup G}
    {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {b : G} (hbΩ : Subgroup.zpowers b ∈ omegaA A) {U : Subgroup G} (hUY : U ≤ Y)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y))
    (hVb : V ≤ img148 A Y (U ⊓ Subgroup.centralizer ({b} : Set G))) (hV3 : ¬ 3 ∣ Nat.card V)
    (hAV : img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ⁅V, img148 A Y A⁆ ≤ img148 A Y (deltaZero A (lB A) U) := by
  have hA : Late.IsE27 A := hS.isE27'
  have hA3' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    hS.toSec13Data.commute ha ha'
  have hbA : b ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp hbΩ).1
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W =
      ((V.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype) ⊓
        (U ⊓ Subgroup.centralizer ({b} : Set G)) := ⟨_, rfl⟩
  have hWsub : W ≤ U ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [hW]
    exact inf_le_right
  have hWU : W ≤ U := hWsub.trans inf_le_left
  have hWY : W ≤ Y := hWU.trans hUY
  have hWM : W ≤ Y ⊔ A := hWY.trans le_sup_left
  have hWmem : ∀ {x : G} (hx : x ∈ U), x ∈ W ↔
      (QuotientGroup.mk' (ker148 A Y) ⟨x, Subgroup.mem_sup_left (hUY hx)⟩ ∈ V ∧
        x ∈ Subgroup.centralizer ({b} : Set G)) := by
    intro x hx
    rw [hW, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hM, -, hC⟩
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hM
      have hm' : m = ⟨x, Subgroup.mem_sup_left (hUY hx)⟩ := Subtype.ext hmx
      subst hm'
      exact ⟨hm, hC⟩
    · rintro ⟨hV', hC⟩
      exact ⟨Subgroup.mem_map.mpr ⟨⟨x, Subgroup.mem_sup_left (hUY hx)⟩, hV', rfl⟩, hx, hC⟩
  have hWV : img148 A Y W = V := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨g, hgM, hgW, rfl⟩ := mem_img148_iff.mp hy
      exact ((hWmem (hWU hgW)).mp hgW).1
    · intro v hv
      obtain ⟨g, hgM, hgC, rfl⟩ := mem_img148_iff.mp (hVb hv)
      exact mem_img148_iff.mpr ⟨g, hgM, (hWmem hgC.1).mpr ⟨hv, hgC.2⟩, rfl⟩
  have hconj : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro a ha w hw
    have hwU : w ∈ U := hWU hw
    have hcw : Commute w b := Subgroup.mem_centralizer_singleton_iff.mp (hWsub hw).2
    have hcomm : Commute a b := hAab a ha b hbA
    have hawU : a * w * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hAU ha) w).mp hwU
    have hcab : Commute (a * w * a⁻¹) b := (hcomm.mul_left hcw).mul_left hcomm.inv_left
    have hkey : QuotientGroup.mk' (ker148 A Y)
          ⟨a * w * a⁻¹, Subgroup.mem_sup_left (hUY hawU)⟩ =
        alpha148 A Y a ha * QuotientGroup.mk' (ker148 A Y)
          ⟨w, Subgroup.mem_sup_left (hUY hwU)⟩ * (alpha148 A Y a ha)⁻¹ := by
      rw [alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul] <;> rfl
    have hwV : QuotientGroup.mk' (ker148 A Y) ⟨w, Subgroup.mem_sup_left (hUY hwU)⟩ ∈ V :=
      ((hWmem hwU).mp hw).1
    have hVconj : QuotientGroup.mk' (ker148 A Y)
        ⟨a * w * a⁻¹, Subgroup.mem_sup_left (hUY hawU)⟩ ∈ V := by
      rw [hkey]
      exact (Subgroup.mem_normalizer_iff.mp (hAV (alpha148_mem_img148 (Y := Y) ha))
        (QuotientGroup.mk' (ker148 A Y) ⟨w, Subgroup.mem_sup_left (hUY hwU)⟩)).mp hwV
    exact (hWmem hawU).mpr ⟨hVconj, Subgroup.mem_centralizer_singleton_iff.mpr hcab⟩
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconj a ha w, fun hw => ?_⟩
    have h2 := hconj a⁻¹ (A.inv_mem ha) (a * w * a⁻¹) hw
    have e : a⁻¹ * (a * w * a⁻¹) * a⁻¹⁻¹ = w := by group
    rw [e] at h2
    exact h2
  have hWN : W ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    have hCN : Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hx
    exact (hWsub.trans inf_le_right).trans hCN
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 3 h3
    have hxW : (x : G) ∈ W := x.2
    have hxU : (x : G) ∈ U := hWU hxW
    have hxY : (x : G) ∈ Y := hUY hxU
    have hxo : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx3
    have hv : QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩ ∈ V :=
      ((hWmem hxU).mp hxW).1
    have hg3 : orderOf (⟨(x : G), Subgroup.mem_sup_left hxY⟩ : ↥(Y ⊔ A)) = 3 :=
      (Subgroup.orderOf_coe (⟨(x : G), Subgroup.mem_sup_left hxY⟩ : ↥(Y ⊔ A))).symm.trans hxo
    have hπ3 : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩)
        ∣ 3 :=
      (orderOf_map_dvd (QuotientGroup.mk' (ker148 A Y)) _).trans (dvd_of_eq hg3)
    have hπV : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩)
        ∣ Nat.card V :=
      Subgroup.orderOf_dvd_natCard V hv
    have hcop : Nat.gcd 3 (Nat.card V) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hV3
    have h1 : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩)
        ∣ 1 := by
      have := Nat.dvd_gcd hπ3 hπV
      rwa [hcop] at this
    have hone : QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩ = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    have hxP : (x : G) ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_one_iff.mp hone
    have h3P : 3 ∣ Nat.card (pPrimeCoreOf 3 Y) := by
      have := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 3 Y) hxP
      rwa [hxo] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 Y) h3P
  have hWQ : W ∈ scriptQ A (lB A) :=
    Proof1413Res3.mem_scriptQ_of_le_normalizer h142 hS hbΩ hWN hAW hW3
  have hcommW : ⁅W, A⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hAW
  have hQ : ⁅W, A⁆ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hWQ hcommW (Subgroup.normalizer_commutator_ge_right W A)
  have hcop3 : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  have hidem : ⁅⁅W, A⁆, A⁆ = ⁅W, A⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three
      A W hA3' hAW hcop3
  have hQ0 : ⁅W, A⁆ ∈ scriptQZero A (lB A) := ⟨hQ, hidem.symm⟩
  have hQle : ⁅W, A⁆ ≤ deltaZero A (lB A) U := le_deltaZero hQ0 (hcommW.trans hWU)
  calc ⁅V, img148 A Y A⁆ = ⁅img148 A Y W, img148 A Y A⁆ := by rw [hWV]
    _ = img148 A Y ⁅W, A⁆ :=
      (HJRes2.img148_commutator_eq hWM (le_sup_right : A ≤ Y ⊔ A)).symm
    _ ≤ img148 A Y (deltaZero A (lB A) U) := img148_mono hQle

section Certificates

theorem jalpha_le_of_member148
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (ih : Ind148 A (lB A) Y) {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G))) {b d : G}
    {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {Yd : Subgroup G}
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hYdJ : Yd ≤ J)
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hYB6 : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)))
    (hdYB : d ∈ YB) (hdA : d ∈ A) [(ker148 A Y).Normal]
    (φ : ↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) {U : Subgroup G} (hUY : U ≤ Y)
    (hUne : U ≠ Y) (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hYBU : YB ≤ U)
    (hUJ : img148 A Y U = img148 A Y J) :
    img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, -, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  have hJcard : Nat.card (img148 A Y J) = 604800 := KFacts.KS14.card_eq_of_j2 ⟨φ⟩
  obtain ⟨-, hCD, -, h9, hYdeq, hYd1080, -, -, -, -⟩ :=
    hj_frame148 h142 h134 h48 Ronan148V.khjPerfectOver_holds hS hY ih hB hYB hc hJ hAJ hYd
      hYBYd hYdJ hA6 hθ hdc hYB6 hdYB hdA ⟨φ⟩
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdα3 : dα ^ 3 = 1 := hA3 _ hdαA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← hdαdef, h, one_mul, mul_one]
  obtain ⟨-, hYd6, hYdp, hYdZ, -⟩ :=
    Ronan148J.img148_yd_facts_of_j2 hY.2 hdA hd3 hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hYdJα : img148 A Y Yd ≤ img148 A Y J := img148_mono hYdJ
  have hYdC : img148 A Y Yd ≤ Subgroup.centralizer {dα} := hYdeq ▸ inf_le_right
  have h3YB : 3 ∣ Nat.card YB := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
      HJRes2.card_of_isTripleCover_six hYB6]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hYBα : img148 A Y YB = img148 A Y Yd := by
    refine Subgroup.eq_of_le_of_card_ge (img148_mono hYBYd) ?_
    have h1 := Ronan148J.card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      h3YB
    rw [HJRes2.card_of_isTripleCover_six hYB6] at h1
    rw [hYd1080]
    exact h1
  have hYdb : img148 A Y Yd ≤ img148 A Y (U ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (le_inf hYBU ((hYBC.trans inf_le_right).trans ?_))
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
  have hAJYd : img148 A Y A ⊓ img148 A Y J ≤ img148 A Y Yd := by
    intro x hx
    rw [hYdeq]
    exact Subgroup.mem_inf.mpr ⟨hx.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx.1 dα hdαA)⟩
  obtain ⟨j, hjAJ, hjd⟩ : ∃ j ∈ img148 A Y A ⊓ img148 A Y J, j ∉ Subgroup.zpowers dα := by
    by_contra hcon
    push Not at hcon
    have hle : img148 A Y A ⊓ img148 A Y J ≤ Subgroup.zpowers dα := fun x hx => hcon x hx
    have h3 : Nat.card ↥(Subgroup.zpowers dα) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hdα3 hdα1]
    have := Subgroup.card_le_of_le hle
    omega
  have hjA : j ∈ img148 A Y A := hjAJ.1
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hjYd : j ∈ img148 A Y Yd := hAJYd hjAJ
  have hjnc : ∃ y ∈ img148 A Y Yd, j * y ≠ y * j := by
    by_contra hcon
    push Not at hcon
    exact hjd (hYdZ j hjYd hcon)
  have hdα1' : dα ≠ 1 := hdα1
  have hdj : dα * j = j * dα := hAab dα hdαA j hjA
  have h9' : Nat.card ↥(Subgroup.zpowers dα ⊔ Subgroup.zpowers j) = 9 :=
    Ronan148J.card_zpowers_sup_zpowers_eq_nine hdj hdα3 hdα1' hj3 hjd
  have hdjle : Subgroup.zpowers dα ⊔ Subgroup.zpowers j ≤ img148 A Y A ⊓ img148 A Y J :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hdαA, hdJα⟩) (Subgroup.zpowers_le.mpr hjAJ)
  have hAJeq : img148 A Y A ⊓ img148 A Y J = Subgroup.zpowers dα ⊔ Subgroup.zpowers j :=
    (Subgroup.eq_of_le_of_card_ge hdjle (by rw [h9', h9])).symm
  have hAV : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ img148 A Y Yd →
      j ∈ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro V hV hjV
    rw [← hCD]
    refine sup_le (fun a ha => Subgroup.centralizer_le_normalizer _ ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp ha.2 v (hYdJα (hV hv))
    · rw [hAJeq]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_))
        (Subgroup.zpowers_le.mpr hjV)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYdC (hV hv))
  have hYdX : img148 A Y Yd ≤ img148 A Y (deltaZero A (lB A) U) :=
    Ronan148J.le_of_forall_commutator_le_tripleCover hYd6 hYdp hjYd hj3 hjnc fun V hV hV3 hjV =>
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hjA)).trans
        (commutator_le_img148_deltaZero_of_point_le h142 hS hY hc.2.1 hUY hAU V (hV.trans hYdb)
          hV3 (hAV V hV hjV))
  have hU : U ∈ scriptY A := ⟨fun h => hY.1 (top_le_iff.mp (h ▸ hUY)), hAU⟩
  have hlt : Nat.card U < Nat.card Y := Subgroup.card_lt_of_lt (lt_of_le_of_ne hUY hUne)
  have h148U := (ih U hU hlt).1
  have hXU : deltaZero A (lB A) U ≤ U := deltaZero_le U
  have hUN := (map_mk_normal_iff hXU).mp h148U
  have hUM : U ≤ Y ⊔ A := hUY.trans le_sup_left
  have hOU : img148 A Y (pPrimeCoreOf 3 U) = ⊥ := by
    set O := img148 A Y (pPrimeCoreOf 3 U) with hO
    have hOJ : O ≤ img148 A Y J := hUJ ▸ img148_mono (pPrimeCoreOf_le 3 U)
    have hON : img148 A Y J ≤ Subgroup.normalizer (O : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      hUJ ▸ img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 U)
    have hO3 : ¬ 3 ∣ Nat.card O := Item148PtRes.not_three_dvd_card_img148
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 U))
    have hOn : (O.subgroupOf (img148 A Y J)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).mpr hON
    rcases hOn.eq_bot_or_eq_top with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hOJ hx⟩ : ↥(img148 A Y J)) ∈ O.subgroupOf (img148 A Y J) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hJO : img148 A Y J ≤ O := Subgroup.subgroupOf_eq_top.mp h
      apply hO3
      have := Subgroup.card_dvd_of_le hJO
      rw [hJcard] at this
      exact (show 3 ∣ 604800 by norm_num).trans this
  have hJN : img148 A Y J ≤ Subgroup.normalizer
      (img148 A Y (deltaZero A (lB A) U) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have h1 := img148_le_normalizer (A := A) (Y := Y) hUN
    rwa [img148_sup (hXU.trans hUM) ((pPrimeCoreOf_le 3 U).trans hUM), hOU, sup_bot_eq,
      hUJ] at h1
  set N := img148 A Y (deltaZero A (lB A) U) ⊓ img148 A Y J with hN
  have hNJ : N ≤ img148 A Y J := inf_le_right
  have hNn : (N.subgroupOf (img148 A Y J)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr
      (Late.le_normalizer_inf hJN Subgroup.le_normalizer)
  have hJN' : img148 A Y J ≤ N := by
    rcases hNn.eq_bot_or_eq_top with h | h
    · exfalso
      have hYdN : img148 A Y Yd ≤ N := le_inf hYdX hYdJα
      have hYdbot : img148 A Y Yd = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hYdJα hx⟩ : ↥(img148 A Y J)) ∈ N.subgroupOf (img148 A Y J) :=
          Subgroup.mem_subgroupOf.mpr (hYdN hx)
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
      rw [hYdbot, Subgroup.card_bot] at hYd1080
      norm_num at hYd1080
    · exact Subgroup.subgroupOf_eq_top.mp h
  exact (hJN'.trans inf_le_left).trans (img148_mono (Sec14.deltaZero_mono hUY))

@[expose] def Step148HJCentPoint2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        omegaA A = {Subgroup.zpowers b} →
        J = Y →
        (∃ a ∈ A, a ≠ 1 ∧ a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ∧
          Y ≤ Subgroup.centralizer ({a} : Set G)) →
        ¬ img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) →
        b ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)

theorem step148HJCentPoint1_of_two (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) (hTwo : Step148HJCentPoint2) : Step148HJCentPoint1 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hJ2 hΩ
  let := ker148_normal hY.2
  by_contra hbJ
  obtain ⟨hYB6, hdYB, hbc⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨hbB, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  obtain ⟨φ⟩ := hJ2
  have hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
    by_contra hJX
    by_cases hJYeq : J = Y
    · obtain ⟨n, hn⟩ := exists_sectionCentralizer_of_j2 hS.mem_partTwoF hY.2 hJ hAJ hdA hYd hYdJ
        (hYBYd hdYB) hA6 hθ hdc hbc φ
      set a := b * (d ^ n)⁻¹ with ha
      have haB : a ∈ B := B.mul_mem hbB (B.inv_mem (B.pow_mem hdB n))
      have haA : a ∈ A := hB.1 haB
      have ha1 : a ≠ 1 := by
        intro h1
        have hbd : b = d ^ n := by
          calc b = (b * (d ^ n)⁻¹) * d ^ n := by group
            _ = d ^ n := by rw [← ha, h1, one_mul]
        have hBle : B ≤ Subgroup.zpowers d := by
          rw [hc.1, Subgroup.closure_le]
          rintro z (rfl | hz)
          · rw [hbd]
            exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n
          · rw [Set.mem_singleton_iff.mp hz]
            exact Subgroup.mem_zpowers d
        have hz3 : Nat.card (Subgroup.zpowers d) ≤ 3 := by
          rw [Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 d hdA))
        have h9 : 3 * Nat.card B = 27 := by rw [← hB.2, hA.2]
        have := Subgroup.card_le_of_le hBle
        omega
      by_cases hYa : Y ≤ Subgroup.centralizer ({a} : Set G)
      · exact hbJ (hTwo G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle
          J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc ⟨φ⟩ hΩ hJYeq
          ⟨a, haA, ha1, hn, hYa⟩ hJX)
      · apply hJX
        have hAab : ∀ x ∈ A, x * a = a * x := fun x hx => hS.toSec13Data.commute hx haA
        refine jalpha_le_of_member148 h142 h134 h48 hS hY ih hB hYB hc hJ hAJ hYd hYBYd hYdJ hA6
          hθ hdc hYB6 hdYB hdA φ (U := Y ⊓ Subgroup.centralizer ({a} : Set G)) inf_le_left
          (fun h => hYa (h ▸ inf_le_right)) ?_ ?_ ?_
        · exact Late.le_normalizer_inf hY.2 fun x hx =>
            Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx))
        · refine le_inf (hYBC.trans inf_le_left) ((hYBC.trans inf_le_right).trans ?_)
          exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
        · have hJa := HJRes2.le_centralizer_of_mem_sectionCentralizer haA hn
          refine le_antisymm ?_ ?_
          · rw [hJYeq]
            exact img148_mono inf_le_left
          · have hJY' : img148 A Y J ≤ img148 A Y Y := img148_mono hJY
            exact le_img148_inf_centralizer hY.2 haA (hA3 a haA) le_rfl hJY' hJa
    · exact hJX (jalpha_le_of_member148 h142 h134 h48 hS hY ih hB hYB hc hJ hAJ hYd hYBYd hYdJ
        hA6 hθ hdc hYB6 hdYB hdA φ hJY hJYeq hAJ hYBJ rfl)
  obtain ⟨-, -, -, -, -, -, -, hXeqH, -, hZtype⟩ :=
    hj_frame148 h142 h134 h48 Ronan148V.khjPerfectOver_holds hS hY ih hB hYB hc hJ hAJ hYd
      hYBYd hYdJ hA6 hθ hdc hYB6 hdYB hdA ⟨φ⟩
  have hno : ∀ a ∈ A, Subgroup.zpowers a ∈ omegaA A →
      a ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
    intro a haA haΩ hac
    rw [hΩ, Set.mem_singleton_iff] at haΩ
    exact hbJ (mem_sectionCentralizer_of_zpowers_eq hJM haA hbA haΩ hac)
  have hexcl : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J → ∀ a ∈ A,
      Subgroup.zpowers a ∈ omegaA A →
      (∃ La ∈ lA A a,
        Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2)) →
      a ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := fun _ a haA haΩ _ => hno a haA haΩ
  have hR : Ronan148V.Step148HJHJCent4 :=
    Ronan148V.step148HJHJCent4_of_cent5 h134 h48 (step148HJHJCent5_holds h134 h48)
  rcases hZtype with hZ1 | hZ5
  ·
    have hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J := by
      rw [hXeqH, hZ1, sup_bot_eq, inf_eq_right.mpr hJX]
    obtain ⟨hpt, -⟩ := Ronan148V.step148HJHJCent3_of_cent4Q h143 hR G A c L hS Y hY hs ih B hB
      hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6
      hdYB hbc ⟨φ⟩ hexcl
    obtain ⟨a, haA, haΩ, hac⟩ := hpt hXJ
    exact hno a haA haΩ hac
  ·
    have h6 := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd
      hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc ⟨φ⟩ hexcl hJX hZ5
    rw [hΩ, Set.ncard_singleton] at h6
    norm_num at h6

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
