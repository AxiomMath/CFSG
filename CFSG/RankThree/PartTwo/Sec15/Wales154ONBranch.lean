module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Assembly
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_deltaZero_of_trivial {A Z : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA3 : IsPGroup 3 A) (hAc : IsMulCommutative A) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZΔ : Z = deltaZero A LB Z) {e : G} (heA : e ∈ A)
    (htriv : ∀ z ∈ Z, e * z * e⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) :
    Z = pPrimeCoreOf 3 Z ⊔
      deltaZero A LB (Z ⊓ Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
  set O := pPrimeCoreOf 3 Z with hO
  set H := Subgroup.normalizer (Subgroup.zpowers e : Set G) with hH
  set E := Subgroup.zpowers e with hE
  have hOZ : O ≤ Z := pPrimeCoreOf_le 3 Z
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAZ.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Z)
  refine le_antisymm ?_ (sup_le hOZ ((deltaZero_le _).trans inf_le_left))
  have hEA : E ≤ A := Subgroup.zpowers_le.mpr heA
  have hE3 : IsPGroup 3 E := hA3.to_le hEA
  have hzt : ∀ x ∈ E, ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ ∈ O := by
    have hS : E ≤ trivSub Z := Subgroup.zpowers_le.mpr ⟨hAZ heA, htriv⟩
    exact fun x hx => (hS hx).2
  have hAC : A ≤ Subgroup.centralizer (E : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (hAc.is_comm.comm ⟨x, hEA hx⟩ ⟨a, ha⟩)
    simpa using h1
  calc Z = deltaZero A LB Z := hZΔ
    _ ≤ O ⊔ deltaZero A LB (Z ⊓ H) := by
      refine sSup_le fun Q hQ => ?_
      obtain ⟨⟨⟨⟨-, hQ3, hAQ⟩, hQB⟩, hQA⟩, hQZ⟩ := hQ
      have hQ3' : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ3
      have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := hEA.trans hAQ
      set C := Q ⊓ Subgroup.centralizer (E : Set G) with hCdef
      set D := ⁅Q, E⁆ with hDdef
      have hfac : Q = D ⊔ C :=
        CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
          Nat.prime_three E Q hE3 hQ3' hEQ
      have hDO : D ≤ O := by
        rw [hDdef, Subgroup.commutator_le]
        intro q hq x hx
        have h1 := hzt x hx q (hQZ hq)
        have e1 : ⁅q, x⁆ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e1]
        exact inv_mem h1
      have hAC' : A ≤ Subgroup.normalizer (C : Set G) :=
        Late.le_normalizer_inf hAQ (hAC.trans Subgroup.le_normalizer)
      have hCQ : C ≤ Q := inf_le_left
      set Q₁ := ⁅C, A⁆ with hQ₁def
      have hQ₁C : Q₁ ≤ C := Subgroup.le_normalizer_iff_commutator_le_left.mp hAC'
      have hC3 : ¬ 3 ∣ Nat.card C := fun h3 => hQ3' (h3.trans (Subgroup.card_dvd_of_le hCQ))
      have hQ₁0 : Q₁ ∈ scriptQZero A LB := by
        refine ⟨⟨⟨le_top, isPiSubgroup_piCompl_of_le hQ3 (hQ₁C.trans hCQ),
          le_normalizer_commutator_of_le hAC' Subgroup.le_normalizer⟩, fun B hB => ?_⟩, ?_⟩
        · exact (inf_le_inf_right _ (hQ₁C.trans hCQ)).trans (hQB B hB)
        · exact (CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3
            Nat.prime_three A C hA3 hAC'
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3)).symm
      have hQ₁ZH : Q₁ ≤ Z ⊓ H :=
        le_inf (hQ₁C.trans (hCQ.trans hQZ))
          (hQ₁C.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
      have hQ₁Δ : Q₁ ≤ deltaZero A LB (Z ⊓ H) := le_sSup ⟨hQ₁0, hQ₁ZH⟩
      refine le_trans ?_ (sup_le_sup_left hQ₁Δ O)
      rw [hQA, Subgroup.commutator_le]
      intro q hq a ha
      have hCD : C ≤ Subgroup.normalizer (D : Set G) :=
        hCQ.trans (Sec6.le_normalizer_commutator_left Q E)
      have hq' : q ∈ ((D ⊔ C : Subgroup G) : Set G) := by
        rw [← hfac]
        exact hq
      rw [Subgroup.coe_mul_of_right_le_normalizer_left D C hCD] at hq'
      obtain ⟨d, hd, c', hc', rfl⟩ := hq'
      have e1 : ⁅d * c', a⁆ = d * ⁅c', a⁆ * (a * d⁻¹ * a⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [e1]
      have had : a * d⁻¹ * a⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hAO ha) _).mp (inv_mem (hDO hd))
      exact mul_mem (mul_mem (Subgroup.mem_sup_left (hDO hd))
        (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hc' ha)))
        (Subgroup.mem_sup_left had)

section Point


theorem eq_inf_sup_of_trivial_point (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {e : G} {Le : Subgroup G}
    (he : Subgroup.zpowers e ∈ omegaA A) (hLe : Le ∈ lA A e) (h3 : 3 ∣ Nat.card Le)
    (hnot : IsEmpty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    {Z : Subgroup G} (hZ : Z ∈ scriptY4 A (lB A))
    (htriv : ∀ z ∈ Z, e * z * e⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) :
    Z = (Z ⊓ Le) ⊔ pPrimeCoreOf 3 Z := by
  have hR' : Sec15R G A e Le := { hR with zpowers_mem_omegaA := he, mem_lA := hLe }
  have heA : e ∈ A := (zpowers_mem_omegaA_iff.mp he).1
  have hZΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hZ
  have hdec := eq_sup_deltaZero_of_trivial hR.toSec14Std.isE27.isPGroup hR.isElemAbelian.1
    hZ.1.2 hZΔ heA htriv
  exact Proof1515.eq_inf_sup_pPrimeCoreOf_of_item142 hR' (h142 G A e Le hR') h3 hnot hZ hdec

theorem card_quot_dvd_of_eq_inf_sup {Z M : Subgroup G}
    (hdec : Z = (Z ⊓ M) ⊔ pPrimeCoreOf 3 Z) :
    Nat.card (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) ∣ Nat.card (Z ⊓ M : Subgroup G) := by
  set f : ↥(Z ⊓ M) →* ↥Z ⧸ CFSG.pPrimeCore 3 ↥Z :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Z)).comp (Subgroup.inclusion inf_le_left) with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥Z) q
    have hON : Z ⊓ M ≤ Subgroup.normalizer (pPrimeCoreOf 3 Z : Set G) :=
      inf_le_left.trans (le_normalizer_pPrimeCoreOf 3 Z)
    have hz : (z : G) ∈ (((Z ⊓ M) ⊔ pPrimeCoreOf 3 Z : Subgroup G) : Set G) := by
      rw [← hdec]
      exact z.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hON] at hz
    obtain ⟨w, hw, o, ho, hwo⟩ := hz
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hzw : z = Subgroup.inclusion inf_le_left ⟨w, hw⟩ * o' := Subtype.ext hwo.symm
    rw [hzw, inv_mul_cancel_left]
    exact ho'
  exact Subgroup.card_dvd_of_surjective hsurj

theorem false_of_trivial_point_of_j2 (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {e : G} {Le : Subgroup G}
    (he : Subgroup.zpowers e ∈ omegaA A) (hLe : Le ∈ lA A e)
    (hJ : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Z : Subgroup G} (hZ : Z ∈ scriptY4 A (lB A))
    (htriv : ∀ z ∈ Z, e * z * e⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z)
    (h81 : 3 ^ 4 ∣ Nat.card (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z)) : False := by
  obtain ⟨φ⟩ := hJ
  have hc := Nat.card_congr φ.toEquiv
  rw [KFacts.KS14.card_nativeJ2] at hc
  have hLc := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥Le)
  rw [hc] at hLc
  have h3 : 3 ∣ Nat.card Le := by
    rw [hLc]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hnot : IsEmpty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hc, CFSG.PGLModel.card_projSL_three_four] at h1
    norm_num at h1
  have hdec := eq_inf_sup_of_trivial_point h134 h48 h142 hR he hLe h3 hnot hZ htriv
  have h1 := (h81.trans (card_quot_dvd_of_eq_inf_sup hdec)).trans
    (Subgroup.card_dvd_of_le inf_le_right)
  rw [hLc] at h1
  have hθ := three_not_dvd_card_aschbacherSolvableCore (G := ↥Le)
  have hcop : Nat.Coprime (3 ^ 4) (Nat.card (aschbacherSolvableCore 3 ↥Le)) :=
    Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ)
  have := hcop.dvd_of_dvd_mul_right h1
  norm_num at this

end Point

theorem mk_mem_pCore_imgX {X Y : Subgroup G} (hXY : X ≤ Y) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
        ⟨x, hXY (CFSG.LieType.BorelTits.pCoreOf_le 2 X hx)⟩ ∈
      (CFSG.pCore 2 ↥(imgX X Y)).map (imgX X Y).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hκ
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hPX : P ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  set W := (P.subgroupOf Y).map κ with hW
  have hWK : W ≤ imgX X Y := Subgroup.map_mono fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hPX (Subgroup.mem_subgroupOf.mp hy))
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hW2 : IsPGroup 2 W := by
    have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    refine IsPGroup.map ?_ κ
    intro g
    obtain ⟨k, hk⟩ := hP2 ⟨((g : ↥Y) : G), Subgroup.mem_subgroupOf.mp g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hWn : (W.subgroupOf (imgX X Y)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨y, hy, hyk⟩ := k.2
    obtain ⟨p, hp, hpn⟩ := hn
    refine ⟨y * p * y⁻¹, ?_, ?_⟩
    · have hy' : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
      have hp' : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
      show y * p * y⁻¹ ∈ P.subgroupOf Y
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (hXP hy') _).mp hp'
      simpa using this
    · rw [map_mul, map_mul, map_inv, hyk, hpn]
      rfl
  have hW2' : IsPGroup 2 (W.subgroupOf (imgX X Y)) :=
    hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hWn hW2'
  have hmem : κ ⟨x, hXY (hPX hx)⟩ ∈ W := ⟨⟨x, hXY (hPX hx)⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact ⟨⟨_, hWK hmem⟩, hle (Subgroup.mem_subgroupOf.mpr hmem), rfl⟩

section Read


theorem read154_hj_pt (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (hR : Sec15R G A c L) (hHJ : AllPointsHJ A) {Z : Subgroup G}
    (hZ : Z ∈ scriptY4 A (lB A)) :
    (∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      (∀ z ∈ Z, c' * z * c'⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) ∧ ∃ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        (Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Sec4.IsTripleCover (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 5)))) ∨
    Sec4.IsTripleCover (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) CFSG.Blueprint.NativeSporadic.ON ∨
    Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 7)) ∨
    (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) := by
  have hZΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hZ
  rcases Proof1523Res3.cases148Full_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hZ hZΔ
    with ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨-, -, -, -, -, -, -, -, -, -, h3⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', hn, hm, -, hε⟩
  · obtain ⟨φJ⟩ := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc'o : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
    have htriv := trivial_of_dec hc'A hc'o hZ.1.2 hdec
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨hL, -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
    · exact Or.inl ⟨c', hc', htriv, L', hL', ⟨φJ⟩, Or.inl ⟨φ.trans φJ⟩⟩
    · exfalso
      rcases hL with ⟨⟨φM⟩⟩ | ⟨_, ⟨φL⟩⟩ | ⟨_, ⟨φU⟩⟩
      · exact KFacts.KS14.ks17J2NotList.2.2.false (φJ.symm.trans φM)
      · exact KFacts.KS14.not_isLThreeEpsAt_j2 5 2 (Or.inl ⟨φJ.symm.trans φL⟩)
      · exact KFacts.KS14.not_isLThreeEpsAt_j2 5 1
          (Or.inr ⟨by norm_num, ⟨φJ.symm.trans φU⟩⟩)
    · exact (KFacts.KS14.ks17J2NotList.1 p (f * e)
        (Proof155w3.isoLThreePi_of_mulEquiv φJ hiso)).elim
    · exact Or.inl ⟨c', hc', htriv, L', hL', ⟨φJ⟩, Or.inr (Or.inl h6)⟩
    · exact Or.inl ⟨c', hc', htriv, L', hL', ⟨φJ⟩, Or.inr (Or.inr h5)⟩
  · rcases h3 with hON | h7 | h7
    · exact Or.inr (Or.inl hON)
    · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr h7))
  · obtain ⟨φJ⟩ := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    exact (KFacts.KS14.ks17J2NotList.2.1.false (φJ.symm.trans φ7)).elim
  · obtain ⟨φJ⟩ := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    exact (KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (IsLThreeEpsAt.of_mulEquiv φJ hε)).elim

end Read

section Branch


theorem item154ProperWhenHJ_ON (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142R) (hONc : KS1523ONCent) (hK : KS154ON) :
    Item154ProperWhenHJ fun Q _ => Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON := by
  intro G _ _ A c L hR hHJ Y hY X hX hXY hYX hON R hRm
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.1.2.2.2
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY.1
  have heqY : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun W _ hWc hcop _ => by
      have hd : Nat.card W ∣ 3 := (Subgroup.card_dvd_of_le hWc).trans (by rw [hON.1])
      have h1 : Nat.card W = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
        · exact h
        · rw [h] at hcop
          norm_num at hcop
      exact Subgroup.eq_bot_of_card_eq W h1
  have hOY : pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y :=
    Proof1515.pPrimeCoreOf_eq_pCoreOf_two heqY
  have hN : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 1382446517760 := by
    rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON]
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  rw [hN] at hdvd hle
  have hq3 := card_quot_pPrimeCore_dvd (Z := ↥X)
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := (le_sup_left : A ≤ A ⊔ X).trans hRm.2.2
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  rcases read154_hj_pt h148 h134 h48 hR hHJ hX with
    ⟨c'', hc'', htriv'', L'', hL'', hJ'', hcase⟩ | hON' | ⟨⟨ψ⟩⟩ | ⟨hp7, ⟨ψ⟩⟩
  · obtain ⟨hc''A, hc''3, -⟩ := zpowers_mem_omegaA_iff.mp hc''
    have hc''o : orderOf c'' = 3 := by rw [← Nat.card_zpowers]; exact hc''3
    have hXq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
    have hneX := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hX
    obtain ⟨heqX, h5X⟩ : CFSG.pPrimeCore 3 ↥X = CFSG.pCore 2 ↥X ∧
        5 ∣ Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
      rcases hcase with ⟨⟨ψ⟩⟩ | h6 | ⟨⟨ψ⟩⟩
      · exfalso
        have h1 : 25 ∣ Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
          rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeJ2]
          norm_num
        have := (h1.trans hq3).trans hdvd
        norm_num at this
      · have hc : Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 1080 := by
          rw [card_of_isTripleCover h6, card_alternatingGroup_six]
        refine ⟨Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hXq hneX fun p hp hp6 => by
          rw [hc]
          exact Proof1515.not_sq_dvd_small (Or.inr rfl) hp hp6, by rw [hc]; norm_num⟩
      · have hc : Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 60 := by
          rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_five]
        refine ⟨Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hXq hneX fun p hp hp6 => by
          rw [hc]
          exact Proof1515.not_sq_dvd_small (Or.inl rfl) hp hp6, by rw [hc]; norm_num⟩
    have hOX : pPrimeCoreOf 3 X = CFSG.Open.pCoreOf 2 X :=
      Proof1515.pPrimeCoreOf_eq_pCoreOf_two heqX
    have hntriv : ¬ ∀ y ∈ Y, c'' * y * c''⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y := fun htY =>
      false_of_trivial_point_of_j2 h134 h48 h142 hR hc'' hL'' hJ'' hY.1 htY (by
        rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq heqY).toEquiv, hN]
        norm_num)
    set m : Subgroup.normalizer (Y : Set G) := ⟨c'', hY.1.1.2 hc''A⟩ with hm
    set α := Sec17.Proof17Res6.actQ Y m with hα
    have hα1 : α ≠ 1 := by
      intro h1
      apply hntriv
      intro y hy
      rw [hOY]
      exact Proof155w3.commutator_mem_of_actQ_eq_one (m := m) h1 y hy
    have hm3 : m ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hc''o ▸ pow_orderOf_eq_one c'')
    have hα3 : orderOf α = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hpow : α ^ 3 = 1 := by rw [hα, ← map_pow, hm3, map_one]
      exact orderOf_eq_prime hpow hα1
    have hKp := isPerfect_imgX hXY (isPerfect_of_mem_scriptY4 hX)
    have h5K : 5 ∣ Nat.card (imgX X Y) :=
      (h5X.trans hq3).trans (card_quot_dvd_card_imgX hXY)
    have hαK : ∀ k ∈ imgX X Y, α k ∈ imgX X Y := fun k hk => actQ_mem_imgX (hX.1.2 hc''A) hk
    have hαtriv : ∀ k ∈ imgX X Y,
        α k * k⁻¹ ∈ (CFSG.pCore 2 ↥(imgX X Y)).map (imgX X Y).subtype := by
      rintro _ ⟨x, hx, rfl⟩
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have h1 : c'' * x * c''⁻¹ * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 X := hOX ▸ htriv'' x hxX
      have e1 : α (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x)⁻¹ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
            ⟨c'' * x * c''⁻¹ * (x : G)⁻¹, hXY (CFSG.LieType.BorelTits.pCoreOf_le 2 X h1)⟩ := by
        rw [hα, Sec17.Proof17Res6.actQ_mk, ← map_inv, ← map_mul]
        congr 1
      rw [e1]
      exact mk_mem_pCore_imgX hXY h1
    have hbot := hK _ hq hON (imgX X Y) hKp h5K α hα3 hαK hαtriv (barR Y R)
      (isPGroup_barR hRm.1 hR2) (conj_mem_normalizer_barR hXY hXR)
      (actQ_mem_normalizer_barR m.2 (hAR hc''A))
    exact Or.inl (commutator_le_pCoreOf_of_barR_eq_bot hRm.1 hbot)
  · exfalso
    rw [card_of_isTripleCover hON', CFSG.Sporadic.ON.card_ON] at hq3
    have := Nat.le_of_dvd Nat.card_pos hq3
    omega
  · have hf : Function.Surjective (ψ.toMonoidHom.comp (QuotientGroup.mk' _)) :=
      ψ.surjective.comp (QuotientGroup.mk'_surjective _)
    exact Or.inl (hONc G Y X R hq hON hXY (Or.inr ⟨_, hf⟩) hR2 hRm.1 hXR)
  · have hf : Function.Surjective (ψ.toMonoidHom.comp (QuotientGroup.mk' _)) :=
      ψ.surjective.comp (QuotientGroup.mk'_surjective _)
    exact Or.inl (hONc G Y X R hq hON hXY (Or.inl ⟨hp7, _, hf⟩) hR2 hRm.1 hXR)

end Branch

end CFSG.RankThree.PartTwo.Sec15.Wales154
