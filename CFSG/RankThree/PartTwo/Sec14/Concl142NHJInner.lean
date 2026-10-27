module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJ
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def SignalE9 (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → ∀ b ∈ E, b ≠ 1 →
    ∃ W : Subgroup X, ¬ 3 ∣ Nat.card W ∧
      Subgroup.centralizer ({b} : Set X) ≤ Subgroup.normalizer (W : Set X) ∧
      ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({b} : Set X) → ¬ 3 ∣ Nat.card U →
        E ≤ Subgroup.normalizer (U : Set X) → U ≤ W

theorem SignalE9.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : SignalE9 Y) :
    SignalE9 X := by
  intro E hE hE9 b hbE hb1
  have hE' : CFSG.Assembly.IsElemAbelian 3 (E.map e.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 e.toMonoidHom E hE
  have hE9' : Nat.card (E.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hE9]
  have hb1' : e b ≠ 1 := fun h1 => hb1 (e.injective (h1.trans e.map_one.symm))
  obtain ⟨W, hW3, hWN, hWle⟩ := h _ hE' hE9' (e b) ⟨b, hbE, rfl⟩ hb1'
  have hcen : (Subgroup.centralizer ({b} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e b} : Set Y) := CFSG.RankThree.PartTwo.map_centralizer_singleton e b
  refine ⟨W.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · rwa [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
  · intro x hx
    have hex : e x ∈ Subgroup.normalizer (W : Set Y) :=
      hWN (hcen ▸ Subgroup.mem_map_of_mem e.toMonoidHom hx)
    rw [Subgroup.mem_normalizer_iff] at hex ⊢
    intro w
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    exact hex (e w)
  · intro U hU hU3 hEU
    have hUC : U.map e.toMonoidHom ≤ Subgroup.centralizer ({e b} : Set Y) :=
      hcen ▸ Subgroup.map_mono hU
    have hU3' : ¬ 3 ∣ Nat.card (U.map e.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective e.injective]
    have hEU' : E.map e.toMonoidHom ≤ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup Y) :
        Set Y) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hEU
    exact Subgroup.map_le_iff_le_comap.mp (hWle _ hUC hU3' hEU')

@[expose] def KS142SignalA7 : Prop :=
  SignalE9 ↥(alternatingGroup (Fin 7))

@[expose] def KS142SignalM22 : Prop :=
  SignalE9 CFSG.Blueprint.NativeSporadic.M22

@[expose] def KS142SignalM12 : Prop :=
  SignalE9 CFSG.Blueprint.NativeSporadic.M12

variable {G : Type} [Group G] [Finite G]

theorem point_facts_of_inner (h131 : Item131) (hspor : SporadicModels131) {A L : Subgroup G}
    {c : G} (hD : Sec13Data G A c L)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    rcases cases131 h131 hspor slTwoCenter hD with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ | ⟨-, hPGL, -⟩ |
        ⟨hcL', -⟩
    · exact h9
    · exact h9
    · exact absurd (facts_of_isZ3PGLThreePi hD hPGL).1 hnL3
    · exact absurd hcL' hcL
  refine ⟨hcL, h9, ?_⟩
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hD.mem_A
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcA inf_le_left
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    hD.commute (hcA hx) hy.1
  have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm

theorem centralizer_le_normalizer_of_three_dvd {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h3 : 3 ∣ Nat.card L) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro x hxc
  refine mem_normalizer_of_map_conj_eq
    ((h.chosen136.2 c h.toSec13Data.zpowers_mem_omegaA L h.toSec13Data.mem_lA).2 _
      (Sec6.map_conj_mem_thetaComponentsAt hxc h.toSec13Data.mem_thetaComponentsAt) ?_)
  rwa [Subgroup.card_map_of_injective (MulAut.conj x).injective]

omit [Finite G] in
theorem three_dvd_card_of_thetaQuot {L : Subgroup G} [Finite L] {X : Type} [Group X]
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* X) (hX : 3 ∣ Nat.card X) : 3 ∣ Nat.card L := by
  have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
  rw [Nat.card_congr φ.toEquiv] at h1
  exact hX.trans h1

theorem le_pPrimeCoreOf_of_signal {L : Subgroup G} {b : G} (hbL : b ∈ L)
    {W : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hW3 : ¬ 3 ∣ Nat.card W)
    (hWN : Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.normalizer (W : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    {B : Subgroup G}
    (hBC : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (B : Set G))
    (hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G))
    {Z : Subgroup G} (hZ : Z ≤ L ⊓ Subgroup.centralizer ({b} : Set G))
    (hZW : (Z.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤ W) :
    Z ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have hZL : Z ≤ L := hZ.trans inf_le_left
  set CL := Subgroup.centralizer ({b'} : Set ↥L) with hCL
  set R := ((W.comap π) ⊓ CL).map L.subtype with hR
  have hZR : Z ≤ R := by
    intro z hz
    have hzL := hZL hz
    have hzC : (⟨z, hzL⟩ : ↥L) ∈ CL := by
      rw [hCL, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hZ hz).2)
    exact ⟨⟨z, hzL⟩, ⟨hZW ⟨⟨z, hzL⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, hzC⟩, rfl⟩
  have hRle : R ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [← CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton L b']
    exact Subgroup.map_mono inf_le_right
  have hR3 : ¬ 3 ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective L.subtype_injective]
    intro h3
    have hker : ¬ 3 ∣ Nat.card π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact hθ3
    exact not_three_dvd_card_comap π hW3 hker (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hRn : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hgL : g ∈ L := hg.1
    set g' : ↥L := ⟨g, hgL⟩
    have hg'C : g' ∈ CL := by
      rw [hCL, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
    have hπg : π g' ∈ Subgroup.normalizer (W : Set (↥L ⧸ θ)) :=
      hWN (mk_mem_centralizer_of_mem_centralizer (L := L) hbL hg'C)
    have hg'N : g' ∈ Subgroup.normalizer (((W.comap π) ⊓ CL : Subgroup ↥L) : Set ↥L) :=
      Late.le_normalizer_inf (A := Subgroup.zpowers g')
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer_comap π hπg))
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hg'C)) (Subgroup.mem_zpowers g')
    exact Subgroup.le_normalizer_map L.subtype ⟨g', hg'N, rfl⟩
  have hRO : R ≤ pPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    le_pPrimeCoreOf hRle hRn ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3)
  have hOO : pPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 _).trans hBC)
      (hCB.trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)) (coprime_card_pPrimeCoreOf 3 _)
  exact hZR.trans (hRO.trans hOO)

theorem inspect142At_of_signal (h131 : Item131) (hspor : SporadicModels131) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L)
    (hZc : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (h3 : 3 ∣ Nat.card L)
    (hsig : SignalE9 (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Inspect142At A c := by
  intro Q hQ B hB hcB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27'
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hcA := hD.mem_A
  have hLc := hD.le_centralizer
  have hCL := centralizer_le_normalizer_of_three_dvd h h3
  obtain ⟨hcL, h9, hAc⟩ := point_facts_of_inner h131 hspor hD hZc hnL3
  have hQc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hQ.prop
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  set Y' := Q ⊓ Subgroup.centralizer (B : Set G) with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) := inf_le_left.trans hQc
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
    le_normalizer_inf_centralizer hA.1.1 hQ.prop.2.2 hB.1
  obtain ⟨b, hbBE, hb1, hBeq⟩ :=
    exists_eq_closure_pair hA hB inf_le_left h9 hcB fun hc => hcL hc.2
  have hbA : b ∈ A := hbBE.2.1
  have hbL : b ∈ L := hbBE.2.2
  have hCBb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbBE.1)
  have hCBc : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  set Z := ⁅Y', A⁆ with hZdef
  have hZY' : Z ≤ Y' := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y' A hAY'
  have hZL : Z ≤ L := commutator_le_of_eq_zpowers_sup hAc hcA hAab hLc hY'c (hY'c.trans hCL)
  have hZb : Z ≤ L ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf hZL (hZY'.trans (inf_le_right.trans hCBb))
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hY'3 (h3.trans (Subgroup.card_dvd_of_le hZY'))
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A Y' hAY'
  have hBC : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [hBeq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc hx.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hCBc.trans hCL) (hCBb.trans Subgroup.le_normalizer)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ebar := (A.subgroupOf L).map π with hEbar
  have hE9 : Nat.card Ebar = 9 := by rw [hEbar, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEe : CFSG.Assembly.IsElemAbelian 3 Ebar :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have hbE : π b' ∈ Ebar := ⟨b', Subgroup.mem_subgroupOf.mpr hbA, rfl⟩
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 b hbA)
  have hπb1 : π b' ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hb1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1 hb'3))
  obtain ⟨W, hW3, hWN, hWle⟩ := hsig Ebar hEe hE9 (π b') hbE hπb1
  set U := (Z.subgroupOf L).map π with hU
  have hUC : U ≤ Subgroup.centralizer ({π b'} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hZb (Subgroup.mem_subgroupOf.mp hx)).2)
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    apply hZ3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]
  have hEU : Ebar ≤ Subgroup.normalizer (U : Set (↥L ⧸ θ)) := map_le_normalizer_map π hAZ
  exact le_pPrimeCoreOf_of_signal hbL hW3 hWN hBC hCB hZb (hWle U hUC hU3 hEU)

theorem not_isoLThreePi_alternating_seven (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi ↥(alternatingGroup (Fin 7)) p e :=
  KFacts.KS14.not_isoLThreePi_of_card KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide +kernel))
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide +kernel))
    p e

theorem not_isLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (hY : ∀ (p e : ℕ) [Fact p.Prime], ¬ Sec4.IsoLThreePi Y p e) : ¬ IsLThreePi X := by
  intro hX
  obtain ⟨p, e, hp, -, h⟩ := isLThreePi_of_mulEquiv φ.symm hX
  exact hY p e h

theorem step142A7_of (h131 : Item131) (hspor : SporadicModels131) (hsig : KS142SignalA7) :
    Step142A7 := by
  intro G _ _ A c L h ⟨φ⟩ _
  refine inspect142At_of_signal h131 hspor h
    (center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2)
    (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    (three_dvd_card_of_thetaQuot φ ?_) (SignalE9.of_mulEquiv φ hsig)
  rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  norm_num

theorem step142M22_of (h131 : Item131) (hspor : SporadicModels131) (hsig : KS142SignalM22) :
    Step142M22 := by
  intro G _ _ A c L h ⟨φ⟩ _
  refine inspect142At_of_signal h131 hspor h (center_eq_bot_of_mulEquiv φ hspor.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
    (three_dvd_card_of_thetaQuot φ ?_) (SignalE9.of_mulEquiv φ hsig)
  rw [KFacts.KS14.card_nativeM22]
  norm_num

theorem step142M12_of (h131 : Item131) (hspor : SporadicModels131) (hsig : KS142SignalM12) :
    Step142M12 := by
  intro G _ _ A c L h ⟨φ⟩ _
  refine inspect142At_of_signal h131 hspor h (center_eq_bot_of_mulEquiv φ hspor.2.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12)
    (three_dvd_card_of_thetaQuot φ ?_) (SignalE9.of_mulEquiv φ hsig)
  rw [KFacts.KS14.card_nativeM12]
  norm_num

end CFSG.RankThree.PartTwo.Sec14
