module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofQN
import CFSG.RankThree.PartTwo.Sec15.Item15Res4Proof
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515HJEndFpfX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
      deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)) =
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)))

@[expose] noncomputable def Step1515HJEndFpfT0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G))) → False

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

namespace Proof15Res7

omit [Finite G] in
theorem oPrimeResidualOf_le_of_le_sup_coprime {H K S : Subgroup G}
    (hcop : Nat.Coprime 3 (Nat.card S)) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hH : H ≤ K ⊔ S) : oPrimeResidualOf 3 H ≤ K := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  exact mem_left_of_pow_prime_pow Nat.prime_three hSK hcop (hH hy) hk

omit [Finite G] in
theorem mem_centralizer_closure_pair {c d x : G}
    (hc : x ∈ Subgroup.centralizer ({c} : Set G)) (hd : x ∈ Subgroup.centralizer ({d} : Set G)) :
    x ∈ Subgroup.centralizer (Subgroup.closure ({c, d} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro y (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hd).symm

end Proof15Res7

open Proof15Res4 Proof15Res7

theorem Conf1515HJ.le_L_of_le_centralizer
    (h : Conf1515HJ A c L Y)
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) : Y ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  obtain ⟨-, -, hAc⟩ := j2_point_facts hD h.j2
  have hY4 := h.mem_scriptY0Star.prop.1
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO
  have hΔ : delta A (lB A) Y ≤ L ⊔ O := by
    refine sSup_le fun Q hQ => ?_
    obtain ⟨hQq, hQY⟩ := hQ
    exact Item148Point.le_sup_of_eq_zpowers_sup142 hS hAc
      ⟨hQY.trans (hYc.trans (centralizer_singleton_le_normalizer_zpowers c)), hQq.1.2.1,
        hQq.1.2.2⟩
  have hOL : O ≤ Subgroup.normalizer (L : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hD.mem_A))).trans (centralizer_le_normalizer_of_j2 hS h.j2)
  calc Y = oPrimeResidualOf 3 Y := hY4.2.1
    _ ≤ L := oPrimeResidualOf_le_of_le_sup_coprime (coprime_card_pPrimeCoreOf 3 _) hOL
        (hY4.2.2.1.le.trans hΔ)

theorem Conf1515HJ.eq_L_of_le_centralizer
    (h : Conf1515HJ A c L Y)
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) : Y = L := by
  have hYL := h.le_L_of_le_centralizer hYc
  have hLY : L ≤ Y ⊔ CFSG.Open.pCoreOf 2 L := h.eq_L.le.trans (sup_le_sup_right inf_le_right _)
  by_cases h2 : CFSG.Open.pCoreOf 2 L = ⊥
  · rw [h2, sup_bot_eq] at hLY
    exact le_antisymm hYL hLY
  have hD := h.sec13Data
  have hR := h.sec15R
  have hS := hR.toSec14Std
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hR.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hD.le_centralizer))
  have hperf := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  obtain ⟨eθ⟩ := h.j2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hsimp : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := eθ.isSimpleGroup
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_thetaQuot_j2 h.j2
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥L (hR.toTheoremFourHyp.sectionFourHyp hLtop) hperf h.j2
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_mulEquiv_nativeJ2 CFSG.Sporadic.J2.isSimpleGroup_J2
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) eJ
  have hL0 : L ∈ scriptY0 A (lB A) :=
    ⟨⟨⟨hLtop, hD.le_normalizer⟩, Sec16.eq_oPrimeResidualOf_of_isSimpleGroup hperf hsimp h3L,
      le_antisymm (Proof155w.le_delta_of_le_of_j2 hS h.j2 le_rfl) (delta_le L), hq⟩,
      ⟨hLtop, hD.le_normalizer⟩, h2⟩
  exact h.mem_scriptY0Star.eq_of_le hL0 hYL

theorem Conf1515HJ.false_of_le_centralizer
    (h : Conf1515HJ A c L Y) (hT : Step1515HJTrans) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) (h155 : Item155w A (lB A))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d)
    (hfix : CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYL := h.eq_L_of_le_centralizer hYc
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hcB : c ∈ B := Subgroup.subset_closure (Set.mem_insert c _)
  have hdB : d ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hD.mem_A
    · exact hdA
  have hcd : c * d ∉ Subgroup.zpowers d := by
    intro hm
    apply h.not_mem_L
    have hc' : c = (c * d) * d⁻¹ := by group
    rw [hc']
    exact (Subgroup.zpowers_le.mpr hdL) ((Subgroup.zpowers d).mul_mem hm
      ((Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d)))
  obtain ⟨w, hwA, hwd, hwc⟩ := hT G A c L h.sec15R h.j2 h.omega_ne d hdA hd1 hdZ (c * d)
    (B.mul_mem hcB hdB) hcd
  rw [map_conj_zpowers] at hwc
  have hwcB : w * c * w⁻¹ ∈ B := by
    have h1 : w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) := hwc ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr (B.mul_mem hcB hdB)) h1
  have hwcn : w * c * w⁻¹ ∉ Subgroup.zpowers c := by
    intro hm
    have h1 : c * d ∈ Subgroup.zpowers c := by
      have h2 : Subgroup.zpowers (c * d) ≤ Subgroup.zpowers c := hwc ▸ Subgroup.zpowers_le.mpr hm
      exact h2 (Subgroup.mem_zpowers _)
    have h2 : d ∈ Subgroup.zpowers c := by
      have hd' : d = c⁻¹ * (c * d) := by group
      rw [hd']
      exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c))
        h1
    have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
    refine h.zpowers_ne hdL (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h2) ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hd3, hD.orderOf_eq]
  have hBw : B.map (MulAut.conj w).toMonoidHom = B := map_conj_closure_eq hwd hwcB
  set Lw := L.map (MulAut.conj w).toMonoidHom with hLw
  have hSa := (h.sec15R_conj hwA).toSec14Std
  have hJa := nonempty_j2_conj h.j2 w
  have hXB := h.residual_eq_conj hdA hd1 hdZ hwA hwd hwcB
  set T := (CFSG.Open.pCoreOf 2 L).map (MulAut.conj w).toMonoidHom with hTdef
  set R := T ⊓ Subgroup.centralizer (B : Set G) with hRdef
  have hT2 : IsPGroup 2 T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).map _
  have hR2 : IsPGroup 2 R := hT2.to_le inf_le_left
  have hLwT : Lw ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)).trans
      (Subgroup.le_normalizer_map _)
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := by
    have h1 : A.map (MulAut.conj w).toMonoidHom = A := map_conj_eq_self_of_mem_normalizer hwA
    rw [← h1]
    exact (Subgroup.map_mono (hD.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))).trans
      (Subgroup.le_normalizer_map _)
  have hR1 : R ≠ ⊥ := by
    obtain ⟨x, ⟨hxO, hxd⟩, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hfix
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hxO
    have hxB : x ∈ Subgroup.centralizer (B : Set G) :=
      mem_centralizer_closure_pair (hD.le_centralizer hxL) hxd
    have hwxB : w * x * w⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ B.map (MulAut.conj w).toMonoidHom := hBw.symm ▸ hy
      obtain ⟨b, hb, rfl⟩ := hy'
      have hbx : b * x = x * b := Subgroup.mem_centralizer_iff.mp hxB b hb
      change w * b * w⁻¹ * (w * x * w⁻¹) = w * x * w⁻¹ * (w * b * w⁻¹)
      calc w * b * w⁻¹ * (w * x * w⁻¹) = w * (b * x) * w⁻¹ := by group
        _ = w * (x * b) * w⁻¹ := by rw [hbx]
        _ = w * x * w⁻¹ * (w * b * w⁻¹) := by group
    intro hbot
    have hmem : w * x * w⁻¹ ∈ R := ⟨⟨x, hxO, rfl⟩, hwxB⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hx1
    calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
      _ = 1 := by rw [hmem]; group
  have hRB : R ≤ Subgroup.centralizer (B : Set G) := inf_le_right
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) :=
    hRB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB))
  have hRd : R ≤ Subgroup.centralizer ({d} : Set G) :=
    hRB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB))
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hYL]
    exact hRc.trans (centralizer_le_normalizer_of_j2 hS h.j2)
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hD.commute (hBA hy) hx
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    Late.le_normalizer_inf hAT (hAB.trans Subgroup.le_normalizer)
  have hR3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hRQ : R ∈ scriptQ A (lB A) :=
    (mem_scriptQ_of_hj_point hS h.j2 ⟨hRc.trans (centralizer_singleton_le_normalizer_zpowers c),
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩).1
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hZc : Z ≤ Subgroup.centralizer ({c} : Set G) :=
    (hZle.trans (inf_le_left.trans inf_le_left)).trans hD.le_centralizer
  have hZB : Z ≤ Subgroup.centralizer (B : Set G) := fun z hz =>
    mem_centralizer_closure_pair (hZc hz) (hZd hz)
  have hZLw : Z ≤ Lw :=
    (zHJ_le_residual_inf L Y d).trans (hXB ▸ Item148HJ.residual_le Lw (w * d * w⁻¹))
  have hZR : Z ≤ Subgroup.normalizer (R : Set G) :=
    Late.le_normalizer_inf (hZLw.trans hLwT) (hZB.trans Subgroup.le_normalizer)
  have hT1 : T ≠ ⊥ := fun h0 => hR1 (le_bot_iff.mp (h0 ▸ inf_le_left))
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hT2 hT1)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (Z ⊔ R) : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAT (sup_le (hZLw.trans hLwT)
      (inf_le_left.trans Subgroup.le_normalizer)) hx)⟩
  have hΔM := h.delta_le_normalizer h152 h153 h155 hdA hd1 hdZ hR2 hR1 hRQ hAR hZR hRY hRd hMm
  have hLwΔ : Lw ≤ delta A (lB A) M := Proof155w.le_delta_of_le_of_j2 hSa hJa (hLwT.trans hle)
  exact h.false_of_le_normalizer_conj hdA hd1 hdZ hwA hwd hwcB hwcn (hLwΔ.trans hΔM)

section Provers


theorem step1515HJEndX_of_res7 (h134 : Item134) (h48 : Sec4.Item4_8) (h152 : Item152R)
    (h153 : Item153MainR) (h155 : Item155wR) (hF : Step1515HJEndFpfX) : Step1515HJEndX := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hodd hYc
  have hR := h.sec15R
  have hYL := h.eq_L_of_le_centralizer hYc
  subst hYL
  by_cases hfree : ∀ e ∈ A, e ≠ 1 → IsZCentral Y e →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({e} : Set G) = ⊥
  · exact hF G A c Y h hfree d hdA hd1 hdZ hodd
  · push Not at hfree
    obtain ⟨e, heA, he1, heZ, hne⟩ := hfree
    exact (h.false_of_le_centralizer (step1515HJTrans_of h134 h48) (h152 G A c Y hR)
      (h153 G A c Y hR) (h155 G A c Y hR) hYc heA he1 heZ hne).elim

theorem step1515HJEndT0_of_res7 (h134 : Item134) (h48 : Sec4.Item4_8) (h152 : Item152R)
    (h153 : Item153MainR) (h155 : Item155wR) (hF : Step1515HJEndFpfT0) : Step1515HJEndT0 := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hodd hYc hX
  have hR := h.sec15R
  have hYL := h.eq_L_of_le_centralizer hYc
  subst hYL
  by_cases hfree : ∀ e ∈ A, e ≠ 1 → IsZCentral Y e →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({e} : Set G) = ⊥
  · exact hF G A c Y h hfree d hdA hd1 hdZ hodd hX
  · push Not at hfree
    obtain ⟨e, heA, he1, heZ, hne⟩ := hfree
    exact h.false_of_le_centralizer (step1515HJTrans_of h134 h48) (h152 G A c Y hR)
      (h153 G A c Y hR) (h155 G A c Y hR) hYc heA he1 heZ hne

theorem step1515HJEndTail_of_res7 (h134 : Item134) (h48 : Sec4.Item4_8) (h152 : Item152R)
    (h153 : Item153MainR) (h155 : Item155wR) (hFX : Step1515HJEndFpfX)
    (hFT : Step1515HJEndFpfT0) : Step1515HJEndTail :=
  step1515HJEndTail_of (step1515HJEndX_of_res7 h134 h48 h152 h153 h155 hFX)
    (step1515HJEndT0_of_res7 h134 h48 h152 h153 h155 hFT)

end Provers

end CFSG.RankThree.PartTwo.Sec15
