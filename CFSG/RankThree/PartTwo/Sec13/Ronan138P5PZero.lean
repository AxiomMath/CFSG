module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Main
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lift
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec13.Ronan138SP
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Aut
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Core
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SSyl
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec6.Item612
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_inSubgroup_theta {L : Subgroup G} {x : G}
    (hx : x ∈ inSubgroup (aschbacherSolvableCore 3) L) {k : ℕ} (hk : x ^ (3 ^ k) = 1) :
    x = 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  have h1 : orderOf (⟨t, ht⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Subtype.ext
    simpa using hk
  have h2 := orderOf_dvd_natCard (⟨t, ht⟩ : aschbacherSolvableCore 3 L)
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (KFacts.not_three_dvd_card_aschbacherSolvableCore L))
  have h3 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have : t = 1 := congrArg Subtype.val h3
  simp [this]

theorem rho_eq_one_of_mem_centralizer {L : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (L : Set G)) (hcN : c ∈ Subgroup.normalizer (L : Set G)) :
    rho L ⟨c, hcN⟩ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change ((L.normalizerMonoidHom ⟨c, hcN⟩ x : L) : L ⧸ aschbacherSolvableCore 3 L) = (x : L ⧸ _)
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, ← Subgroup.mem_centralizer_iff.mp hc x x.2,
      mul_inv_cancel_right]

theorem card_sup_zpowers_eq_nine {c z : G} (hc : orderOf c = 3) (hz3 : z ^ 3 = 1)
    (hzc : z ∉ Subgroup.zpowers c) (hcz : c * z = z * c) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers z : Subgroup G) = 9 := by
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers c = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers z ⊓ Subgroup.zpowers c : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers z ⊓ Subgroup.zpowers c ≤
        Subgroup.zpowers z)
      rwa [Nat.card_zpowers, hz] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers z ⊓ Subgroup.zpowers c = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hz])
      have hzm : z ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers c := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact hzc hzm.2
  have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute c z from hcz) k).eq
  have h := Sec6.card_sup_mul_card_inf hle
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hz, hc, sup_comm] at h
  omega

theorem exists_e9_le {K : Subgroup G} (hK : CFSG.Assembly.IsElemAbelian 3 K) {c : G}
    (hc : orderOf c = 3) (hcK : c ∈ K) (h9 : 9 ≤ Nat.card K) :
    ∃ P₀ ≤ K, c ∈ P₀ ∧ CFSG.Assembly.IsElemAbelian 3 P₀ ∧ Nat.card P₀ = 9 := by
  obtain ⟨z, hzK, hzc⟩ : ∃ z ∈ K, z ∉ Subgroup.zpowers c := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hle : Nat.card K ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le h
    rw [Nat.card_zpowers, hc] at hle
    omega
  have hz3 : z ^ 3 = 1 := hK.2 z hzK
  have hcz : c * z = z * c := congrArg Subtype.val (hK.1.is_comm.comm ⟨c, hcK⟩ ⟨z, hzK⟩)
  refine ⟨Subgroup.zpowers c ⊔ Subgroup.zpowers z,
    sup_le (Subgroup.zpowers_le.mpr hcK) (Subgroup.zpowers_le.mpr hzK),
    Subgroup.mem_sup_left (Subgroup.mem_zpowers c),
    hK.mono (sup_le (Subgroup.zpowers_le.mpr hcK) (Subgroup.zpowers_le.mpr hzK)),
    card_sup_zpowers_eq_nine hc hz3 hzc hcz⟩

theorem step138PZero_of (hcore : Step13PZeroCore) (hcube : Step138NoCubeRootC) :
    Step138PZero := by
  intro G _ _ A c L E hH hPGL F hF P hP hEFP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, hcF, -, -, -⟩ := Ronan138S.exists_frame138 hH hF hPGL
  have hH' := hH
  obtain ⟨h, hL3, hcE, hE3, -, hEN, -, -, hC⟩ := hH'
  have hF' := hF
  obtain ⟨⟨hFEL, hF3, hF27, -, -⟩, hFL9⟩ := hF'
  have hEFeq : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hL := h.mem_thetaComponentsAt
  have hLc := h.le_centralizer
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have hZ := center_eq_bot_of_isLThreePi hLq hL3
  have hL3' := hL3
  obtain ⟨p, e, _, he, hiso⟩ := hL3'
  have h9 := Sec13.not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he hiso
  have hq2 : 2 < p ^ e := by
    obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
    exact Item138Proof.two_lt_of_mulEquiv hLq hK hq ψ
  have hcCL : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hcCL
  have hcθ : c ∈ Sec4.thetaQuotCentralizer L :=
    ⟨⟨c, hcN⟩, rho_eq_one_of_mem_centralizer hcCL hcN, rfl⟩
  have hθL : ∀ x ∈ L, x ∈ Sec4.thetaQuotCentralizer L → x ^ 3 = 1 → x = 1 := fun x hxL hx hx3 =>
    eq_one_of_mem_inSubgroup_theta (k := 1)
      (Sec4.Item424Proof.mem_theta_of_mem_thetaQuotCentralizer hZ hxL hx) (by simpa using hx3)
  have hcL : c ∉ L := fun hcL => h.ne_one (hθL c hcL hcθ hc3)
  have hFLc : Subgroup.zpowers c ⊓ (F ⊓ L) = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers c ⊓ (F ⊓ L) : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers c ⊓ (F ⊓ L) ≤
        Subgroup.zpowers c)
      rwa [Nat.card_zpowers, hc] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ (F ⊓ L) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hc])
      have hcm : c ∈ Subgroup.zpowers c ⊓ (F ⊓ L) := by
        rw [heq]
        exact Subgroup.mem_zpowers c
      exact hcL hcm.2.2
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcFL : Subgroup.zpowers c ≤ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro f hf
    exact hFcomm f hf.1 c hcF
  have hFeq : Subgroup.zpowers c ⊔ (F ⊓ L) = F := by
    have hle : Subgroup.zpowers c ⊔ (F ⊓ L) ≤ F :=
      sup_le (Subgroup.zpowers_le.mpr hcF) inf_le_left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have := Sec6.card_sup_mul_card_inf hcFL
    rw [hFLc, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc, hFL9] at this
    rw [hF27, this]
  have hFcL : F ≤ Subgroup.zpowers c ⊔ L := hFeq ▸ sup_le_sup_left inf_le_right _
  have hFN : F ≤ Subgroup.normalizer (L : Set G) :=
    hFcL.trans (sup_le (Subgroup.zpowers_le.mpr hcN) Subgroup.le_normalizer)
  have hFmax : ∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' →
      Nat.card F' ≤ Nat.card F := by
    intro F' hF'e hFF'
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hyF', hyF⟩ : ∃ y ∈ F', y ∉ F := by
      by_contra hno
      simp only [not_exists, not_and, not_not] at hno
      exact absurd (Subgroup.card_le_of_le hno) (by omega)
    have hy3 : y ^ 3 = 1 := hF'e.2 y hyF'
    have hyFc : ∀ f ∈ F, f * y = y * f := fun f hf =>
      congrArg Subtype.val (hF'e.1.is_comm.comm ⟨f, hFF' hf⟩ ⟨y, hyF'⟩)
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := by
      have hyc : y * c * y⁻¹ ∈ Subgroup.zpowers c := by
        rw [← hyFc c hcF, mul_inv_cancel_right]
        exact Subgroup.mem_zpowers c
      have hLy := Sec11.map_conj_mem_thetaComponentsAt hc3 hL hyc
      by_contra hyL
      have hne : L.map (MulAut.conj y).toMonoidHom ≠ L := fun heq =>
        hyL (Sec13.map_conj_eq_iff_mem_normalizer.mp heq)
      have hle := Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in hLy hL hne
      have hbot : F ⊓ L = ⊥ := by
        rw [eq_bot_iff]
        intro f hf
        rw [Subgroup.mem_bot]
        have hfy : f ∈ L.map (MulAut.conj y).toMonoidHom := by
          refine ⟨f, hf.2, ?_⟩
          change y * f * y⁻¹ = f
          rw [← hyFc f hf.1, mul_inv_cancel_right]
        exact hθL f hf.2 (hle hfy) (hF3.2 f hf.1)
      rw [hbot, Subgroup.card_bot] at hFL9
      norm_num at hFL9
    set F'' : Subgroup G := F ⊔ Subgroup.zpowers y with hF''def
    have hyF'' : ∀ a ∈ F, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute a y from hyFc a ha) k).eq
    have hF''e : CFSG.Assembly.IsElemAbelian 3 F'' :=
      CFSG.Open.IsElemAbelian.sup_of_commute hF3 (CFSG.Open.isElemAbelian_zpowers hy3) hyF''
    have hF''N : F'' ≤ Subgroup.normalizer (L : Set G) :=
      sup_le hFN (Subgroup.zpowers_le.mpr hyN)
    have hy1 : y ≠ 1 := fun h1 => hyF (h1 ▸ F.one_mem)
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hinf : Subgroup.zpowers y ⊓ F = ⊥ := by
      have hdvd : Nat.card (Subgroup.zpowers y ⊓ F : Subgroup G) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers y ⊓ F ≤
          Subgroup.zpowers y)
        rwa [Nat.card_zpowers, hyo] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : Subgroup.zpowers y ⊓ F = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hyo])
        have hym : y ∈ Subgroup.zpowers y ⊓ F := by
          rw [heq]
          exact Subgroup.mem_zpowers y
        exact hyF hym.2
    have hyNF : Subgroup.zpowers y ≤ Subgroup.normalizer (F : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro f hf
      exact hyFc f hf
    have hF''81 : Nat.card F'' = 81 := by
      have := Sec6.card_sup_mul_card_inf hyNF
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hyo, hF27, sup_comm] at this
      rw [hF''def]
      omega
    set φ : F'' →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
      (rho L).comp (Subgroup.inclusion hF''N) with hφ
    have hrange : Nat.card φ.range ≤ 9 := by
      have hre : CFSG.Open.IsElemAbelian 3 φ.range := by
        have h1 := (hF''e.subgroupOf F'').map φ
        rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h1
      exact Sec14.Ronan148W.card_le_nine_of_isElemAbelian_mulAut he hiso hq2 h9 hre
    have hker : 9 ≤ Nat.card φ.ker := by
      have hmul := Subgroup.card_ker_mul_card_range φ
      rw [hF''81] at hmul
      by_contra hk
      rw [not_le] at hk
      have : Nat.card φ.ker * Nat.card φ.range ≤ 8 * 9 :=
        Nat.mul_le_mul (by omega) hrange
      omega
    set K₀ : Subgroup G := φ.ker.map F''.subtype with hK₀
    have hK₀θ : K₀ ≤ Sec4.thetaQuotCentralizer L := by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨Subgroup.inclusion hF''N k, hk, rfl⟩
    have hK₀e : CFSG.Assembly.IsElemAbelian 3 K₀ := hF''e.mono (Subgroup.map_subtype_le _)
    have hcF'' : c ∈ F'' := Subgroup.mem_sup_left hcF
    have hcK₀ : c ∈ K₀ := by
      refine ⟨⟨c, hcF''⟩, ?_, rfl⟩
      show φ ⟨c, hcF''⟩ = 1
      exact rho_eq_one_of_mem_centralizer hcCL _
    have hK₀9 : 9 ≤ Nat.card K₀ := by
      rw [hK₀, Subgroup.card_map_of_injective F''.subtype_injective]
      exact hker
    obtain ⟨P₀, hP₀K, hcP₀, hP₀e, hP₀9⟩ := exists_e9_le hK₀e hc hcK₀ hK₀9
    exact hcore G A c L h hL3 P₀ hcP₀ (hP₀K.trans hK₀θ) hP₀e hP₀9
  have h3L : 3 ∣ Nat.card L := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_right : F ⊓ L ≤ L)
    rw [hFL9] at h1
    exact (show 3 ∣ 9 by norm_num).trans h1
  have hPH := CFSG.ABGLocalTools.IsSylowOf.le hP
  have hP3 := CFSG.ABGLocalTools.IsSylowOf.isPGroup hP
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hPH hg) c).mp (Subgroup.mem_zpowers c)
    have hLg := Sec11.map_conj_mem_thetaComponentsAt hc3 hL hgc
    have h3Lg : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact h3L
    exact Sec13.map_conj_eq_iff_mem_normalizer.mp
      (eq_of_mem_thetaComponentsAt_of_maximal hc hL hZ hFcL hF3 hFmax hLg h3Lg)
  refine ⟨hPN, ?_⟩
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec11.le_centralizer_of_le_normalizer_zpowers hc hP3 hPH
  have hFP : F ≤ P := le_sup_right.trans hEFP
  have hP3elt : ∀ w ∈ P, ∃ k : ℕ, w ^ (3 ^ k) = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hP3 ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcentF : ∀ w ∈ P ⊓ Sec4.thetaQuotCentralizer L, ∀ f ∈ F, f * w = w * f := by
    intro w hw
    have hFw : F ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← hFeq]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hPc hw.1)).symm
      · intro f hf
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨wN, hw1, hwrfl⟩ := hw.2
        have hwN : w ∈ Subgroup.normalizer (L : Set G) := hwrfl ▸ wN.2
        have hwfL : w * f * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwN f).mp hf.2
        have hθ : f⁻¹ * (w * f * w⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
          have h1 : rho L ⟨w, hwN⟩ = 1 := by
            have : (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G)) = wN := Subtype.ext hwrfl.symm
            rw [this]
            exact hw1
          have h2 := congrArg (fun σ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
            σ ((⟨f, hf.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) h1
          change ((⟨w * f * w⁻¹, hwfL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
            ((⟨f, hf.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) at h2
          rw [eq_comm, QuotientGroup.eq] at h2
          exact ⟨_, h2, rfl⟩
        have hP : f⁻¹ * (w * f * w⁻¹) ∈ P :=
          P.mul_mem (P.inv_mem (hFP hf.1)) (P.mul_mem (P.mul_mem hw.1 (hFP hf.1)) (P.inv_mem hw.1))
        obtain ⟨k, hk⟩ := hP3elt _ hP
        have h1 := eq_one_of_mem_inSubgroup_theta hθ hk
        have h2 : w * f * w⁻¹ = f := by
          calc w * f * w⁻¹ = f * (f⁻¹ * (w * f * w⁻¹)) := by group
            _ = f := by rw [h1, mul_one]
        calc f * w = (w * f * w⁻¹) * w := by rw [h2]
          _ = w * f := by group
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hFw hf)
  have horder3 : ∀ w ∈ P ⊓ Sec4.thetaQuotCentralizer L, w ^ 3 = 1 → w ∈ Subgroup.zpowers c := by
    intro w hw hw3
    have hwF : w ∈ F := by
      have hcomm : ∀ a ∈ F, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
        intro a ha b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_right (show Commute a w from hcentF w hw a ha) k).eq
      have hFw := CFSG.Open.IsElemAbelian.sup_of_commute hF3
        (CFSG.Open.isElemAbelian_zpowers hw3) hcomm
      have hle := hFmax _ hFw le_sup_left
      have heq : F ⊔ Subgroup.zpowers w = F :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
      exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    have hwm : w ∈ (Subgroup.zpowers c : Set G) * ((F ⊓ L : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcFL, hFeq]
      exact hwF
    obtain ⟨a, ha, f, hf, rfl⟩ := hwm
    have hfθ : f ∈ Sec4.thetaQuotCentralizer L := by
      have : f = a⁻¹ * (a * f) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _
        ((Subgroup.zpowers_le.mpr hcθ) ha)) hw.2
    have hf1 : f = 1 := hθL f hf.2 hfθ (hF3.2 f hf.1)
    subst hf1
    simpa using ha
  intro w hw
  by_cases hw3 : w ^ 3 = 1
  · exact horder3 w hw hw3
  · exfalso
    obtain ⟨k, hk⟩ := hP3elt w hw.1
    have hdvd : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, hj, hjord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hj2 : 2 ≤ j := by
      by_contra hj2
      have : orderOf w ∣ 3 := by
        rw [hjord]
        interval_cases j <;> norm_num
      exact hw3 (orderOf_dvd_iff_pow_eq_one.mp this)
    set w₁ := w ^ (3 ^ (j - 2)) with hw₁
    have hw₁mem : w₁ ∈ P ⊓ Sec4.thetaQuotCentralizer L := Subgroup.pow_mem _ hw _
    have hdvd2 : 3 ^ (j - 2) ∣ orderOf w := by
      rw [hjord]
      exact pow_dvd_pow 3 (by omega)
    have hw₁o : orderOf w₁ = 9 := by
      rw [hw₁, orderOf_pow_of_dvd (by positivity) hdvd2, hjord,
        Nat.pow_div (by omega) (by norm_num), show j - (j - 2) = 2 by omega]
    set u := w₁ ^ 3 with hu
    have hu3 : u ^ 3 = 1 := by
      rw [hu, ← pow_mul, show 3 * 3 = 9 by rfl, ← hw₁o, pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hw₁o] at this
      norm_num at this
    have humem : u ∈ Subgroup.zpowers c := horder3 u (Subgroup.pow_mem _ hw₁mem 3) hu3
    have hFmax' : ∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F :=
      fun F' hF'e hFF' => (Subgroup.eq_of_le_of_card_ge hFF' (hFmax F' hF'e hFF')).symm
    have hcube' := hcube G A c L E hH hPGL F hF hFmax' P hP hEFP hPN horder3
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp humem
    have hi' : c ^ i = c ^ (i % ((3 : ℕ) : ℤ)) := zpow_eq_zpow_emod' i hc3
    simp only [Nat.cast_ofNat] at hi'
    have hrange : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hrange with h0 | h1 | h2
    · apply hu1
      rw [← hi, hi', h0, zpow_zero]
    · apply hcube' w₁ hw₁mem (hcentF w₁ hw₁mem)
      rw [← hu, ← hi, hi', h1, zpow_one]
    · apply hcube' w₁⁻¹ (Subgroup.inv_mem _ hw₁mem) (hcentF _ (Subgroup.inv_mem _ hw₁mem))
      rw [inv_pow, ← hu, ← hi, hi', h2]
      have hc2 : c ^ (2 : ℤ) * c = 1 := by
        rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]
      exact inv_eq_of_mul_eq_one_right hc2

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
