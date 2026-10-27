module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec17.C174Rank
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag
public import CFSG.Quasithin.EmptyFaithful.T1515eD
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Background.C1GNA7Base

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem c1a_mem_sc {S X Y : Subgroup G} {a : G} :
    a ∈ CFSG.RankThree.PartTwo.Late.sectionCentralizer S X Y ↔
      a ∈ S ∧ ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ Y :=
  Iff.rfl

theorem pCoreOf_le_cQuot (Y₀ : Subgroup G) : CFSG.Open.pCoreOf 2 Y₀ ≤ cQuot Y₀ := by
  intro x hx
  have hxY : x ∈ Y₀ := CFSG.openPCoreOf_le 2 Y₀ hx
  have hxs : (⟨x, hxY⟩ : ↥Y₀) ∈ CFSG.pCore 2 ↥Y₀ :=
    (CFSG.mem_openPCoreOf_iff (⟨x, hxY⟩ : ↥Y₀)).mp hx
  have hinv : (⟨x⁻¹, Y₀.inv_mem hxY⟩ : ↥Y₀) ∈ CFSG.pCore 2 ↥Y₀ :=
    (CFSG.pCore 2 ↥Y₀).inv_mem hxs
  have hN : (CFSG.pCore 2 ↥Y₀).Normal := CFSG.pCore_normal
  rw [← SetLike.mem_coe, coe_cQuot]
  refine c1a_mem_sc.mpr ⟨Subgroup.le_normalizer hxY, fun y hy => ?_⟩
  have hc : (⟨y, hy⟩ : ↥Y₀) * ⟨x⁻¹, Y₀.inv_mem hxY⟩ * (⟨y, hy⟩ : ↥Y₀)⁻¹ ∈ CFSG.pCore 2 ↥Y₀ :=
    hN.conj_mem _ hinv _
  have hmem : y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
    (CFSG.mem_openPCoreOf_iff ((⟨y, hy⟩ : ↥Y₀) * ⟨x⁻¹, Y₀.inv_mem hxY⟩ *
      (⟨y, hy⟩ : ↥Y₀)⁻¹)).mpr hc
  have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [e]
  exact (CFSG.Open.pCoreOf 2 Y₀).mul_mem hx hmem

theorem normalizer_le_normalizer_cQuot (Y₀ : Subgroup G) :
    Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer ((cQuot Y₀ : Subgroup G) : Set G) := by
  have hNO : Subgroup.normalizer (Y₀ : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have key : ∀ n ∈ Subgroup.normalizer (Y₀ : Set G), ∀ z ∈ cQuot Y₀,
      n * z * n⁻¹ ∈ cQuot Y₀ := by
    intro n hn z hz
    have hz' : z ∈ CFSG.RankThree.PartTwo.Late.sectionCentralizer
        (Subgroup.normalizer (Y₀ : Set G)) Y₀ (CFSG.Open.pCoreOf 2 Y₀) := by
      rw [← coe_cQuot]
      exact hz
    obtain ⟨hzN, hzc⟩ := c1a_mem_sc.mp hz'
    rw [← SetLike.mem_coe, coe_cQuot]
    refine c1a_mem_sc.mpr ⟨(Subgroup.normalizer (Y₀ : Set G)).mul_mem
      ((Subgroup.normalizer (Y₀ : Set G)).mul_mem hn hzN)
      ((Subgroup.normalizer (Y₀ : Set G)).inv_mem hn), fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ Y₀ :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Y₀ : Set G)).inv_mem hn) y).mp hy
    have h1 := hzc _ hy'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hNO hn) _).mp h1
    have e : n * (z * (n⁻¹ * y * n⁻¹⁻¹) * z⁻¹ * (n⁻¹ * y * n⁻¹⁻¹)⁻¹) * n⁻¹ =
        n * z * n⁻¹ * y * (n * z * n⁻¹)⁻¹ * y⁻¹ := by group
    rw [e] at h2
    exact h2
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact key m hm z hz
  · intro hz
    have hmi : m⁻¹ ∈ Subgroup.normalizer (Y₀ : Set G) :=
      (Subgroup.normalizer (Y₀ : Set G)).inv_mem hm
    have h1 := key m⁻¹ hmi (m * z * m⁻¹) hz
    have e : m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z := by group
    rw [e] at h1
    exact h1

theorem pCoreOf_normalizer_le_cQuot (h : Sec17Std G A c L Y₀) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ≤ cQuot Y₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := Subgroup.normalizer (Y₀ : Set G)
  set P : Subgroup G := CFSG.Open.pCoreOf 2 M
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMP : M ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hY0M : Y₀ ≤ M := Subgroup.le_normalizer
  have hQ : P ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hP2.of_injective (Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left))
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hw1 := Subgroup.mem_normalizer_iff.mp (hMP (hY0M hy)) w
    have hw2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) w
    show w ∈ P ⊓ Y₀ ↔ y * w * y⁻¹ ∈ P ⊓ Y₀
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr hw1 hw2
  intro x hx
  have hxM : x ∈ M := CFSG.openPCoreOf_le 2 M hx
  rw [← SetLike.mem_coe, coe_cQuot]
  refine c1a_mem_sc.mpr ⟨hxM, fun y hy => ?_⟩
  refine hQ ?_
  rw [Subgroup.mem_inf]
  constructor
  · have hyN : y ∈ Subgroup.normalizer (P : Set G) := hMP (hY0M hy)
    have hyx : y * x⁻¹ * y⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (P.inv_mem hx)
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact P.mul_mem hx hyx
  · have hxy : x * y * x⁻¹ ∈ Y₀ := (Subgroup.mem_normalizer_iff.mp hxM y).mp hy
    exact Y₀.mul_mem hxy (Y₀.inv_mem hy)

theorem normalizer_ne_top_and_fstar (h : Sec17Std G A c L Y₀) :
    Subgroup.normalizer (Y₀ : Set G) ≠ ⊤ ∧
      generalizedFitting ↥(Subgroup.normalizer (Y₀ : Set G)) =
        CFSG.pCore 2 ↥(Subgroup.normalizer (Y₀ : Set G)) := by
  have hM : Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) := by
    rw [h.scriptM_eq]
    exact Set.mem_singleton _
  obtain ⟨_, _, hY2, hF⟩ :=
    CFSG.RankThree.PartTwo.Sec15.facts_of_mem_maximalTwoLocalsContaining h.toSec14Std hM
  exact ⟨hY2.1.1, hF⟩

theorem pRank_three_le_three (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (Y₀ : Set G)) : CFSG.Open.pRank 3 X ≤ 3 := by
  have hM : Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) := by
    rw [h.scriptM_eq]
    exact Set.mem_singleton _
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Y₀ : Set G)) := hM.1.1
  have h1 : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Y₀ : Set G)) :=
    CFSG.SectionRank.pRank_mono (by norm_num) hX
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  exact h1.trans (h2.trans h.toTheoremFourHyp.evenRank_eq.le)

theorem pRank_le_two (h : Sec17Std G A c L Y₀) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (Y₀ : Set G)) :
    CFSG.Open.pRank q X ≤ 2 := by
  have hM : Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) := by
    rw [h.scriptM_eq]
    exact Set.mem_singleton _
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Y₀ : Set G)) := hM.1.1
  have h1 : CFSG.Open.pRank q X ≤ CFSG.Open.pRank q (Subgroup.normalizer (Y₀ : Set G)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt hX
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank q hq _ hloc
  have h3 : CFSG.RankThreeEvenClassification.Helpers.twoLocalRank q G =
      CFSG.Assembly.RankThreeEven.localRank q G := rfl
  have h4 := h.toTheoremFourHyp.localRank_lt q hq hq3
  have h5 := h1.trans (h2.trans h3.le)
  omega

theorem fstar_cQuot_sup (h : Sec17Std G A c L Y₀) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    generalizedFitting ↥(cQuot Y₀ ⊔ T) = CFSG.pCore 2 ↥(cQuot Y₀ ⊔ T) := by
  have hTM : T ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le T hT
  have hCM : cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := fun z hz => by
    have hz' : z ∈ (cQuot Y₀ : Set G) := hz
    rw [coe_cQuot] at hz'
    exact hz'.1
  have hYM : cQuot Y₀ ⊔ T ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le hCM hTM
  have hO : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ≤ cQuot Y₀ ⊔ T :=
    (pCoreOf_normalizer_le_cQuot h).trans le_sup_left
  exact generalizedFitting_eq_pCore_of_le (normalizer_ne_top_and_fstar h).2 hYM hO

theorem mem_scriptY_cQuot_sup (h : Sec17Std G A c L Y₀) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) : cQuot Y₀ ⊔ T ∈ scriptY A := by
  have hTM : T ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le T hT
  have hCM : cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := fun z hz => by
    have hz' : z ∈ (cQuot Y₀ : Set G) := hz
    rw [coe_cQuot] at hz'
    exact hz'.1
  have hYM : cQuot Y₀ ⊔ T ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le hCM hTM
  show cQuot Y₀ ⊔ T ≠ ⊤ ∧ A ≤ Subgroup.normalizer ((cQuot Y₀ ⊔ T : Subgroup G) : Set G)
  refine ⟨fun htop => (normalizer_ne_top_and_fstar h).1 ?_, ?_⟩
  · exact top_le_iff.mp ((le_of_eq htop.symm).trans hYM)
  · have hAY0 : A ≤ Subgroup.normalizer (Y₀ : Set G) :=
      Subgroup.le_normalizer.trans h.normalizer_le
    have hAC : A ≤ Subgroup.normalizer ((cQuot Y₀ : Subgroup G) : Set G) :=
      hAY0.trans (normalizer_le_normalizer_cQuot Y₀)
    have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
      (mem_scriptQ_iff.mp hT.prop.1.1).2.1
    have hsup := CFSG.RankThree.PartTwo.Sec14.le_normalizer_sSup (A := A)
      (S := ({cQuot Y₀, T} : Set (Subgroup G))) (by
        intro Q hQ
        rcases hQ with rfl | rfl
        · exact hAC
        · exact hAT)
    rw [sSup_pair] at hsup
    exact hsup

theorem two_le_pRank_three_of_sl_equiv
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hmod : p ^ e % 3 = 1)
    (φ : X ≃* CFSG.PGLModel.projSL 3 (GaloisField p e)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hdvd : 3 ∣ Nat.gcd 3 (Nat.card (GaloisField p e) - 1) := by
    rw [hK]
    exact Nat.dvd_gcd (dvd_refl 3) (Nat.dvd_of_mod_eq_zero (by omega))
  let ψ : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField p e) :=
    φ.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField p e))
  have hfin : Finite (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField p e)) := Finite.of_equiv X ψ.toEquiv
  have hpR : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField p e))) :=
    GL83.I713.two_le_pRank_projectiveSL_of_dvd (K := GaloisField p e) (n := 3) (le_refl 3)
      Nat.prime_three (by norm_num) hdvd
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) ψ
  rw [heq]
  exact hpR

theorem two_le_pRank_three_of_su_equiv
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hmod : p ^ e % 3 = 2)
    (φ : X ≃* CFSG.PGLModel.projSU 3 p e) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have hdvd : 3 ∣ p ^ e + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  let ψ : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ e) (GaloisField p (2 * e))) :=
    φ.trans (CFSG.PGLModel.projSUEquivStatedProj 3 p e)
  have hfin : Finite (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ e)
      (GaloisField p (2 * e)))) := Finite.of_equiv X ψ.toEquiv
  have hpR : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ e) (GaloisField p (2 * e))))) :=
    GL83.I713.two_le_pRank_statedPSU_of_dvd (K := GaloisField p (2 * e)) (q := p ^ e) (n := 3)
      (ℓ := 3) hK Nat.prime_three (by norm_num) (le_refl 3) (dvd_refl 3) hdvd
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) ψ
  rw [heq]
  exact hpR

theorem two_le_pRank_three_of_isoLThreePi
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi X p e) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases h with ⟨hmod, ⟨φ⟩⟩ | ⟨hmod, ⟨φ⟩⟩
  · exact two_le_pRank_three_of_sl_equiv he hmod φ
  · exact two_le_pRank_three_of_su_equiv he hmod φ

theorem lBar_transport {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    (hs : IsSimpleGroup Y) (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) :
    IsSimpleGroup X ∧ 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  haveI := hs
  refine ⟨e.isSimpleGroup, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact hr

theorem exists_noncomm_of_simple_pRank {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  simp only [not_exists, not_not] at hcomm
  letI : CommGroup X := { ‹Group X› with mul_comm := fun a b => hcomm a b }
  have htop : IsCyclic (⊤ : Subgroup X) :=
    isCyclic_of_surjective (Subgroup.topEquiv.symm : X ≃* (⊤ : Subgroup X))
      (Subgroup.topEquiv.symm).surjective
  have h1 := CFSG.SectionRank.pRank_le_one_of_isCyclic (p := 3) Nat.prime_three htop
  omega

theorem three_dvd_card_of_two_le_pRank {X : Type} [Group X] [Finite X]
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : 3 ∣ Nat.card X := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    rw [hE]
    exact pow_dvd_pow 3 hr
  exact ((dvd_pow_self 3 two_ne_zero).trans h9).trans (Subgroup.card_subgroup_dvd_card E)

theorem lBar_simple_and_pRank
    (h : Sec14Std G A c L) :
    IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have hLc : L ∈ thetaComponentsAt 3 c := lA_subset A c h.mem_lA
  haveI hperf : Group.IsPerfect ↥L :=
    CFSG.RankThree.PartTwo.Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hcases := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  rcases hcases with hJ | hL3 | hA7 | hM22 | hM12
  · haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
    obtain ⟨e⟩ := hJ
    exact lBar_transport e CFSG.Sporadic.J2.isSimpleGroup_J2
      CFSG.Quasithin.two_le_pRank_J2_1515e
  · obtain ⟨p, e, hp, he, hiso⟩ := hL3
    haveI : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := inferInstance
    exact ⟨(CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso).1,
      two_le_pRank_three_of_isoLThreePi he hiso⟩
  · haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨e⟩ := hA7
    exact lBar_transport e inferInstance CFSG.Quasithin.C1GN.two_le_pRank_alt7
  · haveI : Finite CFSG.Blueprint.NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
    obtain ⟨e⟩ := hM22
    exact lBar_transport e CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      CFSG.Quasithin.two_le_pRank_M22_1515e
  · haveI : Finite CFSG.Blueprint.NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
    obtain ⟨e⟩ := hM12
    exact lBar_transport e CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      CFSG.Quasithin.two_le_pRank_M12_1515e

theorem lBar_nonabelian
    (h : Sec14Std G A c L) :
    ∃ a b : ↥L ⧸ aschbacherSolvableCore 3 ↥L, a * b ≠ b * a := by
  obtain ⟨hs, hr⟩ := lBar_simple_and_pRank h
  haveI := hs
  exact exists_noncomm_of_simple_pRank hr

theorem three_dvd_card_L
    (h : Sec14Std G A c L) : 3 ∣ Nat.card L :=
  (three_dvd_card_of_two_le_pRank (lBar_simple_and_pRank h).2).trans
    (Subgroup.card_quotient_dvd_card _)

theorem inf_cQuot_le_theta (h : Sec17Std G A c L Y₀)
    (hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hna : ∃ a b : ↥L ⧸ aschbacherSolvableCore 3 ↥L, a * b ≠ b * a) :
    L ⊓ cQuot Y₀ ≤ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
  classical
  set Q₀ : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hQ₀
  set C₀ : Subgroup G := cQuot Y₀ with hC₀
  set θ : Subgroup ↥L := aschbacherSolvableCore 3 ↥L with hθ
  set S : Subgroup ↥L := (L ⊓ C₀).subgroupOf L with hS
  set N₂ : Subgroup ↥L := (Q₀ ⊓ L).subgroupOf L with hN₂
  set K : Subgroup ↥S := N₂.subgroupOf S with hK
  have hLN : L ≤ Subgroup.normalizer (Y₀ : Set G) := h.le_y0.trans Subgroup.le_normalizer
  have hLC : L ≤ Subgroup.normalizer (C₀ : Set G) :=
    hLN.trans (normalizer_le_normalizer_cQuot Y₀)
  have hCcomm : ∀ a : G, a ∈ C₀ → ∀ b ∈ Y₀, a * b * a⁻¹ * b⁻¹ ∈ Q₀ := by
    intro a ha b hb
    have ha' : a ∈ (cQuot Y₀ : Set G) := ha
    rw [coe_cQuot] at ha'
    exact ha'.2 b hb
  have hSnormal : S.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hS, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnL, hnC⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact L.mul_mem (L.mul_mem g.2 hnL) (L.inv_mem g.2)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hLC g.2) _).mp hnC
  have hKsolv : Group.IsSolvable ↥K := by
    have hKQ : ∀ x : ↥K, (((x.1 : ↥S) : ↥L) : G) ∈ Q₀ := by
      intro x
      have h1 : ((x.1 : ↥S) : ↥L) ∈ N₂ := Subgroup.mem_subgroupOf.mp x.2
      have h2 : (((x.1 : ↥S) : ↥L) : G) ∈ Q₀ ⊓ L := Subgroup.mem_subgroupOf.mp h1
      exact (Subgroup.mem_inf.mp h2).1
    let ψ : ↥K →* ↥Q₀ :=
      { toFun := fun x => ⟨(((x.1 : ↥S) : ↥L) : G), hKQ x⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp }
    have hψ : Function.Injective ψ := by
      intro x y hxy
      have h3 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h3))
    have hK2 : IsPGroup 2 ↥K :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀).of_injective ψ hψ
    haveI := hK2.isNilpotent
    infer_instance
  have hcomm : commutator ↥S ≤ K := by
    have hK_comm : ∀ x y : ↥S, ⁅x, y⁆ ∈ K := by
      intro x y
      rw [hK, Subgroup.mem_subgroupOf, hN₂, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨?_, ((⁅x, y⁆ : ↥S) : ↥L).2⟩
      have e : (((⁅x, y⁆ : ↥S) : ↥L) : G) =
          ((x : ↥L) : G) * ((y : ↥L) : G) * ((x : ↥L) : G)⁻¹ * ((y : ↥L) : G)⁻¹ := by
        simp [commutatorElement_def]
      rw [e]
      have hxC : ((x : ↥L) : G) ∈ C₀ := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.2)).2
      have hyY : ((y : ↥L) : G) ∈ Y₀ := h.le_y0 (y : ↥L).2
      exact hCcomm _ hxC _ hyY
    show ⁅(⊤ : Subgroup ↥S), ⊤⁆ ≤ K
    exact Subgroup.commutator_le.mpr fun x _ y _ => hK_comm x y
  have hSsolv : Group.IsSolvable ↥S := by
    have hc : Group.IsSolvable ↥(commutator ↥S) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hcomm)
    exact Group.isSolvable_commutator_iff.mp hc
  haveI := hs
  set φ : ↥L →* ↥L ⧸ θ := QuotientGroup.mk' θ with hφ
  have hSbar : (S.map φ).Normal := hSnormal.map φ (QuotientGroup.mk'_surjective θ)
  have hS_le : S ≤ θ := by
    rcases hs.eq_bot_or_eq_top_of_normal (S.map φ) with hbot | htop
    · intro x hx
      have hmem : φ x ∈ S.map φ := Subgroup.mem_map_of_mem φ hx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    · exfalso
      have hsurj : Function.Surjective (φ.comp S.subtype) := by
        intro q
        have hq : q ∈ S.map φ := by rw [htop]; exact Subgroup.mem_top q
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
        exact ⟨⟨x, hx⟩, rfl⟩
      have hsolv : Group.IsSolvable (↥L ⧸ θ) := Group.isSolvable_of_surjective hsurj
      obtain ⟨a, b, hab⟩ := hna
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  rintro x ⟨hxL, hxC⟩
  have hmem : (⟨x, hxL⟩ : ↥L) ∈ S := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hxL, hxC⟩)
  exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hS_le hmem, rfl⟩

theorem map_conj_eq_of_mem_normalizer_D1 {H : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj x).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  · intro y hy
    refine ⟨x⁻¹ * y * x⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (inv_mem hx) y).mp hy, ?_⟩
    show x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y
    group

abbrev nH (c : G) : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

theorem normalizer_zpowers_le_normalizer_L (h : Sec14Std G A c L) (h3 : 3 ∣ Nat.card L) :
    nH c ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  have hx' : x ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := hx
  have hmap : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers c :=
    map_conj_eq_of_mem_normalizer_D1 hx'
  have hzc : Subgroup.zpowers (x * c * x⁻¹) = Subgroup.zpowers c := by
    have h1 := MonoidHom.map_zpowers (MulAut.conj x).toMonoidHom c
    rw [hmap] at h1
    exact h1.symm
  have hLc : L.map (MulAut.conj x).toMonoidHom ∈ thetaComponentsAt 3 (x * c * x⁻¹) :=
    CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three
      h.mem_lA.1 x
  rw [CFSG.RankThree.PartTwo.Sec15.Proof1515.thetaComponentsAt_eq_of_zpowers_eq hzc] at hLc
  have hcard : Nat.card (L.map (MulAut.conj x).toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have h3' : 3 ∣ Nat.card (L.map (MulAut.conj x).toMonoidHom) := by
    rw [hcard]
    exact h3
  have hEq : L.map (MulAut.conj x).toMonoidHom = L :=
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 _ hLc h3'
  exact CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq hEq

theorem le_nH_of_mem_lA (h : Sec14Std G A c L) : L ≤ nH c :=
  (CFSG.RankThree.PartTwo.Sec14.le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1).trans
    (CFSG.RankThree.PartTwo.Sec14.centralizer_singleton_le_normalizer_zpowers c)

theorem isSolvable_centralizer_of_pRank_aux {Γ : Type*} [Group Γ] [Finite Γ]
    (hO : CFSG.pPrimeCore 3 Γ = ⊥) {z : Γ} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzN : (Subgroup.zpowers z).Normal) {Λ : Subgroup Γ} [Λ.Normal]
    (hΛz : Λ ≤ Subgroup.centralizer ({z} : Set Γ))
    (hcen : Λ ⊓ Subgroup.centralizer (Λ : Set Γ) = ⊥)
    (hΛ : 2 ≤ CFSG.Open.pRank 3 Λ) (hΓ : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 3) :
    Group.IsSolvable (Subgroup.centralizer (Λ : Set Γ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (Subgroup.centralizer (Λ : Set Γ)).Normal := inferInstance
  have hzD : z ∈ Subgroup.centralizer (Λ : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hΛz hh)
  have hrk : CFSG.Open.pRank 3 (Subgroup.centralizer (Λ : Set Γ)) ≤ 1 := by
    by_contra hcon
    have hcon' : 2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (Λ : Set Γ)) := by omega
    obtain ⟨E, hED, hE, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) hcon'
    obtain ⟨F, hFΛ, hF, hFcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) hΛ
    have hc : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hED ha) b (hFΛ hb)).symm
    have hEFbot : E ⊓ F = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      rw [← hcen]
      exact Subgroup.mem_inf.mpr ⟨hFΛ hx.2, hED hx.1⟩
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E F hc).1
    rw [hEFbot, Subgroup.card_bot, mul_one, hEcard, hFcard] at hprod
    have hk : Nat.card (E ⊔ F : Subgroup Γ) = 3 ^ 4 := hprod.trans (by norm_num)
    have hEF : CFSG.Open.IsElemAbelian 3 (E ⊔ F : Subgroup Γ) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hE hF hc
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Γ) :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hEF hk
    omega
  exact isSolvable_of_normal_pRank_le_one hO hz3 hz1 hzN inferInstance hzD hrk

theorem case148One_of_img_three_prime {LB : Subgroup G → Subgroup G} {Y : Subgroup G}
    [(ker148 A Y).Normal] (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hnorm : (((deltaZero A LB Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal)
    (h3 : ¬ 3 ∣ Nat.card ↥(img148 A Y (deltaZero A LB Y))) : Case148One A LB Y := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec15.Y4Core.nonempty_img148_equiv_map hAY
    (deltaZero_le (A := A) (LB := LB) Y)
  have hcard : ¬ 3 ∣ Nat.card ↥(((deltaZero A LB Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) := by
    rwa [← Nat.card_congr e.toEquiv]
  have hcop : Nat.Coprime 3 (Nat.card ↥(((deltaZero A LB Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcard
  have hle := CFSG.le_pPrimeCore_of_normal_coprime (G := ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) hnorm hcop
  have hbot : CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  rw [hbot] at hle
  unfold Case148One
  intro x hx
  have hxY : x ∈ Y := (deltaZero_le (A := A) (LB := LB) Y) hx
  have hmem : (⟨x, hxY⟩ : ↥Y) ∈ CFSG.pPrimeCore 3 ↥Y := by
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) (⟨x, hxY⟩ : ↥Y) ∈
        (((deltaZero A LB Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    have h2 := hle h1
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  unfold pPrimeCoreOf
  exact Subgroup.mem_map_of_mem Y.subtype hmem

theorem pRank_three_img148_le {Y X : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hXY : X ≤ Y) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img148 A Y X)) ≤ CFSG.Open.pRank 3 Y := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec15.Y4Core.nonempty_img148_equiv_map hAY hXY
  have hK : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y))
  calc CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img148 A Y X))
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥((X.subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
    _ = CFSG.Open.pRank 3 ((X.subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) :=
        CFSG.SectionRank.pRank_mono (by norm_num) le_top
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore 3 ↥Y) hK
    _ = CFSG.Open.pRank 3 Y := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y).symm

end CFSG.RankThree.PartTwo.Sec17.C174
