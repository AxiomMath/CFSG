module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTen
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate8168
public import Certificates.Certificate8169
public import Certificates.Certificate10019
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofA10
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.J2
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate2201
public import Certificates.Certificate2202
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Item148Res4

variable {G : Type} [Group G] [Finite G]

theorem not_isIrreducibleOn_of_hj_point
    (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {c' d : G} {L' : Subgroup G}
    (hc'Ω : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (hJ2 : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L' d) :
    ¬ Sec21.IsIrreducibleOn (wStar A) := by
  intro hirr
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27
  have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc'Ω).1
  have hc'3 : Nat.card (Subgroup.zpowers c') = 3 := (zpowers_mem_omegaA_iff.mp hc'Ω).2.1
  have hc'1 : c' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc'3
    exact absurd hc'3 (by norm_num)
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L') Nat.prime_three
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ2 hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ2 hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hRK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hc'A hdA hc'1 hL'.1 hJq
  have hdata : Sec13Data G A c' L' := { hD with zpowers_mem_omegaA := hc'Ω, mem_lA := hL' }
  have hline : ∀ x ∈ A, x ≠ 1 → Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set G) → False := by
    intro x hxA hx1 hN
    have hx3 : Nat.card (Subgroup.zpowers x) = 3 := card_zpowers_eq_three hA.1 hxA hx1
    refine Item148Rank.false_of_isIrreducibleOn_wStar148 hirr (Subgroup.zpowers_le.mpr hxA) ?_
      ?_ hN
    · intro hb
      rw [hb, Subgroup.card_bot] at hx3
      norm_num at hx3
    · intro hb
      rw [hb, hD.card_eq] at hx3
      norm_num at hx3
  rcases h134 G A c' L' hdata hJ2 d hdA hd1 ⟨_, hS⟩ K hK hRK with
    ⟨-, -, hΩ1⟩ | ⟨-, -, hNd, -⟩ | ⟨-, hNd, -⟩
  · refine hline c' hc'A hc'1 fun w hw => ?_
    have hmem : (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
      (map_conj_mem_omegaA_iff hw).mpr hc'Ω
    rw [hΩ1, Set.mem_singleton_iff] at hmem
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmem
  · exact hline d hdA hd1 hNd
  · exact hline d hdA hd1 hNd

theorem exists_eq_mul_of_lift148Ten {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hAF : A ∈ partTwoF G) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A)
    (he1 : e ≠ 1) {K J : Subgroup G}
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G))) (hKJ : K ≤ J)
    (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hTen : Lift148Ten A Y K J) {a : G} (ha : a ∈ A) :
    ∃ (k : G) (i : ℤ), k ∈ K ∧ (k * e ^ i)⁻¹ * a ∈ pPrimeCoreOf 3 Y := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hle := Item148Rank.img148_le_of_lift148Ten148 hAF hAY he hK hKJ hJY hAJ hsec hTen
  obtain ⟨⟨φK⟩, ⟨φJ⟩⟩ := hTen
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) :=
    (le_of_mem_thetaComponentsIn hK).trans inf_le_right
  set Jb := img148 A Y J with hJb
  set Kb := img148 A Y K with hKb
  have hKJb : Kb ≤ Jb := img148_mono hKJ
  have heJ : alpha148 A Y e he ∈ Jb := hle (alpha148_mem_img148 he)
  set x : ↥Jb := ⟨alpha148 A Y e he, heJ⟩ with hx
  have hx3 : x ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hx]
    exact alpha148_pow_three hA3 he)
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : alpha148 A Y e he = alpha148 A Y 1 A.one_mem := by
      have h3 : alpha148 A Y e he = 1 := congrArg Subtype.val h1
      rw [h3, alpha148_eq_mk']
      exact (map_one _).symm
    exact he1 (alpha148_injective hA3 he A.one_mem h2)
  set K' := Kb.subgroupOf Jb with hK'
  have hK'7 : Nonempty (↥K' ≃* alternatingGroup (Fin 7)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKJb).trans φK⟩
  have hK'x : K' ≤ Subgroup.centralizer {x} := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨g, hg, hgK, hgz⟩ := mem_img148_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (z : ↥(Y ⊔ A) ⧸ ker148 A Y) * alpha148 A Y e he =
      alpha148 A Y e he * (z : ↥(Y ⊔ A) ⧸ ker148 A Y)
    rw [← hgz, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKC hgK))
  have hcent := centralizer_le_zpowers_sup_of_a10 φJ hx3 hx1 hK'7 hK'x
  have haJ : alpha148 A Y a ha ∈ Jb := hle (alpha148_mem_img148 ha)
  have hac : (⟨alpha148 A Y a ha, haJ⟩ : ↥Jb) ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (alpha148_comm hAc ha he)
  have hmem := hcent hac
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (K' : Set ↥Jb) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (K' : Set ↥Jb) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK'x hy)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K' _ hxN] at hmem
  obtain ⟨k', hk', y, hy, hky⟩ := hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk'
  obtain ⟨k, hkM, hkK, hkk⟩ := mem_img148_iff.mp hk'
  refine ⟨k, i, hkK, ?_⟩
  have hkeM : k * e ^ i ∈ Y ⊔ A := (Y ⊔ A).mul_mem hkM (Subgroup.zpow_mem _
    (Subgroup.mem_sup_right he) i)
  have key : QuotientGroup.mk' (ker148 A Y) ⟨k * e ^ i, hkeM⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨a, Subgroup.mem_sup_right ha⟩ := by
    have h1 : ((k' * x ^ i : ↥Jb) : ↥(Y ⊔ A) ⧸ ker148 A Y) = alpha148 A Y a ha :=
      congrArg Subtype.val hky
    rw [Subgroup.coe_mul, Subgroup.coe_zpow] at h1
    have h1' : (k' : ↥(Y ⊔ A) ⧸ ker148 A Y) * alpha148 A Y e he ^ i = alpha148 A Y a ha := h1
    rw [← alpha148_eq_mk' ha, ← h1', ← hkk, alpha148_eq_mk', ← map_zpow, ← map_mul]
    congr 1
  exact mk'_ker148_eq_iff.mp key

theorem false_of_mem_sup_pPrimeCoreOf {A : Subgroup G} (hAF : A ∈ partTwoF G) {e : G}
    (he : e ∈ A) {K Le N : Subgroup G} (hKLe : K ≤ Le) (hLe : Le ∈ lA A e)
    (hN : Nat.Coprime 3 (Nat.card N))
    (hdec : ∀ a ∈ A, ∃ (k : G) (i : ℤ), k ∈ K ∧ (k * e ^ i)⁻¹ * a ∈ N)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA e Le A)) : False := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set H := Subgroup.normalizer (Subgroup.zpowers e : Set G) with hH
  set θH := aschbacherSolvableCore 3 ↥H with hθH
  set Γ := lBarA e Le A with hΓ
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLe.1
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e he)
  have hCH : Subgroup.centralizer ({e} : Set G) ≤ H := centralizer_singleton_le_normalizer_zpowers e
  have hLAH : Le ⊔ A ≤ H := sup_le (hLeC.trans hCH) (hAC.trans hCH)
  set F : ↥(Le ⊔ A) →* ↥Γ := ((QuotientGroup.mk' θH).comp (Subgroup.inclusion hLAH)).codRestrict Γ
    (fun g => ⟨Subgroup.inclusion hLAH g, Subgroup.mem_subgroupOf.mpr g.2, rfl⟩) with hF
  have hFsurj : Function.Surjective F := by
    rintro ⟨γ, hγ⟩
    obtain ⟨h, hh, rfl⟩ := hγ
    refine ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, Subtype.ext ?_⟩
    rfl
  have hLp : Group.IsPerfect ↥Le := isPerfect_of_mem_thetaComponentsIn hLe.1
  set FL : ↥Le →* ↥Γ := F.comp (Subgroup.inclusion (le_sup_left : Le ≤ Le ⊔ A)) with hFL
  have hFL : ∀ l : ↥Le, FL l ∈ commutator ↥Γ := by
    intro l
    have hl : l ∈ commutator ↥Le := Group.IsPerfect.mem_commutator
    have h1 : FL l ∈ (commutator ↥Le).map FL := ⟨l, hl, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  set ebar : ↥Γ := F ⟨e, Subgroup.mem_sup_right he⟩ with hebar
  set D := commutator ↥Γ ⊔ Subgroup.zpowers ebar with hD
  have hAD : ∀ (a : G) (ha : a ∈ A), F ⟨a, Subgroup.mem_sup_right ha⟩ ∈ D := by
    intro a ha
    obtain ⟨k, i, hkK, hr⟩ := hdec a ha
    have hkLA : k ∈ Le ⊔ A := Subgroup.mem_sup_left (hKLe hkK)
    have heLA : e ∈ Le ⊔ A := Subgroup.mem_sup_right he
    have haLA : a ∈ Le ⊔ A := Subgroup.mem_sup_right ha
    set r := (k * e ^ i)⁻¹ * a with hr'
    have hrLA : r ∈ Le ⊔ A := (Le ⊔ A).mul_mem ((Le ⊔ A).inv_mem
      ((Le ⊔ A).mul_mem hkLA ((Le ⊔ A).zpow_mem heLA i))) haLA
    have hsplit : (⟨a, haLA⟩ : ↥(Le ⊔ A)) =
        ⟨k, hkLA⟩ * ⟨e, heLA⟩ ^ i * ⟨r, hrLA⟩ := by
      apply Subtype.ext
      show a = k * e ^ i * r
      rw [hr']
      group
    have hk' : F ⟨k, hkLA⟩ ∈ commutator ↥Γ := hFL ⟨k, hKLe hkK⟩
    have hr3 : Abelianization.of (F ⟨r, hrLA⟩) ^ 3 = 1 := by
      have hrexp : (⟨r, hrLA⟩ : ↥(Le ⊔ A)) =
          (⟨k, hkLA⟩ * ⟨e, heLA⟩ ^ i)⁻¹ * ⟨a, haLA⟩ := by
        rw [hsplit]
        group
      have hkab : Abelianization.of (F ⟨k, hkLA⟩) = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hk'
      have he3 : Abelianization.of (F ⟨e, heLA⟩) ^ 3 = 1 := by
        rw [← map_pow, ← map_pow]
        have : (⟨e, heLA⟩ : ↥(Le ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 e he)
        rw [this, map_one, map_one]
      have ha3 : Abelianization.of (F ⟨a, haLA⟩) ^ 3 = 1 := by
        rw [← map_pow, ← map_pow]
        have : (⟨a, haLA⟩ : ↥(Le ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 a ha)
        rw [this, map_one, map_one]
      rw [hrexp, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_zpow, map_zpow, hkab,
        one_mul, mul_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, mul_comm i,
        zpow_mul, zpow_natCast, he3, one_zpow, inv_one, one_mul, zpow_natCast, ha3]
    have hrm : Abelianization.of (F ⟨r, hrLA⟩) ^ orderOf r = 1 := by
      rw [← map_pow, ← map_pow]
      have : (⟨r, hrLA⟩ : ↥(Le ⊔ A)) ^ orderOf r = 1 :=
        Subtype.ext (by simp)
      rw [this, map_one, map_one]
    have hcop : Nat.Coprime 3 (orderOf r) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hr) hN
    have hr1 : Abelianization.of (F ⟨r, hrLA⟩) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hr3, hrm⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    have hr' : F ⟨r, hrLA⟩ ∈ commutator ↥Γ := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact hr1
    rw [hsplit, map_mul, map_mul, map_zpow]
    exact D.mul_mem (D.mul_mem (Subgroup.mem_sup_left hk')
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ i))) (Subgroup.mem_sup_left hr')
  have hDtop : D = ⊤ := by
    rw [eq_top_iff]
    rintro γ -
    obtain ⟨g, rfl⟩ := hFsurj γ
    have hle : (Le ⊔ A).subgroupOf (Le ⊔ A) ≤ D.comap F := by
      rw [Subgroup.subgroupOf_sup (le_sup_left : Le ≤ Le ⊔ A) (le_sup_right : A ≤ Le ⊔ A)]
      refine sup_le (fun l hl => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_subgroupOf] at hl
        exact Subgroup.mem_sup_left (hFL ⟨l, hl⟩)
      · rw [Subgroup.mem_subgroupOf] at ha
        exact hAD a ha
    exact hle (Subgroup.mem_subgroupOf.mpr g.2)
  obtain ⟨π, p, f, Kf, hKf, hPi, hmod, hiso⟩ := hPGL
  exact kf148PGLAbel ↥Γ p f ⟨π, Kf, hKf, hPi, hmod, hiso⟩ ebar hDtop

end Item148Res4

open Item148Res4

section Steps


theorem step148RankTenRest_of (h134 : Item134) (h48 : Sec4.Item4_8) : Step148RankTenRest := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hTen hA hXJ hcase
  exfalso
  have := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hstd.toSec13Data.mem_partTwoE
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) := hP.2.2.2.2.2.1
  have hle : img148 A Y A ≤ img148 A Y J :=
    Item148Rank.img148_le_of_lift148Ten148 hAF hAY he hK hKJ hJY hAJ hkt.1 hTen
  have hirr : Sec21.IsIrreducibleOn (wStar A) :=
    Item148Rank.isIrreducibleOn_wStar148 hA27 hle hTen.2
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  rcases hcase with hON | ⟨heΩ, hLeA, -, hPGL⟩
  ·
    rcases hP.2.2.2.2.2.2.2.2.2 with ⟨heΩ, hLeA⟩ | ⟨c', L', hc'Ω, -, hL'A, hJ2, hcent, -⟩
    · exact Main148.not_isTripleCover_of_mem_lA148 hstd heΩ hLeA hON
    · exact not_isIrreducibleOn_of_hj_point h134 h48 hstd hc'Ω hL'A hJ2 he he1 hcent hirr
  ·
    exact false_of_mem_sup_pPrimeCoreOf hAF he hP.2.2.2.2.2.2.2.1 hLeA
      (coprime_card_pPrimeCoreOf 3 Y)
      (fun a ha => exists_eq_mul_of_lift148Ten hAF hAY he he1 hK hKJ hJY hAJ hkt.1 hTen ha) hPGL

theorem step148RankTen_of_item134 (h133 : Item133) (h134 : Item134) (h48 : Sec4.Item4_8) :
    Step148RankTen :=
  step148RankTen_of h133 (step148RankTenRest_of h134 h48)

end Steps

end CFSG.RankThree.PartTwo.Sec14
