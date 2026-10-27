module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920Force
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CentOverO2Inner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5QuotBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.GroupTheory.SylowSupCentralizer
public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.Adapters.Certificate43Check
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Competitor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.UEqZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.SmithC27Star
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartOne.N1322.Statements
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartTwo.KFacts.K412Alternating
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1721Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1726Proof
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.RankThree.ThinCatalog.MathieuThreeRank
public import CFSG.Sporadic.Schreier.M11
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem three_mem_piSet_of_subset_mul {A J : Subgroup G}
    (hJ : (J : Set G) ⊆ (pCoreOf 2 J : Set G) * (A : Set G))
    (hJ3 : 3 ∣ Nat.card (Bar2 J)) (hAodd : Odd (Nat.card A)) : 3 ∈ piSet A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 J) 3 hJ3
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  obtain ⟨o, ho, a, ha, hoa⟩ := Set.mem_mul.mp (hJ x.2)
  have hoJ : o ∈ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J ho
  have haJ : a ∈ J := by
    have hae : a = o⁻¹ * (x : G) := by rw [← hoa]; group
    rw [hae]
    exact J.mul_mem (J.inv_mem hoJ) x.2
  have hoP : (⟨o, hoJ⟩ : ↥J) ∈ CFSG.pCore 2 ↥J := (CFSG.mem_openPCoreOf_iff _).mp ho
  have hmk : (QuotientGroup.mk (⟨a, haJ⟩ : ↥J) : Bar2 J) = QuotientGroup.mk x := by
    have hxe : x = ⟨o, hoJ⟩ * ⟨a, haJ⟩ := Subtype.ext hoa.symm
    rw [hxe, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hoP, one_mul]
  have ha3P : a ^ 3 ∈ pCoreOf 2 J := by
    have h1 : (QuotientGroup.mk ((⟨a, haJ⟩ : ↥J) ^ 3) : Bar2 J) = 1 := by
      rw [QuotientGroup.mk_pow, hmk, ← hxb, pow_orderOf_eq_one]
    have h2 : (⟨a, haJ⟩ : ↥J) ^ 3 ∈ CFSG.pCore 2 ↥J := (QuotientGroup.eq_one_iff _).mp h1
    have h3 := (CFSG.mem_openPCoreOf_iff ((⟨a, haJ⟩ : ↥J) ^ 3)).mpr h2
    simpa using h3
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pCoreOf 2 J)) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J).exists_card_eq
    rw [hk]
    exact hAodd.coprime_two_right.pow_right k
  have ha3 : a ^ 3 = 1 := by
    have hmem : a ^ 3 ∈ A ⊓ pCoreOf 2 J := ⟨A.pow_mem ha 3, ha3P⟩
    rw [Subgroup.inf_eq_bot_of_coprime hcop] at hmem
    exact (Subgroup.mem_bot).mp hmem
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h1 : (QuotientGroup.mk (⟨1, haJ⟩ : ↥J) : Bar2 J) = 1 := by
      rw [show (⟨1, haJ⟩ : ↥J) = 1 from rfl, QuotientGroup.mk_one]
    rw [hmk] at h1
    rw [h1, orderOf_one] at hxb
    norm_num at hxb
  have hord : orderOf (⟨a, ha⟩ : ↥A) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha3 ha1
  exact ⟨Nat.prime_three, hord ▸ orderOf_dvd_natCard _⟩

theorem jzero_le_and_normal (M Dsub : Subgroup G) :
    S17.oUpperTwo (Opp 2 (Dsub ⊓ M)) ≤ Dsub ⊓ M ∧
      ((S17.oUpperTwo (Opp 2 (Dsub ⊓ M))).subgroupOf (Dsub ⊓ M)).Normal := by
  have hle : S17.oUpperTwo (Opp 2 (Dsub ⊓ M)) ≤ Dsub ⊓ M :=
    (S17.oUpperTwo_le _).trans (close16_opp_le 2 _)
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 fun g hg => ?_⟩
  rw [S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
  exact CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure _
    (close16_mem_normalizer_opp 2 (Subgroup.le_normalizer hg))

theorem dynkin_J_le_and_normal {D : Data G} {Dsub : Subgroup G} {d : ℕ}
    {K J : Fin d → Subgroup G} (hfam : IsDynkinComponentFamily D Dsub d K J) (i : Fin d) :
    J i ≤ Dsub ⊓ D.M ∧ ((J i).subgroupOf (Dsub ⊓ D.M)).Normal := by
  have hK := hfam.1 i
  have hJ : J i = S17.oUpperTwo (K i) := hfam.2.2.2.2 i
  have hle : J i ≤ Dsub ⊓ D.M := hJ ▸ (S17.oUpperTwo_le _).trans hK.2.1
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_⟩
  rw [hJ, S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hK.2.1).1 hK.2.2.1).trans
    (CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure _)

theorem bar2_three_elts_comm {D : Data G} {A : Subgroup G} (h13 : Concl19_13 D A)
    (h3 : 3 ∈ piSet A) (Dsub : Subgroup G) :
    ∀ P : Subgroup (Bar2 Dsub), IsPGroup 3 P → ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP x hx y hy hx3 hy3
  set π : ↥Dsub →* Bar2 Dsub := QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub) with hπ
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (P.comap π)
  have hRmap : CFSG.ABGLocalTools.IsSylowOf 3 (R.map π) P := by
    have h1 := isSylowOf_map_mk' (N := CFSG.pCore 2 ↥Dsub) hR
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h1
  obtain ⟨hRle, -, hRidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hRmap
  have hPle : P ≤ R.map π := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : (R.map π).relIndex P ∣ 3 ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      exact hRidx (hj ▸ dvd_pow_self 3 hj0)
    rw [hj0, pow_zero] at hj
    exact Subgroup.relIndex_eq_one.mp hj
  obtain ⟨hRP, hR3, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hR
  have hdisj : Disjoint R (CFSG.pCore 2 ↥Dsub) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) R _ hR3 CFSG.pCore_isPGroup
  have hlift : ∀ z ∈ P, z ^ 3 = 1 → ∃ z' ∈ R, π z' = z ∧ z' ^ 3 = 1 := by
    intro z hz hz3
    obtain ⟨z', hz'R, hz'⟩ := Subgroup.mem_map.mp (hPle hz)
    refine ⟨z', hz'R, hz', ?_⟩
    have hker : z' ^ 3 ∈ CFSG.pCore 2 ↥Dsub := by
      rw [← QuotientGroup.eq_one_iff]
      change π (z' ^ 3) = 1
      rw [map_pow, hz', hz3]
    have hmem : z' ^ 3 ∈ R ⊓ CFSG.pCore 2 ↥Dsub := ⟨R.pow_mem hz'R 3, hker⟩
    rw [disjoint_iff.mp hdisj] at hmem
    exact (Subgroup.mem_bot).mp hmem
  obtain ⟨x', hx'R, rfl, hx'3⟩ := hlift x hx hx3
  obtain ⟨y', hy'R, rfl, hy'3⟩ := hlift y hy hy3
  have hRG : IsPGroup 3 (R.map Dsub.subtype) := hR3.map _
  have hcomm := omegaOne_comm_of_concl19_13 h13 h3 hRG
  have hxo : (x' : G) ∈ CFSG.LocalAnalysis.UniquenessCase.UCK.omegaOne 3 (R.map Dsub.subtype) :=
    Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem _ hx'R, by
      rw [← Subgroup.coe_pow, hx'3, Subgroup.coe_one]⟩
  have hyo : (y' : G) ∈ CFSG.LocalAnalysis.UniquenessCase.UCK.omegaOne 3 (R.map Dsub.subtype) :=
    Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem _ hy'R, by
      rw [← Subgroup.coe_pow, hy'3, Subgroup.coe_one]⟩
  have hxy : x' * y' = y' * x' := by
    apply Subtype.ext
    have := congrArg Subtype.val (hcomm.is_comm.comm ⟨_, hxo⟩ ⟨_, hyo⟩)
    simpa using this
  rw [← map_mul, ← map_mul, hxy]

theorem le_M_and_normalizer_le_M {D : Data G} {A E Q : Subgroup G}
    (h123 : Concl19_12 D A 3) (hEA : E ≤ A) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hQ : IsPGroup 3 Q) (hEQ : E ≤ Q) : Q ≤ D.M ∧ normalizer (Q : Set G) ≤ D.M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    h123 E hEA hEel (by rw [hEcard]; norm_num)
  have hQM : Q ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hE hEQ hQ
  exact ⟨hQM, CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
    ⟨hQM, fun g hg => hE.2 g (hEQ.trans hg)⟩⟩

theorem exists_sylow_normalizer_le_barOfInter (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : Concl19_17 A Dsub) (h123 : Concl19_12 D A 3) (h3 : 3 ∈ piSet A)
    (hinn : ∀ τ : MulAut (Bar2 Dsub), τ ^ 3 = 1 →
      τ ∈ (MulAut.conj : Bar2 Dsub →* MulAut (Bar2 Dsub)).range)
    (hZ : center (Bar2 Dsub) = ⊥) :
    ∃ S₃ : Subgroup (Bar2 Dsub), CFSG.ABGLocalTools.IsSylowOf 3 S₃ ⊤ ∧
      normalizer (S₃ : Set (Bar2 Dsub)) ≤ barOfInter D.M Dsub := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm_of_le : ∀ {K₀ : Subgroup G} {g : G},
      K₀.map (MulAut.conj g).toMonoidHom ≤ K₀ → g ∈ normalizer (K₀ : Set G) := by
    intro K₀ g hle
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    exists_isElemAbelian_card_prime_sq_of_isZModSq h.ctx.hAcard Nat.prime_three h3.2
  have hEN : E ≤ normalizer (Dsub : Set G) := hEA.trans h17
  set W : Subgroup G := Dsub ⊔ E with hW
  have hWN : W ≤ normalizer (Dsub : Set G) := sup_le Subgroup.le_normalizer hEN
  have hDW : Dsub ≤ W := le_sup_left
  set C : Subgroup G := F08.CentOverO2 W Dsub with hC
  set O : Subgroup G := pCoreOf 2 Dsub with hO
  have hOD : O ≤ Dsub := CFSG.LieType.BorelTits.pCoreOf_le 2 Dsub
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Dsub
  have hWO : W ≤ normalizer (O : Set G) :=
    hWN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Dsub)
  set π : ↥Dsub →* Bar2 Dsub := QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub) with hπ
  have hπO : ∀ z : ↥Dsub, π z = 1 ↔ (z : G) ∈ O := by
    intro z
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← CFSG.mem_openPCoreOf_iff]
  have hWC : W ≤ normalizer (C : Set G) := by
    intro w hw
    refine hnorm_of_le ?_
    rintro y ⟨c, hc, rfl⟩
    obtain ⟨hcW, hcc⟩ := mem_centOverO2_iff.mp hc
    refine mem_centOverO2_iff.mpr ⟨?_, fun l hl => ?_⟩
    · change w * c * w⁻¹ ∈ W
      exact W.mul_mem (W.mul_mem hw hcW) (W.inv_mem hw)
    · change w * c * w⁻¹ * l * (w * c * w⁻¹)⁻¹ * l⁻¹ ∈ O
      have hl' : w⁻¹ * l * w⁻¹⁻¹ ∈ Dsub :=
        (Subgroup.mem_normalizer_iff.mp (hWN (W.inv_mem hw)) l).mp hl
      have h1 := hcc _ hl'
      have h2 := (Subgroup.mem_normalizer_iff.mp (hWO hw) _).mp h1
      have heq : w * (c * (w⁻¹ * l * w⁻¹⁻¹) * c⁻¹ * (w⁻¹ * l * w⁻¹⁻¹)⁻¹) * w⁻¹ =
          w * c * w⁻¹ * l * (w * c * w⁻¹)⁻¹ * l⁻¹ := by group
      rw [← heq]
      exact h2
  have hEDC : E ≤ Dsub ⊔ C := by
    intro e he
    have heW : e ∈ W := Subgroup.mem_sup_right he
    have hinner := hinn ((rhoL Dsub).comp (Subgroup.inclusion hWN) ⟨e, heW⟩) (by
      rw [← map_pow]
      have h1 : (⟨e, heW⟩ : ↥W) ^ 3 = 1 := Subtype.ext (by simpa using hEel.2 e he)
      rw [h1, map_one])
    exact mem_sup_centOverO2_of_mem_inner hDW hWN hinner
  have hWDC : W ≤ Dsub ⊔ C := sup_le le_sup_left hEDC
  have hDC : Dsub ⊓ C ≤ O := by
    intro d hd
    obtain ⟨-, hdc⟩ := mem_centOverO2_iff.mp hd.2
    have hcen : π ⟨d, hd.1⟩ ∈ center (Bar2 Dsub) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Dsub) z
      have hmem := hdc l l.2
      have h1 : π ⁅(⟨d, hd.1⟩ : ↥Dsub), l⁆ = 1 := by
        rw [hπO]
        simpa [commutatorElement_def] using hmem
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [hZ, Subgroup.mem_bot, hπO] at hcen
    exact hcen
  have hcop : Nat.Coprime 3 (Nat.card (Dsub ⊓ C : Subgroup G)) := by
    obtain ⟨k, hk⟩ := (hO2.to_le hDC).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by decide)
  obtain ⟨Q, hQsyl, hEQ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge
    (p := 3) (le_sup_right : E ≤ W) (CFSG.Open.IsElemAbelian.isPGroup hEel)
  obtain ⟨hQW, hQ3, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hQsyl
  obtain ⟨hQM, hNQM⟩ :=
    le_M_and_normalizer_le_M h123 hEA hEel (by rw [hEcard]; norm_num) hQ3 hEQ
  have hQD : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ Dsub) Dsub :=
    hQsyl.inf_of_le_normalizer hDW hWN
  have hsplit : (Q ⊓ Dsub) ⊔ (Q ⊓ C) = Q :=
    CFSG.GroupTheory.sup_inf_eq_of_isSylowOf_inf hQ3 (hQW.trans hWDC) (hQW.trans hWN)
      (hQW.trans hWC) (hDW.trans hWC) hcop hQD
  have hQnorm : Q ≤ normalizer ((Q ⊓ Dsub : Subgroup G) : Set G) := by
    intro g hg
    refine hnorm_of_le ?_
    rintro y ⟨z, hz, rfl⟩
    change g * z * g⁻¹ ∈ Q ⊓ Dsub
    exact ⟨Q.mul_mem (Q.mul_mem hg hz.1) (Q.inv_mem hg),
      (Subgroup.mem_normalizer_iff.mp (hWN (hQW hg)) z).mp hz.2⟩
  set S₀ : Subgroup ↥Dsub := (Q ⊓ Dsub).subgroupOf Dsub with hS₀
  have hS₀syl : CFSG.ABGLocalTools.IsSylowOf 3 S₀ ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Dsub, hS₀,
      Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr inf_le_right]
    exact hQD
  refine ⟨S₀.map π, ?_, ?_⟩
  · have h1 := isSylowOf_map_mk' (N := CFSG.pCore 2 ↥Dsub) hS₀syl
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  · intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Dsub) xb
    set K : Subgroup G := Q ⊔ O with hK
    have hxK : (x : G) ∈ normalizer (K : Set G) := by
      refine hnorm_of_le ?_
      rw [hK, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro y ⟨q, hq, rfl⟩
        change (x : G) * q * (x : G)⁻¹ ∈ Q ⊔ O
        have hq' : q ∈ (((Q ⊓ Dsub) ⊔ (Q ⊓ C) : Subgroup G) : Set G) := by
          rw [hsplit]
          exact hq
        rw [Subgroup.coe_mul_of_right_le_normalizer_left (Q ⊓ Dsub) (Q ⊓ C)
          (inf_le_left.trans hQnorm)] at hq'
        obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hq'
        have hxa : (x : G) * a * (x : G)⁻¹ ∈ Q ⊔ O := by
          have haD : a ∈ Dsub := ha.2
          set a' : ↥Dsub := ⟨a, haD⟩ with ha'
          have hmemS : π a' ∈ S₀.map π :=
            Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
          have hconj : π (x * a' * x⁻¹) ∈ S₀.map π := by
            rw [map_mul, map_mul, map_inv]
            exact (Subgroup.mem_normalizer_iff.mp hxb (π a')).mp hmemS
          obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hconj
          have hker : π (b⁻¹ * (x * a' * x⁻¹)) = 1 := by
            rw [map_mul, map_inv, hbeq, inv_mul_cancel]
          have hO' := (hπO _).mp hker
          have heq : (x : G) * a * (x : G)⁻¹ =
              (b : G) * ((b⁻¹ * (x * a' * x⁻¹) : ↥Dsub) : G) := by
            simp only [ha', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
            group
          rw [heq]
          exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hb).1 hO'
        have hxc : (x : G) * c * (x : G)⁻¹ ∈ Q ⊔ O := by
          obtain ⟨-, hcc⟩ := mem_centOverO2_iff.mp (C.inv_mem hc.2)
          have h1 := hcc (x : G) x.2
          have heq : (x : G) * c * (x : G)⁻¹ =
              c * (c⁻¹ * (x : G) * c⁻¹⁻¹ * (x : G)⁻¹) := by group
          rw [heq]
          exact Subgroup.mul_mem_sup hc.1 h1
        have heq2 : (x : G) * (a * c) * (x : G)⁻¹ =
            ((x : G) * a * (x : G)⁻¹) * ((x : G) * c * (x : G)⁻¹) := by group
        rw [heq2]
        exact (Q ⊔ O).mul_mem hxa hxc
      · rintro y ⟨o, ho, rfl⟩
        change (x : G) * o * (x : G)⁻¹ ∈ Q ⊔ O
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hWO (hDW x.2)) o).mp ho)
    have hxM : (x : G) ∈ D.M := by
      have hfr := uc22p22t_frattini_sup (q := 3) (H := normalizer (K : Set G)) (K := K) (S := Q)
        Subgroup.le_normalizer le_rfl (hQsyl.of_le le_sup_left (sup_le hQW (hOD.trans hDW)))
      have hK_M : K ≤ D.M := sup_le hQM h.hO2
      exact (sup_le hK_M (inf_le_right.trans hNQM)) (hfr hxK)
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨x.2, hxM⟩)

theorem exists_normal_two_three {D : Data G} {Dsub J : Subgroup G}
    (hJle : J ≤ Dsub ⊓ D.M) (hJn : (J.subgroupOf (Dsub ⊓ D.M)).Normal)
    (hJ : Nonempty (Bar2 J ≃* Multiplicative (ZMod 3)) ∨
      Nonempty (Bar2 J ≃* Multiplicative (ZMod 3 × ZMod 3))) :
    ∃ Nn : Subgroup (Bar2 Dsub), Nn ≤ barOfInter D.M Dsub ∧
      (Nn.subgroupOf (barOfInter D.M Dsub)).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥Dsub →* Bar2 Dsub := QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub) with hπ
  have hJD : J ≤ Dsub := hJle.trans inf_le_left
  have hNG : Dsub ⊓ D.M ≤ normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mp hJn
  have hsub : J.subgroupOf Dsub ≤ (Dsub ⊓ D.M).subgroupOf Dsub := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hJle (Subgroup.mem_subgroupOf.mp hx))
  have hle : (J.subgroupOf Dsub).map π ≤ barOfInter D.M Dsub := Subgroup.map_mono hsub
  have hcardJ : Nat.card (Bar2 J) ∣ 9 := by
    rcases hJ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp
  refine ⟨(J.subgroupOf Dsub).map π, hle, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    have hnorm : (Dsub ⊓ D.M).subgroupOf Dsub ≤
        normalizer ((J.subgroupOf Dsub : Subgroup ↥Dsub) : Set ↥Dsub) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hyN : (y : G) ∈ normalizer (J : Set G) := hNG (Subgroup.mem_subgroupOf.mp hy)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hyN z
    exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map π)
  ·
    obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 J) 3
      (by
        rcases hJ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
          simp
        · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
          simp)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    set w : ↥Dsub := ⟨(x : G), hJD x.2⟩ with hw
    have hwN : π w ∈ (J.subgroupOf Dsub).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr x.2)
    have h3x : 3 ∣ orderOf x := by
      rw [← hxb]
      exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) x
    have hxw : orderOf x = orderOf w := by
      rw [← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe w]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (w ^ orderOf (π w)) ^ 2 ^ k = 1 := by
      have hmem : w ^ orderOf (π w) ∈ CFSG.pCore 2 ↥Dsub := by
        rw [← QuotientGroup.eq_one_iff]
        change π (w ^ orderOf (π w)) = 1
        rw [map_pow, pow_orderOf_eq_one]
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Dsub)) ⟨_, hmem⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hdvd : orderOf w ∣ orderOf (π w) * 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hk
    have h3 : 3 ∣ orderOf (π w) := by
      have h3' : 3 ∣ orderOf (π w) * 2 ^ k := (hxw ▸ h3x).trans hdvd
      exact (Nat.Coprime.pow_right k (by decide : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3'
    refine h3.trans ?_
    rw [← Subgroup.orderOf_mk (π w) hwN]
    exact orderOf_dvd_natCard _
  ·
    intro q hq hqN
    have hdvd1 : Nat.card ((J.subgroupOf Dsub).map π) ∣ Nat.card J := by
      refine (Subgroup.card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJD).toEquiv]
    have hcard : Nat.card J = Nat.card (Bar2 J) * Nat.card (CFSG.pCore 2 ↥J) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).exists_card_eq
    have hq' : q ∣ 9 * 2 ^ k := by
      refine (hqN.trans hdvd1).trans ?_
      rw [hcard, hk]
      exact Nat.mul_dvd_mul_right hcardJ _
    rcases (Nat.Prime.dvd_mul hq).mp hq' with h9 | h2
    · right
      have h3 : q ∣ 3 := hq.dvd_of_dvd_pow (show q ∣ 3 ^ 2 by simpa using h9)
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)

theorem three_dvd_card_bar2_of_iso {J : Subgroup G}
    (hJ : Nonempty (Bar2 J ≃* Multiplicative (ZMod 3)) ∨
      Nonempty (Bar2 J ≃* Multiplicative (ZMod 3 × ZMod 3))) : 3 ∣ Nat.card (Bar2 J) := by
  rcases hJ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp

theorem bar2_isL3_of_subset_mul (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : Concl19_17 A Dsub) (h123 : 3 ∈ piSet A → Concl19_12 D A 3)
    (h13 : Concl19_13 D A) (hforce : K_19_20_force)
    (hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter D.M Dsub) ∨
      (IsLieTypeOver2 (BarInf Dsub) ∧ List19_16_5 (BarInf Dsub) ∧
        IsNontrivialParabolic (Bar2 Dsub) (barOfInter D.M Dsub)))
    {J : Subgroup G} (hJle : J ≤ Dsub ⊓ D.M) (hJn : (J.subgroupOf (Dsub ⊓ D.M)).Normal)
    (hJA : (J : Set G) ⊆ (pCoreOf 2 J : Set G) * (A : Set G))
    (hJ : Nonempty (Bar2 J ≃* Multiplicative (ZMod 3)) ∨
      Nonempty (Bar2 J ≃* Multiplicative (ZMod 3 × ZMod 3))) :
    LieModel (Bar2 Dsub) .PSL 3 2 1 := by
  have h3 : 3 ∈ piSet A :=
    three_mem_piSet_of_subset_mul hJA (three_dvd_card_bar2_of_iso hJ) (odd_card_of_ctx19_10 h.ctx)
  have hq : CFSG.Open.IsQuasisimple (Bar2 Dsub) := h.hD.1.2.2
  exact hforce (Bar2 Dsub) (BarInf Dsub) (barOfInter D.M Dsub) hq
    (TwelveThirteen.pCore_bar2_eq_bot Dsub) (uc22p21k_barInf_equiv hq) hshape
    (bar2_three_elts_comm h13 h3 Dsub) (exists_sylow_normalizer_le_barOfInter D h h17 (h123 h3) h3)
    (exists_normal_two_three hJle hJn hJ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
