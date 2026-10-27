module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof159Odd
public import CFSG.RankThree.PartTwo.KFacts.KP4
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof159W
import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofL325Image
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTrans
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofLA7
import CFSG.RankThree.PartTwo.Sec15.Item153
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159Y0
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U43Action
import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofEven
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofM22
import CFSG.RankThree.PartTwo.Sec19.Item1912
import CFSG.RankThree.PartTwo.Sec21.Item22Statements
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10012
import Certificates.Certificate10013
import Certificates.Certificate10014
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16040
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def sigTwo {X : Type} [Group X] [Finite X] (a : X) : Subgroup X :=
  inSubgroup (CFSG.pCore 2)
    (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X)))

@[expose] def KS159TorusPair : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    ((∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) ∧
        Sec4.IsoLThreePi X p e) ∨ Nonempty (X ≃* alternatingGroup (Fin 7))) →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      ∃ a ∈ D, ∃ b ∈ D, ¬ IsPGroup 2 ↥(sigTwo a ⊔ sigTwo b)

namespace Proof15Res3NT

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_commutator {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK ha)]

theorem isPGroup_sigTwo {X : Type} [Group X] [Finite X] (a : X) : IsPGroup 2 (sigTwo a) :=
  CFSG.pCore_isPGroup.map _

theorem centralizer_le_normalizer_sigTwo {X : Type} [Group X] [Finite X] (a : X) :
    Subgroup.centralizer ({a} : Set X) ≤ Subgroup.normalizer (sigTwo a : Set X) := by
  have h1 := Proof15Res3L325Image.le_normalizer_inSubgroup_theta
    (Subgroup.centralizer ({a} : Set X))
  exact h1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.pCore 2 ↥(inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X)))))

theorem map_sigTwo {X : Type} [Group X] [Finite X] (σ : MulAut X) (a : X) :
    (sigTwo a).map σ.toMonoidHom = sigTwo (σ a) := by
  unfold sigTwo
  rw [KFacts.KP4.map_pCore_two, KFacts.KP4.map_theta, KFacts.KP4.map_centralizer_singleton]

theorem theta_eq_bot
    (h135 : Item135) {A L : Subgroup G} {c : G}
    (ctx : Ctx159 G A c L) (hO : CFSG.Open.pCoreOf 2 L = ⊥) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  have hD := ctx.toSec13Data
  have hq := h135 G A c L hD ctx.hypS_or_hypT
  have hθ := Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult hq (by
    rcases ctx.types with h3 | h7 | h22
    · exact Or.inl h3
    · exact Or.inr (Or.inr (Or.inr (Or.inl h7)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h22))))
  rw [hθ]
  have hO' : (CFSG.pCore 2 ↥L).map L.subtype = ⊥ := by
    exact hO
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hO'

theorem exists_commutator_le_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ A ≤ Subgroup.normalizer (P : Set G) ∧ P ≠ ⊥ ∧ P ≤ L := by
  have h := ctx.toSec15R
  have hD := h.toSec13Data
  obtain ⟨Q, D, hQ2, hAQ, hDh, -, hcD, hQD⟩ := Proof15Res3W.exists_hyperplane_mem_of_ctx159 ctx
  have hcommA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hD.isElemAbelian.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAD : A ≤ Subgroup.centralizer (D : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hcommA d (hDh.1 hd) a ha
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (ctx.card_inf ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hCL : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcD)).trans
      ((centralizer_singleton_le_normalizer_zpowers c).trans
        (Sec16.normalizer_zpowers_le_normalizer_L h h3L))
  refine ⟨⁅Q ⊓ Subgroup.centralizer (D : Set G), A ⊓ L⁆, ?_, ?_, hQD, ?_⟩
  · refine hQ2.to_le ((Subgroup.commutator_le).mpr fun g₁ hg₁ g₂ hg₂ => ?_)
    rw [commutatorElement_def]
    have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAQ hg₂.1) g₁⁻¹).mp (Q.inv_mem hg₁.1)
    simpa [mul_assoc] using Q.mul_mem hg₁.1 h1
  · exact le_normalizer_commutator (Late.le_normalizer_inf hAQ (hAD.trans Subgroup.le_normalizer))
      (Late.le_normalizer_inf Subgroup.le_normalizer hD.le_normalizer)
  · refine (Subgroup.commutator_le).mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCL hg₁.2) g₂).mp hg₂.2) (L.inv_mem hg₂.2)

theorem false_of_even
    (h135 : Item135) (h138 : Item138N) {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L)
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) {f : ℕ} (hf : 1 ≤ f)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := ctx.toSec15R
  have hD := h.toSec13Data
  have hθ := theta_eq_bot h135 ctx hO
  have h9 := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC hf hiso ctx.prod
  obtain ⟨P, hP2, hAP, hP1, hPL⟩ := exists_commutator_le_of_ctx159 ctx
  have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hD.isElemAbelian.2 x hx.1⟩
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  apply hP1
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hBe (by rw [ctx.card_inf]; norm_num)
    (inf_le_left.trans hAP) hcop fun b hb hb1 => ?_
  rintro z ⟨hzP, hzb⟩
  rw [Subgroup.mem_bot]
  have hzL := hPL hzP
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  obtain ⟨k, hk⟩ := hP2 ⟨z, hzP⟩
  have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hinj : ∀ y : ↥L, π y = 1 → (y : G) = 1 := fun y hy => by
    have hy' : y ∈ aschbacherSolvableCore 3 ↥L := (QuotientGroup.eq_one_iff y).mp hy
    rw [hθ, Subgroup.mem_bot] at hy'
    rw [hy']
    rfl
  have hz1 : π ⟨z, hzL⟩ = 1 := by
    refine Proof1513Res3.eq_one_of_commute_of_pow_two_pow' hf hiso h9 (x := π ⟨b, hb.2⟩) ?_ ?_ ?_
      (k := k) ?_
    · rw [← map_pow]
      have : (⟨b, hb.2⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 b hb.1)
      rw [this, map_one]
    · intro h1
      exact hb1 (hinj _ h1)
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzb)
    · rw [← map_pow]
      have : (⟨z, hzL⟩ : ↥L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
  exact hinj _ hz1

theorem not_transOn_of_pair (h142 : Item142R) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h3L : 3 ∣ Nat.card L)
    (hθ2 : IsPGroup 2 ↥(aschbacherSolvableCore 3 ↥L))
    {U₁ U₂ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hU₁ : IsPGroup 2 U₁)
    (hU₂ : IsPGroup 2 U₂)
    (hAU₁ : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.normalizer (U₁ : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hAU₂ : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.normalizer (U₂ : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hinv : ∀ x ∈ xA A, ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
      U₁.map (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x, hx⟩)).toMonoidHom ≤ U₁)
    (hnot : ¬ IsPGroup 2 ↥(U₁ ⊔ U₂)) :
    ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  intro htr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hpre : ∀ U : Subgroup (↥L ⧸ θ), IsPGroup 2 U →
      (A.subgroupOf L).map π ≤ Subgroup.normalizer (U : Set (↥L ⧸ θ)) →
      (U.comap π).map L.subtype ∈ scriptQPi A (lB A) H (piOf 2) := by
    intro U hU hAU
    have hR2 : IsPGroup 2 ((U.comap π).map L.subtype) := by
      refine (hU.comap_of_ker_isPGroup π ?_).map _
      rw [hπ, QuotientGroup.ker_mk']
      exact hθ2
    have hAR := Proof1515Res.le_normalizer_map_comap_of h hAeq hAU
    have hRc : (U.comap π).map L.subtype ≤ Subgroup.centralizer ({c} : Set G) :=
      (Subgroup.map_subtype_le _).trans hD.le_centralizer
    exact ⟨⟨Proof15Res3W.mem_scriptQ_of_le_centralizer h142 h hR2 hAR hRc,
      hRc.trans (centralizer_singleton_le_normalizer_zpowers c)⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hR2⟩
  set R₁ := (U₁.comap π).map L.subtype with hR₁def
  set R₂ := (U₂.comap π).map L.subtype with hR₂def
  obtain ⟨S₁, hRS₁, hS₁⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) H (piOf 2))) (hpre U₁ hU₁ hAU₁)
  obtain ⟨S₂, hRS₂, hS₂⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) H (piOf 2))) (hpre U₂ hU₂ hAU₂)
  obtain ⟨x, hx, hS₂eq⟩ := htr S₁ hS₁ S₂ hS₂
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3L hx.2
  have hR₁x : R₁.map (MulAut.conj x).toMonoidHom ≤ R₁ := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨L.normalizerMonoidHom ⟨x, hxL⟩ l, ?_, rfl⟩
    show π (L.normalizerMonoidHom ⟨x, hxL⟩ l) ∈ U₁
    apply hinv x hx.1 hxL
    exact ⟨π l, hl, (Sec4.thetaQuotMulAut_mk _ l).symm⟩
  have hR₁eq : R₁.map (MulAut.conj x).toMonoidHom = R₁ :=
    Subgroup.eq_of_le_of_card_ge hR₁x
      (by rw [Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
        (MulAut.conj x).injective])
  have hR₁S₂ : R₁ ≤ S₂ := by
    rw [hS₂eq, ← hR₁eq]
    exact Subgroup.map_mono hRS₁
  have hS₂2 : IsPGroup 2 S₂ := (isPiSubgroup_piOf_iff Nat.prime_two S₂).mp hS₂.prop.2
  have hR12 : IsPGroup 2 ((R₁ ⊔ R₂).subgroupOf L) :=
    (hS₂2.to_le (sup_le hR₁S₂ hRS₂)).comap_subtype
  have himg : ∀ U : Subgroup (↥L ⧸ θ), (((U.comap π).map L.subtype).subgroupOf L).map π = U := by
    intro U
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θ)]
  have hU12 : U₁ ⊔ U₂ ≤ ((R₁ ⊔ R₂).subgroupOf L).map π := by
    refine sup_le ?_ ?_
    · rw [← himg U₁]
      exact Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
    · rw [← himg U₂]
      exact Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy))
  exact hnot ((hR12.map π).to_le hU12)

theorem thetaQuotMulAut_fix {A L : Subgroup G} {x : G}
    (hxA : x ∈ Subgroup.centralizer (A : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    {y : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hy : y ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x, hxL⟩) y = y := by
  obtain ⟨a, ha, rfl⟩ := hy
  rw [QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  show x * (a : G) * x⁻¹ = a
  rw [(Subgroup.mem_centralizer_iff.mp hxA a (Subgroup.mem_subgroupOf.mp ha)).symm,
    mul_inv_cancel_right]

end Proof15Res3NT

open Proof15Res3NT

theorem step159Y0NotTrans_of
    (h135 : Item135) (h138 : Item138N) (h142 : Item142R) (hK : KS159TorusPair) :
    Step159Y0NotTrans := by
  intro G _ _ A c L ctx hO
  have h := ctx.toSec15R
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hθ := theta_eq_bot h135 ctx hO
  have hθ2 : IsPGroup 2 θ := by
    rw [hθdef, hθ]
    exact IsPGroup.of_bot
  obtain ⟨-, hAeq⟩ := Proof15Res3W.eq_sup_of_ctx159 ctx
  obtain ⟨hAbE, hAb9⟩ := Proof1515Res.isElemAbelian_card_aBar_of h ctx.card_inf
  set Ab := (A.subgroupOf L).map π with hAb
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (ctx.card_inf ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hxC : ∀ x ∈ xA A, x ∈ Subgroup.centralizer (A : Set G) := fun x hx => pPrimeCoreOf_le 3 _ hx
  have htorus : ∀ a ∈ Ab, ∀ b ∈ Ab, ¬ IsPGroup 2 ↥(sigTwo a ⊔ sigTwo b) →
      ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    intro a ha b hb hnot
    have hAbC : ∀ y ∈ Ab, Ab ≤ Subgroup.centralizer ({y} : Set (↥L ⧸ θ)) := fun y hy z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAbE.1.is_comm.comm ⟨z, hz⟩ ⟨y, hy⟩))
    refine not_transOn_of_pair h142 h hAeq h3L hθ2 (isPGroup_sigTwo a) (isPGroup_sigTwo b)
      ((hAbC a ha).trans (centralizer_le_normalizer_sigTwo a))
      ((hAbC b hb).trans (centralizer_le_normalizer_sigTwo b)) (fun x hx hxL => ?_) hnot
    rw [map_sigTwo, thetaQuotMulAut_fix (hxC x hx) hxL ha]
  rcases ctx.types with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | hM
  · by_cases hp2 : p = 2
    · subst hp2
      exact (false_of_even h135 h138 ctx hO he hiso).elim
    · have h9 := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he hiso ctx.prod
      have hperf : Group.IsPerfect (↥L ⧸ θ) :=
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
      obtain ⟨a, ha, b, hb, hnot⟩ :=
        hK _ hperf (Or.inl ⟨p, e, hp, hp2, he, h9, hiso⟩) Ab hAbE hAb9
      exact htorus a ha b hb hnot
  · have hperf : Group.IsPerfect (↥L ⧸ θ) :=
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
    obtain ⟨a, ha, b, hb, hnot⟩ := hK _ hperf (Or.inr ⟨φ⟩) Ab hAbE hAb9
    exact htorus a ha b hb hnot
  ·
    obtain ⟨a, b, -, -, -, hne, hpair⟩ := KFacts.KP4.m22_maxInvariant_eq_pair hM hAb9
    set R₀ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set (↥L ⧸ θ))) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set (↥L ⧸ θ))) with hR₀
    set R₁ := inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({a * b} : Set (↥L ⧸ θ))) ⊔
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({a * b ^ 2} : Set (↥L ⧸ θ))) with hR₁
    have hR₀m : R₀ ∈ maxInvariantPiSubgroups ⊤ Ab (piCompl 3) := by
      rw [hpair]
      exact Set.mem_insert _ _
    have hR₁m : R₁ ∈ maxInvariantPiSubgroups ⊤ Ab (piCompl 3) := by
      rw [hpair]
      exact Set.mem_insert_of_mem _ rfl
    have hR₀2 := KFacts.KP4.m22_isPGroup_of_mem_invariant hM hAb9 hR₀m.prop
    have hR₁2 := KFacts.KP4.m22_isPGroup_of_mem_invariant hM hAb9 hR₁m.prop
    refine not_transOn_of_pair h142 h hAeq h3L hθ2 hR₀2 hR₁2 hR₀m.prop.2.2 hR₁m.prop.2.2
      (fun x hx hxL => ?_) fun h2 => hne ?_
    · obtain ⟨e', he', hσ⟩ := KFacts.KP4.m22_aut_fix_eq_conj hM hAb9
        (fun y hy => thetaQuotMulAut_fix (hxC x hx) hxL hy)
      rw [hσ]
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hR₀m.prop.2.2 he')).le
    ·
      have hJ : R₀ ⊔ R₁ ∈ invariantPiSubgroups ⊤ Ab (piCompl 3) := by
        refine ⟨le_top, ?_, le_normalizer_sup hR₀m.prop.2.2 hR₁m.prop.2.2⟩
        rw [isPiSubgroup_piCompl_iff Nat.prime_three]
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
        rw [hn]
        intro h3
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
      exact (hR₀m.eq_of_le hJ le_sup_left).trans (hR₁m.eq_of_le hJ le_sup_right).symm

end CFSG.RankThree.PartTwo.Sec15
