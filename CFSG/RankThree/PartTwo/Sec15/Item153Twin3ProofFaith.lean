module

public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofFaith
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofOmega
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156QThetaMeet (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} →
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ (f : G) (Lf : Subgroup G), Subgroup.zpowers f ∈ omegaA A →
        Subgroup.zpowers f ≤ Subgroup.closure {c₀, d} →
        Subgroup.zpowers f ≠ Subgroup.zpowers d → Lf ∈ lA A f →
        Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2) →
          CFSG.Open.pCoreOf 2 M ⊓ inSubgroup (aschbacherSolvableCore 3) Lf = ⊥

@[expose] noncomputable def Step156QThetaMeetR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156QThetaMeet A (lB A)

namespace Proof153Twin3

theorem inf_centralizer_le_thetaQuotCentralizer
    {A : Subgroup G} {f : G} {Lf : Subgroup G}
    (hf : Sec14Std G A f Lf)
    (hJf : Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h142 : Item142 A (lB A) f Lf hf.toSec13Data.isElemAbelian.1 hf.toSec13Data.mem_A)
    {X₁ : Subgroup G} (hX4 : X₁ ∈ scriptY4 A (lB A))
    (h6 : Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)))
    (hfsc : f ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁)) {M : Subgroup G}
    (hXM : X₁ ≤ M) :
    CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) ≤
      Sec4.thetaQuotCentralizer Lf := by
  obtain ⟨D', z, hD'XL, hz1, hzc, hD'img⟩ :=
    exists_cover_eq_centralizer_of_six hf hJf h142 hX4 h6 hfsc
  have hCN : Subgroup.centralizer ({f} : Set G) ≤ Subgroup.normalizer (Lf : Set G) :=
    centralizer_le_normalizer_of_j2 hf hJf
  set U := CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) with hU
  have hUN : U ≤ Subgroup.normalizer (Lf : Set G) := inf_le_right.trans hCN
  set φ : ↥(Subgroup.normalizer (Lf : Set G)) →* MulAut (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) :=
    (Sec4.thetaQuotMulAut ↥Lf).comp Lf.normalizerMonoidHom with hφ
  set R := (U.subgroupOf (Subgroup.normalizer (Lf : Set G))).map φ with hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_left
  have hR2 : IsPGroup 2 R :=
    (hU2.comap_of_injective (Subgroup.normalizer (Lf : Set G)).subtype
      (Subgroup.normalizer (Lf : Set G)).subtype_injective).map φ
  have hMQ : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hRN : (Subgroup.centralizer ({z} : Set (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf))).map
      (MulAut.conj : (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf) →* MulAut _) ≤
      Subgroup.normalizer (R : Set (MulAut (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf))) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun a ha r hr => ?_
    obtain ⟨g, hg, rfl⟩ := ha
    rw [← hD'img] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    obtain ⟨q, hq, rfl⟩ := hr
    have hyL : (y : G) ∈ Lf := y.2
    have hyD : (y : G) ∈ D' := Subgroup.mem_subgroupOf.mp hy
    have hyX : (y : G) ∈ X₁ := (hD'XL hyD).1
    have hyN : (y : G) ∈ Subgroup.normalizer (Lf : Set G) := Subgroup.le_normalizer hyL
    have hφy : φ ⟨y, hyN⟩ = MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lf) y) :=
      thetaQuotMulAut_eq_conj hyL
    have hqU : (q : G) ∈ U := Subgroup.mem_subgroupOf.mp hq
    have hyqU : (y : G) * q * (y : G)⁻¹ ∈ U := by
      have hyC : (y : G) ∈ Subgroup.centralizer ({f} : Set G) :=
        (Sec6.le_centralizer_of_mem_thetaComponentsAt hf.toSec13Data.mem_lA.1) hyL
      refine Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hMQ (hXM hyX)) _).mp (Subgroup.mem_inf.mp hqU).1, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyC (Subgroup.mem_inf.mp hqU).2)
        (Subgroup.inv_mem _ hyC)
    refine ⟨⟨(y : G) * q * (y : G)⁻¹, hUN hyqU⟩, Subgroup.mem_subgroupOf.mpr hyqU, ?_⟩
    have he : (⟨(y : G) * q * (y : G)⁻¹, hUN hyqU⟩ : ↥(Subgroup.normalizer (Lf : Set G))) =
        ⟨y, hyN⟩ * q * ⟨y, hyN⟩⁻¹ := Subtype.ext rfl
    rw [he, map_mul, map_mul, map_inv, hφy]
  have hRbot : R = ⊥ := ks156J2Norm_holds _ hJf z hz1 hzc R hR2 hRN
  intro u hu
  have h1 : φ ⟨u, hUN hu⟩ ∈ R := ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [hRbot, Subgroup.mem_bot] at h1
  exact ⟨⟨u, hUN hu⟩, MonoidHom.mem_ker.mpr h1, rfl⟩

theorem false_of_centralizer_le (hchar : CFSG.Assembly.IsCharTwoType G) {A M : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hM : IsMaximalTwoLocal M) (hAM : A ≤ M) {c d : G}
    (hc : c ∈ A) (hc3 : Nat.card (Subgroup.zpowers c) = 3) (hd : d ∈ A) (hd1 : d ≠ 1)
    (hdc : d ∉ Subgroup.zpowers c)
    (hC : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} → Nat.card F = 3 →
      F ≠ Subgroup.zpowers d → CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) ≤
        Subgroup.centralizer (Subgroup.zpowers d : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({c, d} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hc
    · exact hd
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => hA.2 x (hEA hx)
  have hEab : CFSG.Open.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (hA.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩))⟩⟩, hE3⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hcE : Subgroup.zpowers c ≤ E :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c _))
  have hdE : d ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have hk2 : 2 ≤ k := by
    have hdvd : Nat.card (Subgroup.zpowers c) ∣ Nat.card E := Subgroup.card_dvd_of_le hcE
    rw [hc3, hk] at hdvd
    have hk1 : k ≠ 0 := by
      rintro rfl
      norm_num at hdvd
    by_contra hk2
    have hk1' : k = 1 := by omega
    have hcard : Nat.card E ≤ Nat.card (Subgroup.zpowers c) := by rw [hk, hc3, hk1', pow_one]
    exact hdc ((Subgroup.eq_of_le_of_card_ge hcE hcard).symm ▸ hdE)
  have hE9 : 3 ^ (1 + 1) ≤ Nat.card E := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    (hEA.trans hAM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
  have hcop : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Q hEab hE9 hEQ hcop
  have hQd : Q ≤ Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    by_cases hFd : F = Subgroup.zpowers d
    · rw [hFd]
      exact inf_le_right
    · exact hC F hF.1 (by rw [hF.2, pow_one]) hFd
  have hdM : d ∈ M := hAM hd
  have hMc : IsCharacteristicP 2 ↥M := CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar hM.1
  have hdC : (⟨d, hdM⟩ : ↥M) ∈
      Subgroup.centralizer ((CFSG.pCore 2 ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : (y : G) ∈ Q := by
      rw [hQ, CFSG.Open.pCoreOf]
      exact ⟨y, hy, rfl⟩
    have hyd := Subgroup.mem_centralizer_iff.mp (hQd hyQ) d (Subgroup.mem_zpowers d)
    exact Subtype.ext hyd.symm
  have hdO : (⟨d, hdM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := hMc hdC
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥M)) ⟨_, hdO⟩
  have hdj : d ^ 2 ^ j = 1 := by
    have := congrArg (fun z : CFSG.pCore 2 ↥M => ((z : ↥M) : G)) hj
    simpa using this
  have hd3 : d ^ 3 = 1 := hA.2 d hd
  apply hd1
  have hco : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
  have h1 := (pow_gcd_eq_one (a := d)).mpr ⟨hdj, hd3⟩
  rwa [hco.gcd_eq_one, pow_one] at h1

theorem false_of_meet
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hMF : Step156QThetaMeet A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (htype : IsType156 Y) {c₀ : G} {L₀ : Subgroup G} {d : G}
    {X₁ : Subgroup G} (D : Data156 A (lB A) Y c₀ L₀ d X₁) (hΩ : omegaA A ≠ {Subgroup.zpowers c₀})
    (h6 : Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6))) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) : False := by
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp D.omega
  have hdc : d ∉ Subgroup.zpowers c₀ := not_mem_zpowers_of_data156 h₀ D
  have hAM : A ≤ M := fun a ha => hM.2 (Subgroup.mem_sup_right ha)
  have hXM : X₁ ≤ M := fun x hx => hM.2 (Subgroup.mem_sup_left (D.le_x hx))
  refine false_of_centralizer_le h₀.toTheoremFourHyp.charTwoType h₀.toSec13Data.isElemAbelian
    hM.1 hAM hcA hc3 D.mem_d D.ne_d hdc fun F hF hF3 hFd => ?_
  have hFΩ : F ∈ omegaA A := step156CQOmega_of h134 h48 h Y hY htype c₀ L₀ d X₁ D hΩ F hF hF3 hFd
  obtain ⟨-, -, f, hFf, -⟩ := mem_omegaA_iff.mp hFΩ
  have hfΩ : Subgroup.zpowers f ∈ omegaA A := hFf ▸ hFΩ
  obtain ⟨Lf, hLf, hJf⟩ := allPointsHJ_of_j2 h134 h48 h₀ D.hj f hfΩ
  have hf : Sec14Std G A f Lf := { h with zpowers_mem_omegaA := hfΩ, mem_lA := hLf }
  have hfE : f ∈ Subgroup.closure ({c₀, d} : Set G) := hF (hFf ▸ Subgroup.mem_zpowers f)
  have hfsc : f ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact hfE
  have hUC := inf_centralizer_le_thetaQuotCentralizer hf hJf (h142 G A f Lf hf) D.mem_x.1 h6
    hfsc hXM
  obtain ⟨d', hd'A, -, hd'L, hcent⟩ :=
    exists_d_of_mem_sectionCentralizer hf hJf (h142 G A f Lf hf) D.mem_x.1 D.type_x hfsc
  obtain ⟨hd'Lf, -⟩ := hd'L
  have hmeet := hMF Y hY htype c₀ L₀ d X₁ D hΩ h6 M hM f Lf hfΩ (hFf ▸ hF) (hFf ▸ hFd) hLf hJf
  have hdfd' : d ∈ Subgroup.closure ({f, d'} : Set G) := by
    have h1 : (Subgroup.closure ({c₀, d} : Set G) : Set G) =
        (Subgroup.closure ({f, d'} : Set G) : Set G) := D.cent.symm.trans hcent
    have h2 : d ∈ (Subgroup.closure ({c₀, d} : Set G) : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem c₀ rfl)
    rw [h1] at h2
    exact h2
  intro q hq
  obtain ⟨hqQ, hqF⟩ := Subgroup.mem_inf.mp hq
  have hqf : q ∈ Subgroup.centralizer ({f} : Set G) := by
    rw [← KFacts.KS14.centralizer_zpowers_eq f, ← hFf]
    exact hqF
  have hqθ := (Sec6.mem_thetaQuotCentralizer_iff.mp (hUC ⟨hqQ, hqf⟩)).2 d' hd'Lf
  have hd'N : d'⁻¹ ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hAM (A.inv_mem hd'A))
  have hqQ' : d'⁻¹ * (q * d' * q⁻¹) ∈ CFSG.Open.pCoreOf 2 M := by
    have h1 : d'⁻¹ * q * d'⁻¹⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp hd'N q).mp hqQ
    have e : d'⁻¹ * (q * d' * q⁻¹) = (d'⁻¹ * q * d'⁻¹⁻¹) * q⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hqQ)
  have h1 : d'⁻¹ * (q * d' * q⁻¹) = 1 := by
    have : d'⁻¹ * (q * d' * q⁻¹) ∈ CFSG.Open.pCoreOf 2 M ⊓
        inSubgroup (aschbacherSolvableCore 3) Lf := ⟨hqQ', hqθ⟩
    rwa [hmeet, Subgroup.mem_bot] at this
  have hqd' : q * d' = d' * q := by
    have h2 : q * d' * q⁻¹ = d' := by
      calc q * d' * q⁻¹ = d' * (d'⁻¹ * (q * d' * q⁻¹)) := by group
        _ = d' := by rw [h1, mul_one]
    calc q * d' = q * d' * q⁻¹ * q := by group
      _ = d' * q := by rw [h2]
  have hqE : Subgroup.closure ({f, d'} : Set G) ≤ Subgroup.centralizer ({q} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hqf x (Set.mem_singleton x))
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hqd'.symm
  rw [KFacts.KS14.centralizer_zpowers_eq d, Subgroup.mem_centralizer_iff]
  rintro y (rfl : y = d)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hqE hdfd'))

end Proof153Twin3

open Proof153Twin3

theorem step156CQFaithfulN_of_meet
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hMF : Step156QThetaMeet A (lB A)) :
    Step156CQFaithfulN A (lB A) := by
  intro Y hY htype c₀ L₀ d X₁ D hΩ _ h6 M hM _ _ _ _ _ _ _ _ _ _
  exact (false_of_meet h134 h48 h142 h hMF hY htype D hΩ h6 hM).elim

theorem step156CQFaithfulNR_of_meet
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (hMF : Step156QThetaMeetR) :
    Step156CQFaithfulNR :=
  fun G _ _ A c L hR => step156CQFaithfulN_of_meet h134 h48 h142 hR.toSec14Std (hMF G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
