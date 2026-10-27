module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22se
import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
import CFSG.LieType.BorelTits.Basic
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22x
import CFSG.Milestones.ASVolI.B6
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B5FinOut
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B69E22Pre
import CFSG.Quasithin.Background.B69Final
import CFSG.Quasithin.Background.B69Iso
import CFSG.Quasithin.Background.B69Lift
import CFSG.Quasithin.Background.B69Mod
import CFSG.Quasithin.Background.B69Simple
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2Three
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22mc_pCoreOf_le_T (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hN : D.M ≤ normalizer (L : Set G)) : pCoreOf 2 L ≤ D.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)
    (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).trans ?_
  exact uc22p22e_pCoreOf_le_T D

theorem uc22mc_conj_mem_jOf (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hN : D.M ≤ normalizer (L : Set G)) (hJL : ⁅jOf D.T, L⁆ ≤ pCoreOf 2 L) {y : G}
    (hy : y ∈ L) : ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := by
  refine uc22p22e_conj_jOf (fun x hx => ?_)
  have h1 : ⁅x, y⁆ ∈ pCoreOf 2 L := hJL (Subgroup.commutator_mem_commutator hx hy)
  have h2 : ⁅y, x⁆ ∈ D.T := by
    rw [← commutatorElement_inv]
    exact D.T.inv_mem (uc22mc_pCoreOf_le_T D hLM hN h1)
  have h3 : y * x * y⁻¹ = ⁅y, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [h3]
  exact D.T.mul_mem h2 (uc22p22e_jOf_le_self D.T hx)

theorem uc22mc_mem_normalizer_proofE (D : Data G) {y : G}
    (h1 : ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T) (h2 : ∀ x ∈ jOf D.T, y⁻¹ * x * y ∈ jOf D.T) :
    y ∈ normalizer (proofE D : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact fun hz => uc22p22e_conj_omegaZJ h1 h2 z hz
  · intro hz
    have := uc22p22e_conj_omegaZJ (y := y⁻¹) (by simpa using h2) (by simpa using h1) _ hz
    show z ∈ omegaZJ22 D.T
    simpa [mul_assoc] using this

theorem uc22mc_le_normalizer_proofE (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hN : D.M ≤ normalizer (L : Set G)) (hJL : ⁅jOf D.T, L⁆ ≤ pCoreOf 2 L) :
    L ≤ normalizer (proofE D : Set G) := fun y hy =>
  uc22mc_mem_normalizer_proofE D (uc22mc_conj_mem_jOf D hLM hN hJL hy)
    (fun x hx => by simpa using uc22mc_conj_mem_jOf D hLM hN hJL (L.inv_mem hy) x hx)

omit [Finite G] in
theorem uc22mc_conj_mem_centralizer {E : Subgroup G} {y c : G}
    (hy : y ∈ normalizer (E : Set G)) (hc : c ∈ centralizer (E : Set G)) :
    y * c * y⁻¹ ∈ centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have he' : y⁻¹ * e * y ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) e).mp he
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hc _ he'
  calc e * (y * c * y⁻¹) = y * ((y⁻¹ * e * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * e * y)) * y⁻¹ := by rw [h]
    _ = y * c * y⁻¹ * e := by group

theorem uc22mc_inf_centralizer_le_pCoreOf (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hN : D.M ≤ normalizer (L : Set G)) (hsimple : IsSimpleGroup (Bar2 L))
    (hU1 : D.U ⊓ centralizer (L : Set G) = ⊥) (hLE : L ≤ normalizer (proofE D : Set G)) :
    L ⊓ centralizer (proofE D : Set G) ≤ pCoreOf 2 L := by
  have := hsimple
  have hNn : ((L ⊓ centralizer (proofE D : Set G)).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, uc22mc_conj_mem_centralizer (hLE g.2) hn.2⟩
    exact L.mul_mem (L.mul_mem g.2 n.2) (L.inv_mem g.2)
  have hmapn := hNn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  rcases hmapn.eq_bot_or_eq_top with hbot | htop
  · intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx.1⟩ ∈
        ((L ⊓ centralizer (proofE D : Set G)).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_map_of_mem L.subtype h1
  · exfalso
    apply uc22main1_Z_ne_bot D
    rw [eq_bot_iff, ← hU1]
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨uc22main1_Z_le_U D hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        ((L ⊓ centralizer (proofE D : Set G)).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hnN, hnl⟩ := Subgroup.mem_map.mp hl1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    have hnZ : z * (n : G) = (n : G) * z :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hnN).2 z
        (uc22p22se_Z_le_proofE D hz)
    obtain ⟨o, hoT, hlo⟩ : ∃ o ∈ D.T, l = (n : G) * o :=
      ⟨_, uc22mc_pCoreOf_le_T D hLM hN (Subgroup.mem_map_of_mem L.subtype hnl), by simp⟩
    have hoZ : z * o = o * z :=
      Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D hoT) z hz
    rw [hlo]
    calc (n : G) * o * z = n * (z * o) := by rw [mul_assoc, hoZ]
      _ = z * (n * o) := by rw [← mul_assoc, ← hnZ, mul_assoc]

theorem uc22mc_le_normalizer_proofS_of_comm_le (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hN : D.M ≤ normalizer (L : Set G)) (hsimple : IsSimpleGroup (Bar2 L))
    (hU1 : D.U ⊓ centralizer (L : Set G) = ⊥) (hJL : ⁅jOf D.T, L⁆ ≤ pCoreOf 2 L) :
    L ⊔ D.T ≤ normalizer (proofS D : Set G) := by
  have hLE := uc22mc_le_normalizer_proofE D hLM hN hJL
  have hX := uc22mc_inf_centralizer_le_pCoreOf D hLM hN hsimple hU1 hLE
  have hTE : D.T ≤ normalizer (proofE D : Set G) := fun y hy =>
    uc22mc_mem_normalizer_proofE D (uc22p22e_normalizes_jOf_T D y hy)
      (fun x hx => by simpa using uc22p22e_normalizes_jOf_T D y⁻¹ (D.T.inv_mem hy) x hx)
  refine sup_le (fun l hl => ?_) (fun t ht => ?_)
  · rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ L, ∀ s ∈ proofS D, y * s * y⁻¹ ∈ proofS D := by
      intro y hy s hs
      have hsT : s ∈ D.T := hs.1
      have hsC : s ∈ centralizer (proofE D : Set G) := hs.2
      have hc1 : y * s * y⁻¹ ∈ centralizer (proofE D : Set G) :=
        uc22mc_conj_mem_centralizer (hLE hy) hsC
      have hsN : s ∈ normalizer (L : Set G) := hN (D.sylowM.le hsT)
      have hcomm : ⁅y, s⁆ ∈ L ⊓ centralizer (proofE D : Set G) := by
        refine ⟨?_, ?_⟩
        · have h1 : s * y⁻¹ * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN _).mp (L.inv_mem hy)
          have : ⁅y, s⁆ = y * (s * y⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
          rw [this]
          exact L.mul_mem hy h1
        · have : ⁅y, s⁆ = (y * s * y⁻¹) * s⁻¹ := by simp only [commutatorElement_def]
          rw [this]
          exact Subgroup.mul_mem _ hc1 (Subgroup.inv_mem _ hsC)
      have hcT : ⁅y, s⁆ ∈ D.T := uc22mc_pCoreOf_le_T D hLM hN (hX hcomm)
      have h3 : y * s * y⁻¹ = ⁅y, s⁆ * s := by simp only [commutatorElement_def]; group
      refine ⟨?_, hc1⟩
      rw [h3]
      exact D.T.mul_mem hcT hsT
    intro s
    refine ⟨fun hs => key l hl s hs, fun hs => ?_⟩
    have := key l⁻¹ (L.inv_mem hl) _ hs
    simpa [mul_assoc] using this
  · rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ D.T, ∀ s ∈ proofS D, y * s * y⁻¹ ∈ proofS D := fun y hy s hs =>
      ⟨D.T.mul_mem (D.T.mul_mem hy hs.1) (D.T.inv_mem hy),
        uc22mc_conj_mem_centralizer (hTE hy) hs.2⟩
    intro s
    refine ⟨fun hs => key t ht s hs, fun hs => ?_⟩
    have := key t⁻¹ (D.T.inv_mem ht) _ hs
    simpa [mul_assoc] using this

theorem uc22mc_le_normalizer_proofS_of_core (D : Data G) {X R : Subgroup G} (hTX : D.T ≤ X)
    (hXM : X ≤ D.M) (hJR : jOf D.T ≤ R) (hRT : R ≤ D.T) (hXR : X ≤ normalizer (R : Set G))
    (hY : IsPGroup 2 ↥(X ⊓ centralizer (proofE D : Set G))) :
    X ≤ normalizer (proofS D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ y ∈ X, ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := fun y hy => by
    refine uc22p22e_conj_jOf (fun x hx => hRT ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hXR hy) x).mp (hJR hx)
  have hXE : X ≤ normalizer (proofE D : Set G) := fun y hy =>
    uc22mc_mem_normalizer_proofE D (hconj y hy)
      (fun x hx => by simpa using hconj y⁻¹ (X.inv_mem hy) x hx)
  set Y : Subgroup G := X ⊓ centralizer (proofE D : Set G) with hYdef
  have hXY : X ≤ normalizer (Y : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ X, ∀ c ∈ Y, g * c * g⁻¹ ∈ Y := fun g hg c hc =>
      ⟨X.mul_mem (X.mul_mem hg hc.1) (X.inv_mem hg), uc22mc_conj_mem_centralizer (hXE hg) hc.2⟩
    intro c
    refine ⟨fun hc => key y hy c hc, fun hc => ?_⟩
    have := key y⁻¹ (X.inv_mem hy) _ hc
    simpa [mul_assoc] using this
  have hTXs : CFSG.ABGLocalTools.IsSylowOf 2 D.T X := D.sylowM.of_le hTX hXM
  have hYT : Y ≤ D.T :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_le_of_le_normalizer hTXs hY inf_le_left hXY
  have hYS : Y = proofS D := by
    apply le_antisymm
    · exact fun c hc => ⟨hYT hc, hc.2⟩
    · exact fun c hc => ⟨hTX hc.1, hc.2⟩
  rw [← hYS]
  exact hXY

omit [Finite G] in
theorem uc22mc_isPGroup_of_le_sup {N T Y : Subgroup G} (hTN : T ≤ normalizer (N : Set G))
    (hT : IsPGroup 2 ↥T) (hYS : Y ≤ N ⊔ T) (hYN : IsPGroup 2 ↥(Y ⊓ N)) : IsPGroup 2 ↥Y := by
  intro y
  have hNS : (N.subgroupOf (N ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTN)
  have hyS : (y : G) ∈ N ⊔ T := hYS y.2
  have hyS' : (⟨y, hyS⟩ : ↥(N ⊔ T)) ∈ N.subgroupOf (N ⊔ T) ⊔ T.subgroupOf (N ⊔ T) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, t, ht, hnt⟩ := (Subgroup.mem_sup_of_normal_left
    (s := N.subgroupOf (N ⊔ T)) (t := T.subgroupOf (N ⊔ T))).1 hyS'
  obtain ⟨l, hl⟩ := hT ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩
  have hl' : t ^ 2 ^ l = 1 := Subtype.ext (by simpa using congrArg Subtype.val hl)
  set π := QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) with hπ
  have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  have hπy : π ⟨y, hyS⟩ = π t := by
    rw [← hnt, map_mul, hn1, one_mul]
  have hpow : π (⟨y, hyS⟩ ^ 2 ^ l) = 1 := by rw [map_pow, hπy, ← map_pow, hl', map_one]
  have hmemN : ((⟨y, hyS⟩ : ↥(N ⊔ T)) ^ 2 ^ l : ↥(N ⊔ T)) ∈ N.subgroupOf (N ⊔ T) :=
    (QuotientGroup.eq_one_iff _).mp hpow
  have hyN : (y : G) ^ 2 ^ l ∈ N := by
    have := Subgroup.mem_subgroupOf.mp hmemN
    simpa using this
  obtain ⟨m, hm⟩ := hYN ⟨(y : G) ^ 2 ^ l, Y.pow_mem y.2 _, hyN⟩
  have hm' : ((y : G) ^ 2 ^ l) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  refine ⟨l + m, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_add, pow_mul, hm', Subgroup.coe_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22
