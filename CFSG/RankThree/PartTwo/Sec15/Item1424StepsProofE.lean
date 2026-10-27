module

public import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofNotHJ
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] def KS1424NonToral : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (T : Type) [Group T], Sec4.IsoLThreePi T 2 n →
    ∀ Ā : Subgroup (Multiplicative (ZMod 3) × T), CFSG.Assembly.IsElemAbelian 3 Ā →
      Nat.card Ā = 27 →
      Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ⊔
          ⨆ (B : Subgroup (Multiplicative (ZMod 3) × T)) (_ : B ≤ Ā) (_ : Nat.card B = 9),
            pPrimeCoreOf 3 (Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T))) = ⊤ →
        Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ≤ Ā

@[expose] def KS1424Torus : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (T : Type) [Group T], Sec4.IsoLThreePi T 2 n →
    ∀ Ā : Subgroup (Multiplicative (ZMod 3) × T), CFSG.Assembly.IsElemAbelian 3 Ā →
      Nat.card Ā = 27 → Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ≤ Ā →
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ Ē : Subgroup (Multiplicative (ZMod 3) × T),
        CFSG.Assembly.IsElemAbelian p Ē ∧ Nat.card Ē = p ^ 2 ∧
        Ā ≤ Subgroup.normalizer (Ē : Set (Multiplicative (ZMod 3) × T)) ∧ ⁅Ē, Ā⁆ = Ē ∧
        Nat.card (Ā ⊓ Subgroup.centralizer (Ē : Set (Multiplicative (ZMod 3) × T)) :
          Subgroup (Multiplicative (ZMod 3) × T)) = 9

namespace Proof1424Steps

variable {G : Type} [Group G] [Finite G]

theorem lA_eq_of_zpowers_eq {A : Subgroup G} {c c' : G}
    (h : Subgroup.zpowers c = Subgroup.zpowers c') : lA A c = lA A c' := by
  ext K
  simp only [mem_lA_iff, thetaComponentsAt_eq_thetaComponentsIn,
    centralizer_singleton_eq_of_zpowers_eq h, h]
  rw [h]

theorem lB_eq_bot_of_ctx {A L Y : Subgroup G} {c : G} {n : ℕ} (hctx : Ctx1424 G A c L Y n)
    (B : Subgroup G) : lB A B = ⊥ := by
  refine lB_eq_bot fun b d L' hcfg => ?_
  obtain ⟨-, hbΩ, hLb, ⟨φ⟩, -⟩ := hcfg
  rw [hctx.omegaA_eq, Set.mem_singleton_iff] at hbΩ
  have hL : L ∈ lA A b := (lA_eq_of_zpowers_eq hbΩ).symm ▸ hctx.std.toSec13Data.mem_lA
  rw [hLb, Set.mem_singleton_iff] at hL
  subst hL
  have : IsSimpleGroup ↥L := hctx.simple
  have hθ := aschbacherSolvableCore_eq_bot hctx
  have hJ1 : 1 < Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_nativeJ2]
    norm_num
  rcases (CFSG.pCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with h2 | h2
  · exact step1424NotHJ G A c L Y n hctx
      ⟨(QuotientGroup.quotientMulEquivOfEq (h2.trans hθ.symm)).symm.trans φ⟩
  · have : Subsingleton (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [h2]
      exact QuotientGroup.subsingleton_quotient_top
    have h1 := Nat.card_congr φ.toEquiv
    rw [Nat.card_unique] at h1
    omega

theorem commutator_le_pPrimeCoreOf {A Q B : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hQ : Q ∈ scriptQ A (lB A))
    (hB : IsHyperplane A B) (hLB : lB A B = ⊥) :
    ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  set MB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hMB
  set MA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hMA
  have hle : Q ⊓ Subgroup.centralizer (B : Set G) ≤ MB ⊔ MA := by
    have h := hQ.2 B hB
    simp only [qBound, hLB, sup_bot_eq] at h
    exact h
  have hAC : A ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hAab b (hB.1 hb) x hx
  have hMBn : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (MB : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hMAn : MA ≤ Subgroup.normalizer (MB : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le hB.1)).trans hMBn
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hx' : x ∈ ((MB : Set G) * (MA : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left MB MA hMAn]
    exact hle hx
  obtain ⟨m, hm, k, hk, rfl⟩ := hx'
  have hka : k * a = a * k :=
    (Subgroup.mem_centralizer_iff.mp ((pPrimeCoreOf_le 3 _) hk) a ha).symm
  have hkey : ⁅m * k, a⁆ = m * (a * m⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc m * k * a * (m * k)⁻¹ * a⁻¹ = m * (k * a) * k⁻¹ * m⁻¹ * a⁻¹ := by group
      _ = m * (a * k) * k⁻¹ * m⁻¹ * a⁻¹ := by rw [hka]
      _ = m * (a * m⁻¹ * a⁻¹) := by group
  rw [hkey]
  exact mul_mem hm ((Subgroup.mem_normalizer_iff.mp (hMBn (hAC ha)) m⁻¹).mp (inv_mem hm))

theorem map_pPrimeCoreOf_centralizer_le {A Y B : Subgroup G} {M : Type*} [Group M]
    {f : ↥(A ⊔ Y) →* M} (hfs : Function.Surjective f) (hker : f.ker = kerAO2 A Y)
    (hBA : B ≤ A) (hB3 : IsPGroup 3 B) :
    ((pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))).subgroupOf (A ⊔ Y)).map f ≤
      pPrimeCoreOf 3 (Subgroup.centralizer
        (((B.subgroupOf (A ⊔ Y)).map f : Subgroup M) : Set M)) := by
  have hB'3 : IsPGroup 3 (B.subgroupOf (A ⊔ Y)) := hB3.comap_subtype
  have hC : Subgroup.centralizer (((B.subgroupOf (A ⊔ Y)).map f : Subgroup M) : Set M) =
      (Subgroup.centralizer ((B.subgroupOf (A ⊔ Y) : Subgroup ↥(A ⊔ Y)) :
        Set ↥(A ⊔ Y))).map f := by
    have h := map_inf_centralizer_of_not_dvd_ker f Nat.prime_three (X := ⊤) hB'3
      (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun _ => by simp)
      (not_three_dvd_card_ker hker)
    rw [top_inf_eq, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hfs, top_inf_eq] at h
    exact h.symm
  refine le_pPrimeCoreOf ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hwC : (w : G) ∈ Subgroup.centralizer (B : Set G) := pPrimeCoreOf_le 3 _ hw
    have hbw := Subgroup.mem_centralizer_iff.mp hwC (b : G) hb
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext hbw)
  · rw [hC]
    refine map_le_normalizer_map f ?_
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hγB : (γ : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hγ ⟨b, (le_sup_left : A ≤ A ⊔ Y) (hBA hb)⟩ hb)
    exact Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 _ hγB) (w : G)
  · have h1 := Subgroup.card_map_dvd
      ((pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))).subgroupOf (A ⊔ Y)) f
    have h2 : Nat.card ((pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))).subgroupOf
        (A ⊔ Y)) ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) := by
      rw [← Subgroup.card_map_of_injective (A ⊔ Y).subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (coprime_card_pPrimeCoreOf 3 _).coprime_dvd_right (h1.trans h2)

theorem sup_iSup_pPrimeCoreOf_eq_top {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) {M : Type*} [Group M] {f : ↥(A ⊔ Y) →* M}
    (hfs : Function.Surjective f) (hker : f.ker = kerAO2 A Y) :
    Subgroup.centralizer (((A.subgroupOf (A ⊔ Y)).map f : Subgroup M) : Set M) ⊔
      ⨆ (B : Subgroup M) (_ : B ≤ (A.subgroupOf (A ⊔ Y)).map f) (_ : Nat.card B = 9),
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set M)) = ⊤ := by
  have hD := hctx.std.toSec13Data
  have hAe := hD.isElemAbelian
  have hA27 := hD.card_eq
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  set Ā := (A.subgroupOf (A ⊔ Y)).map f with hĀ
  set J := Subgroup.centralizer (Ā : Set M) ⊔
    ⨆ (B : Subgroup M) (_ : B ≤ Ā) (_ : Nat.card B = 9),
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set M)) with hJ
  set K := (J.comap f).map (A ⊔ Y).subtype with hK
  have hcen : ∀ X : Subgroup G, X ≤ A ⊔ Y → X ≤ Subgroup.centralizer (A : Set G) → X ≤ K := by
    intro X hXY hXA
    refine le_map_comap_of_map_le f J hXY (le_trans ?_ le_sup_left)
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hXA hx) a ha))
  have hAK : A ≤ K := hcen A le_sup_left fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y hy x hx
  have hOK : ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊓ (A ⊔ Y) ≤ K := by
    intro B hBA hB9
    refine le_map_comap_of_map_le f J inf_le_right ?_
    rw [Subgroup.inf_subgroupOf_right]
    refine (map_pPrimeCoreOf_centralizer_le hfs hker hBA (hA3.to_le hBA)).trans ?_
    have hBP : B ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ :=
      inf_pCoreOf_eq_bot_of_coprime (by rw [hB9]; norm_num)
    have hBbar9 : Nat.card ((B.subgroupOf (A ⊔ Y)).map f) = 9 := by
      rw [card_map_of_inf_pCoreOf_eq_bot hker (hBA.trans le_sup_left) hBP, hB9]
    exact le_sup_of_le_right (le_iSup_of_le ((B.subgroupOf (A ⊔ Y)).map f)
      (le_iSup_of_le (Subgroup.map_mono (Subgroup.comap_mono hBA)) (le_iSup_of_le hBbar9 le_rfl)))
  have hQK : ∀ Q ∈ collectionIn (scriptQ A (lB A)) Y, Q ≤ K := by
    rintro Q ⟨hQ, hQY⟩
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.2.1
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.2.2
    refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hAe
      (by rw [hA27]; norm_num) hAQ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
      fun B hBA hB9 => ?_
    have hB : IsHyperplane A B := ⟨hBA, by rw [hA27, hB9]; norm_num⟩
    have hR3 : ¬ 3 ∣ Nat.card (Q ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := fun h =>
      hQ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hAR : A ≤ Subgroup.normalizer
        ((Q ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf_centralizer hAe.1 hAQ hBA
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three A _ hA3 hR3 hAR]
    refine sup_le ?_ ?_
    · refine le_trans ?_ (hOK B hBA hB9)
      refine le_inf (commutator_le_pPrimeCoreOf hAab hQ hB (lB_eq_bot_of_ctx hctx B)) ?_
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hAR).trans
        (inf_le_left.trans (hQY.trans le_sup_right))
    · exact hcen _ ((inf_le_left.trans inf_le_left).trans (hQY.trans le_sup_right)) inf_le_right
  have hYK : Y ≤ K := hctx.mem_scriptY3.2.le.trans (sSup_le hQK : delta A (lB A) Y ≤ K)
  have hAYK : A ⊔ Y ≤ K := sup_le hAK hYK
  rw [eq_top_iff]
  intro m _
  obtain ⟨γ, rfl⟩ := hfs m
  exact map_mem_of_le_map_comap f hAYK γ.2

theorem sylow_of_fusionIsSylowIn {X : Type} [Group X] {p : ℕ} [Fact p.Prime] {T U : Subgroup X}
    (h : CFSG.Open.fusionIsSylowIn p T U) :
    ∃ P : Sylow p ↥U, (P : Subgroup ↥U) = T.subgroupOf U := by
  obtain ⟨hTU, hT, hmax⟩ := h
  refine ⟨⟨T.subgroupOf U, hT.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map U.subtype) (Subgroup.map_subtype_le Q) (hQ.map U.subtype) fun s hs =>
    ⟨⟨s, hTU hs⟩, hTQ (show (⟨s, hTU hs⟩ : U) ∈ T.subgroupOf U from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective U.subtype_injective Q).symm

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers' (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have h : Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h]
  exact Subgroup.centralizer_le_normalizer _

theorem exists_isE1424_of_torus {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) (h142 : Concl142 A (lB A)) {M : Type*} [Group M] [Finite M]
    {f : ↥(A ⊔ Y) →* M} (hfs : Function.Surjective f) (hker : f.ker = kerAO2 A Y)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Ē : Subgroup M}
    (hEe : CFSG.Assembly.IsElemAbelian p Ē) (hEcard : Nat.card Ē = p ^ 2)
    (hAE : (A.subgroupOf (A ⊔ Y)).map f ≤ Subgroup.normalizer (Ē : Set M))
    (hEA : ⁅Ē, (A.subgroupOf (A ⊔ Y)).map f⁆ = Ē)
    (hC9 : Nat.card ((A.subgroupOf (A ⊔ Y)).map f ⊓ Subgroup.centralizer (Ē : Set M) :
      Subgroup M) = 9) :
    ∃ E : Subgroup G, IsE1424 A L Y p E := by
  have hD := hctx.std.toSec13Data
  have hA27 := hD.card_eq
  have hAe := hD.isElemAbelian
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  have : Fact p.Prime := ⟨hp⟩
  have hp3' : p ≠ 3 := by omega
  have hYn : (Y.subgroupOf (A ⊔ Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hctx.le_normalizer Subgroup.le_normalizer)
  have hWn : ((Y.subgroupOf (A ⊔ Y)).map f).Normal := hYn.map f hfs
  have hEW : Ē ≤ ((Y ⊓ L).subgroupOf (A ⊔ Y)).map f := by
    rw [map_inf_eq_map hctx.eq_sup hker]
    have h1 := Subgroup.relIndex_dvd_index_of_normal ((Y.subgroupOf (A ⊔ Y)).map f) Ē
    have h2 := index_map_dvd_twentySeven hctx.le_normalizer hA27 hfs hker
    have h3 := Subgroup.relIndex_dvd_card ((Y.subgroupOf (A ⊔ Y)).map f) Ē
    rw [hEcard] at h3
    have hcop : Nat.Coprime 27 (p ^ 2) := by
      have h : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
      exact Nat.Coprime.pow 3 2 h
    exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop (h1.trans h2) h3)
  set H₀ : Subgroup ↥(A ⊔ Y) := (Y ⊓ L).subgroupOf (A ⊔ Y) ⊓ Ē.comap f with hH₀
  have hfH₀ : H₀.map f = Ē := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro e he
      obtain ⟨γ, hγ, rfl⟩ := hEW he
      exact ⟨γ, ⟨hγ, he⟩, rfl⟩
  have hA'3 : IsPGroup 3 (A.subgroupOf (A ⊔ Y)) := hA3.comap_subtype
  have hA'H₀ : A.subgroupOf (A ⊔ Y) ≤ Subgroup.normalizer (H₀ : Set ↥(A ⊔ Y)) := by
    refine Late.le_normalizer_inf ?_ ?_
    · have hAYL : A ≤ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G) :=
        Late.le_normalizer_inf hctx.le_normalizer hD.le_normalizer
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hAYL ha) (x : G)
    · intro a ha
      exact Subgroup.le_normalizer_comap f (Subgroup.mem_comap.mpr (hAE ⟨a, ha, rfl⟩))
  have hE3 : ¬ 3 ∣ Nat.card Ē := by
    rw [hEcard]
    intro h
    exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hH₀3 : ¬ 3 ∣ Nat.card H₀ := by
    have h1 := not_three_dvd_card_comap f hE3 (not_three_dvd_card_ker hker)
    exact fun h => h1 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨EΓ, hEsyl, -, hAEΓ⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hp hA'3 hH₀3 hA'H₀ bot_le IsPGroup.of_bot
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun _ => by simp)
  have hEH₀ : EΓ ≤ H₀ := hEsyl.1
  have hEp : IsPGroup p EΓ := hEsyl.2.1
  have hfE : EΓ.map f = Ē := by
    obtain ⟨S, hS⟩ := sylow_of_fusionIsSylowIn hEsyl
    have hidx : ¬ p ∣ (EΓ.subgroupOf H₀).index := hS ▸ S.not_dvd_index
    set g : ↥H₀ →* M := f.comp H₀.subtype with hg
    have hgr : g.range = Ē := by
      rw [hg, MonoidHom.range_comp, Subgroup.range_subtype, hfH₀]
    have hgE : (EΓ.subgroupOf H₀).map g = EΓ.map f := by
      rw [hg, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hEH₀]
    have hle : (EΓ.subgroupOf H₀).map g ≤ g.range := Subgroup.map_le_range g _
    have h1 := Subgroup.index_map (EΓ.subgroupOf H₀) g
    have h2 := Subgroup.relIndex_mul_index hle
    have hri : g.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 : ((EΓ.subgroupOf H₀).map g).relIndex g.range =
        (EΓ.subgroupOf H₀ ⊔ g.ker).index :=
      Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hri) (h2.trans h1)
    have h4 : (EΓ.subgroupOf H₀ ⊔ g.ker).index ∣ (EΓ.subgroupOf H₀).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h5 : ((EΓ.subgroupOf H₀).map g).relIndex g.range ∣ p ^ 2 := by
      have h := Subgroup.relIndex_dvd_card ((EΓ.subgroupOf H₀).map g) g.range
      have hc : Nat.card g.range = p ^ 2 := by rw [hgr, hEcard]
      rwa [hc] at h
    have h6 : ((EΓ.subgroupOf H₀).map g).relIndex g.range = 1 := by
      obtain ⟨k, -, hkeq⟩ := (Nat.dvd_prime_pow hp).mp h5
      rcases k with _ | k
      · simpa using hkeq
      · exfalso
        rw [← h3, hkeq] at h4
        exact hidx ((dvd_pow_self p (Nat.succ_ne_zero k)).trans h4)
    have h7 := Subgroup.relIndex_eq_one.mp h6
    rw [hgr, hgE] at h7
    exact le_antisymm (hfH₀ ▸ Subgroup.map_mono hEH₀) h7
  set E : Subgroup G := EΓ.map (A ⊔ Y).subtype with hE
  have hEsub : E.subgroupOf (A ⊔ Y) = EΓ :=
    Subgroup.comap_map_eq_self_of_injective (A ⊔ Y).subtype_injective EΓ
  have hEAY : E ≤ A ⊔ Y := Subgroup.map_subtype_le EΓ
  have hEpG : IsPGroup p E := hEp.map _
  have hEP : E ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ := by
    refine inf_pCoreOf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEpG
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  have hfE' : (E.subgroupOf (A ⊔ Y)).map f = Ē := by rw [hEsub, hfE]
  have hEc : Nat.card E = p ^ 2 := by
    rw [← card_map_of_inf_pCoreOf_eq_bot hker hEAY hEP, hfE', hEcard]
  have hEYL : E ≤ Y ⊓ L := by
    rw [hE, Subgroup.map_le_iff_le_comap]
    exact hEH₀.trans inf_le_left
  have hAEn : A ≤ Subgroup.normalizer (E : Set G) := by
    have h := map_le_normalizer_map (A ⊔ Y).subtype hAEΓ
    rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_left] at h
  have hinj : ∀ {x y : ↥(A ⊔ Y)}, (x : G) ∈ E → (y : G) ∈ E → f x = f y → x = y :=
    fun hx hy hxy => eq_of_map_eq hker hEP hx hy hxy
  have hmemE : ∀ {x : ↥(A ⊔ Y)}, (x : G) ∈ E → f x ∈ Ē := fun {x} hx => by
    rw [← hfE']
    exact ⟨x, hx, rfl⟩
  have hEelem : CFSG.Assembly.IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hcomm : f (⟨x, hEAY x.2⟩ * ⟨y, hEAY y.2⟩) = f (⟨y, hEAY y.2⟩ * ⟨x, hEAY x.2⟩) := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨_, hmemE (x := ⟨x, hEAY x.2⟩) x.2⟩
          ⟨_, hmemE (x := ⟨y, hEAY y.2⟩) y.2⟩)
      have h := hinj (mul_mem x.2 y.2) (mul_mem y.2 x.2) hcomm
      exact congrArg (Subtype.val : ↥(A ⊔ Y) → G) h
    · have h1 : f ((⟨x, hEAY hx⟩ : ↥(A ⊔ Y)) ^ p) = f 1 := by
        rw [map_pow, map_one]
        exact hEe.2 _ (hmemE (x := ⟨x, hEAY hx⟩) hx)
      have h2 := hinj (x := (⟨x, hEAY hx⟩ : ↥(A ⊔ Y)) ^ p) (y := 1)
        (by simpa using pow_mem hx p) (one_mem E) h1
      exact congrArg Subtype.val h2
  have hEA' : E = ⁅E, A⁆ := by
    have hle : ⁅E, A⁆ ≤ E := Subgroup.le_normalizer_iff_commutator_le_left.mp hAEn
    have hcAY : ⁅E, A⁆ ≤ A ⊔ Y := hle.trans hEAY
    have h1 : (⁅E, A⁆).subgroupOf (A ⊔ Y) = ⁅E.subgroupOf (A ⊔ Y), A.subgroupOf (A ⊔ Y)⁆ := by
      apply Subgroup.map_injective (A ⊔ Y).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEAY,
        Subgroup.map_subgroupOf_eq_of_le le_sup_left, Subgroup.map_subgroupOf_eq_of_le hcAY]
    have hcomm : ((⁅E, A⁆).subgroupOf (A ⊔ Y)).map f = Ē := by
      rw [h1, Subgroup.map_commutator, hfE', hEA]
    have hcP : ⁅E, A⁆ ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ hle).trans hEP.le)
    have hc : Nat.card (⁅E, A⁆ : Subgroup G) = Nat.card E := by
      rw [← card_map_of_inf_pCoreOf_eq_bot hker hcAY hcP, hcomm, hEcard, hEc]
    exact (Subgroup.eq_of_le_of_card_ge hle hc.ge).symm
  have hEQ : E ∈ scriptQ A (lB A) := by
    have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (hEYL.trans inf_le_right).trans
        (hD.le_centralizer.trans (centralizer_le_normalizer_zpowers' c))
    have hEn3 : ¬ 3 ∣ Nat.card E := by
      rw [hEc]
      intro h
      exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have hEinv : E ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3) :=
      ⟨hEN, (isPiSubgroup_piCompl_iff Nat.prime_three E).mpr hEn3, hAEn⟩
    obtain ⟨Q, hQ, hEQ⟩ := exists_le_mem_maxInvariantPiSubgroups hEinv
    exact mem_scriptQ_of_le (h142 c hD.zpowers_mem_omegaA Q hQ).1 hEQ hAEn
  have hAC : ((A ⊓ Subgroup.centralizer (E : Set G)).subgroupOf (A ⊔ Y)).map f =
      (A.subgroupOf (A ⊔ Y)).map f ⊓ Subgroup.centralizer (Ē : Set M) := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨a, ha.1, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      rw [← hfE'] at he
      obtain ⟨e', he', rfl⟩ := he
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (Subgroup.mem_centralizer_iff.mp ha.2 _ he'))
    · rintro _ ⟨⟨a', ha', rfl⟩, hc⟩
      refine ⟨a', Subgroup.mem_inf.mpr ⟨ha', ?_⟩, rfl⟩
      show (a' : G) ∈ Subgroup.centralizer (E : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h1 : (a' * ⟨e, hEAY he⟩ * a'⁻¹ : ↥(A ⊔ Y)) = ⟨e, hEAY he⟩ := by
        refine hinj ((Subgroup.mem_normalizer_iff.mp (hAEn ha') e).mp he) he ?_
        rw [map_mul, map_mul, map_inv]
        have h2 := Subgroup.mem_centralizer_iff.mp hc (f ⟨e, hEAY he⟩)
          (hmemE (x := ⟨e, hEAY he⟩) he)
        rw [← h2]
        group
      have h2 : (a' : G) * e * (a' : G)⁻¹ = e := congrArg Subtype.val h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hACP : (A ⊓ Subgroup.centralizer (E : Set G)) ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans
      (inf_pCoreOf_eq_bot_of_coprime (by rw [hA27]; norm_num)).le)
  have h9 : Nat.card (A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) = 9 := by
    rw [← card_map_of_inf_pCoreOf_eq_bot hker (inf_le_left.trans le_sup_left) hACP, hAC, hC9]
  exact ⟨E, hp, hp3, hEelem, hEc, hEA', hEQ, hEYL, inf_le_left, by rw [hA27, h9]⟩

end Proof1424Steps

open Proof1424Steps in
theorem step1424E_of (h142 : Concl142S14) (hNT : KS1424NonToral) (hT : KS1424Torus) :
    Step1424E := by
  intro G _ _ A c L Y n hctx
  obtain ⟨T, _, f, hTiso, hfs, hker⟩ := exists_quotMap hctx
  have : Finite (Multiplicative (ZMod 3) × T) := Finite.of_surjective f hfs
  have hD := hctx.std.toSec13Data
  have hAe := hD.isElemAbelian
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf (A ⊔ Y)) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hD.commute (Subgroup.mem_subgroupOf.mp y.2) (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hAe.2 _ (Subgroup.mem_subgroupOf.mp hy))
  have hĀe : CFSG.Assembly.IsElemAbelian 3 ((A.subgroupOf (A ⊔ Y)).map f) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f _ hA'
  have hAP : A ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ :=
    inf_pCoreOf_eq_bot_of_coprime (by rw [hD.card_eq]; norm_num)
  have hĀ27 : Nat.card ((A.subgroupOf (A ⊔ Y)).map f) = 27 := by
    rw [card_map_of_inf_pCoreOf_eq_bot hker le_sup_left hAP, hD.card_eq]
  have hcen := hNT n hctx.four_le T hTiso _ hĀe hĀ27 (sup_iSup_pPrimeCoreOf_eq_top hctx hfs hker)
  obtain ⟨p, hp, hp3, Ē, hEe, hEcard, hAE, hEA, hC9⟩ :=
    hT n hctx.four_le T hTiso _ hĀe hĀ27 hcen
  exact ⟨p, exists_isE1424_of_torus hctx (h142 G A c L hctx.std) hfs hker hp hp3 hEe hEcard hAE
    hEA hC9⟩

end CFSG.RankThree.PartTwo.Sec15
