module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2Proof
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate120
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofCensus
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.Simplicity.ReeLargeModel
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Sporadic.Schreier.TitsIso
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartOne.S12K.Rigidity
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Kernel.ThCent.Leaves
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec5.Hyp
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.Walter.Defs
import Certificates.Kernel.SporSch.Th.Orb2315
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

@[expose] def K419AutThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsType419 K →
    ∀ b ∈ Subgroup.normalizer (K : Set G), b ^ 3 = 1 → b ∉ Subgroup.centralizer (K : Set G) →
      ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ b ∈ Subgroup.normalizer (T : Set G) ∧
        ¬ T ≤ Subgroup.centralizer ({b} : Set G)

namespace Res419Two

theorem not_prime_of_four_dvd {n : ℕ} (h : 4 ∣ n) : ¬ n.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd 4 h with h1 | h1
  · norm_num at h1
  · rw [← h1] at hp
    norm_num at hp

theorem three_dvd_two_pow_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 n
  rw [one_pow] at h
  rw [← pow_mul, mul_comm, pow_mul]
  exact h

section Types

theorem four_dvd_card {K : Type} [Group K] (h : IsType419 K) : 4 ∣ Nat.card K := by
  rcases card_cases h with h6 | hU | ⟨h8, -⟩
  · obtain ⟨e⟩ := h6
    rw [Nat.card_congr e.toEquiv, Res4Three419.card_alternatingGroup_six]
    norm_num
  · obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three]
    norm_num
  · exact (pow_dvd_pow 2 (by norm_num : 2 ≤ 8)).trans h8

theorem three_dvd_card {K : Type} [Group K] (h : IsType419 K) : 3 ∣ Nat.card K := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, hSp⟩ | hA
  · rw [(CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG2).1 rfl, CFSG.Open.ordG2]
    exact Dvd.dvd.mul_left (three_dvd_two_pow_sq_sub_one n) _
  · obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three]
    norm_num
  · rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hF4, CFSG.Open.ordTwistedF4]
    have h4 : 3 ∣ (2 ^ n) ^ 4 - 1 := by
      have h := Nat.sub_dvd_pow_sub_pow 16 1 n
      rw [one_pow] at h
      rw [← pow_mul, mul_comm, pow_mul]
      exact (show (3 : ℕ) ∣ 16 - 1 by norm_num).trans h
    exact (((h4.mul_left _).mul_right _).mul_right _)
  · rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hT, CFSG.Open.ordTits]
    norm_num
  · obtain ⟨e⟩ := hSp
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSp_two
      (by omega)]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_two_pow_sq_sub_one n) _) _
  · obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, Res4Three419.card_alternatingGroup_six]
    norm_num

theorem center_eq_bot_of_isType419
    {K : Type} [Group K] (h : IsType419 K) :
    Subgroup.center K = ⊥ := by
  have hnp := not_prime_of_four_dvd (four_dvd_card h)
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, hSp⟩ | hA
  · have := (CFSG.LieType.Simplicity.fam_g2_simplicity K 2 n hG2).2
    exact center_eq_bot_of_simple hnp
  · obtain ⟨e⟩ := hU
    exact center_eq_bot_of_projSU_three_three e
  · have := (CFSG.LieType.Simplicity.fam_2f4_simplicity K 2 n hF4).2
    exact center_eq_bot_of_simple hnp
  · obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1 hT
    have := CFSG.Sporadic.Schreier.Tits.titsD_simple
    have : IsSimpleGroup K := e.isSimpleGroup
    exact center_eq_bot_of_simple hnp
  · obtain ⟨e⟩ := hSp
    have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
      (GaloisField 2 n) 2 (by norm_num) (Or.inl (Or.inr h4))
    have : IsSimpleGroup K := (e.trans (Sec4.projSpEquivStatedProj 2 _)).isSimpleGroup
    exact center_eq_bot_of_simple hnp
  · obtain ⟨e⟩ := hA
    have := alternatingGroup.isSimpleGroup (α := Fin 6) (by rw [Nat.card_fin]; norm_num)
    have : IsSimpleGroup K := e.isSimpleGroup
    exact center_eq_bot_of_simple hnp

theorem exists_noncentral_three
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : IsType419 K) : ∃ e ∈ K, e ^ 3 = 1 ∧ ∃ k ∈ K, e * k ≠ k * e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card h)
  have he1 : e ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at he
    norm_num at he
  have heZ : e ∉ Subgroup.center K := by
    rw [center_eq_bot_of_isType419 h, Subgroup.mem_bot]
    exact he1
  rw [Subgroup.mem_center_iff] at heZ
  push Not at heZ
  obtain ⟨k, hk⟩ := heZ
  refine ⟨e, e.2, ?_, k, k.2, fun h' => hk (Subtype.ext h'.symm)⟩
  have h3 : e ^ 3 = 1 := he ▸ pow_orderOf_eq_one e
  exact congrArg Subtype.val h3

theorem exists_two {G : Type} [Group G] [Finite G] {K : Subgroup G} (h : IsType419 K) :
    ∃ t ∈ K, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
    ((show (2 : ℕ) ∣ 4 by norm_num).trans (four_dvd_card h))
  exact ⟨t, t.2, by rw [Subgroup.orderOf_coe]; exact ht⟩

end Types

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {H : Subgroup G} {y : G}
    (h : ∀ n ∈ H, y * n * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.mem_normalizer_fintype h

theorem commute_conj_of_not_mem_normalizer {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    {a y : G} (hL : IsComponent L) (hK : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    (hya : y * a = a * y) (hyK : y ∉ Subgroup.normalizer (K : Set G)) :
    ∀ k ∈ K, ∀ k' ∈ K, k * (y * k' * y⁻¹) = (y * k' * y⁻¹) * k := by
  intro k hk k' hk'
  by_cases hyL : y ∈ Subgroup.normalizer (L : Set G)
  · set M : Subgroup G := L ⊓ Subgroup.centralizer ({a} : Set G) with hM
    have hyM : y ∈ Subgroup.normalizer (M : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro n hn
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hyL n).mp hn.1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hn' : n * a = a * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
      have hya' : y⁻¹ * a = a * y⁻¹ := by
        calc y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * a) * y⁻¹ := by rw [hya]
          _ = a * y⁻¹ := by group
      calc y * n * y⁻¹ * a = y * n * (y⁻¹ * a) := by group
        _ = y * (n * a) * y⁻¹ := by rw [hya']; group
        _ = y * (a * n) * y⁻¹ := by rw [hn']
        _ = (y * a) * n * y⁻¹ := by group
        _ = a * (y * n * y⁻¹) := by rw [hya]; group
    set φ : MulAut M := M.normalizerMonoidHom ⟨y, hyM⟩ with hφ
    have hK2 : IsComponent ((K.subgroupOf M).map φ.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv φ hKc
    rcases CFSG.LocalCores.distinct_components_commute hKc hK2 with heq | hcomm
    · exfalso
      apply hyK
      apply mem_normalizer_of_conj_mem
      intro n hn
      have hmem : φ ⟨n, hK hn⟩ ∈ (K.subgroupOf M).map φ.toMonoidHom :=
        ⟨⟨n, hK hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [← heq] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have h1 := Subgroup.mem_centralizer_iff.mp
        (hle (show (⟨k, hK hk⟩ : M) ∈ K.subgroupOf M from Subgroup.mem_subgroupOf.mpr hk))
        (φ ⟨k', hK hk'⟩) ⟨⟨k', hK hk'⟩, Subgroup.mem_subgroupOf.mpr hk', rfl⟩
      exact (congrArg Subtype.val h1).symm
  · have hL' : IsComponent (L.map (MulAut.conj y).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv _ hL
    rcases CFSG.LocalCores.distinct_components_commute hL hL' with heq | hcomm
    · exfalso
      apply hyL
      apply mem_normalizer_of_conj_mem
      intro n hn
      have hmem : y * n * y⁻¹ ∈ L.map (MulAut.conj y).toMonoidHom := ⟨n, hn, rfl⟩
      rwa [← heq] at hmem
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact (Subgroup.mem_centralizer_iff.mp (hle (hK hk).1) (y * k' * y⁻¹)
        ⟨k', (hK hk').1, rfl⟩).symm

theorem isElemAbelian_zpowers {G : Type} [Group G] {u : G} (hu : u ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers u) := CFSG.Open.isElemAbelian_zpowers hu

theorem mem_centralizer_map_conj {G : Type} [Group G] {K : Subgroup G} {y z : G}
    (hzy : z * y = y * z) (hz : z ∈ Subgroup.centralizer (K : Set G)) :
    z ∈ Subgroup.centralizer ((K.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have hkz : k * z = z * k := Subgroup.mem_centralizer_iff.mp hz k hk
  have hyz : y⁻¹ * z = z * y⁻¹ := by
    calc y⁻¹ * z = y⁻¹ * (z * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * z) * y⁻¹ := by rw [hzy]
      _ = z * y⁻¹ := by group
  change y * k * y⁻¹ * z = z * (y * k * y⁻¹)
  calc y * k * y⁻¹ * z = y * k * (y⁻¹ * z) := by group
    _ = y * (k * z) * y⁻¹ := by rw [hyz]; group
    _ = y * (z * k) * y⁻¹ := by rw [hkz]
    _ = (y * z) * k * y⁻¹ := by group
    _ = z * (y * k * y⁻¹) := by rw [← hzy]; group

theorem conj_not_mem_centralizer {G : Type} [Group G] {K : Subgroup G} {y e k : G} (hk : k ∈ K)
    (hek : e * k ≠ k * e) :
    y * e * y⁻¹ ∉
      Subgroup.centralizer ((K.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  intro h
  apply hek
  have h1 := Subgroup.mem_centralizer_iff.mp h (y * k * y⁻¹) ⟨k, hk, rfl⟩
  have h2 : y * (k * e) * y⁻¹ = y * (e * k) * y⁻¹ := by
    calc y * (k * e) * y⁻¹ = y * k * y⁻¹ * (y * e * y⁻¹) := by group
      _ = y * e * y⁻¹ * (y * k * y⁻¹) := h1
      _ = y * (e * k) * y⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem sup_zpowers_of_noncentral {G : Type} [Group G] [Finite G] {S H : Subgroup G} {u : G}
    (hS : CFSG.Assembly.IsElemAbelian 3 S) (hSH : S ≤ Subgroup.centralizer (H : Set G))
    (hu : u ∉ Subgroup.centralizer (H : Set G)) (hu3 : u ^ 3 = 1)
    (hSu : S ≤ Subgroup.centralizer ({u} : Set G)) :
    CFSG.Assembly.IsElemAbelian 3 (S ⊔ Subgroup.zpowers u) ∧
      Nat.card (S ⊔ Subgroup.zpowers u : Subgroup G) = Nat.card S * 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Sec5.isElemAbelian_sup_zpowers hS (fun h => hu (hSH h)) hu3
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hSu hs))

section Config

theorem le_normalizer_of_config {G : Type} [Group G] [Finite G] {L A K : Subgroup G} {c a : G}
    (hcfg : Config419 G L A c a K) (ht : IsType419 K) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, hL, hA, -, hAc, hc, ha, hac, hK, hKc, hF⟩ := hcfg
  intro x hxA
  by_contra hxK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.prop.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcAL : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcAL.1
  have hcL : c ∈ Subgroup.centralizer (L : Set G) := hcAL.2
  have hx3 : x ^ 3 = 1 := hA.prop.2 x hxA
  have hx2A : x ^ 2 ∈ A := pow_mem hxA 2
  have hx2K : x ^ 2 ∉ Subgroup.normalizer (K : Set G) := by
    intro h
    apply hxK
    have hx : x = (x ^ 2) ^ 2 := by
      calc x = x ^ 3 * x := by rw [hx3, one_mul]
        _ = (x ^ 2) ^ 2 := by group
    rw [hx]
    exact pow_mem h 2
  have h01 := commute_conj_of_not_mem_normalizer hL hK hKc (hcomA x hxA a ha) hxK
  have h02 := commute_conj_of_not_mem_normalizer hL hK hKc (hcomA _ hx2A a ha) hx2K
  have h12 : ∀ k ∈ K, ∀ k' ∈ K, (x * k * x⁻¹) * (x ^ 2 * k' * (x ^ 2)⁻¹) =
      (x ^ 2 * k' * (x ^ 2)⁻¹) * (x * k * x⁻¹) := by
    intro k hk k' hk'
    have h := h01 k hk k' hk'
    calc (x * k * x⁻¹) * (x ^ 2 * k' * (x ^ 2)⁻¹) = x * (k * (x * k' * x⁻¹)) * x⁻¹ := by
          simp only [sq]; group
      _ = x * ((x * k' * x⁻¹) * k) * x⁻¹ := by rw [h]
      _ = (x ^ 2 * k' * (x ^ 2)⁻¹) * (x * k * x⁻¹) := by simp only [sq]; group
  set Kx : Subgroup G := K.map (MulAut.conj x).toMonoidHom with hKx
  set Kxx : Subgroup G := K.map (MulAut.conj (x ^ 2)).toMonoidHom with hKxx
  have hcK : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le (fun k hk => (hK hk).1) hcL
  have haK : a ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK hk).2
  have hcKx := mem_centralizer_map_conj (hcomA c hcA x hxA) hcK
  have hcKxx := mem_centralizer_map_conj (hcomA c hcA _ hx2A) hcK
  have haKx := mem_centralizer_map_conj (hcomA a ha x hxA) haK
  have haKxx := mem_centralizer_map_conj (hcomA a ha _ hx2A) haK
  obtain ⟨e, heK, he3, k₀, hk₀, hek₀⟩ := exists_noncentral_three ht
  have heKx : e ∈ Subgroup.centralizer (Kx : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact (h01 e heK k hk).symm
  have heKxx : e ∈ Subgroup.centralizer (Kxx : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact (h02 e heK k hk).symm
  set e₁ : G := x * e * x⁻¹ with he₁
  set e₂ : G := x ^ 2 * e * (x ^ 2)⁻¹ with he₂
  have he₁Kxx : e₁ ∈ Subgroup.centralizer (Kxx : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact (h12 e heK k hk).symm
  have he₁3 : e₁ ^ 3 = 1 := by
    rw [he₁, ← MulAut.conj_apply, ← map_pow, he3, map_one]
  have he₂3 : e₂ ^ 3 = 1 := by
    rw [he₂, ← MulAut.conj_apply, ← map_pow, he3, map_one]
  have he₁Kx : e₁ ∈ Kx := ⟨e, heK, rfl⟩
  have he₂Kxx : e₂ ∈ Kxx := ⟨e, heK, rfl⟩
  have heC : e ∉ Subgroup.centralizer (K : Set G) := fun h =>
    hek₀ (Subgroup.mem_centralizer_iff.mp h k₀ hk₀).symm
  have he₁C : e₁ ∉ Subgroup.centralizer (Kx : Set G) := conj_not_mem_centralizer hk₀ hek₀
  have he₂C : e₂ ∉ Subgroup.centralizer (Kxx : Set G) := conj_not_mem_centralizer hk₀ hek₀
  have hcomm : ∀ {H : Subgroup G} {u v : G}, u ∈ Subgroup.centralizer (H : Set G) → v ∈ H →
      u ∈ Subgroup.centralizer ({v} : Set G) := fun hu hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu _ hv).symm
  have hc3 : c ^ 3 = 1 := hA.prop.2 c hcA
  have ha3 : a ^ 3 = 1 := hA.prop.2 a ha
  have hc1 : c ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc; norm_num at hc
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  have hS₀ := Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hc3) hac ha3
    (fun s hs => hcomA s (Subgroup.zpowers_le.mpr hcA hs) a ha)
  have hS₀C : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcK) (Subgroup.zpowers_le.mpr haK)
  have hS₁ := sup_zpowers_of_noncentral hS₀.1 hS₀C heC he3
    (sup_le (Subgroup.zpowers_le.mpr (hcomm hcK heK)) (Subgroup.zpowers_le.mpr (hcomm haK heK)))
  have hS₁C : Subgroup.zpowers c ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers e ≤
      Subgroup.centralizer (Kx : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hcKx) (Subgroup.zpowers_le.mpr haKx))
      (Subgroup.zpowers_le.mpr heKx)
  have hS₂ := sup_zpowers_of_noncentral hS₁.1 hS₁C he₁C he₁3
    (sup_le (sup_le (Subgroup.zpowers_le.mpr (hcomm hcKx he₁Kx))
      (Subgroup.zpowers_le.mpr (hcomm haKx he₁Kx))) (Subgroup.zpowers_le.mpr (hcomm heKx he₁Kx)))
  have hS₂C : Subgroup.zpowers c ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers e ⊔
      Subgroup.zpowers e₁ ≤ Subgroup.centralizer (Kxx : Set G) :=
    sup_le (sup_le (sup_le (Subgroup.zpowers_le.mpr hcKxx) (Subgroup.zpowers_le.mpr haKxx))
      (Subgroup.zpowers_le.mpr heKxx)) (Subgroup.zpowers_le.mpr he₁Kxx)
  have hS₃ := sup_zpowers_of_noncentral hS₂.1 hS₂C he₂C he₂3
    (sup_le (sup_le (sup_le (Subgroup.zpowers_le.mpr (hcomm hcKxx he₂Kxx))
      (Subgroup.zpowers_le.mpr (hcomm haKxx he₂Kxx))) (Subgroup.zpowers_le.mpr
        (hcomm heKxx he₂Kxx))) (Subgroup.zpowers_le.mpr (hcomm he₁Kxx he₂Kxx)))
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = Subgroup.zpowers c ⊔ Subgroup.zpowers a ⊔
      Subgroup.zpowers e ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := ⟨_, rfl⟩
  have hSel : CFSG.Assembly.IsElemAbelian 3 S := hS ▸ hS₃.1
  have hScard : Nat.card S = 243 := by
    rw [hS, hS₃.2, hS₂.2, hS₁.2, hS₀.2, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have haS : a ∈ S := hS ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))))
  have heS : e ∈ S := hS ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)))
  have he₁S : e₁ ∈ S := hS ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers e₁))
  have hE₀ := Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers ha3)
    (fun h => heC (Subgroup.zpowers_le.mpr haK h)) he3
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.zpowers_le.mpr (hcomm haK heK) hs))
  have hE := sup_zpowers_of_noncentral hE₀.1
    (sup_le (Subgroup.zpowers_le.mpr haKx) (Subgroup.zpowers_le.mpr heKx)) he₁C he₁3
    (sup_le (Subgroup.zpowers_le.mpr (hcomm haKx he₁Kx))
      (Subgroup.zpowers_le.mpr (hcomm heKx he₁Kx)))
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G,
      E = Subgroup.zpowers a ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers e₁ := ⟨_, rfl⟩
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := hEdef ▸ hE.1
  have hEcard : Nat.card E = 27 := by
    rw [hEdef, hE.2, hE₀.2, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  obtain ⟨t, htK, ht2⟩ := exists_two ht
  have ht₂K : x ^ 2 * t * (x ^ 2)⁻¹ ∈ Kxx := ⟨t, htK, rfl⟩
  have ht₂o : orderOf (x ^ 2 * t * (x ^ 2)⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
  have hEN : E ≤ Subgroup.normalizer
      ((Subgroup.zpowers (x ^ 2 * t * (x ^ 2)⁻¹) : Subgroup G) : Set G) := by
    have hEC : E ≤ Subgroup.centralizer
        ((Subgroup.zpowers (x ^ 2 * t * (x ^ 2)⁻¹) : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, hEdef]
      exact sup_le (sup_le (Subgroup.zpowers_le.mpr (hcomm haKxx ht₂K))
        (Subgroup.zpowers_le.mpr (hcomm heKxx ht₂K))) (Subgroup.zpowers_le.mpr
          (hcomm he₁Kxx ht₂K))
    exact hEC.trans (Subgroup.centralizer_le_normalizer _)
  have hne : Subgroup.zpowers (x ^ 2 * t * (x ^ 2)⁻¹) ≠ ⊥ := by
    intro h
    have h1 : x ^ 2 * t * (x ^ 2)⁻¹ ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at ht₂o
    norm_num at ht₂o
  have hp2 : IsPGroup 2 (Subgroup.zpowers (x ^ 2 * t * (x ^ 2)⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht₂o, pow_one])
  have hEmem : E ∈ partTwoE G := ⟨hEel, hEcard, _, hne, hp2, hEN⟩
  have hES : E ≤ S := by
    rw [hEdef]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr haS) (Subgroup.zpowers_le.mpr heS))
      (Subgroup.zpowers_le.mpr he₁S)
  obtain ⟨A₀, hSA₀, hA₀⟩ :=
    Finite.exists_le_maximal (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hSel
  have hA₀F : A₀ ∈ partTwoF G :=
    ⟨hA₀.prop, fun B hB hAB => le_antisymm (hA₀.2 hB hAB) hAB, E, hEmem, hES.trans hSA₀⟩
  have h1 := hF A₀ hA₀F
  have h2 : Nat.card S ≤ Nat.card A₀ := Subgroup.card_le_of_le hSA₀
  rw [hScard] at h2
  norm_num at h1
  omega

theorem exists_mem_not_mem_centralizer {G : Type} [Group G] [Finite G] {L A K : Subgroup G}
    {c a : G} (hcfg : Config419 G L A c a K) (ht : IsType419 K) :
    ∃ b ∈ A, b ∉ Subgroup.centralizer (K : Set G) := by
  obtain ⟨-, -, hA, -, -, -, -, -, -, -, -⟩ := hcfg
  by_contra hcon
  push Not at hcon
  obtain ⟨e, heK, he3, k, hk, hek⟩ := exists_noncentral_three ht
  have heC : e ∉ Subgroup.centralizer (K : Set G) := fun h =>
    hek (Subgroup.mem_centralizer_iff.mp h k hk).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heA : e ∉ A := fun h => heC (hcon e h)
  have hsup := Sec5.isElemAbelian_sup_zpowers hA.prop heA he3
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (hcon x hx) e heK).symm)
  exact heA (hA.2 hsup.1 le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)))

end Config

end Res419Two

open Res419Two

theorem k419E27_of_autThree
    (hK : K419AutThree) :
    K419E27 := by
  intro G _ _ L A c a K hcfg ht
  have hN := le_normalizer_of_config hcfg ht
  obtain ⟨b, hbA, hbC⟩ := exists_mem_not_mem_centralizer hcfg ht
  obtain ⟨-, -, hA, -, hAc, hc, ha, hac, hKle, -, -⟩ := hcfg
  obtain ⟨T, hTK, hT2, hbT, hTb⟩ := hK G K ht b (hN hbA) (hA.prop.2 b hbA) hbC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.prop.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcAL : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hcK : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le (fun k hk => (hKle hk).1) hcAL.2
  have haK : a ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKle hk).2
  have hc3 : c ^ 3 = 1 := hA.prop.2 c hcAL.1
  have hc1 : c ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc; norm_num at hc
  have hE₀ := Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hc3) hac (hA.prop.2 a ha)
    (fun s hs => hcomA s (Subgroup.zpowers_le.mpr hcAL.1 hs) a ha)
  have hE := sup_zpowers_of_noncentral hE₀.1
    (sup_le (Subgroup.zpowers_le.mpr hcK) (Subgroup.zpowers_le.mpr haK)) hbC (hA.prop.2 b hbA)
    (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomA c hcAL.1 b hbA)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hcomA a ha b hbA))))
  set E : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b with hEdef
  have hEcard : Nat.card E = 27 := by
    rw [hEdef, hE.2, hE₀.2, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hEA : E ≤ A :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hcAL.1) (Subgroup.zpowers_le.mpr ha))
      (Subgroup.zpowers_le.mpr hbA)
  have hCN : ∀ u ∈ Subgroup.centralizer (K : Set G), u ∈ Subgroup.normalizer (T : Set G) :=
    fun u hu => Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTK hu)
  refine ⟨E, hEA, ⟨hE.1, hEcard⟩, T, ⟨hTK.trans (fun z hz => (hKle hz).1),
    (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2, sup_le (sup_le
      (Subgroup.zpowers_le.mpr (hCN c hcK)) (Subgroup.zpowers_le.mpr (hCN a haK)))
      (Subgroup.zpowers_le.mpr hbT)⟩, fun hle => hTb fun t ht => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp (hle ht) b
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm

end CFSG.RankThree.PartTwo.Sec4
