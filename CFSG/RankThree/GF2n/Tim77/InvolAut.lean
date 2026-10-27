module

public import CFSG.RankThree.GF2n.Tim77.InvolAutDefs
public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.T75I.CenX1
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.RankThree.S4Free.Stellmacher24Sz
public import CFSG.RankThree.S4Free.StellmacherSzSylow
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.LieType.Ree.SuzukiPerfect
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
public import CFSG.Blueprint.SourceExceptionalModels
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2Layer
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.WeakClosure81.TenFive
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.S4Free.Statement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem sec34_le_of_normal_two [Finite G] {X M N : Subgroup G} [(M.subgroupOf X).Normal]
    (hO2 : ∀ K : Subgroup (↥X ⧸ M.subgroupOf X), K.Normal → IsPGroup 2 K → K = ⊥)
    (hNX : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hNle : N ≤ X) (hN2 : ∀ n ∈ N, n * n = 1) :
    N ≤ M := by
  have hNn : (N.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hNX g.1 g.2 n hn
      simpa using this⟩
  have hKn : ((N.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have hKp : IsPGroup 2 ((N.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    have hy2 : y * y = 1 := Subtype.ext (hN2 y.1 (Subgroup.mem_subgroupOf.mp hy))
    have hy1 : y ^ 2 = 1 := by rw [sq]; exact hy2
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hy1, map_one]
  intro n hn
  have hnX : n ∈ X := hNle hn
  have hmem : QuotientGroup.mk' (M.subgroupOf X) (⟨n, hnX⟩ : ↥X) ∈
      (N.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
  rw [hO2 _ hKn hKp, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem)

theorem invAut_inv_mul_mem {X M : Subgroup G} [(M.subgroupOf X).Normal] (hMX : M ≤ X) {m x : G}
    (hm : m ∈ M) (hx : x ∈ X) : x⁻¹ * m * x ∈ M := by
  have hc := (‹(M.subgroupOf X).Normal›).conj_mem ⟨m, hMX hm⟩
    (Subgroup.mem_subgroupOf.mpr hm) ⟨x, hx⟩⁻¹
  have hc' := Subgroup.mem_subgroupOf.mp hc
  simpa using hc'

theorem invAut_conj_inv_mem {M : Subgroup G} {u : G} (hMu : conjSubgroup u M = M) {m : G}
    (hm : m ∈ M) : u⁻¹ * m * u ∈ M := by
  have h := (Subgroup.mem_normalizer_iff.mp
    (Subgroup.inv_mem _ (mem_normalizer_of_conjSubgroup_eq hMu)) m).mp hm
  rwa [inv_inv] at h

theorem invAut_conj_mem {M : Subgroup G} {u : G} (hMu : conjSubgroup u M = M) {m : G}
    (hm : m ∈ M) : u * m * u⁻¹ ∈ M :=
  (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_conjSubgroup_eq hMu) m).mp hm

theorem invAut_conj_eq_of_normalizes [Finite G] {X M : Subgroup G}
    [(M.subgroupOf X).Normal]
    (hO2 : ∀ K : Subgroup (↥X ⧸ M.subgroupOf X), K.Normal → IsPGroup 2 K → K = ⊥)
    (hMX : M ≤ X) (hMe : ∀ m ∈ M, m * m = 1) {u : G} (hu : conjSubgroup u X = X) :
    conjSubgroup u M = M := by
  have hXiff : ∀ z : G, z ∈ X ↔ u⁻¹ * z * u ∈ X := fun z =>
    mem_iff_conj_of_conjSubgroup_eq hu z
  apply conjSubgroup_eq_of_le
  apply sec34_le_of_normal_two (X := X) hO2
  · intro x hx n hn
    rw [mem_conjSubgroup] at hn ⊢
    have hx' : u⁻¹ * x * u ∈ X := (hXiff x).1 hx
    have hn' : (⟨u⁻¹ * n * u, hMX hn⟩ : ↥X) ∈ M.subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hn
    have hc := (‹(M.subgroupOf X).Normal›).conj_mem _ hn' ⟨u⁻¹ * x * u, hx'⟩
    have e : u⁻¹ * (x * n * x⁻¹) * u = (u⁻¹ * x * u) * (u⁻¹ * n * u) * (u⁻¹ * x * u)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_subgroupOf.mp hc
  · intro n hn
    rw [mem_conjSubgroup] at hn
    exact (hXiff n).2 (hMX hn)
  · intro n hn
    rw [mem_conjSubgroup] at hn
    have e : n * n = u * ((u⁻¹ * n * u) * (u⁻¹ * n * u)) * u⁻¹ := by group
    rw [e, hMe _ hn, mul_one, mul_inv_cancel]

theorem invAut_quot_mul_self {X M : Subgroup G} [(M.subgroupOf X).Normal] {u : G}
    (hu : conjSubgroup u X = X) (hMu : conjSubgroup u M = M)
    (hsq : ∀ x ∈ X, (u * u)⁻¹ * x⁻¹ * (u * u) * x ∈ M) :
    (quotConjAut X M u hu hMu : MulAut (↥X ⧸ M.subgroupOf X)) *
      (quotConjAut X M u hu hMu : MulAut (↥X ⧸ M.subgroupOf X)) = 1 := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  show quotConjAut X M u hu hMu (quotConjAut X M u hu hMu (QuotientGroup.mk x)) =
    QuotientGroup.mk x
  rw [quotConjAut_mk, quotConjAut_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (u * (u * (x : G) * u⁻¹) * u⁻¹)⁻¹ * (x : G) =
      (u * (u * ((u * u)⁻¹ * (x : G)⁻¹ * (u * u) * (x : G)) * u⁻¹) * u⁻¹)⁻¹ := by
    group
  show (u * (u * (x : G) * u⁻¹) * u⁻¹)⁻¹ * (x : G) ∈ M
  rw [e]
  exact M.inv_mem (invAut_conj_mem hMu (invAut_conj_mem hMu (hsq (x : G) x.2)))

theorem invAut_lift {X M : Subgroup G} [(M.subgroupOf X).Normal] {u : G}
    (hu : conjSubgroup u X = X) (hMu : conjSubgroup u M = M) {x₀ : G} (hx₀ : x₀ ∈ X)
    (hx₀2 : x₀ * x₀ = 1)
    (hσ : ∀ y : ↥X, quotConjAut X M u hu hMu (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨x₀, hx₀⟩ * QuotientGroup.mk y * (QuotientGroup.mk ⟨x₀, hx₀⟩)⁻¹) :
    ∀ x ∈ X, (x₀ * u)⁻¹ * x⁻¹ * (x₀ * u) * x ∈ M := by
  intro x hx
  have h1 := hσ ⟨x, hx⟩
  rw [quotConjAut_mk] at h1
  simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at h1
  have hm : (u * x * u⁻¹)⁻¹ * (x₀ * x * x₀⁻¹) ∈ M :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
  have hx0 : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hx₀2
  have e : (x₀ * u)⁻¹ * x⁻¹ * (x₀ * u) * x = u⁻¹ * ((u * x * u⁻¹)⁻¹ * (x₀ * x * x₀⁻¹))⁻¹ * u := by
    simp only [mul_inv_rev, inv_inv, hx0]
    group
  rw [e]
  exact invAut_conj_inv_mem hMu (M.inv_mem hm)

theorem invAut_inner_of_isL2Pair {X : Type} [Group X] {S : Subgroup X} {q : ℕ}
    (hL : IsL2Pair X S q) (σ : MulAut X) (hfix : ∀ y ∈ S, σ y = y) {g : X}
    (hg : conjSubgroup g S ≠ S) : ∃ s ∈ S, ∀ z : X, σ z = s * z * s⁻¹ := by
  have hmapS : S.map σ.toMonoidHom = S := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hfix z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, hfix y hy]⟩
  have hσg : conjSubgroup (σ g) S ≠ S := by
    intro h
    apply hg
    apply Subgroup.map_injective (f := σ.toMonoidHom) σ.injective
    rw [map_conjSubgroup_mulEquiv σ g S, hmapS, h]
  obtain ⟨s, hs, hgs⟩ := hL.exists_mem_conj_eq hg hσg
  have hKσ : (conjSubgroup g S).map σ.toMonoidHom = conjSubgroup s (conjSubgroup g S) := by
    rw [map_conjSubgroup_mulEquiv σ g S, hmapS, hgs]
  have hmemσ : ∀ z : X, σ z ∈ conjSubgroup s (conjSubgroup g S) ↔ z ∈ conjSubgroup g S := by
    intro z
    rw [← hKσ]
    exact Subgroup.mem_map_iff_mem (f := σ.toMonoidHom) σ.injective
  obtain ⟨φ, hφz⟩ : ∃ φ : X ≃* X, ∀ z, φ z = s⁻¹ * σ z * s :=
    ⟨σ.trans (MulAut.conj s⁻¹), fun z => by simp [MulAut.conj_apply]⟩
  have hφK : ∀ z : X, φ z ∈ conjSubgroup g S ↔ z ∈ conjSubgroup g S := by
    intro z
    have h1 : σ z ∈ conjSubgroup s (conjSubgroup g S) ↔
        s⁻¹ * σ z * s ∈ conjSubgroup g S := mem_conjSubgroup
    rw [hφz, ← hmemσ z]
    exact h1.symm
  have hmapφ : (conjSubgroup g S).map φ.toMonoidHom = conjSubgroup g S := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hφK z).mpr hz
    · intro hy
      refine ⟨φ.symm y, (hφK (φ.symm y)).mp ?_, φ.apply_symm_apply y⟩
      rw [MulEquiv.apply_symm_apply]
      exact hy
  have hfixφ : ∀ y ∈ S, φ y = y := by
    intro y hy
    rw [hφz, hfix y hy]
    have hc : s * y = y * s := elemAbelian_mul_comm hL.isElemAbelian hs hy
    calc s⁻¹ * y * s = s⁻¹ * (y * s) := by group
      _ = s⁻¹ * (s * y) := by rw [← hc]
      _ = y := by group
  have hid := CFSG.CGT.T75I.eq_refl_of_fix_of_map_conj hL φ hfixφ hg hmapφ
  refine ⟨s, hs, fun z => ?_⟩
  have hz : φ z = z := by rw [hid]; rfl
  rw [hφz] at hz
  calc σ z = s * (s⁻¹ * σ z * s) * s⁻¹ := by group
    _ = s * z * s⁻¹ := by rw [hz]

theorem invAut_inner_of_suzuki {X : Type} [Group X] [Finite X]
    {a : ℕ} (ha : 1 ≤ a) (e : X ≃* Sz a) (σ : MulAut X) (hσ2 : σ * σ = 1) {S : Subgroup X}
    (hS : IsElemAbelian 2 S) (hcard : Nat.card S = 2 ^ (2 * a + 1))
    (hfix : ∀ y ∈ S, σ y = y) : ∃ s ∈ S, ∀ z : X, σ z = s * z * s⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover.exists_eq_conj_of_suzuki ha e σ hσ2
  obtain ⟨P, hSP⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e hS hcard
  obtain ⟨e₁⟩ :=
    CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hKc : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  let e' : X ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)) := e.trans e₁
  have hSne : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have h1 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨⟨t, htS⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hot : orderOf t = 2 := orderOf_eq_prime (hS.2 t htS) ht1'
  have htP : t ∈ (P : Subgroup X) := by
    have h := htS
    rw [hSP] at h
    exact (Subgroup.mem_inf.mp h).1
  have hC : centralizer ({t} : Set X) = (P : Subgroup X) :=
    CFSG.RankThree.S4Free.Suzuki.centralizer_eq_sylow_of_mulEquiv hKc e' P hot htP
  have hbt : b * t = t * b := by
    have h1 := hfix t htS
    rw [hb, MulAut.conj_apply] at h1
    calc b * t = (b * t * b⁻¹) * b := by group
      _ = t * b := by rw [h1]
  have hbP : b ∈ (P : Subgroup X) := by
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hbt.symm
  have hcc : ∀ g : X, (b * b) * g = g * (b * b) := by
    intro g
    have h1 : σ (σ g) = g := by
      have h2 := congrArg (fun f : MulAut X => f g) hσ2
      exact h2
    rw [hb, MulAut.conj_apply, MulAut.conj_apply] at h1
    calc (b * b) * g = (b * (b * g * b⁻¹) * b⁻¹) * (b * b) := by group
      _ = g * (b * b) := by rw [h1]
  have hcenS : Subgroup.center (CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1))) = ⊥ := by
    obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hKc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)))) with h | h
    · exact h
    · have h1 := (CFSG.LieType.Ree.suzuki_perfect ha hKc).1
      rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
      exact absurd h1 bot_ne_top
  have hbb : b * b = 1 := by
    have hz : e' (b * b) ∈
        Subgroup.center (CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e'.surjective g
      rw [← map_mul, ← map_mul, hcc y]
    rw [hcenS, Subgroup.mem_bot] at hz
    exact e'.injective (hz.trans (map_one e').symm)
  have hbb2 : b ^ 2 = 1 := by rw [sq]; exact hbb
  have hbC : b ∈ centralizer ((P : Subgroup X) : Set X) :=
    CFSG.RankThree.S4Free.Suzuki.mem_centralizer_of_sq_eq_one hKc e' P hbP hbb2
  refine ⟨b, ?_, fun z => ?_⟩
  · rw [hSP]
    exact Subgroup.mem_inf.mpr ⟨hbP, hbC⟩
  · rw [hb, MulAut.conj_apply]

theorem sec34_exists_k [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M) :
    ∃ k ∈ A ⊔ Ab, Lb = conjSubgroup k L := by
  obtain ⟨k, hk, hAk⟩ := S.exists_conj_eq
  have hne : conjSubgroup k A ≠ A := by
    rw [← hAk]; exact S.Ab_ne
  refine ⟨k, hk, ?_⟩
  rw [S.hLb, hAk]
  exact (S.setup_conj hk hne).hLb.symm

theorem prop24Inner_holds :
    Prop24InnerStatement := by
  intro G _ _ A Ab L Lb M S hrel u hu hC hsq
  obtain ⟨hN, hO2, hmod⟩ := S.tim77_2_4_one CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  haveI := hN
  have hMe : ∀ m ∈ M, m * m = 1 := fun m hm => by
    rw [← sq]
    exact S.isElemAbelian_M.2 m hm
  have hMu : conjSubgroup u M = M := invAut_conj_eq_of_normalizes hO2 S.M_le_X hMe hu
  have hfix : ∀ y ∈ (A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))),
      quotConjAut (A ⊔ Ab) M u hu hMu y = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have hux : u * (x : G) * u⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_iff.mp hC (x : G) hxA, mul_inv_cancel_right]
    show quotConjAut (A ⊔ Ab) M u hu hMu (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [quotConjAut_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext hux)
  have hC' : ∃ s ∈ (A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))),
      ∀ z, quotConjAut (A ⊔ Ab) M u hu hMu z = s * z * s⁻¹ := by
    rcases hmod with ⟨f, hf, hrelf, ⟨e⟩⟩ | ⟨a, ha, hrela, ⟨e⟩⟩ | ⟨m, hm, h3, hrelm, ⟨e⟩⟩
    ·
      have hS := S.strongWC_image
      have hT0 := S.image_ne_bot
      obtain ⟨P, hTP⟩ := (isPGroup_of_strongWC hS).exists_le_sylow
      have hL2 := IsL2Pair.of_psl_sylow (by omega : f ≠ 0) ⟨e⟩ P
      have hTeq := hL2.eq_of_isWC hTP hT0 hS.isWC
      rw [← hTeq] at hL2
      obtain ⟨b, hbAb, hbL⟩ : ∃ b ∈ Ab, b ∉ Lb := by
        by_contra hcon
        exact S.Lb_ne (le_antisymm S.Lb_le fun b hb => by
          by_contra hbL
          exact hcon ⟨b, hb, hbL⟩)
      obtain ⟨x₀, hx₀⟩ := S.exists_image_conj
      have hg : conjSubgroup (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) x₀)
          ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))) ≠
          (A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) := by
        intro h
        have hmem' : QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨b, le_sup_right (a := A) hbAb⟩ ∈
            (Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbAb)
        rw [hx₀, h] at hmem'
        exact S.mk_not_mem_image hbAb hbL hmem'
      exact invAut_inner_of_isL2Pair hL2 (quotConjAut (A ⊔ Ab) M u hu hMu) hfix hg
    ·
      have hcard : Nat.card ((A.subgroupOf (A ⊔ Ab)).map
          (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))) = 2 ^ (2 * a + 1) := by
        rw [← S.relIndex_eq_card_image]
        exact hrela
      have hel : IsElemAbelian 2 ((A.subgroupOf (A ⊔ Ab)).map
          (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))) :=
        isElemAbelian_map' (isElemAbelian_subgroupOf S.elem _) _
      have hσ2 := invAut_quot_mul_self hu hMu hsq
      exact invAut_inner_of_suzuki ha e (quotConjAut (A ⊔ Ab) M u hu hMu) hσ2 hel hcard hfix
    · exfalso
      omega
  obtain ⟨s, hs, hσ⟩ := hC'
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hs
  have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
  refine ⟨(x : G), hxA, invAut_lift hu hMu x.2 (S.sq_A hxA) (fun y => ?_)⟩
  exact hσ (QuotientGroup.mk y)

end CFSG.RankThree.GF2n.Tim77
