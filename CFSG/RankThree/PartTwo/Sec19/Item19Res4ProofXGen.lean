module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase
public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def KS1917XGenFaithful :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X E : Subgroup G) (c : G),
    Group.IsPerfect X → IsQuasisimple (X ⧸ CFSG.pCore 2 X) →
    E ≤ Subgroup.normalizer (X : Set G) → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    c ∈ E →
    (∀ a ∈ E, (∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → a = 1) →
    ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ 2 < p ^ e ∧
        Sec4.IsoLThreePi (X ⧸ CFSG.pCore 2 X) p (3 * e) ∧ KFacts.InducesStdKind X c .field) ∨
      ∃ n : ℕ, 2 ≤ n ∧ CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ CFSG.pCore 2 X)
        .trialityD4 2 n ∧ Sec4.InducesOuterTheta c X) →
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X

namespace Item19Res4Proof

open TauCeti CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
open CFSG.LieType.SeitzGeneration

section Action

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quotAct_mk_eq_iff {X E : Subgroup G} (hEX : E ≤ Subgroup.normalizer (X : Set G)) (a : E)
    (x : X) :
    Step1910Proof.quotAct hEX a (x : X ⧸ CFSG.pCore 2 X) = (x : X ⧸ CFSG.pCore 2 X) ↔
      (x : G)⁻¹ * (a * x * (a : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨x', hx', hq⟩ := Step1910Proof.quotAct_mk hEX a x
  rw [hq, eq_comm, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
    Subgroup.coe_inv, hx']

omit [Finite G] in
theorem quotAct_eq_one_iff {X E : Subgroup G} (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (a : E) :
    Step1910Proof.quotAct hEX a = 1 ↔
      ∀ x ∈ X, x⁻¹ * (a * x * (a : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 X := by
  constructor
  · intro h x hx
    have h1 := congrArg (fun ψ : MulAut (X ⧸ CFSG.pCore 2 X) =>
      ψ ((⟨x, hx⟩ : X) : X ⧸ CFSG.pCore 2 X)) h
    simp only [MulAut.one_apply] at h1
    exact (quotAct_mk_eq_iff hEX a ⟨x, hx⟩).mp h1
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.one_apply]
    exact (quotAct_mk_eq_iff hEX a x).mpr (h x x.2)

omit [Finite G] in
theorem commutator_mem_pCoreOf_iff {X : Subgroup G} {a x : G} (hx : x ∈ X) :
    a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X ↔ x⁻¹ * (a * x * a⁻¹) ∈ CFSG.Open.pCoreOf 2 X := by
  have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.inv_mem hx)
  rw [Subgroup.mem_normalizer_iff.mp hN]
  have e : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹) := by group
  rw [e]

theorem quotAct_not_mem_range_conj {X E : Subgroup G}
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) {c : G} (hcE : c ∈ E)
    (hout : Sec4.InducesOuterTheta c X) :
    Step1910Proof.quotAct hEX ⟨c, hcE⟩ ∉
      (MulAut.conj : X ⧸ CFSG.pCore 2 X →* MulAut (X ⧸ CFSG.pCore 2 X)).range := by
  obtain ⟨hc, hnot⟩ := hout
  rintro ⟨y, hy⟩
  apply hnot
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hθ : CFSG.pCore 2 X ≤ aschbacherSolvableCore 3 X :=
    (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.2.2.2 2
      Nat.prime_two (by norm_num)
  refine ⟨(y₀ : X ⧸ aschbacherSolvableCore 3 X), ?_⟩
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 := congrArg (fun ψ : MulAut (X ⧸ CFSG.pCore 2 X) =>
    ψ (z : X ⧸ CFSG.pCore 2 X)) hy
  obtain ⟨z', hz', hq⟩ := Step1910Proof.quotAct_mk hEX ⟨c, hcE⟩ z
  simp only [MulAut.conj_apply] at h1
  rw [hq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at h1
  rw [MulAut.conj_apply, Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hzz : (Sec4.compAction X ⟨c, hc⟩ z : X) = z' := Subtype.ext (by rw [hz']; rfl)
  rw [hzz]
  exact hθ h1

omit [Finite G] in
theorem isElemAbelian_range_quotAct {X E : Subgroup G}
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (Step1910Proof.quotAct hEX).range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : MulAut (X ⧸ CFSG.pCore 2 X)) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, hE.1.is_comm.comm a b]
  · rintro _ ⟨a, rfl⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hE.2 a a.2)
    rw [← map_pow, ha3, map_one]

end Action

section Lift

variable {G : Type} [Group G] [Finite G]

theorem zpow_apply_eq_self {Y : Type*} [Group Y] {ψ : MulAut Y} {y : Y} (h : ψ y = y) (k : ℤ) :
    (ψ ^ k) y = y := by
  have hmem : ψ ∈ MulAction.stabilizer (MulAut Y) y := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have := (MulAction.stabilizer (MulAut Y) y).zpow_mem hmem k
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

theorem le_iSup_sup_of_closure_eq_top {X E : Subgroup G}
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) (hE3 : IsPGroup 3 E)
    (hEexp : ∀ e ∈ E, e ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hker : Nat.card (Step1910Proof.quotAct hEX).ker = 3)
    (hgen : Subgroup.closure (fixSet (Step1910Proof.quotAct hEX).range) = ⊤) :
    X ≤ (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := Step1910Proof.quotAct hEX with hρ
  set O := CFSG.Open.pCoreOf 2 X with hO
  set S := (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
    X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ O with hS
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hEO : E ≤ Subgroup.normalizer (O : Set G) :=
    hEX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hrange : Nat.card ρ.range = 9 := by
    have h1 := ρ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, hE27] at h1
    omega
  set T : Subgroup (X ⧸ CFSG.pCore 2 X) := (S.subgroupOf X).map (QuotientGroup.mk' _) with hT
  have hfixT : fixSet ρ.range ⊆ T := by
    rintro y ⟨ψ, ⟨a, rfl⟩, hψ1, hfix⟩
    set F₀ : Subgroup E := (Subgroup.zpowers (ρ a)).comap ρ with hF₀
    have ha3 : ρ a ^ 3 = 1 := by
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hEexp a a.2)
      rw [← map_pow, this, map_one]
    have hord : orderOf (ρ a) = 3 := orderOf_eq_prime ha3 hψ1
    have hz3 : Nat.card (Subgroup.zpowers (ρ a)) = 3 := by rw [Nat.card_zpowers, hord]
    have hzle : Subgroup.zpowers (ρ a) ≤ ρ.range := Subgroup.zpowers_le.mpr ⟨a, rfl⟩
    have hrel : (Subgroup.zpowers (ρ a)).relIndex ρ.range = 3 := by
      have h1 := ((Subgroup.zpowers (ρ a)).subgroupOf ρ.range).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, hz3, hrange] at h1
      rw [Subgroup.relIndex]
      omega
    have hF₀9 : Nat.card F₀ = 9 := by
      have h1 : Nat.card F₀ * ((Subgroup.zpowers (ρ a)).comap ρ).index = Nat.card E :=
        F₀.card_mul_index
      rw [Subgroup.index_comap, hrel, hE27] at h1
      omega
    set F : Subgroup G := F₀.map E.subtype with hF
    have hFE : F ≤ E := Subgroup.map_subtype_le F₀
    have hF9 : Nat.card F = 9 := by
      rw [hF, Subgroup.card_map_of_injective E.subtype_injective, hF₀9]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hFx : ∀ b ∈ F, (x : G)⁻¹ * (b * x * b⁻¹) ∈ O := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hb)
      have hbx : ρ b (x : X ⧸ CFSG.pCore 2 X) = x := by
        rw [← hk]
        exact zpow_apply_eq_self hfix k
      exact (quotAct_mk_eq_iff hEX b x).mp hbx
    obtain ⟨y₁, hy₁, hy₁F⟩ :=
      Step199Proof.exists_fixed_mem_coset (hE3.to_le hFE) hO3 (hFE.trans hEO) hFx
    have hy₁X : y₁ ∈ X := by
      have := X.mul_mem x.2 (hOX hy₁)
      simpa using this
    have hy₁S : y₁ ∈ S := by
      exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem ⟨F, hFE, hF9⟩
        ⟨hy₁X, Subgroup.mem_centralizer_iff.mpr fun b hb => hy₁F b hb⟩)
    refine ⟨⟨y₁, hy₁X⟩, Subgroup.mem_subgroupOf.mpr hy₁S, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
      Subgroup.coe_inv]
    have := O.inv_mem hy₁
    simpa using this
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hfixT
  intro x hx
  have hxT : ((⟨x, hx⟩ : X) : X ⧸ CFSG.pCore 2 X) ∈ T := by rw [hTtop]; trivial
  obtain ⟨s, hs, hsx⟩ := hxT
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
    Subgroup.coe_inv] at hsx
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have e : x = (s : G) * ((s : G)⁻¹ * x) := by group
  rw [e]
  exact S.mul_mem hsS (le_sup_right (a := ⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
    X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) hsx)

end Lift

end Item19Res4Proof

end CFSG.RankThree.PartTwo.Sec19
