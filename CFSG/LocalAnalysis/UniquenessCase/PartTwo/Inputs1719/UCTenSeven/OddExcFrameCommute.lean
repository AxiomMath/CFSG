module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35FrameExc
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.LieType.Chevalley.BorelStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.StandardType.TableBExcTwo
open CFSG.LieType.Steinberg.TwistedE6 (proj)
open CFSG.LieType.Steinberg.Exceptional (twistedE6Datum twistedE6Group)
open scoped MatrixGroups


private theorem excCommute_commutes_map_zpowers
    {K X : Type} [Group K] [Group X] {ι : Type} {A : ι → Subgroup K} {ψ : K →* X}
    {b : X} (hcomm : ∀ k, ∀ x ∈ (A k).map ψ, Commute x b) :
    ∀ k, Commutes ((A k).map ψ) (Subgroup.zpowers b) := by
  intro k u hu v hv
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← hz]
  exact (hcomm k (ψ a) (Subgroup.mem_map_of_mem ψ ha)).zpow_right z

private theorem excCommute_exists_conj_family
    {K X : Type} [Group K] [Group X] [Finite X]
    {q : ℕ} {ι : Type} {A : ι → Subgroup K} {ψ : K →* X}
    (hAfund : ∀ k, IsFundamentalOver q ((A k).map ψ))
    (hAcomm : ∀ i j, i ≠ j → Commutes ((A i).map ψ) ((A j).map ψ))
    (P : Sylow 2 X) :
    ∃ c : X, ∀ k, (A k).map ((MulAut.conj c).toMonoidHom.comp ψ) ∈
      F14.FunSet (fundPred q) X (P : Subgroup X) := by
  have hnorm : ∀ i j, (A j).map ψ ≤ Subgroup.normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) :=
        fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => hAcomm i j hij b hb a ha)
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred q)
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAfund hnorm P
  exact ⟨c, fun k => by simpa only [Subgroup.map_map] using hc k⟩

private theorem excCommute_commute_of_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] {x y : ModGL τ L}
    (hx : x ∈ torusGroup τ L) (hy : y ∈ torusGroup τ L) : x * y = y * x := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l hy

private theorem excCommute_baseChange_mem_torus
    {τ : Tag} (hτ : τ ≠ .G2) {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0)
    {y : adjointGroup τ (GaloisField p e)}
    (hc : ∀ j, ∀ x ∈ (rho (GaloisField p e) D j).range, Commute y x) :
    baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
        (y : ModGL τ (GaloisField p e)) ∈ torusGroup τ (AlgClosGF p e) := by
  let F := GaloisField p e
  let L := AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff L p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp2 h2
  refine mem_torusGroup_of_commutes_rootFrame D hweighted
    (baseChangeGL_mem_adjointGroup ι y.2) ?_
  intro j x hx
  refine commute_rootRankOne_baseChange_of_ne_g2 hτ ι h2 (D.isRoot j) ?_ x hx
  intro x' hx'
  obtain ⟨A, rfl⟩ := hx'
  exact congrArg (fun z : adjointGroup τ F => (z : ModGL τ F))
    (hc j (rho F D j A) ⟨A, rfl⟩)

private theorem excCommute_of_commutator_mem_center
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    {ι : Type} (i₀ : ι) (A : ι → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hAc : ∀ i j, i ≠ j → Commutes (A i) (A j))
    (hm : ∀ a b : (modelUniv t n p e hp.out).K, (∀ k, ∀ x ∈ A k, Commute x a) →
      (∀ k, ∀ x ∈ A k, Commute x b) →
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (modelUniv t n p e hp.out).K)
    (P : Sylow 2 X) {y₁ y₂ : X}
    (h₁ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      y₁ ∈ centralizer (K : Set X))
    (h₂ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      y₂ ∈ centralizer (K : Set X)) :
    y₁ * y₂ = y₂ * y₁ := by
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have hAfund : ∀ k, IsFundamentalOver (p ^ e) ((A k).map ψ) := fun k =>
    ⟨t, n, p, e, hp.out, hp2, rfl, hfund, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hAcomm : ∀ i j, i ≠ j → Commutes ((A i).map ψ) ((A j).map ψ) :=
    fun i j hij => CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hAc i j hij)
  obtain ⟨c, hc⟩ := excCommute_exists_conj_family hAfund hAcomm P
  let ψc : (modelUniv t n p e hp.out).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) :=
    fun k => by simpa only [ψc] using hc k
  have hZ : center X = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple
      (exists_noncommuting_of_isFundamentalOver (hc' i₀).1)
  obtain ⟨b₁, hb₁⟩ := hψc y₁
  obtain ⟨b₂, hb₂⟩ := hψc y₂
  have hcomm₁ : ∀ k, ∀ x ∈ (A k).map ψc, Commute x y₁ :=
    fun k x hx => Subgroup.mem_centralizer_iff.mp (h₁ _ (hc' k)) x hx
  have hcomm₂ : ∀ k, ∀ x ∈ (A k).map ψc, Commute x y₂ :=
    fun k x hx => Subgroup.mem_centralizer_iff.mp (h₂ _ (hc' k)) x hx
  have hcommMap₁ := excCommute_commutes_map_zpowers hcomm₁
  have hcommMap₂ := excCommute_commutes_map_zpowers hcomm₂
  have hcommK₁ : ∀ k, ∀ x ∈ A k, Commute x b₁ := by
    intro k x hx
    have hk : Commutes (A k) (Subgroup.zpowers b₁) := by
      apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC (hA k)
      rw [MonoidHom.map_zpowers, hb₁]
      exact hcommMap₁ k
    exact hk x hx b₁ (Subgroup.mem_zpowers b₁)
  have hcommK₂ : ∀ k, ∀ x ∈ A k, Commute x b₂ := by
    intro k x hx
    have hk : Commutes (A k) (Subgroup.zpowers b₂) := by
      apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC (hA k)
      rw [MonoidHom.map_zpowers, hb₂]
      exact hcommMap₂ k
    exact hk x hx b₂ (Subgroup.mem_zpowers b₂)
  have hzX : ψc (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) ∈ Subgroup.center X :=
    Subgroup.map_center_le_center hψc
      (Subgroup.mem_map_of_mem ψc (hm b₁ b₂ hcommK₁ hcommK₂))
  rw [hZ] at hzX
  have htriv : ψc (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) = 1 := Subgroup.mem_bot.mp hzX
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hb₁, hb₂] at htriv
  refine mul_inv_eq_one.mp ?_
  rw [mul_inv_rev, ← mul_assoc]
  exact htriv

private theorem excCommute_of_rootFrame_model
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] {τ : Tag} (hτ : τ ≠ .G2)
    (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0)
    (π : (modelUniv t n p e hp.out).K →* adjointGroup τ (GaloisField p e))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (A : Fin (d + 1) → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (A k).map π = (rho (GaloisField p e) D k).range)
    (P : Sylow 2 X) {y₁ y₂ : X}
    (h₁ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      y₁ ∈ centralizer (K : Set X))
    (h₂ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      y₂ ∈ centralizer (K : Set X)) :
    y₁ * y₂ = y₂ * y₁ := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  let F := GaloisField p e
  let L := AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 hfund hadm π hπker (hA i).1
    rw [(hA i).2, (hA j).2]
    rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
    exact commute_rho D hij B C
  refine excCommute_of_commutator_mem_center hp2 hfund hadm hX 0 A (fun k => (hA k).1) hAc ?_
    P h₁ h₂
  intro a b ha hb
  have hcommA : ∀ k, ∀ x ∈ (rho F D k).range, Commute (π a) x := by
    intro k x hx
    rw [← (hA k).2] at hx
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp hx
    exact ((ha k a' ha').map π).symm
  have hcommB : ∀ k, ∀ x ∈ (rho F D k).range, Commute (π b) x := by
    intro k x hx
    rw [← (hA k).2] at hx
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hx
    exact ((hb k b' hb').map π).symm
  have hTa : baseChangeGL ι (π a : ModGL τ F) ∈ torusGroup τ L :=
    excCommute_baseChange_mem_torus hτ hp2 D hweighted hcommA
  have hTb : baseChangeGL ι (π b : ModGL τ F) ∈ torusGroup τ L :=
    excCommute_baseChange_mem_torus hτ hp2 D hweighted hcommB
  have hT := excCommute_commute_of_mem_torusGroup hTa hTb
  have hcommF : (π a : ModGL τ F) * (π b : ModGL τ F) =
      (π b : ModGL τ F) * (π a : ModGL τ F) :=
    baseChangeGL_injective ι (by rw [map_mul, map_mul]; exact hT)
  have hπcomm : π a * π b = π b * π a := Subtype.ext hcommF
  apply hπker
  rw [MonoidHom.mem_ker]
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπcomm]
  group

theorem commute_of_mem_centralizer_funSet_e6 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .E6 0 p e) (P : Sylow 2 X) {y₁ y₂ : X}
    (h₁ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₁ ∈ centralizer (K : Set X))
    (h₂ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₂ ∈ centralizer (K : Set X)) :
    y₁ * y₂ = y₂ * y₁ := by
  let F := GaloisField p e
  let D : OrthFrame .E6 3 := CFSG.LieType.SeitzGeneration.frameE6
  let A : Fin 4 → Subgroup (modelUniv .E6 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (CFSG.LieType.Steinberg.Minuscule.e6Datum F) (D.root k)
  let π : (modelUniv .E6 0 p e hp.out).K →* adjointGroup .E6 F :=
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny F
  have hπker : π.ker ≤ Subgroup.center (modelUniv .E6 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center F
  have hstd : ∀ β, IsRoot .E6 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.ClassicalInvolution.ModelFacts.e6AdjDatum F) β =
        (rootRankOneGroup .E6 F β).subgroupOf (adjointGroup .E6 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e6_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e6Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π =
          CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (CFSG.ClassicalInvolution.ModelFacts.e6AdjDatum F) (D.root k) :=
        map_stdRankOne_e6_root (D.isRoot k)
      rw [hmap, hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact excCommute_of_rootFrame_model (τ := .E6) (by decide) hp2 (by trivial)
    hadm hX D weighted_kernel_all_frameE6 π hπker A hA P h₁ h₂

theorem commute_of_mem_centralizer_funSet_e7 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E7 0 p e)
    (hX : CFSG.Blueprint.LieModel X .E7 0 p e) (P : Sylow 2 X) {y₁ y₂ : X}
    (h₁ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₁ ∈ centralizer (K : Set X))
    (h₂ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₂ ∈ centralizer (K : Set X)) :
    y₁ * y₂ = y₂ * y₁ := by
  let F := GaloisField p e
  let D : OrthFrame .E7 6 := frameE7
  let A : Fin 7 → Subgroup (modelUniv .E7 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (CFSG.LieType.Steinberg.Minuscule.e7Datum F) (D.root k)
  let π : (modelUniv .E7 0 p e hp.out).K →* adjointGroup .E7 F :=
    CFSG.LieType.Steinberg.Isogeny.e7Isogeny F
  have hπker : π.ker ≤ Subgroup.center (modelUniv .E7 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e7Isogeny_ker_le_center F
  have hstd : ∀ β, IsRoot .E7 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.ClassicalInvolution.ModelFacts.e7AdjDatum F) β =
        (rootRankOneGroup .E7 F β).subgroupOf (adjointGroup .E7 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e7_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e7Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π =
          CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (CFSG.ClassicalInvolution.ModelFacts.e7AdjDatum F) (D.root k) :=
        map_stdRankOne_e7_root (D.isRoot k)
      rw [hmap, hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact excCommute_of_rootFrame_model (τ := .E7) (by decide) hp2 (by trivial)
    hadm hX D weighted_kernel_all_frameE7 π hπker A hA P h₁ h₂

theorem commute_of_mem_centralizer_funSet_e8 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E8 0 p e)
    (hX : CFSG.Blueprint.LieModel X .E8 0 p e) (P : Sylow 2 X) {y₁ y₂ : X}
    (h₁ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₁ ∈ centralizer (K : Set X))
    (h₂ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₂ ∈ centralizer (K : Set X)) :
    y₁ * y₂ = y₂ * y₁ := by
  let F := GaloisField p e
  let D : OrthFrame .E8 7 := frameE8
  let A : Fin 8 → Subgroup (modelUniv .E8 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (CFSG.LieType.Steinberg.Adjoint.e8Datum F) (D.root k)
  let π : (modelUniv .E8 0 p e hp.out).K →* adjointGroup .E8 F := MonoidHom.id _
  have hπker : π.ker ≤ Subgroup.center (modelUniv .E8 0 p e hp.out).K := by
    intro x hx
    have hx1 : x = 1 := MonoidHom.mem_ker.mp hx
    rw [hx1]
    exact one_mem _
  have hstd : ∀ β, IsRoot .E8 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.LieType.Steinberg.Adjoint.e8Datum F) β =
        (rootRankOneGroup .E8 F β).subgroupOf (adjointGroup .E8 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e8_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E8 (modelUniv .E8 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e8Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π = A k := Subgroup.map_id _
      rw [hmap]
      change CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.LieType.Steinberg.Adjoint.e8Datum F) (D.root k) = _
      rw [hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact excCommute_of_rootFrame_model (τ := .E8) (by decide) hp2 (by trivial)
    hadm hX D weighted_kernel_all_frameE8 π hπker A hA P h₁ h₂

private theorem excCommute_twE6_commutator_mem_center {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) {a b : twistedE6Group p e}
    (ha : ∀ k : Fin 4, ∀ x ∈ CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (twistedE6Datum p e) (proj (CFSG.LieType.SeitzGeneration.frameE6Root k)), Commute x a)
    (hb : ∀ k : Fin 4, ∀ x ∈ CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (twistedE6Datum p e) (proj (CFSG.LieType.SeitzGeneration.frameE6Root k)), Commute x b) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (twistedE6Group p e) := by
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let Φ := CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e
  have hcommΦa : ∀ k : Fin 4, ∀ x ∈ rootRankOneGroup .E6 L
      (CFSG.LieType.SeitzGeneration.frameE6Root k), Commute (Φ a) x := by
    intro k
    apply commute_rootRankOne_of_commutes_phi_stdRankTwE6 hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot k) (rho_frameE6Root k)
    intro x hx
    exact ((ha k x hx).map Φ).symm
  have hcommΦb : ∀ k : Fin 4, ∀ x ∈ rootRankOneGroup .E6 L
      (CFSG.LieType.SeitzGeneration.frameE6Root k), Commute (Φ b) x := by
    intro k
    apply commute_rootRankOne_of_commutes_phi_stdRankTwE6 hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot k) (rho_frameE6Root k)
    intro x hx
    exact ((hb k x hx).map Φ).symm
  have hTa : Φ a ∈ torusGroup .E6 L :=
    mem_torusGroup_of_commutes_rootFrame CFSG.LieType.SeitzGeneration.frameE6
      weighted_kernel_all_frameE6
      (CFSG.LieType.AlgebraicGroups.mem_fixedPointsIn.mp
        (CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi_mem_fixedPointsIn
          p e hp2 he a)).1 hcommΦa
  have hTb : Φ b ∈ torusGroup .E6 L :=
    mem_torusGroup_of_commutes_rootFrame CFSG.LieType.SeitzGeneration.frameE6
      weighted_kernel_all_frameE6
      (CFSG.LieType.AlgebraicGroups.mem_fixedPointsIn.mp
        (CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi_mem_fixedPointsIn
          p e hp2 he b)).1 hcommΦb
  have hcommT : Φ a * Φ b = Φ b * Φ a := excCommute_commute_of_mem_torusGroup hTa hTb
  have h : Φ a * Φ b * (Φ a)⁻¹ * (Φ b)⁻¹ = 1 := by
    rw [hcommT]
    group
  apply CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center p e L
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact h

theorem commute_of_mem_centralizer_funSet_twistedE6 {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p e) (P : Sylow 2 X) {y₁ y₂ : X}
    (h₁ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₁ ∈ centralizer (K : Set X))
    (h₂ : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), y₂ ∈ centralizer (K : Set X)) :
    y₁ * y₂ = y₂ * y₁ := by
  have he : 1 ≤ e := hadm.2.1
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let A : Fin 4 → Subgroup (modelUniv .twistedE6 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne (twistedE6Datum p e)
      (proj (CFSG.LieType.SeitzGeneration.frameE6Root k))
  have hA : ∀ k, A k ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p e hp.out).D := by
    intro k
    exact CFSG.ClassicalInvolution.ModelFacts.longestFundamental_subset .twistedE6 _
      (stdRank_mem_longestFundamental_TwE6 (CFSG.LieType.SeitzGeneration.frameE6.isRoot k)
        (rho_frameE6Root k))
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 (t := .twistedE6) (by trivial) hadm
      (CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e)
      (CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center p e L) (hA i)
    intro x hx y hy
    obtain ⟨B, rfl⟩ := phi_map_stdRank_le hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot i) (rho_frameE6Root i) hx
    obtain ⟨C, rfl⟩ := phi_map_stdRank_le hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot j) (rho_frameE6Root j) hy
    exact congrArg (fun x : adjointGroup .E6 L => (x : ModGL .E6 L))
      (commute_rho CFSG.LieType.SeitzGeneration.frameE6 hij B C)
  refine excCommute_of_commutator_mem_center hp2 (by trivial) hadm hX 0 A hA hAc ?_ P h₁ h₂
  exact fun a b ha hb => excCommute_twE6_commutator_mem_center hp2 he ha hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

end
