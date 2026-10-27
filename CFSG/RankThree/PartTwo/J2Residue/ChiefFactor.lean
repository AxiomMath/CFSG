module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ChiefFactorScalar
import CFSG.GroupTheory.PerfectChiefStability
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.LieType.BorelTits.Basic
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open scoped commutatorElement

private theorem le_pCore_of_isPGroup_of_le_fittingSubgroup {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {D : Subgroup H} (hD : IsPGroup p D)
    (hDF : D ≤ CFSG.fittingSubgroup H) : D ≤ CFSG.pCore p H := by
  set F : Subgroup H := CFSG.fittingSubgroup H with hF
  have hD' : IsPGroup p (D.subgroupOf F) := hD.comap_subtype
  obtain ⟨S, hS⟩ := hD'.exists_le_sylow
  have hSn : (S : Subgroup F).Normal := inferInstance
  have hSc : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S hSn
  have hmapn : ((S : Subgroup F).map F.subtype).Normal := inferInstance
  have hle : (S : Subgroup F).map F.subtype ≤ CFSG.pCore p H :=
    le_sSup ⟨hmapn, S.isPGroup'.map _⟩
  intro x hx
  exact hle ⟨⟨x, hDF hx⟩, hS hx, rfl⟩

private theorem exists_prime_not_le_centralizer_pCoreOf {G : Type*} [Group G] [Finite G]
    {Θ U : Subgroup G} (hs : Group.IsSolvable ↥Θ) (h3 : ¬ 3 ∣ Nat.card Θ)
    (hO2 : CFSG.pCore 2 ↥Θ = ⊥) (hUΘ : U ≤ Θ) (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧
      ¬ U ≤ Subgroup.centralizer (CFSG.Open.pCoreOf r Θ : Set G) := by
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ := U.subgroupOf Θ with hU₀
  have hU₀2 : IsPGroup 2 U₀ := hU2.comap_subtype
  have hcent : ∀ r : (Nat.card ↥Θ).primeFactors.attach,
      U₀ ≤ Subgroup.centralizer (CFSG.pCore r.1.1 ↥Θ : Set ↥Θ) := by
    rintro ⟨⟨r, hr⟩, -⟩
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    by_cases hr2 : r = 2
    · subst hr2
      rw [hO2]
      intro u _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hz
      rw [hz, one_mul, mul_one]
    have hr3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr)
    have hr3' : 3 < r := by
      have := hrp.two_le
      omega
    have h := hall r hrp hr3'
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_subgroupOf.mp hu)) (z : G)
      ⟨z, hz, rfl⟩
    exact Subtype.ext this
  have hF := CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcent
  have hFF := hF.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
  have hle := le_pCore_of_isPGroup_of_le_fittingSubgroup hU₀2 hFF
  rw [hO2] at hle
  apply hU1
  rw [eq_bot_iff]
  intro u hu
  have hmem : (⟨u, hUΘ hu⟩ : ↥Θ) ∈ (⊥ : Subgroup ↥Θ) := hle (Subgroup.mem_subgroupOf.mpr hu)
  rw [Subgroup.mem_bot] at hmem ⊢
  exact congrArg Subtype.val hmem

private theorem commutator_le_commutator_commutator_of_coprime {G : Type*} [Group G]
    {P X : Subgroup G} (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅P, X⁆ ≤ ⁅⁅P, X⁆, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  intro x hx
  rw [← hmap, ← h2] at hx
  exact hmap2 hx

theorem exists_chiefFactor {G : Type} [Group G] [Finite G] {Θ U Y : Subgroup G}
    (hΘs : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hΘ2 : CFSG.Open.pCoreOf 2 Θ = ⊥)
    (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥) (hUΘ : U ≤ Θ) (hUY : U ≤ Y)
    (hYΘ : Y ≤ Subgroup.normalizer (Θ : Set G)) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ∃ F₁ F₂ : Subgroup G, F₁ ≤ CFSG.Open.pCoreOf r Θ ∧
      CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂ ∧ ∃ u ∈ U, ∃ f ∈ F₁, ⁅f, u⁆ ∉ F₂ := by
  classical
  have hO2 : CFSG.pCore 2 ↥Θ = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Θ.subtype_injective).mp hΘ2
  obtain ⟨r, hr, hr3, hrU⟩ := exists_prime_not_le_centralizer_pCoreOf hΘs hΘ3 hO2 hUΘ hU2 hU
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr5 : 5 ≤ r := by
    have hr4 : r ≠ 4 := by
      rintro rfl
      exact absurd hr (by norm_num)
    omega
  set P : Subgroup G := CFSG.Open.pCoreOf r Θ with hPdef
  have hP : IsPGroup r P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := r) Θ
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    hYΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := r) Θ)
  set H : Subgroup G := P ⊔ Y with hHdef
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hYP
  have hUH : U ≤ H := hUY.trans le_sup_right
  have hUP : U ≤ Subgroup.normalizer (P : Set G) := hUH.trans hHP
  have hPU : ¬ ⁅P, U⁆ ≤ ⊥ := by
    intro h
    apply hrU
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact le_bot_iff.mp h
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  let s₂ : Set (Subgroup G) :=
    {K | K ≤ P ∧ H ≤ Subgroup.normalizer (K : Set G) ∧ ¬ ⁅P, U⁆ ≤ K}
  have hbot : H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨F₂, ⟨hF₂P, hHF₂, hUF₂⟩, hF₂m⟩ :=
    (Set.toFinite s₂).exists_maximal ⟨⊥, bot_le, hbot, hPU⟩
  let s₁ : Set (Subgroup G) :=
    {K | F₂ < K ∧ K ≤ P ∧ H ≤ Subgroup.normalizer (K : Set G) ∧ ¬ ⁅K, U⁆ ≤ F₂}
  have hPs₁ : P ∈ s₁ := by
    refine ⟨lt_of_le_of_ne hF₂P ?_, le_rfl, hHP, hUF₂⟩
    rintro rfl
    exact hUF₂ (Subgroup.le_normalizer_iff_commutator_le_left.mp hUP)
  obtain ⟨F₁, ⟨hF₂F₁, hF₁P, hHF₁, hUF₁⟩, hF₁m⟩ := (Set.toFinite s₁).exists_minimal ⟨P, hPs₁⟩
  have hmin : ∀ K : Subgroup G, F₂ ≤ K → K ≤ F₁ → H ≤ Subgroup.normalizer (K : Set G) →
      K = F₂ ∨ K = F₁ := by
    intro K hF₂K hKF₁ hHK
    by_contra hne
    push Not at hne
    obtain ⟨hK2, hK1⟩ := hne
    have hlt2 : F₂ < K := lt_of_le_of_ne hF₂K (Ne.symm hK2)
    have hKU : ⁅K, U⁆ ≤ F₂ := by
      by_contra hKU
      exact hK1 (le_antisymm hKF₁ (hF₁m ⟨hlt2, hKF₁.trans hF₁P, hHK, hKU⟩ hKF₁))
    have hPUK : ⁅P, U⁆ ≤ K := by
      by_contra hPUK
      exact hK2 (le_antisymm (hF₂m ⟨hKF₁.trans hF₁P, hHK, hPUK⟩ hF₂K) hF₂K)
    apply hUF₁
    have hcop : Nat.Coprime (Nat.card U) (Nat.card F₁) :=
      IsPGroup.coprime_card_of_ne 2 r (by omega) U F₁ hU2 (hP.to_le hF₁P)
    calc ⁅F₁, U⁆ ≤ ⁅⁅F₁, U⁆, U⁆ :=
          commutator_le_commutator_commutator_of_coprime (hUH.trans hHF₁) hcop
      _ ≤ ⁅K, U⁆ :=
          Subgroup.commutator_mono ((Subgroup.commutator_mono_left hF₁P).trans hPUK) le_rfl
      _ ≤ F₂ := hKU
  have hPF₁ : ⁅F₁, P⁆ ≤ F₂ :=
    CFSG.GroupTheory.commutator_le_of_chief_of_isPGroup hP le_sup_left hHP hF₂F₁ hF₁P hHF₂
      hHF₁ hmin
  have hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂ :=
    CFSG.GroupTheory.isChiefFactorUnder_of_commutator_le hP hF₂F₁ hF₁P hPF₁
      (le_sup_right.trans hHF₂) (le_sup_right.trans hHF₁) hmin
  refine ⟨r, hr, hr5, F₁, F₂, hF₁P, hchief, ?_⟩
  rw [Subgroup.commutator_le] at hUF₁
  push Not at hUF₁
  obtain ⟨f, hf, u, hu, hfu⟩ := hUF₁
  exact ⟨u, hu, f, hf, hfu⟩

end CFSG.RankThree.PartTwo.J2Residue
