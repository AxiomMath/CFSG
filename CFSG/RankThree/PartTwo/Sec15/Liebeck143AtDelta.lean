module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.RankThree.PartTwo.Sec15.Liebeck156Theta
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_sup_le_of_le_centralizer {A N₀ O' : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N₀ : Set G)) (hO'N : O' ≤ Subgroup.normalizer (N₀ : Set G))
    (hO'A : O' ≤ Subgroup.centralizer (A : Set G)) : ⁅O' ⊔ N₀, A⁆ ≤ N₀ := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hx' : x ∈ ((O' ⊔ N₀ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right O' N₀ hO'N] at hx'
  obtain ⟨o, ho, n, hn, rfl⟩ := hx'
  have hoa : a * o = o * a := Subgroup.mem_centralizer_iff.mp (hO'A ho) a ha
  have hna : n * a * n⁻¹ * a⁻¹ ∈ N₀ := by
    have h1 : a * n⁻¹ * a⁻¹ ∈ N₀ := (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (inv_mem hn)
    have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem hn h1
  have e : ⁅o * n, a⁆ = o * (n * a * n⁻¹ * a⁻¹) * o⁻¹ := by
    rw [commutatorElement_def]
    have : o * n * a * (o * n)⁻¹ * a⁻¹ = o * (n * a * n⁻¹ * a⁻¹) * (a * o⁻¹ * a⁻¹) := by group
    rw [this]
    congr 1
    calc a * o⁻¹ * a⁻¹ = (a * o * a⁻¹)⁻¹ := by group
      _ = o⁻¹ := by rw [hoa, mul_inv_cancel_right]
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hO'N ho) _).mp hna

theorem deltaZero_le_of_delta_le_sup {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y N₀ O' : Subgroup G} (hAN : A ≤ Subgroup.normalizer (N₀ : Set G))
    (hO'N : O' ≤ Subgroup.normalizer (N₀ : Set G))
    (hO'A : O' ≤ Subgroup.centralizer (A : Set G)) (hΔ : delta A LB Y ≤ O' ⊔ N₀) :
    deltaZero A LB Y ≤ N₀ := by
  refine sSup_le fun Q hQ => ?_
  have hQΔ : Q ≤ delta A LB Y := le_delta hQ.1.1 hQ.2
  calc Q = ⁅Q, A⁆ := hQ.1.2
    _ ≤ ⁅O' ⊔ N₀, A⁆ := Subgroup.commutator_mono (hQΔ.trans hΔ) le_rfl
    _ ≤ N₀ := commutator_sup_le_of_le_centralizer hAN hO'N hO'A

variable [Finite G]

theorem deltaZero_le_of_inv143Q {A : Subgroup G} {a d : G} {X : Subgroup G} (haA : a ∈ A)
    (hAa : A ≤ Subgroup.centralizer ({a} : Set G))
    (hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hinv : Ronan148Q.Inv143Q A a d X) :
    deltaZero A (lB A) (Subgroup.centralizer ({a} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set O := pPrimeCoreOf 3 C with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hO'A : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hO'C : O' ≤ C := hO'A.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hO'NA : O' ≤ Subgroup.normalizer (A : Set G) :=
    hO'A.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm : C ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G) := by
    rcases hinv with hinv | ⟨-, -, -, hinv⟩
    · exact inf_le_left.trans hinv
    · exact hinv
  refine deltaZero_le_of_delta_le_sup ((le_inf hAa Subgroup.le_normalizer).trans hnorm)
    ((le_inf hO'C hO'NA).trans hnorm) hO'A ?_
  rw [hΔ]
  exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    (le_sup_right.trans le_sup_right)

theorem theta_le_pPrimeCoreOf_of_subset {a : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 a) :
    inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  refine (theta_sSup_le h𝒳).trans (le_pPrimeCoreOf (Sec17.Proof171Steps.theta_le C)
    (Sec17.Proof171Steps.le_normalizer_theta C) ?_)
  rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).2.2.1

theorem inf_pPrimeCoreOf_le_theta {X C : Subgroup G} (hXC : X ≤ C)
    (hno : Ronan148W.NoNormal3 (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    X ⊓ pPrimeCoreOf 3 C ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  set O := pPrimeCoreOf 3 C with hO
  set N : Subgroup ↥X := (X ⊓ O).subgroupOf X with hN
  have hON : X ≤ Subgroup.normalizer (O : Set G) := hXC.trans (le_normalizer_pPrimeCoreOf 3 C)
  have hNn : N.Normal := by
    rw [hN, Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : X ⊓ O ≤ X)]
    exact (le_inf Subgroup.le_normalizer hON).trans Subgroup.inf_normalizer_le_normalizer_inf
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) with hπ
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 C
  have hN3 : Nat.Coprime 3 (Nat.card N) := by
    have hcard : Nat.card N = Nat.card (X ⊓ O : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ O ≤ X)).toEquiv
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hO3
  have hmap : N.map π = ⊥ := by
    refine hno _ (hNn.map π (QuotientGroup.mk'_surjective _)) ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N π) hN3)
  have hker : N ≤ aschbacherSolvableCore 3 ↥X := by
    have h := (Subgroup.map_eq_bot_iff N).mp hmap
    rwa [hπ, QuotientGroup.ker_mk'] at h
  intro x hx
  exact ⟨⟨x, hx.1⟩, hker (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem inf_pPrimeCoreOf_eq_theta {a : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 a)
    (hno : Ronan148W.NoNormal3 (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) :
    sSup 𝒳 ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) =
      inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
  have hXC : sSup 𝒳 ≤ Subgroup.centralizer ({a} : Set G) := sSup_le fun L hL => by
    obtain ⟨L', -, rfl⟩ := h𝒳 hL
    exact Subgroup.map_subtype_le L'
  exact le_antisymm (inf_pPrimeCoreOf_le_theta hXC hno)
    (le_inf (Sec17.Proof171Steps.theta_le _) (theta_le_pPrimeCoreOf_of_subset h𝒳))

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
