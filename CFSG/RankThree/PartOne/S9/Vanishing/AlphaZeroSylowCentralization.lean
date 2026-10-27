module

public import CFSG.RankThree.PartOne.S9.StatementsAlpha
public import CFSG.RankThree.PartOne.S9.StatementsSylow
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaCentralizerTransfer
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace Vanish

variable {G : Type} [Group G]

theorem commutator_pCore_centralizer_eq_bot {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hα : ∀ E : Subgroup G, E ≤ A → Nat.card E = p ^ 2 → twoCoreAlpha E = ⊥) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) :
    ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥ := by
  have := hA
  set V := inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)) with hV
  have hVa : V ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact SteinbergBY.inSubgroup_pCore_le 2 _
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hxa : x ∈ Subgroup.zpowers a
  · exact Subgroup.mem_centralizer_iff.mp (hVa hv) x hxa
  · set E := Subgroup.zpowers a ⊔ Subgroup.zpowers x with hE
    have hEA : E ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hx)
    have hEcard : Nat.card E = p ^ 2 :=
      SteinbergBY.card_zpowers_sup_zpowers hp hAcard ha ha1 hx hxa
    have haE : a ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    have hJ : ⁅V, E⁆ ≤ ⊥ := by
      rw [← hα E hEA hEcard]
      exact (commutator_le_twoCoreJ haE ha1).trans (twoCoreJ_le_twoCoreAlpha E)
    have hvE : v ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hJ) hv
    exact Subgroup.mem_centralizer_iff.mp hvE x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

end Vanish

theorem alphaZeroSylowCentralization_of (hUAV : SectionNineUniformAlphaVerification)
    (hS2A : SylowTwoAlternatives) : AlphaZeroSylowCentralization := by
  intro G _ _ p hS hgood A hA hAcard B hBA hBcard hα
  have hp := hS.prime
  have hp2 : p ≠ 2 := by
    have := hS.three_lt
    omega
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  have hαall : ∀ E : Subgroup G, E ≤ A → Nat.card E = p ^ 2 → twoCoreAlpha E = ⊥ :=
    fun E hEA hE => ((hUAV G p hS hgood A hA hAcard).2.2 B E hBA hBcard hEA hE).symm.trans hα
  have hfirst : ∀ a ∈ A, a ≠ 1 →
      ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥ :=
    fun a ha ha1 => Vanish.commutator_pCore_centralizer_eq_bot hp hA hAcard hαall ha ha1
  refine ⟨hfirst, fun c hc hc1 => ?_⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set θ := inSubgroup (aschbacherSolvableCore p) H with hθ
  have hcA : ∀ x ∈ A, x ∈ H := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (by
      rw [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
        Subgroup.mem_centralizer_singleton_iff]
      exact Vanish.mul_comm_of_isElementaryAbelian hA hx hc)
  have hAθ : A ≤ Subgroup.normalizer (θ : Set G) := fun x hx =>
    Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore p H (hcA x hx)
  have hθcop : Nat.Coprime p (Nat.card θ) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore hp H)
  obtain ⟨T, hT, hAT⟩ := DihedralBlueprint.normalized_exists_sylow p 2 hp Nat.prime_two A θ hAp
    hAθ hθcop
  have hTS : IsSylowOf 2 T θ := Vanish.isSylowOf_of_isSylowIn hT
  refine ⟨T, hTS, ?_⟩
  rcases hS2A G p hS A hA hAcard c hc hc1 T hTS hAT with h1 | ⟨-, -, a, ha, ha1, hne⟩ |
    ⟨h7, q, hq, hq7, hrank⟩
  ·
    have hoc : orderOf c = p := SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hc hc1
    have hOeq : inSubgroup (pCore 2) (Subgroup.centralizer ({c} : Set G)) =
        inSubgroup (pCore 2) H :=
      (SteinbergBY.alpha_normal_odd_cyclic_centralizer_transfer_normalizer hp hp2 hoc).2.2.1
    have hT2 : IsPGroup 2 T := hT.2.1
    have hTcop : ¬ p ∣ Nat.card T := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    have hidem := RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A T hAp
      hTcop hAT
    rw [← hidem]
    refine le_bot_iff.mp ?_
    calc ⁅⁅T, A⁆, A⁆ ≤ ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({c} : Set G)), A⁆ := by
          rw [hOeq]
          exact Subgroup.commutator_mono h1 le_rfl
      _ = ⊥ := hfirst c hc hc1
      _ ≤ ⊥ := le_rfl
  · exact absurd (hfirst a ha ha1) hne
  · have := hgood h7 q hq hq7
    omega

end CFSG.RankThree.PartOne
