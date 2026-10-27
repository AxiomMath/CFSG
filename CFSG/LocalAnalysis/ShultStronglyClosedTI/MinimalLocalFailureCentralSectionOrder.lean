module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSectionIso

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem section_index
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    ((minimalLocalFailurePairActionPointHull H z).subgroupOf A).index =
        Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nat.card A = Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 := by
  obtain ⟨hAH, hAN, hQA, hAM, -⟩ := d.section_basic hA
  have hQltA := hA.2.2.1
  obtain ⟨hQH, hQn, -, hQ4, -, hBH, hXB, -, -, hXcard, -⟩ := d.point_data
  obtain ⟨-, -, hJne, -⟩ := d.J_data
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  have hcardQ' : Nat.card (Q.subgroupOf A) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv
  have hmul := Subgroup.card_mul_index (Q.subgroupOf A)
  rw [hcardQ'] at hmul
  set m := (Q.subgroupOf A).index with hm
  obtain ⟨j, hj1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJne
  obtain ⟨φ, -, hker, -⟩ := d.section_commutator_hom hA j.2 (fun h => hj1 (Subtype.ext h))
  have hle : m ≤ Nat.card Q := by
    rw [hm, ← hker, Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  let Γ : Set G := (A : Set G) \ Q
  have hpres : ∀ ω ∈ Γ, ∀ x ∈ X, x⁻¹ * ω * x ∈ Γ := by
    rintro ω ⟨hωA, hωQ⟩ x hx
    have hxH : x ∈ H := hBH (hXB hx)
    refine ⟨?_, fun hQ' => hωQ ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hAN (H.inv_mem hxH)) ω).mp hωA
      rw [inv_inv] at this
      exact this
    · have := hQn.conj_mem ⟨_, hQH hQ'⟩ hQ' ⟨x, hxH⟩
      change x * (x⁻¹ * ω * x) * x⁻¹ ∈ Q at this
      have h2 : x * (x⁻¹ * ω * x) * x⁻¹ = ω := by group
      rw [h2] at this
      exact this
  have hfree : ∀ ω ∈ Γ, ∀ x ∈ X, x⁻¹ * ω * x = ω → x = 1 := by
    rintro ω ⟨hωA, hωQ⟩ x hx hfix
    by_contra hx1
    have hmem : ω ∈ A ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hωA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc ω * x = x * (x⁻¹ * ω * x) := by group
        _ = x * ω := by rw [hfix]
    rw [d.section_centralizer_X_eq_bot hA hx hx1, Subgroup.mem_bot] at hmem
    exact hωQ (hmem ▸ Q.one_mem)
  have hdvd := CyclicSemiregular.card_dvd_card_of_free (fun ω g => g⁻¹ * ω * g)
    (fun ω => by group) (fun ω g h => by group) X Γ (Set.toFinite Γ) hpres hfree
  have hΓ : Nat.card Γ = Nat.card A - Nat.card Q := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff hQA, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    rfl
  rw [hΓ, hXcard, ← hmul] at hdvd
  have hm2 : 2 ≤ m := by
    have hne : Q.subgroupOf A ≠ ⊤ := by
      rw [Ne, Subgroup.subgroupOf_eq_top]
      exact hQltA.not_ge
    exact Subgroup.one_lt_index_of_ne_top hne
  have hcop : Nat.Coprime (Nat.card Q - 1) (Nat.card Q) :=
    (Nat.coprime_self_sub_left (by omega)).mpr (Nat.coprime_one_left _)
  have hdvd' : Nat.card Q - 1 ∣ m - 1 := by
    apply hcop.dvd_of_dvd_mul_left
    have : Nat.card Q * m - Nat.card Q = Nat.card Q * (m - 1) := by
      rw [Nat.mul_sub, mul_one]
    rwa [this] at hdvd
  have hge : Nat.card Q ≤ m := by
    have := Nat.le_of_dvd (by omega) hdvd'
    omega
  have hmq : m = Nat.card Q := le_antisymm hle hge
  refine ⟨hmq, ?_⟩
  rw [← hmul, hmq, sq]

theorem section_commutator_iso
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    A ⊓ Subgroup.centralizer ({j} : Set G) = minimalLocalFailurePairActionPointHull H z ∧
      ∃ φ : A →* minimalLocalFailurePairActionPointHull H z,
        (∀ a : A, (φ a : G) = (a : G) * j * (a : G)⁻¹ * j⁻¹) ∧
        φ.ker = (minimalLocalFailurePairActionPointHull H z).subgroupOf A ∧
        Function.Surjective φ ∧
        ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), ∀ a a' : A,
          (a' : G) = x * a * x⁻¹ → (φ a' : G) = x * φ a * x⁻¹ := by
  obtain ⟨-, -, hQA, hAM, -⟩ := d.section_basic hA
  obtain ⟨φ, hφ, hker, hequiv⟩ := d.section_commutator_hom hA hj hj1
  refine ⟨?_, φ, hφ, hker, ?_, hequiv⟩
  · rw [d.section_centralizer_J hQA hAM hj hj1, d.section_inf_J hA, sup_bot_eq]
  · rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.index_ker, hker]
    exact (d.section_index hA).1

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain
