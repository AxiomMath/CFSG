module

public import CFSG.RankThree.PartOne.S11d.FourCaseOneProof
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec11Indeed

variable {G : Type} [Group G] [Finite G]

theorem fourClaim_of (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) (hNL : FieldFixedNonLocal) (hLift : FourThetaLift) :
    FourClaim := by
  intro G _ _ p A c L a d sit f hf hf1 R hR
  classical
  have hp := sit.prime
  have hp3 := sit.three_lt
  have hp5 := sit.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq sit.setup).le
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
  have hfA : f ∈ A := by
    have : zpowers a ⊔ zpowers c ≤ A := sup_le (zpowers_le.mpr sit.a_mem) (zpowers_le.mpr hcA)
    exact this hf
  obtain ⟨i, j, hij⟩ := sit.exists_zpow_mul hf
  have hi : ¬ (p : ℤ) ∣ i := by
    intro hdiv
    have hai : a ^ i = 1 := by
      obtain ⟨t, rfl⟩ := hdiv
      rw [zpow_mul, zpow_natCast, hap, one_zpow]
    have hfc : f = c ^ j := by rw [hij, hai, one_mul]
    have hj : ¬ (p : ℤ) ∣ j := by
      intro hdj
      apply hf1
      rw [hfc]
      obtain ⟨t, rfl⟩ := hdj
      rw [zpow_mul, zpow_natCast, hcp, one_zpow]
    have hcent := S11d.centralizer_zpow_eq (G := G) hp hcp hj
    have hRc : R ≤ centralizer ({c} : Set G) := by
      rw [← hcent, ← hfc]
      exact hR.le_cent
    apply hR.ne_bot
    have h1 : ⁅R, zpowers c⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hrc : r * c = c * r := Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
      exact (Commute.zpow_left (show Commute c r from hrc.symm) k).eq
    rw [hR.comm, h1]
  have hfa : InducesFieldAut p f L := hij ▸ sit.inducesFieldAut_mul j hi
  have hEq := fixedRes_isQuasisimple hfa
  obtain ⟨K₀, hK₀, hEK₀⟩ := exists_thetaComponent_ge_fixedRes hS sit.setup hcA sit.c_ne_one hfA hf1
    sit.L_mem.2 hEq
  set E := inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) with hE
  have hK₀F : K₀ ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨f, hfA, hf1, hK₀⟩
  have hAK₀ : A ≤ normalizer (K₀ : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he p hp hp3 A sit.A_elem K₀ hK₀F
  have hcf : c ∈ centralizer ({f} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sit.A_comm hcA hfA
  have hRK₀ : R ≤ normalizer (K₀ : Set G) :=
    commutator_normalizes_thetaComponentsAt he hp hp3 hcf ⟨1, by
      rw [pow_one]; exact orderOf_eq_prime hcp sit.c_ne_one⟩ hR.le_cent hR.comm.le hK₀
  by_cases hmove : ⁅R, K₀⁆ ≤ inSubgroup (aschbacherSolvableCore p) K₀
  · exact (fourCaseOne_of_lift hS h112 hbridge hK hLS hFix hCent hNL hLift G p A c L a d sit f hf
      hf1 R hR K₀ hK₀ hEK₀ hmove).elim
  have hmove' : ∃ r ∈ R, ∃ k ∈ K₀,
      r * k * r⁻¹ * k⁻¹ ∉ inSubgroup (aschbacherSolvableCore p) K₀ := by
    by_contra hno
    push Not at hno
    apply hmove
    rw [Subgroup.commutator_le]
    intro r hr k hk
    rw [commutatorElement_def]
    exact hno r hr k hk
  obtain ⟨hmem, hq₀, hALK₀, hsetK, -⟩ :=
    four_main hS h112 hbridge hK hLS hFix hCent sit hij hi hf1 hR hK₀ hEK₀ hmove'
  have hne : ⁅K₀, R⁆ ≠ ⊥ := by
    obtain ⟨r, hr, k, hk, hno⟩ := hmove'
    intro h0
    have hmem : ⁅k, r⁆ ∈ ⁅K₀, R⁆ := Subgroup.commutator_mem_commutator hk hr
    rw [h0, Subgroup.mem_bot] at hmem
    apply hno
    have h2 : r * k * r⁻¹ * k⁻¹ = (⁅k, r⁆)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2, hmem, inv_one]
    exact Subgroup.one_mem _
  have hRK := Sec125.commutator_eq_of_ne_bot hq₀ hRK₀ hne
  refine ⟨K₀, hmem, hEK₀, hALK₀, ?_, hsetK.2.2.2.2.2.2⟩
  rw [Subgroup.commutator_comm]
  exact hRK

end Sec11Indeed

end CFSG.RankThree.PartOne
