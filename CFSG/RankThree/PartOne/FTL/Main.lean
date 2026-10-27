module

public import CFSG.RankThree.PartOne.S11d.FourClaim
public import CFSG.RankThree.PartOne.FTL.Active
public import CFSG.RankThree.PartOne.FTL.Fit
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator

public section

namespace CFSG.RankThree.PartOne.FTL

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Blueprint CFSG.RankThree
  CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.Sec11Indeed
open scoped commutatorElement


theorem fourCaseOne_of_inputs (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) (hNL : FieldFixedNonLocal) : FourCaseOne := by
  intro G _ _ p A c L a d sit f hf hf1 R hR K₀ hK₀ hEK₀ hmove
  classical
  have hp := sit.prime
  have hp3 := sit.three_lt
  have hp5 := sit.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hdA := sit.d_mem
  have hAcard : Nat.card A = p ^ 3 := sit.setup.2.2.2.2.2.2.2.1
  have heG : evenRank G = 3 := sectionTenSetup_evenRank_eq sit.setup
  have he : evenRank G ≤ 3 := heG.le
  have hsig : p ∈ sigmaA G := sectionTenSetup_mem_sigmaA sit.setup
  have hAe : IsElementaryAbelian p A := sit.A_elem
  obtain ⟨i, j, hij, hi⟩ := sit.exists_coords_of_witness hf hf1 hR
  have hfA : f ∈ A := by
    rw [hij]
    exact A.mul_mem (A.zpow_mem sit.a_mem i) (A.zpow_mem hcA j)
  have hfa : InducesFieldAut p f L := hij ▸ sit.inducesFieldAut_mul j hi
  have hEq := fixedRes_isQuasisimple hfa
  set E := inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) with hE
  have hEp : Group.IsPerfect ↥E := EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have hEcomm : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hEp
  have hEL : E ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hLF : L ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨c, hcA, sit.c_ne_one, sit.L_mem.2⟩
  have hAL : A ≤ normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he p hp hp3 A sit.A_elem L hLF
  have hAf : A ≤ centralizer ({f} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (sit.A_comm hx hfA)
  have hAE : A ≤ normalizer (E : Set G) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      (L ⊓ centralizer ({f} : Set G))
      (FourSeed.mem_normalizer_inf' (hAL hx) (Subgroup.le_normalizer (hAf hx)))
  have hdp : d ^ p = 1 := sit.pow_eq_one hdA
  have hordd : orderOf d = p := orderOf_eq_prime hdp sit.d_ne_one
  have hdE : d ∈ E :=
    hFix G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA) (sit.fieldAutRank hfA) d
      ⟨sit.d_mem_L, Subgroup.mem_centralizer_singleton_iff.mpr (sit.A_comm hdA hfA)⟩
      ⟨1, by rw [pow_one]; exact hordd⟩
  have hdnc : ∃ e ∈ E, d * e ≠ e * d := by
    by_contra hno
    push Not at hno
    have hDc : (⟨d, sit.d_mem_L⟩ : ↥L) ∈ Subgroup.center ↥L :=
      hCent G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA) (sit.fieldAutRank hfA)
        ⟨d, sit.d_mem_L⟩ hno
    have h1 := orderOf_dvd_natCard (⟨⟨d, sit.d_mem_L⟩, hDc⟩ : Subgroup.center ↥L)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hordd] at h1
    exact sit.p_ndvd h1
  set Θ := inSubgroup (aschbacherSolvableCore p) K₀ with hΘ
  let P : Subgroup G → Prop := fun R' => R' ≤ centralizer ({f} : Set G) ∧ R' ≠ ⊥ ∧
    IsPGroup 2 R' ∧ A ≤ normalizer (R' : Set G) ∧ ⁅R', A⁆ = R' ∧ ⁅R', K₀⁆ ≤ Θ
  have hPR : P R := by
    refine ⟨hR.le_cent, hR.ne_bot, hR.two, hR.norm, ?_, hmove⟩
    apply le_antisymm
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hR.norm
    · calc R = ⁅R, zpowers c⁆ := hR.comm
        _ ≤ ⁅R, A⁆ := Subgroup.commutator_mono le_rfl (zpowers_le.mpr hcA)
  obtain ⟨R₀, hR₀P, hR₀min⟩ := wellFounded_lt.has_min {R' | P R'} ⟨R, hPR⟩
  obtain ⟨hR₀f, hR₀1, hR₀2, hAR, hR₀A, hR₀move⟩ := hR₀P
  have hminR : ∀ U : Subgroup G, U < R₀ → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U → U = ⊥ := by
    intro U hUR hAU hUA
    by_contra hU1
    exact hR₀min U ⟨hUR.le.trans hR₀f, hU1, hR₀2.to_le hUR.le, hAU, hUA,
      (Subgroup.commutator_mono hUR.le le_rfl).trans hR₀move⟩ hUR
  have hEK : E ≤ K₀ := hEK₀
  have hAd : A ≤ normalizer (zpowers d : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute d x from sit.A_comm hdA hx) m).eq)
  have hdR : ∀ r ∈ R₀, d * r = r * d := by
    set U : Subgroup G := ⁅R₀, zpowers d⁆ with hU
    have hzd : zpowers d ≤ A := zpowers_le.mpr hdA
    have hURle : U ≤ R₀ :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (hAR hdA))
    have hUΘ : U ≤ Θ :=
      (Subgroup.commutator_mono le_rfl ((zpowers_le.mpr hdE).trans hEK)).trans hR₀move
    have hU2 : IsPGroup 2 U := hR₀2.to_le hURle
    have hAU : A ≤ normalizer (U : Set G) := fun x hx =>
      FourSeed.mem_normalizer_commutator (hAR hx) (hAd hx)
    have hUA0 : ⁅U, A⁆ = ⊥ :=
      FourSeed.commutator_centralized_of_le_theta sit.setup hfA hf1 hK₀ hUΘ hU2 hAU
    have hUd : ⁅U, zpowers d⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hzd).trans hUA0.le)
    have hself := FourSeed.commutator_zpowers_self hp hp2 hordd hR₀2 (hAR hdA)
    have hU0 : U = ⊥ := hself.symm.trans hUd
    have hRC : R₀ ≤ centralizer (zpowers d : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU0
    intro r hr
    exact Subgroup.mem_centralizer_iff.mp (hRC hr) d (mem_zpowers d)
  have hdB : d ∈ A ⊓ Subgroup.centralizer (R₀ : Set G) :=
    ⟨hdA, Subgroup.mem_centralizer_iff.mpr fun r hr => (hdR r hr).symm⟩
  have hfB : f ∈ A ⊓ Subgroup.centralizer (R₀ : Set G) :=
    ⟨hfA, Subgroup.mem_centralizer_iff.mpr fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (hR₀f hr)⟩
  have hBcard : Nat.card ↥(A ⊓ Subgroup.centralizer (R₀ : Set G)) = p ^ 2 := by
    have hdnf : d ∉ zpowers f := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      have hac : Commute a c := sit.A_comm sit.a_mem hcA
      have e1 : f ^ k = a ^ (i * k) * c ^ (j * k) := by
        rw [hij, (hac.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul]
      have h2 : a ^ (i * k) * c ^ (j * k) * d ^ (-1 : ℤ) = 1 := by
        rw [← e1, hk]
        simp
      have h3 := (sit.coords_eq_one h2).2.2
      have h4 : (p : ℤ) ∣ 1 := by simpa using h3
      have := Int.eq_one_of_dvd_one (by positivity) h4
      have h5 : p = 1 := by exact_mod_cast this
      exact hp.one_lt.ne' h5
    have : IsElementaryAbelian p A := hAe
    have h2 := SteinbergBY.card_zpowers_sup_zpowers hp hAcard hfA hf1 hdA hdnf
    have hle : zpowers f ⊔ zpowers d ≤ A ⊓ Subgroup.centralizer (R₀ : Set G) :=
      sup_le (zpowers_le.mpr hfB) (zpowers_le.mpr hdB)
    have hcardle := Subgroup.card_dvd_of_le hle
    rw [h2] at hcardle
    have hdvd : Nat.card ↥(A ⊓ Subgroup.centralizer (R₀ : Set G)) ∣ p ^ 3 :=
      hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j', hj3, hjc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hjc] at hcardle ⊢
    have hj2 : 2 ≤ j' := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hcardle
    have hj3' : j' ≠ 3 := by
      rintro rfl
      have hAeq : A ⊓ Subgroup.centralizer (R₀ : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left) (by rw [hjc, hAcard])
      have hAC : A ≤ Subgroup.centralizer (R₀ : Set G) := by
        rw [← hAeq]; exact inf_le_right
      have h0 : ⁅R₀, A⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAC
      exact hR₀1 (by rw [← hR₀A, h0])
    congr 1
    omega
  have hAZ : A ≤ normalizer (⁅R₀, E⁆ : Subgroup G) := fun x hx =>
    FourSeed.mem_normalizer_commutator (hAR hx) (hAE hx)
  have hEZ : E ≤ normalizer (⁅R₀, E⁆ : Subgroup G) := Subgroup.normalizer_commutator_ge_right R₀ E
  set Z : Subgroup G := ⁅R₀, E⁆ with hZ
  have hZΘ : Z ≤ Θ := (Subgroup.commutator_mono le_rfl hEK).trans hR₀move
  obtain ⟨hΘs, hΘp⟩ := theta_solvable_and_not_dvd hp K₀
  have hZs : Group.IsSolvable ↥Z :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hZΘ)
      (Subgroup.inclusion_injective hZΘ)
  have hpZ : ¬ p ∣ Nat.card ↥Z := fun h => hΘp (h.trans (Subgroup.card_dvd_of_le hZΘ))
  have hO2 : inSubgroup (pCore 2) Z = ⊥ := by
    by_contra hne
    have hT2 : IsPGroup 2 (inSubgroup (pCore 2) Z) := SteinbergBY.isPGroup_inSubgroup_pCore 2 Z
    have hAT : A ≤ normalizer (inSubgroup (pCore 2) Z : Set G) := fun x hx =>
      SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 Z (hAZ hx)
    have hET : E ≤ normalizer (inSubgroup (pCore 2) Z : Set G) := fun x hx =>
      SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 Z (hEZ hx)
    exact four_seed_false hS h112 hbridge hK hLS hFix hCent hNL sit hij hi hT2 hne hAT hET
  have hRZ : R₀ ≤ normalizer (Z : Set G) := Subgroup.normalizer_commutator_ge_left R₀ E
  have hactive : ∀ s : ℕ, s.Prime → ⁅R₀, inSubgroup (pCore s) Z⁆ ≠ ⊥ →
      E ≤ Subgroup.centralizer (inSubgroup (pCore s) Z : Set G) := by
    intro s hs hRM
    have hMne : inSubgroup (pCore s) Z ≠ ⊥ := fun h => hRM (by rw [h, Subgroup.commutator_bot_right])
    have hs2 : s ≠ 2 := by
      rintro rfl
      exact hMne hO2
    have hMq : IsPGroup s (inSubgroup (pCore s) Z) := SteinbergBY.isPGroup_inSubgroup_pCore s Z
    have hsp : s ≠ p := by
      rintro rfl
      have : Fact s.Prime := ⟨hs⟩
      rcases hMq.card_eq_or_dvd with h1 | h1
      · exact hMne (Subgroup.eq_bot_of_card_eq _ h1)
      · exact hpZ (h1.trans (Subgroup.card_dvd_of_le (SteinbergBY.inSubgroup_pCore_le s Z)))
    exact active_core_centralized twoActionInputs_of_S9 hp hp3 heG hsig hs hs2 hsp hAe hAcard hAR
      hR₀2 hR₀A hR₀1 hBcard hminR hdB hEq hdE hdnc hMq hMne
      (fun r hr => SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s Z (hRZ hr))
      (fun x hx => SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s Z (hAZ hx))
      (fun x hx => SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s Z (hEZ hx)) hRM
  have hZbot : Z = ⊥ := eq_bot_of_active hZ hEcomm hR₀2 hZs hO2 hactive
  have hER : E ≤ normalizer (R₀ : Set G) := by
    have hc : E ≤ centralizer (R₀ : Set G) := by
      have h0 : ⁅E, R₀⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hZbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    exact fun x hx => Subgroup.centralizer_le_normalizer _ (hc hx)
  exact four_seed_false hS h112 hbridge hK hLS hFix hCent hNL sit hij hi hR₀2 hR₀1 hAR hER

theorem fourThetaLift_of_inputs (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) (hNL : FieldFixedNonLocal) : FourThetaLift := by
  intro G _ _ p A c L a d sit f hf hf1 R hR K₀ hK₀ hEK₀ hmove
  exact (fourCaseOne_of_inputs hS h112 hbridge hK hLS hFix hCent hNL G p A c L a d sit f hf hf1 R
    hR K₀ hK₀ hEK₀ hmove).elim

theorem fourClaim_of_inputs (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) (hNL : FieldFixedNonLocal) : FourClaim :=
  fourClaim_of hS h112 hbridge hK hLS hFix hCent hNL
    (fourThetaLift_of_inputs hS h112 hbridge hK hLS hFix hCent hNL)

end CFSG.RankThree.PartOne.FTL
