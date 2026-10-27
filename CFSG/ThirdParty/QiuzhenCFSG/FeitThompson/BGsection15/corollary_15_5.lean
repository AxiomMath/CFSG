module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.corollary_15_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-! # Corollary 15 5 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
private theorem CFSG.section15_normal_isPiSubgroup_le_hall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {H N : Subgroup R} [N.Normal]
    (hH : IsHallSubgroup π H)
    (hNπ : IsPiSubgroup (G := R) π N) :
    N ≤ H := by
  let S : Subgroup R := H ⊔ N
  have hHπ : IsPiSubgroup (G := R) π H := by
    intro p hp
    exact hH.p_in_pi_of_p_dvd_card p hp
  have hSπ : IsPiSubgroup (G := R) π S := by
    simpa [S] using section15_isPiSubgroup_sup_of_normal_right hHπ hNπ
  have hSHall : IsHallSubgroup π S := by
    refine isHallSubgroup_of (G := R) (π := π) (H := S) hSπ ?_
    intro p hpπ hpidx
    have hidx_dvd : S.index ∣ H.index := by
      exact Subgroup.index_dvd_of_le (by simp [S])
    exact (hH.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ
  have hEq : H = S := hH.eq_of_le hSHall (by simp [S])
  intro x hx
  have hxS : x ∈ S := by
    have hNleS : N ≤ S := by
      simp [S]
    exact hNleS hx
  simpa [hEq] using hxS

/-- Corollary 15.5(a): for `H = M_F` and
`Y = O_{σ(M)'}(F(M))`, `Y` is a cyclic `τ₂(M)`-subgroup of `F(M)`. -/
public theorem CFSG.section15_sigma_complement_fitting_core_tau2
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section15MFSubgroup M MF) :
    IsPiSubgroup (G := G) (section12Tau2Primes M)
      (section15SigmaComplementFittingCore M) := by
  classical
  let S : Subgroup G := section10Msigma M
  let C : Subgroup G := subgroupCentralizerIn M S
  let Y : Subgroup G := section15SigmaComplementFittingCore M
  have hSne : S ≠ ⊥ := by
    simpa [S] using theorem_10_2_e (M := M) hM
  have hSHall : section15HallSubgroupOf S S := by
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    refine isHallSubgroup_of (G := S) (π := subgroupPrimeSet S)
      (H := (⊤ : Subgroup S)) ?_ ?_
    · intro p hp
      simpa [subgroupPrimeSet] using hp
    · intro p _ hpidx
      exact p.property.not_dvd_one (by simpa using hpidx)
  rcases section15_corollary15_3_a_hall_factor
      (M := M) (H := S) hM hSne hSHall with
    ⟨X, hXleC, _hXcyc, hXτ2, hXHallσc, _hfactor⟩
  have hYleF : Y ≤ section8FittingSubgroup M := by
    simpa [Y, section15SigmaComplementFittingCore] using
      (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M))
  have hYleM : Y ≤ M :=
    hYleF.trans (section8FittingSubgroup_le M)
  have hYcentS : Y ≤ Subgroup.centralizer (S : Set G) := by
    simpa [S, Y, section15SigmaComplementFittingCore] using
      section10_sigma_compl_fitting_core_le_centralizer_msigma (G := G) hM
  have hYleC : Y ≤ C := by
    intro y hy
    exact ⟨hYleM hy, hYcentS hy⟩
  let Ysub : Subgroup C := Y.subgroupOf C
  have hYσc : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Y := by
    simpa [Y, section15SigmaComplementFittingCore] using
      piCoreIn_isPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M)
  have hYsubσc : IsPiSubgroup (G := C) (section10SigmaPrimes M)ᶜ Ysub := by
    intro p hpY
    have hcard : Nat.card Ysub = Nat.card Y := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (G := G) (H := Y) (K := C) hYleC).toEquiv
    exact hYσc p (by simpa [Ysub, hcard] using hpY)
  have hC_norm_F : C ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
    intro c hc
    have hM_norm_F : M ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
      have hFNorm : ((section8FittingSubgroup M).subgroupOf M).Normal :=
        section8FittingSubgroup_normal_in M
      letI : ((section8FittingSubgroup M).subgroupOf M).Normal := hFNorm
      exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)
    exact hM_norm_F hc.1
  have hC_norm_Y : C ≤ Subgroup.normalizer (Y : Set G) := by
    simpa [Y, section15SigmaComplementFittingCore] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (G := G) (π := (section10SigmaPrimes M)ᶜ)
        (H := section8FittingSubgroup M) (P := C) hC_norm_F
  haveI : Ysub.Normal := by
    simpa [Ysub] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYleC).2 hC_norm_Y
  let Xsub : Subgroup C := X.subgroupOf C
  have hYsub_le_Xsub : Ysub ≤ Xsub :=
    section15_normal_isPiSubgroup_le_hall
      (R := C) (π := (section10SigmaPrimes M)ᶜ)
      (H := Xsub) (N := Ysub) (by simpa [C, Xsub] using hXHallσc) hYsubσc
  have hYleX : Y ≤ X := by
    intro y hyY
    have hyC : y ∈ C := hYleC hyY
    let yC : C := ⟨y, hyC⟩
    have hyYsub : yC ∈ Ysub := by
      simpa [Ysub, yC, Subgroup.mem_subgroupOf] using hyY
    have hyXsub : yC ∈ Xsub := hYsub_le_Xsub hyYsub
    simpa [Xsub, yC, Subgroup.mem_subgroupOf] using hyXsub
  exact IsPiSubgroup.of_le hYleX hXτ2

private theorem CFSG.section15_corollary15_5_a_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (_hEq : MF = section10Msigma M) :
    section15SigmaComplementFittingCore M ≤ section8FittingSubgroup M ∧
      IsCyclic (section15SigmaComplementFittingCore M) ∧
        IsPiSubgroup (G := G) (section12Tau2Primes M)
          (section15SigmaComplementFittingCore M) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [section15SigmaComplementFittingCore] using
      (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M))
  · change IsCyclic
      (piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M))
    exact section10_sigma_compl_fitting_core_isCyclic (G := G) hM
  · exact section15_sigma_complement_fitting_core_tau2 hM hMF

/-- Corollary 15.5(a), proper branch `M_F ≠ M_σ`: Theorem 15.2(g) and
Corollary 15.3(a) identify the `σ(M)'` Fitting factor as cyclic `τ₂(M)`. -/
private theorem CFSG.section15_corollary15_5_a_of_MF_ne_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (_hNe : MF ≠ section10Msigma M) :
    section15SigmaComplementFittingCore M ≤ section8FittingSubgroup M ∧
      IsCyclic (section15SigmaComplementFittingCore M) ∧
        IsPiSubgroup (G := G) (section12Tau2Primes M)
          (section15SigmaComplementFittingCore M) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [section15SigmaComplementFittingCore] using
      (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M))
  · change IsCyclic
      (piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M))
    exact section10_sigma_compl_fitting_core_isCyclic (G := G) hM
  · exact section15_sigma_complement_fitting_core_tau2 hM hMF

public theorem CFSG.corollary_15_5_a
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    section15SigmaComplementFittingCore M ≤ section8FittingSubgroup M ∧
      IsCyclic (section15SigmaComplementFittingCore M) ∧
        IsPiSubgroup (G := G) (section12Tau2Primes M)
          (section15SigmaComplementFittingCore M) := by
  by_cases hEq : MF = section10Msigma M
  · exact section15_corollary15_5_a_of_MF_eq_msigma hM hMF hEq
  · exact section15_corollary15_5_a_of_MF_ne_msigma hM hMF hEq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_secondDerived_le_of_quotientAbelian_ambientDerived
    {M K : Subgroup G}
    (hquot : section15QuotientAbelian (ambientDerivedSubgroup M) K) :
    section15SecondDerivedSubgroup M ≤ K := by
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hquot with ⟨hKD, hKnorm, hComm⟩
  let Kloc : Subgroup D := K.subgroupOf D
  haveI : Kloc.Normal := by
    simpa [Kloc] using hKnorm
  have hder_le_Kloc : derivedSubgroup D ≤ Kloc :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Kloc)).1 hComm
  intro x hx
  change x ∈ ambientDerivedSubgroup D at hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  change ((y : D) : G) ∈ K
  simpa [Kloc, Subgroup.mem_subgroupOf] using hder_le_Kloc hy

omit [IsMinCE G] in
private theorem CFSG.section15_nilpotent_top_le_hall_sup_centralizer
    {R : Type*} [Group R] [Finite R] {H : Subgroup R}
    (hnil : Group.IsNilpotent R)
    (hHall : IsHallSubgroup (subgroupPrimeSet H) H) :
    (⊤ : Subgroup R) ≤ H ⊔ Subgroup.centralizer (H : Set R) := by
  classical
  let π : Set Nat.Primes := subgroupPrimeSet H
  let Z : Subgroup R := piCore πᶜ R
  haveI : H.Normal := section15_hall_subgroup_normal_of_nilpotent hnil hHall
  haveI : Z.Normal := by
    simpa [Z] using (inferInstance : (piCore πᶜ R).Normal)
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup R) := by
    let e : R ≃* (⊤ : Subgroup R) :=
      (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R).symm
    exact Group.nilpotent_of_mulEquiv (G := R) (G' := (⊤ : Subgroup R)) e
  have htop_le_sup :
      (⊤ : Subgroup R) ≤
        ⨆ q : (Nat.card R).primeFactors.attach, pCore q.1.1 R :=
    normal_nilpotent_le_sup_pCore
      (G := R) (N := (⊤ : Subgroup R)) (hN := inferInstance) htop_nil
  have hcores_le :
      (⨆ q : (Nat.card R).primeFactors.attach, pCore q.1.1 R) ≤ H ⊔ Z := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    haveI : Fact q.val.Prime := ⟨q.property⟩
    by_cases hqπ : q ∈ π
    · have hcore_le_H : pCore q.val R ≤ H :=
        section15_pSubgroup_le_normal_hall_of_prime_mem
          (R := R) (π := π) (H := H) (A := pCore q.val R)
          hHall hqπ (pCore_isPGroup (G := R) (p := q.val))
      exact hcore_le_H.trans le_sup_left
    · have hcoreπc : IsPiSubgroup (G := R) πᶜ (pCore q.val R) :=
        section15_isPiSubgroup_of_isPGroup_of_mem
          (R := R) (π := πᶜ) (p := q) (P := pCore q.val R)
          (pCore_isPGroup (G := R) (p := q.val))
          (by simpa [Set.mem_compl_iff] using hqπ)
      have hcore_le_Z : pCore q.val R ≤ Z := by
        simpa [Z] using
          le_piCore_of_normal_isPiSubgroup
            (G := R) πᶜ (pCore q.val R) hcoreπc
      exact hcore_le_Z.trans le_sup_right
  have hHπ : IsPiSubgroup (G := R) π H := by
    intro p hp
    exact hHall.p_in_pi_of_p_dvd_card p hp
  have hZπ : IsPiSubgroup (G := R) πᶜ Z := by
    simpa [Z] using piCore_isPiSubgroup (G := R) πᶜ
  have hπdisj : Disjoint πᶜ π := by
    rw [Set.disjoint_left]
    intro p hpπc hpπ
    exact hpπc hpπ
  have hZHdisj : Disjoint Z H := by
    rw [Subgroup.disjoint_def]
    intro x hxZ hxH
    have hcop : Nat.Coprime (Nat.card Z) (Nat.card H) := by
      refine Nat.coprime_of_dvd ?_
      intro q hqprime hqZ hqH
      let q' : Nat.Primes := ⟨q, hqprime⟩
      have hqπc : q' ∈ πᶜ := hZπ q' hqZ
      have hqπ : q' ∈ π := hHπ q' hqH
      exact (Set.disjoint_left.mp hπdisj hqπc) hqπ
    have hcop_order : Nat.Coprime (orderOf x) (Nat.card H) :=
      Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard Z hxZ) hcop
    have hx_order_one : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_order dvd_rfl
        (Subgroup.orderOf_dvd_natCard H hxH)
    exact orderOf_eq_one_iff.mp hx_order_one
  have hZcentH : Z ≤ Subgroup.centralizer (H : Set R) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hcommZ : ⁅z, h⁆ ∈ Z := by
      have hhz : h * z⁻¹ * h⁻¹ ∈ Z :=
        (show Z.Normal from inferInstance).conj_mem z⁻¹ (Z.inv_mem hz) h
      simpa [commutatorElement_def, mul_assoc] using Z.mul_mem hz hhz
    have hcommH : ⁅z, h⁆ ∈ H := by
      have hzh : z * h * z⁻¹ ∈ H :=
        (show H.Normal from inferInstance).conj_mem h hh z
      simpa [commutatorElement_def, mul_assoc] using H.mul_mem hzh (H.inv_mem hh)
    have hcomm_one : ⁅z, h⁆ = 1 :=
      Subgroup.disjoint_def.mp hZHdisj hcommZ hcommH
    have hmul : z * h = h * z :=
      commutatorElement_eq_one_iff_mul_comm.mp hcomm_one
    exact hmul.symm
  exact htop_le_sup.trans (hcores_le.trans (sup_le_sup_left hZcentH H))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_MF_le_fitting
    {M MF : Subgroup G}
    (hMF : section15MFSubgroup M MF) :
    MF ≤ section8FittingSubgroup M := by
  rcases hMF.1 with ⟨hMFM, hMFnormM, hMFnil, _hMFHall⟩
  haveI : Group.IsNilpotent (MF.subgroupOf M) := by
    let e := (Subgroup.subgroupOfEquivOfLe (G := G) (H := MF) (K := M) hMFM).symm
    exact Group.nilpotent_of_mulEquiv (G := MF) (G' := MF.subgroupOf M) e
  have hMF_le_fit_local : MF.subgroupOf M ≤ fittingSubgroup M :=
    le_sSup ⟨hMFnormM, (inferInstance : Group.IsNilpotent (MF.subgroupOf M))⟩
  have hmap_le :
      (MF.subgroupOf M).map M.subtype ≤ section8FittingSubgroup M :=
    Subgroup.map_mono hMF_le_fit_local
  simpa [section8FittingSubgroup, fittingSubgroupOf, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hMFM] using hmap_le

omit [IsMinCE G] in
private theorem CFSG.section15_fitting_eq_centralizer_sup_of_MF
    {M MF : Subgroup G}
    (hMF : section15MFSubgroup M MF)
    (hC_le_F : subgroupCentralizerIn M MF ≤ section8FittingSubgroup M) :
    section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let C : Subgroup G := subgroupCentralizerIn M MF
  let Hloc : Subgroup F := MF.subgroupOf F
  let Cloc : Subgroup F := Subgroup.centralizer (Hloc : Set F)
  have hMFleF : MF ≤ F := by
    simpa [F] using section15_MF_le_fitting (M := M) (MF := MF) hMF
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, hMFHallM⟩
  have hHallMF_M : section15HallSubgroupOf MF M := ⟨hMFM, hMFHallM⟩
  have hHallMF_F : section15HallSubgroupOf MF F :=
    section15_hallSubgroupOf_of_le hHallMF_M hMFleF (section8FittingSubgroup_le M)
  have htop_le :
      (⊤ : Subgroup F) ≤ Hloc ⊔ Cloc := by
    have hprime_eq : subgroupPrimeSet Hloc = subgroupPrimeSet MF := by
      exact section8_subgroupPrimeSet_subgroupOf_eq
        (G := G) (H := MF) (K := F) hMFleF
    simpa [Hloc, Cloc] using
      section15_nilpotent_top_le_hall_sup_centralizer
        (R := F) (H := Hloc)
        (by simpa [F] using section8FittingSubgroup_isNilpotent M)
        (by simpa [Hloc, hprime_eq] using hHallMF_F.2)
  have hHloc_map_le : Hloc.map F.subtype ≤ MF := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [Hloc, Subgroup.mem_subgroupOf] using hy
  have hCloc_map_le : Cloc.map F.subtype ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine ⟨section8FittingSubgroup_le M y.property, ?_⟩
    change F.subtype y ∈ Subgroup.centralizer (MF : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    let hF : F := ⟨h, hMFleF hh⟩
    have hhloc : hF ∈ Hloc := by
      simpa [hF, Hloc, Subgroup.mem_subgroupOf] using hh
    have hcomm : hF * y = y * hF :=
      Subgroup.mem_centralizer_iff.mp hy hF hhloc
    simpa [hF] using congrArg Subtype.val hcomm
  have hjoin_map_le : (Hloc ⊔ Cloc).map F.subtype ≤ MF ⊔ C := by
    rw [Subgroup.map_sup]
    exact sup_le (hHloc_map_le.trans le_sup_left) (hCloc_map_le.trans le_sup_right)
  apply le_antisymm
  · intro x hxF
    let xF : F := ⟨x, hxF⟩
    have hxJoin : xF ∈ Hloc ⊔ Cloc := htop_le (Subgroup.mem_top xF)
    have hxMap : x ∈ (Hloc ⊔ Cloc).map F.subtype :=
      Subgroup.mem_map.mpr ⟨xF, hxJoin, rfl⟩
    have hx : x ∈ MF ⊔ C := hjoin_map_le hxMap
    simpa [C, sup_comm] using hx
  · exact sup_le hC_le_F hMFleF

omit [IsMinCE G] in
private theorem CFSG.section15_fitting_eq_of_normal_le_fitting
    {M S : Subgroup G}
    (hSM : S ≤ M)
    (hSnormM : (S.subgroupOf M).Normal)
    (hFleS : section8FittingSubgroup M ≤ S) :
    section8FittingSubgroup S = section8FittingSubgroup M := by
  classical
  let FS : Subgroup G := section8FittingSubgroup S
  let F : Subgroup G := section8FittingSubgroup M
  have hFSleS : FS ≤ S := by
    simpa [FS] using section8FittingSubgroup_le S
  have hFSleM : FS ≤ M := hFSleS.trans hSM
  have hM_norm_S : M ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).1 hSnormM
  have hmapFS : (fittingSubgroup S).map S.subtype = FS := by
    rfl
  have hM_norm_FS : M ≤ Subgroup.normalizer (FS : Set G) := by
    intro m hm
    have hm' :
        m ∈ Subgroup.normalizer
          (((fittingSubgroup S).map S.subtype : Subgroup G) : Set G) :=
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := S) (K := fittingSubgroup S)) (hM_norm_S hm)
    simpa [hmapFS] using hm'
  have hFSnormM : (FS.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFSleM).2 hM_norm_FS
  have hFSsub_nil : Group.IsNilpotent (FS.subgroupOf M) := by
    let e : FS.subgroupOf M ≃* FS :=
      Subgroup.subgroupOfEquivOfLe (H := FS) (K := M) hFSleM
    exact Group.nilpotent_of_mulEquiv (G := FS) (G' := FS.subgroupOf M)
      (_h := by simpa [FS] using section8FittingSubgroup_isNilpotent S) e.symm
  have hFSsub_le_fit : FS.subgroupOf M ≤ fittingSubgroup M :=
    le_sSup ⟨hFSnormM, hFSsub_nil⟩
  have hFS_le_F : FS ≤ F := by
    have hmap_le : (FS.subgroupOf M).map M.subtype ≤ F :=
      Subgroup.map_mono hFSsub_le_fit
    simpa [F, section8FittingSubgroup, fittingSubgroupOf,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hFSleM] using hmap_le
  have hF_norm_S : (F.subgroupOf S).Normal := by
    have hM_norm_F : M ≤ Subgroup.normalizer (F : Set G) := by
      simpa [F] using section10_le_normalizer_fitting (G := G) M
    have hS_norm_F : S ≤ Subgroup.normalizer (F : Set G) := hSM.trans hM_norm_F
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFleS).2 hS_norm_F
  have hFsub_nil : Group.IsNilpotent (F.subgroupOf S) := by
    let e : F.subgroupOf S ≃* F :=
      Subgroup.subgroupOfEquivOfLe (H := F) (K := S) hFleS
    exact Group.nilpotent_of_mulEquiv (G := F) (G' := F.subgroupOf S)
      (_h := by simpa [F] using section8FittingSubgroup_isNilpotent M) e.symm
  have hFsub_le_fitS : F.subgroupOf S ≤ fittingSubgroup S :=
    le_sSup ⟨hF_norm_S, hFsub_nil⟩
  have hF_le_FS : F ≤ FS := by
    have hmap_le : (F.subgroupOf S).map S.subtype ≤ FS :=
      Subgroup.map_mono hFsub_le_fitS
    intro x hxF
    exact hmap_le (Subgroup.mem_map.mpr
      ⟨⟨x, hFleS hxF⟩, by simpa [Subgroup.mem_subgroupOf] using hxF, rfl⟩)
  exact le_antisymm hFS_le_F hF_le_FS

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_msigma_le_fitting_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section10Msigma M ≤ section8FittingSubgroup M := by
  rw [← hEq]
  exact section15_MF_le_fitting hMF

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_fitting_msigma_eq_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section8FittingSubgroup (section10Msigma M) = section10Msigma M := by
  rcases hMF.1 with ⟨_hMFM, _hMFnorm, hMFnil, _hMFHall⟩
  have hσnil : Group.IsNilpotent (section10Msigma M) := by
    rw [← hEq]
    exact hMFnil
  have hfit_top : fittingSubgroup (section10Msigma M) = ⊤ := by
    letI : Group.IsNilpotent (section10Msigma M) := hσnil
    exact fitting_eq_top_of_nilpotent (section10Msigma M)
  apply le_antisymm
  · exact section8FittingSubgroup_le (section10Msigma M)
  · intro x hx
    change x ∈ (fittingSubgroup (section10Msigma M)).map (section10Msigma M).subtype
    refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [hfit_top]
    simp

omit [IsMinCE G] in
public theorem CFSG.section15_fitting_eq_msigma_sup_sigma_compl_core_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section8FittingSubgroup M =
      section10Msigma M ⊔ section15SigmaComplementFittingCore M := by
  apply le_antisymm
  · simpa [section15SigmaComplementFittingCore] using
      section10_fitting_le_msigma_sup_sigma_compl_fitting_core (G := G) M
  · refine sup_le ?_ ?_
    · exact section15_msigma_le_fitting_of_MF_eq_msigma hMF hEq
    · simpa [section15SigmaComplementFittingCore] using
        (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
          (section8FittingSubgroup M))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_coprime_card_of_isPiSubgroup_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup π A) (hB : IsPiSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqA hqB
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqπ : q' ∈ π := hA q' hqA
  have hqρ : q' ∈ ρ := hB q' hqB
  exact (Set.disjoint_left.mp hπρ hqπ) hqρ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_disjoint_of_isPiSubgroup_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup π A) (hB : IsPiSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  have hcop : Nat.Coprime (Nat.card A) (Nat.card B) :=
    section15_coprime_card_of_isPiSubgroup_disjoint_primes hA hB hπρ
  have hcop_order : Nat.Coprime (orderOf x) (Nat.card B) :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard A hxA) hcop
  have hx_order_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order dvd_rfl
      (Subgroup.orderOf_dvd_natCard B hxB)
  exact orderOf_eq_one_iff.mp hx_order_one

public theorem CFSG.section15_internalDirectProduct_msigma_sigma_compl_core_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section12InternalDirectProduct
      (section8FittingSubgroup (section10Msigma M))
      (section15SigmaComplementFittingCore M)
      (section8FittingSubgroup M) := by
  classical
  let S : Subgroup G := section10Msigma M
  let Y : Subgroup G := section15SigmaComplementFittingCore M
  have hfitS : section8FittingSubgroup S = S := by
    simpa [S] using section15_fitting_msigma_eq_of_MF_eq_msigma hMF hEq
  have hFeq : section8FittingSubgroup M = S ⊔ Y := by
    simpa [S, Y] using
      section15_fitting_eq_msigma_sup_sigma_compl_core_of_MF_eq_msigma hMF hEq
  have hSleF : S ≤ section8FittingSubgroup M := by
    simpa [S] using section15_msigma_le_fitting_of_MF_eq_msigma hMF hEq
  have hYleF : Y ≤ section8FittingSubgroup M := by
    simpa [Y, section15SigmaComplementFittingCore] using
      (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M))
  have hSπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
    intro p hp
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hp
  have hYπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Y := by
    simpa [Y, section15SigmaComplementFittingCore] using
      piCoreIn_isPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ
        (section8FittingSubgroup M)
  have hπdisj : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes M)ᶜ := by
    rw [Set.disjoint_left]
    intro p hp hpcompl
    exact hpcompl hp
  have hSYdisj : Disjoint S Y :=
    section15_disjoint_of_isPiSubgroup_disjoint_primes hSπ hYπ hπdisj
  have hYcentS : Y ≤ Subgroup.centralizer (S : Set G) := by
    simpa [S, Y, section15SigmaComplementFittingCore] using
      section10_sigma_compl_fitting_core_le_centralizer_msigma (G := G) hM
  have hScentY : S ≤ Subgroup.centralizer (Y : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hYcentS hy) s hs).symm
  refine ⟨?_, hYleF, ?_, ?_, ?_⟩
  · rw [hfitS]
    exact hSleF
  · simpa [S, Y, hfitS] using hFeq
  · simpa [S, Y, hfitS] using hSYdisj
  · simpa [S, Y, hfitS] using hScentY

public theorem CFSG.section15_centralizer_MF_le_fitting_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    subgroupCentralizerIn M MF ≤ section8FittingSubgroup M := by
  classical
  let S : Subgroup G := section10Msigma M
  let C : Subgroup G := subgroupCentralizerIn M MF
  let Cσ : Subgroup G := subgroupCentralizerIn S MF
  have hSne : S ≠ ⊥ := by
    simpa [S] using theorem_10_2_e (M := M) hM
  have hMFne : MF ≠ ⊥ := by
    simpa [S, hEq] using hSne
  have hSHall : section15HallSubgroupOf S S := by
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    refine isHallSubgroup_of (G := S) (π := subgroupPrimeSet S)
      (H := (⊤ : Subgroup S)) ?_ ?_
    · intro p hp
      simpa [subgroupPrimeSet] using hp
    · intro p _ hpidx
      exact p.property.not_dvd_one (by simpa using hpidx)
  have hMFHall : section15HallSubgroupOf MF S := by
    simpa [S, hEq] using hSHall
  rcases section15_corollary15_3_a_hall_factor
      (M := M) (H := MF) hM hMFne hMFHall with
    ⟨X, hXleC, hXcyc, _hXτ2, hXHallσc, hfactor⟩
  have hC_le_M : C ≤ M := fun _ hx => hx.1
  have hCσleC : Cσ ≤ C := by
    intro x hx
    exact ⟨section15_msigma_le hx.1, hx.2⟩
  have hCσleS : Cσ ≤ S := fun _ hx => hx.1
  have hCσleMF : Cσ ≤ MF := by
    intro x hx
    exact (by simpa [S, hEq] using hCσleS hx)
  have hC_norm_S : C ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    exact section15_msigma_le_normalizer (M := M) hx.1
  have hC_norm_MF : C ≤ Subgroup.normalizer (MF : Set G) := by
    intro x hx
    exact centralizer_le_normalizer MF hx.2
  have hC_norm_Cσ : C ≤ Subgroup.normalizer (Cσ : Set G) := by
    simpa [C, Cσ] using
      section15_le_normalizer_subgroupCentralizerIn
        (G := G) (N := C) (E := S) (A := MF)
        hC_norm_S hC_norm_MF
  haveI : (Cσ.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCσleC).2 hC_norm_Cσ
  have hCσnormC : section10NormalIn Cσ C :=
    ⟨hCσleC, (inferInstance : (Cσ.subgroupOf C).Normal)⟩
  have hSπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
    intro p hp
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hp
  have hCσπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Cσ :=
    IsPiSubgroup.of_le hCσleS hSπ
  have hXσc : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ X := by
    intro p hpX
    have hcard : Nat.card (X.subgroupOf C) = Nat.card X :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (G := G) (H := X) (K := C) hXleC).toEquiv
    exact hXHallσc.p_in_pi_of_p_dvd_card p (by simpa [C, hcard] using hpX)
  have hσdisj : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes M)ᶜ := by
    rw [Set.disjoint_left]
    intro p hp hpcompl
    exact hpcompl hp
  have hCσXdisj : Disjoint Cσ X :=
    section15_disjoint_of_isPiSubgroup_disjoint_primes hCσπ hXσc hσdisj
  have hCeq : C = Cσ ⊔ X := by
    apply le_antisymm
    · intro z hzC
      have hzProd : z ∈ (Cσ : Set G) * (X : Set G) := by
        have hzProd0 :
            z ∈ (subgroupCentralizerIn (section10Msigma M) MF : Set G) *
              (X : Set G) := by
          rw [← hfactor]
          simpa [C] using hzC
        simpa [S, Cσ] using hzProd0
      rcases hzProd with ⟨a, haCσ, b, hbX, hab⟩
      rw [← hab]
      exact (Cσ ⊔ X).mul_mem (Subgroup.mem_sup_left haCσ) (Subgroup.mem_sup_right hbX)
    · exact sup_le hCσleC hXleC
  have hcompCX : section12ComplementIn C Cσ X :=
    ⟨hCσleC, hXleC, hCeq, hCσXdisj⟩
  have hσnil : Group.IsNilpotent S := by
    have hS_eq_MF : S = MF := by
      simpa [S] using hEq.symm
    rw [hS_eq_MF]
    exact hMF.1.2.2.1
  have hCσnil : Group.IsNilpotent Cσ := by
    letI : Group.IsNilpotent S := hσnil
    have hCσsub_nil : Group.IsNilpotent (Cσ.subgroupOf S) := by infer_instance
    let e : Cσ.subgroupOf S ≃* Cσ := Subgroup.subgroupOfEquivOfLe hCσleS
    exact Group.nilpotent_of_mulEquiv (G := Cσ.subgroupOf S) (G' := Cσ)
      (_h := hCσsub_nil) e
  have hXnil : Group.IsNilpotent X := by
    letI : IsCyclic X := hXcyc
    have hXcomm : IsMulCommutative X := by infer_instance
    letI : IsMulCommutative X := hXcomm
    letI : CommGroup X := IsMulCommutative.instCommGroup
    infer_instance
  have hCσcentX : Cσ ≤ Subgroup.centralizer (X : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    have hxCentMF : x ∈ Subgroup.centralizer (MF : Set G) := (hXleC hxX).2
    exact (Subgroup.mem_centralizer_iff.mp hxCentMF c (hCσleMF hc)).symm
  have hCnil : Group.IsNilpotent C :=
    section15_nilpotent_of_central_complement hcompCX hCσnormC
      hCσnil hXnil hCσcentX
  rcases hMF.1 with ⟨hMFM, hMFnormM, _hMFnil, _hMFHall⟩
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnormM
  have hM_norm_C : M ≤ Subgroup.normalizer (C : Set G) := by
    simpa [C] using
      section15_le_normalizer_subgroupCentralizerIn
        (G := G) (N := M) (E := M) (A := MF)
        (Subgroup.le_normalizer (H := M)) hM_norm_MF
  haveI : (C.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_M).2 hM_norm_C
  have hCsub_nil : Group.IsNilpotent (C.subgroupOf M) := by
    let e : C.subgroupOf M ≃* C := Subgroup.subgroupOfEquivOfLe hC_le_M
    exact Group.nilpotent_of_mulEquiv (G := C) (G' := C.subgroupOf M)
      (_h := hCnil) e.symm
  have hCsub_le_fit : C.subgroupOf M ≤ fittingSubgroup M :=
    le_sSup ⟨(inferInstance : (C.subgroupOf M).Normal), hCsub_nil⟩
  have hmap_le :
      (C.subgroupOf M).map M.subtype ≤ section8FittingSubgroup M :=
    Subgroup.map_mono hCsub_le_fit
  simpa [C, section8FittingSubgroup, fittingSubgroupOf,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hC_le_M] using hmap_le

private theorem CFSG.section15_corollary15_5_b_centralizer_product_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF := by
  classical
  let S : Subgroup G := section10Msigma M
  let Y : Subgroup G := section15SigmaComplementFittingCore M
  let C : Subgroup G := subgroupCentralizerIn M MF
  have hFeq : section8FittingSubgroup M = S ⊔ Y := by
    simpa [S, Y] using
      section15_fitting_eq_msigma_sup_sigma_compl_core_of_MF_eq_msigma hMF hEq
  have hC_le_F : C ≤ section8FittingSubgroup M := by
    simpa [C] using
      section15_centralizer_MF_le_fitting_of_MF_eq_msigma hM hMF hEq
  have hMF_le_F : MF ≤ section8FittingSubgroup M := by
    intro x hx
    have hxS : x ∈ S := by
      simpa [S, hEq] using hx
    exact section15_msigma_le_fitting_of_MF_eq_msigma hMF hEq hxS
  apply le_antisymm
  · rw [hFeq]
    refine sup_le ?_ ?_
    · intro x hxS
      exact Subgroup.mem_sup_right (by simpa [S, hEq] using hxS : x ∈ MF)
    · have hYleF : Y ≤ section8FittingSubgroup M := by
        simpa [Y, section15SigmaComplementFittingCore] using
          (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
            (section8FittingSubgroup M))
      have hYleM : Y ≤ M := hYleF.trans (section8FittingSubgroup_le M)
      have hYcentMF : Y ≤ Subgroup.centralizer (MF : Set G) := by
        simpa [S, Y, hEq, section15SigmaComplementFittingCore] using
          section10_sigma_compl_fitting_core_le_centralizer_msigma (G := G) hM
      intro y hyY
      exact Subgroup.mem_sup_left (show y ∈ C from ⟨hYleM hyY, hYcentMF hyY⟩)
  · exact sup_le hC_le_F hMF_le_F

/-- Corollary 15.5(b): `M'' ≤ F(M) = C_M(M_F)M_F =
F(M_σ) × O_{σ(M)'}(F(M))`. -/
private theorem CFSG.section15_corollary15_5_b_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section15SecondDerivedSubgroup M ≤ section8FittingSubgroup M ∧
      section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF ∧
        section8FittingSubgroup M =
          section8FittingSubgroup (section10Msigma M) ⊔
            section15SigmaComplementFittingCore M ∧
          section12InternalDirectProduct
            (section8FittingSubgroup (section10Msigma M))
            (section15SigmaComplementFittingCore M)
            (section8FittingSubgroup M) := by
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU⟩
  have h151a := lemma_15_1_a (G := G) (M := M) (K := K) (U := U) hM hKU
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (section15_secondDerived_le_of_quotientAbelian_ambientDerived
      h151a.2.2.2.2).trans
        (section15_msigma_le_fitting_of_MF_eq_msigma hMF hEq)
  · exact section15_corollary15_5_b_centralizer_product_of_MF_eq_msigma
      hM hMF hEq
  · rw [section15_fitting_msigma_eq_of_MF_eq_msigma hMF hEq]
    exact section15_fitting_eq_msigma_sup_sigma_compl_core_of_MF_eq_msigma hMF hEq
  · exact section15_internalDirectProduct_msigma_sigma_compl_core_of_MF_eq_msigma
      hM hMF hEq

/-- Corollary 15.5(b), proper branch `M_F ≠ M_σ`: Theorem 15.2(g) supplies
the displayed Fitting and centralizer chain. -/
private theorem CFSG.section15_corollary15_5_b_remaining_of_MF_ne_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hNe : MF ≠ section10Msigma M) :
    section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF ∧
      section8FittingSubgroup M =
        section8FittingSubgroup (section10Msigma M) ⊔
          section15SigmaComplementFittingCore M ∧
        section12InternalDirectProduct
          (section8FittingSubgroup (section10Msigma M))
          (section15SigmaComplementFittingCore M)
          (section8FittingSubgroup M) := by
  classical
  let S : Subgroup G := section10Msigma M
  let F : Subgroup G := section8FittingSubgroup M
  let C : Subgroup G := subgroupCentralizerIn M MF
  let Y : Subgroup G := section15SigmaComplementFittingCore M
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with
    ⟨K, hK⟩
  rcases theorem_15_2_c (M := M) (MF := MF) (K := K)
      hM hMF hK hNe with
    ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
  rcases theorem_15_2_d (M := M) (MF := MF) (K := K) (Q := Q)
      (q := q) hM hMF hK hNe hq hQ hQnormal hQMF with
    ⟨D, hD⟩
  have hg := theorem_15_2_g (M := M) (MF := MF) (K := K)
    (Q := Q) (D := D) (q := q) hM hMF hK hNe hq hQ hQnormal hQMF hD
  have hF_eq_QC : F = Q ⊔ subgroupCentralizerIn M Q := by
    simpa [F] using hg.2.2.1
  have hC_le_CQ : C ≤ subgroupCentralizerIn M Q := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyQ
    exact Subgroup.mem_centralizer_iff.mp hx.2 y (hQMF hyQ)
  have hC_le_F : C ≤ F := by
    intro x hx
    rw [hF_eq_QC]
    exact Subgroup.mem_sup_right (hC_le_CQ hx)
  have hF_eq_CMFMF : F = C ⊔ MF := by
    simpa [F, C] using
      section15_fitting_eq_centralizer_sup_of_MF
        (M := M) (MF := MF) hMF (by simpa [F, C] using hC_le_F)
  have hFleS : F ≤ S := by
    simpa [F, S] using le_of_lt hg.2.2.2.2.2.1
  have hFitS_eq_F : section8FittingSubgroup S = F := by
    have hSnormM : (S.subgroupOf M).Normal := by
      simpa [S] using (section15_msigma_normalIn (M := M)).2
    simpa [S, F] using
      section15_fitting_eq_of_normal_le_fitting
        (M := M) (S := S) (by simpa [S] using section15_msigma_le (M := M))
        hSnormM (by simpa [S, F] using hFleS)
  have hYbot : Y = ⊥ := by
    have hYleF : Y ≤ F := by
      simpa [Y, F, section15SigmaComplementFittingCore] using
        (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
          (section8FittingSubgroup M))
    have hYleS : Y ≤ S := hYleF.trans hFleS
    have hYπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Y := by
      simpa [Y, section15SigmaComplementFittingCore] using
        piCoreIn_isPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ
          (section8FittingSubgroup M)
    have hSπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
      intro p hp
      exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hp
    have hπdisj : Disjoint (section10SigmaPrimes M)ᶜ (section10SigmaPrimes M) := by
      rw [Set.disjoint_left]
      intro p hpcompl hp
      exact hpcompl hp
    have hYSdisj : Disjoint Y S :=
      section15_disjoint_of_isPiSubgroup_disjoint_primes hYπ hSπ hπdisj
    apply le_antisymm ?_ bot_le
    intro y hy
    exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hYSdisj hy (hYleS hy))
  have hF_decomp : F = section8FittingSubgroup S ⊔ Y := by
    simp [hFitS_eq_F, hYbot]
  have hIDP :
      section12InternalDirectProduct
        (section8FittingSubgroup S) Y F := by
    refine ⟨?_, ?_, hF_decomp, ?_, ?_⟩
    · rw [hFitS_eq_F]
    · rw [hYbot]
      exact bot_le
    · rw [Subgroup.disjoint_def]
      intro x _ hxY
      rw [hYbot] at hxY
      exact Subgroup.mem_bot.mp hxY
    · intro x _hx
      rw [hYbot, Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : y = 1 := Subgroup.mem_bot.mp hy
      rw [hy1]
      simp
  exact ⟨by simpa [F, C] using hF_eq_CMFMF,
    by simpa [F, S, Y] using hF_decomp,
    by simpa [F, S, Y] using hIDP⟩

private theorem CFSG.section15_corollary15_5_b_of_MF_ne_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hNe : MF ≠ section10Msigma M) :
    section15SecondDerivedSubgroup M ≤ section8FittingSubgroup M ∧
      section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF ∧
        section8FittingSubgroup M =
          section8FittingSubgroup (section10Msigma M) ⊔
            section15SigmaComplementFittingCore M ∧
          section12InternalDirectProduct
            (section8FittingSubgroup (section10Msigma M))
            (section15SigmaComplementFittingCore M)
            (section8FittingSubgroup M) := by
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with
    ⟨K, hK⟩
  rcases theorem_15_2_c (M := M) (MF := MF) (K := K)
      hM hMF hK hNe with
    ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
  rcases theorem_15_2_d (M := M) (MF := MF) (K := K) (Q := Q)
      (q := q) hM hMF hK hNe hq hQ hQnormal hQMF with
    ⟨D, hD⟩
  have hg := theorem_15_2_g (M := M) (MF := MF) (K := K)
    (Q := Q) (D := D) (q := q) hM hMF hK hNe hq hQ hQnormal hQMF hD
  exact ⟨hg.2.1, section15_corollary15_5_b_remaining_of_MF_ne_msigma
    hM hMF hNe⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_quotientAbelian_implies_quotientNilpotent
    {H K : Subgroup G}
    (h : section15QuotientAbelian H K) :
    section10QuotientNilpotent H K := by
  rcases h with ⟨hKH, hNorm, hComm⟩
  refine ⟨hKH, hNorm, ?_⟩
  letI : IsMulCommutative (H ⧸ K.subgroupOf H) := hComm
  letI : CommGroup (H ⧸ K.subgroupOf H) := IsMulCommutative.instCommGroup
  infer_instance

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_quotient_nilpotent_of_normal_complement_le
    {S Q D N : Subgroup G}
    (hcomp : section12ComplementIn S Q D)
    (hQnorm : section10NormalIn Q S)
    (hQleN : Q ≤ N)
    (hNleS : N ≤ S)
    (hNnorm : (N.subgroupOf S).Normal)
    (hDnil : Group.IsNilpotent D) :
    section10QuotientNilpotent S N := by
  classical
  let Qloc : Subgroup S := Q.subgroupOf S
  let Nloc : Subgroup S := N.subgroupOf S
  let Dloc : Subgroup S := D.subgroupOf S
  haveI : Qloc.Normal := by
    simpa [Qloc] using hQnorm.2
  haveI : Nloc.Normal := by
    simpa [Nloc] using hNnorm
  have hcomp_symm : section12ComplementIn S D Q := by
    rcases hcomp with ⟨hQS, hDS, hsup, hdisj⟩
    exact ⟨hDS, hQS, by simpa [sup_comm] using hsup, hdisj.symm⟩
  have hcomp' : Dloc.IsComplement' Qloc := by
    simpa [Qloc, Dloc] using
      section15_normal_complementIn_isComplement'
        (M := S) (K := D) (N := Q) hcomp_symm hQnorm
  have hDloc_nil : Group.IsNilpotent Dloc := by
    let e : Dloc ≃* D :=
      Subgroup.subgroupOfEquivOfLe (H := D) (K := S) hcomp.2.1
    exact Group.nilpotent_of_mulEquiv (G := D) (G' := Dloc) (_h := hDnil) e.symm
  have hquotQ_nil : Group.IsNilpotent (S ⧸ Qloc) := by
    let e : S ⧸ Qloc ≃* Dloc := hcomp'.QuotientMulEquiv
    exact Group.nilpotent_of_mulEquiv (G := Dloc) (G' := S ⧸ Qloc)
      (_h := hDloc_nil) e.symm
  have hQloc_le_Nloc : Qloc ≤ Nloc := by
    intro x hx
    have hxQ : (x : G) ∈ Q := by
      simpa [Qloc, Subgroup.mem_subgroupOf] using hx
    exact hQleN hxQ
  have hQloc_le_Nloc' : Qloc ≤ Nloc.comap (MonoidHom.id S) := by
    simpa [Subgroup.comap_id] using hQloc_le_Nloc
  let π : S ⧸ Qloc →* S ⧸ Nloc :=
    QuotientGroup.map Qloc Nloc (MonoidHom.id S) hQloc_le_Nloc'
  have hπ_surj : Function.Surjective π := by
    intro y
    refine QuotientGroup.induction_on y ?_
    intro s
    exact ⟨QuotientGroup.mk' Qloc s, by simp [π]⟩
  refine ⟨hNleS, hNnorm, ?_⟩
  exact Group.nilpotent_of_surjective (G := S ⧸ Qloc) (G' := S ⧸ Nloc)
    π hπ_surj

public theorem CFSG.corollary_15_5_b
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    section15SecondDerivedSubgroup M ≤ section8FittingSubgroup M ∧
      section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF ∧
        section8FittingSubgroup M =
          section8FittingSubgroup (section10Msigma M) ⊔
            section15SigmaComplementFittingCore M ∧
          section12InternalDirectProduct
            (section8FittingSubgroup (section10Msigma M))
            (section15SigmaComplementFittingCore M)
            (section8FittingSubgroup M) := by
  by_cases hEq : MF = section10Msigma M
  · exact section15_corollary15_5_b_of_MF_eq_msigma hM hMF hEq
  · exact section15_corollary15_5_b_of_MF_ne_msigma hM hMF hEq

/-- Corollary 15.5(c): `M_F ≤ M'` and `M'/M_F` is nilpotent. -/
private theorem CFSG.section15_corollary15_5_c_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    MF ≤ ambientDerivedSubgroup M ∧
      section10QuotientNilpotent (ambientDerivedSubgroup M) MF := by
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU⟩
  have h151a := lemma_15_1_a (G := G) (M := M) (K := K) (U := U) hM hKU
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact h151a.2.2.2.1
  · rw [hEq]
    exact section15_quotientAbelian_implies_quotientNilpotent h151a.2.2.2.2

/-- Corollary 15.5(c), proper branch `M_F ≠ M_σ`: Theorem 15.2(g) yields
`M_σ = M'`, and the proper-branch quotient is nilpotent. -/
private theorem CFSG.section15_corollary15_5_c_of_MF_ne_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hNe : MF ≠ section10Msigma M) :
    MF ≤ ambientDerivedSubgroup M ∧
      section10QuotientNilpotent (ambientDerivedSubgroup M) MF := by
  refine ⟨?_, ?_⟩
  · exact (section15_MF_le_msigma hM hMF).trans
      (section15_msigma_le_ambientDerived hM)
  · rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with
      ⟨K, hK⟩
    rcases theorem_15_2_c (M := M) (MF := MF) (K := K)
        hM hMF hK hNe with
      ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
    rcases theorem_15_2_d (M := M) (MF := MF) (K := K) (Q := Q)
        (q := q) hM hMF hK hNe hq hQ hQnormal hQMF with
      ⟨D, hD⟩
    have hMFleS : MF ≤ section10Msigma M :=
      section15_MF_le_msigma hM hMF
    have hQleS : Q ≤ section10Msigma M := hQMF.trans hMFleS
    have hQnormS : section10NormalIn Q (section10Msigma M) := by
      refine ⟨hQleS, ?_⟩
      have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
      have hS_norm_Q :
          section10Msigma M ≤ Subgroup.normalizer (Q : Set G) :=
        section15_msigma_le.trans hM_norm_Q
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQleS).2 hS_norm_Q
    have hMFnormS : (MF.subgroupOf (section10Msigma M)).Normal := by
      rcases hMF.1 with ⟨hMFM, hMFnormM, _hMFnil, _hMFHall⟩
      have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnormM
      have hS_norm_MF :
          section10Msigma M ≤ Subgroup.normalizer (MF : Set G) :=
        section15_msigma_le.trans hM_norm_MF
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleS).2 hS_norm_MF
    rw [← hD.1]
    exact section15_quotient_nilpotent_of_normal_complement_le
      (S := section10Msigma M) (Q := Q) (D := D) (N := MF)
      hD.2.1 hQnormS hQMF hMFleS hMFnormS hD.2.2.1

public theorem CFSG.corollary_15_5_c
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    MF ≤ ambientDerivedSubgroup M ∧
      section10QuotientNilpotent (ambientDerivedSubgroup M) MF := by
  by_cases hEq : MF = section10Msigma M
  · exact section15_corollary15_5_c_of_MF_eq_msigma hM hMF hEq
  · exact section15_corollary15_5_c_of_MF_ne_msigma hM hMF hEq

omit [IsMinCE G] in
private theorem CFSG.section15_MFamilyP_of_nontrivial_hall_kappa
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKne : K ≠ ⊥) :
    M ∈ section14MFamilyP G := by
  classical
  rcases hK with ⟨hKM, hKHall⟩
  have hK_card_ne_one : Nat.card K ≠ 1 := by
    intro hcard
    exact hKne ((Subgroup.card_eq_one (H := K)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hK_card_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hcard_sub : Nat.card (K.subgroupOf M) = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKM).toEquiv
  have hq_sub : q.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [q, hcard_sub] using hq0dvd
  exact ⟨hM, ⟨q, hKHall.p_in_pi_of_p_dvd_card q hq_sub⟩⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_complement_isHall_compl_of_isHall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {K D : Subgroup R}
    (hKHall : IsHallSubgroup π K)
    (hcomp : K.IsComplement' D) :
    IsHallSubgroup πᶜ D := by
  classical
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := D) ?_ ?_
  · intro q hqD hqπ
    have hqKidx : q.val ∣ K.index := by
      simpa [hcomp.symm.index_eq_card] using hqD
    exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqDidx
    have hqK : q.val ∣ Nat.card K := by
      simpa [hcomp.index_eq_card] using hqDidx
    exact hqπc (hKHall.p_in_pi_of_p_dvd_card q hqK)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isPiSubgroup_le_normal_hall_of_solvable
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {N X : Subgroup R}
    (hsolv : IsSolvable R)
    [N.Normal]
    (hNHall : IsHallSubgroup π N)
    (hXπ : IsPiSubgroup (G := R) π X) :
    X ≤ N := by
  classical
  letI : MulDistribMulAction Unit R := {
    smul := fun _ x => x
    one_smul := fun x => rfl
    mul_smul := fun _ _ x => rfl
    smul_mul := fun _ x y => rfl
    smul_one := fun _ => rfl }
  have hXinv : IsInvariant Unit R X := by
    refine ⟨?_⟩
    intro a x
    simp
  rcases exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := R) (A := Unit) hsolv (by simp) π X hXπ hXinv with
    ⟨H, hHHall, _hHinv, hXH⟩
  exact hXH.trans (hNHall.le_of_normal hHHall)

private theorem CFSG.section15_tau2_subset_kappa_compl_of_MFamilyP
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12Tau2Primes M ⊆ (section14KappaPrimes M)ᶜ := by
  intro q hqτ2 hqκ
  have hκeq : section14KappaPrimes M = section12Tau1Primes M :=
    (theorem_14_7_c (G := G) (M := M) (K := K) hM hK).2
  have hqτ1 : q ∈ section12Tau1Primes M := by
    simpa [hκeq] using hqκ
  exact (section15_tau2_disjoint_tau1_tau3 (M := M) (q := q) hqτ2)
    (Or.inl hqτ1)

private theorem CFSG.section15_sigma_complement_fitting_core_le_derived_of_nontrivial_K
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKne : K ≠ ⊥) :
    section15SigmaComplementFittingCore M ≤ ambientDerivedSubgroup M := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Y : Subgroup G := section15SigmaComplementFittingCore M
  let Kloc : Subgroup M := K.subgroupOf M
  let Dloc : Subgroup M := D.subgroupOf M
  let Yloc : Subgroup M := Y.subgroupOf M
  have hMP : M ∈ section14MFamilyP G :=
    section15_MFamilyP_of_nontrivial_hall_kappa hM hK hKne
  have hDnorm : section10NormalIn D M := by
    simpa [D] using section15_ambientDerived_normalIn (M := M)
  have hcompAmb : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := M) (K := K) hMP hK
  have hcompLoc : Kloc.IsComplement' Dloc := by
    simpa [Kloc, Dloc] using
      section15_normal_complementIn_isComplement'
        (M := M) (K := K) (N := D) hcompAmb hDnorm
  have hKlocHall : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hDlocHall : IsHallSubgroup (section14KappaPrimes M)ᶜ Dloc :=
    section15_complement_isHall_compl_of_isHall hKlocHall hcompLoc
  haveI : Dloc.Normal := by
    simpa [Dloc] using hDnorm.2
  have hYleM : Y ≤ M := by
    exact (piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ
      (section8FittingSubgroup M)).trans (section8FittingSubgroup_le M)
  have hYτ2 : IsPiSubgroup (G := G) (section12Tau2Primes M) Y := by
    simpa [Y] using section15_sigma_complement_fitting_core_tau2
      (M := M) (MF := MF) hM hMF
  have hτ2κc :
      section12Tau2Primes M ⊆ (section14KappaPrimes M)ᶜ :=
    section15_tau2_subset_kappa_compl_of_MFamilyP (M := M) (K := K) hMP hK
  have hYlocπ :
      IsPiSubgroup (G := M) (section14KappaPrimes M)ᶜ Yloc := by
    intro q hqYloc
    have hcard : Nat.card Yloc = Nat.card Y :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Y) (K := M) hYleM).toEquiv
    exact hτ2κc (hYτ2 q (by simpa [Yloc, hcard] using hqYloc))
  have hMsolv : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hYloc_le_Dloc : Yloc ≤ Dloc :=
    section15_isPiSubgroup_le_normal_hall_of_solvable
      (R := M) (π := (section14KappaPrimes M)ᶜ)
      (N := Dloc) (X := Yloc) hMsolv hDlocHall hYlocπ
  intro x hxY
  have hxM : x ∈ M := hYleM hxY
  have hxYloc : (⟨x, hxM⟩ : M) ∈ Yloc := by
    simpa [Yloc, Subgroup.mem_subgroupOf] using hxY
  have hxDloc : (⟨x, hxM⟩ : M) ∈ Dloc := hYloc_le_Dloc hxYloc
  simpa [D, Dloc, Subgroup.mem_subgroupOf] using hxDloc

/-- Corollary 15.5(d): if `K ≠ 1`, then `F(M) ≤ M'`. -/
private theorem CFSG.section15_corollary15_5_fitting_le_derived_of_nontrivial_K
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKne : K ≠ ⊥) :
    section8FittingSubgroup M ≤ ambientDerivedSubgroup M := by
  by_cases hEq : MF = section10Msigma M
  · rw [section15_fitting_eq_msigma_sup_sigma_compl_core_of_MF_eq_msigma hMF hEq]
    exact sup_le (section15_msigma_le_ambientDerived hM)
      (section15_sigma_complement_fitting_core_le_derived_of_nontrivial_K
        hM hMF hK hKne)
  · rcases theorem_15_2_c (M := M) (MF := MF) (K := K)
        hM hMF hK hEq with
      ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
    rcases theorem_15_2_d (M := M) (MF := MF) (K := K) (Q := Q)
        (q := q) hM hMF hK hEq hq hQ hQnormal hQMF with
      ⟨D, hD⟩
    have hg := theorem_15_2_g (M := M) (MF := MF) (K := K) (Q := Q)
      (D := D) (q := q) hM hMF hK hEq hq hQ hQnormal hQMF hD
    have hFleS : section8FittingSubgroup M ≤ section10Msigma M :=
      le_of_lt hg.2.2.2.2.2.1
    rw [← hg.2.2.2.2.2.2]
    exact hFleS

public theorem CFSG.corollary_15_5_d
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKne : K ≠ ⊥) :
    section8FittingSubgroup M ≤ ambientDerivedSubgroup M := by
  exact section15_corollary15_5_fitting_le_derived_of_nontrivial_K
    hM hMF hK hKne

end Section15
