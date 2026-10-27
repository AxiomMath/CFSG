module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_5
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe u v

/-! ## (13.5) -/


private theorem theorem_13_5_virtualCharacter_one_eq_int
    {K : Type u}
    [Group K]
    [Finite K]
    {phi : Section1.ClassFunction K}
    (hphi : Theory.Character.IsVirtualCharacter phi) :
    ∃ z : ℤ, phi 1 = (z : ℂ) := by
  classical
  rcases hphi with ⟨r, m, n, rho, hphi_eq⟩
  refine ⟨∑ i : Fin r, m i * (n i : ℤ), ?_⟩
  have hdegree : ∀ i : Fin r, (rho i).character 1 = (n i : ℂ) := by
    intro i
    simp
  rw [hphi_eq]
  unfold Theory.Character.virtualCharacterOfRepresentations
  simp_rw [hdegree]
  exact_mod_cast (rfl : (∑ i : Fin r, m i * (n i : ℤ)) =
    ∑ i : Fin r, m i * (n i : ℤ))

private theorem theorem_13_5_subgroup_restriction_raw_energy_eq_ambient
    {K : Type u}
    [Group K]
    [Finite K]
    (H M : Subgroup K)
    (phiM : Section1.ClassFunction M)
    (phiH : Section1.ClassFunction H)
    (hres : classFunctionRestrictionData H M phiM phiH)
    (hsupp : Section1.supportedOn phiM (H.subgroupOf M : Set M)) :
    (Nat.card H : ℝ) * Section5.cfNormSq phiH =
      (Nat.card M : ℝ) * Section5.cfNormSq phiM := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype M := Fintype.ofFinite M
  rcases hres with ⟨hHM, hres⟩
  let e : H.subgroupOf M ≃ H :=
    (Subgroup.subgroupOfEquivOfLe hHM).toEquiv
  have heval : ∀ x : H.subgroupOf M, phiH (e x) = phiM (x : M) := by
    intro x
    simpa [e] using hres (e x)
  have hsum_subgroup :
      (∑ x : H.subgroupOf M, Complex.normSq (phiM (x : M))) =
        ∑ x : H, Complex.normSq (phiH x) := by
    calc
      (∑ x : H.subgroupOf M, Complex.normSq (phiM (x : M))) =
          ∑ x : H.subgroupOf M, Complex.normSq (phiH (e x)) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            rw [heval]
      _ = ∑ x : H, Complex.normSq (phiH x) :=
        Equiv.sum_comp e (fun x : H => Complex.normSq (phiH x))
  have hsum_support :
      (∑ x : M, Complex.normSq (phiM x)) =
        ∑ x : H.subgroupOf M, Complex.normSq (phiM (x : M)) := by
    have hfiltered :
        (∑ x : M, Complex.normSq (phiM x)) =
          ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ H.subgroupOf M),
            Complex.normSq (phiM x) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : x ∈ H.subgroupOf M
      · simp [hx]
      · have hzero := (Section1.supportedOn_iff.mp hsupp) x hx
        simp [hx, hzero]
    rw [hfiltered]
    exact Finset.sum_subtype
      (s := Finset.univ.filter (fun x : M => x ∈ H.subgroupOf M))
      (p := fun x : M => x ∈ H.subgroupOf M)
      (f := fun x : M => Complex.normSq (phiM x)) (by simp)
  rw [Section5.cfNormSq_eq_inv_card_mul_sum_normSq,
    Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
  have hHcard : (Nat.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hMcard : (Nat.card M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := M)).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hHcard, one_mul,
    ← mul_assoc, mul_inv_cancel₀ hMcard, one_mul]
  exact hsum_subgroup.symm.trans hsum_support.symm

private theorem theorem_13_5_punctured_energy_eq_card_mul_cfNormSq_sub_one
    {K : Type u}
    [Group K]
    [Finite K]
    (H : Subgroup K)
    (phi : Section1.ClassFunction H) :
    Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) phi =
      (Nat.card H : ℝ) * Section5.cfNormSq phi - Complex.normSq (phi 1) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have henergy :
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) phi =
        ∑ x : H, if x = 1 then 0 else Complex.normSq (phi x) := by
    unfold Section7.subgroupSupportEnergy
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp
    ·
      intro x _hx
      by_cases hx : x = 1
      · simp [Section7.puncturedSubgroupSet, hx]
      · have hxK : (x : K) ≠ 1 := by
          intro h
          exact hx (Subtype.ext h)
        simp [Section7.puncturedSubgroupSet, hx, hxK]
  have hsum :
      (∑ x : H, if x = 1 then 0 else Complex.normSq (phi x)) =
        (∑ x : H, Complex.normSq (phi x)) - Complex.normSq (phi 1) := by
    calc
      (∑ x : H, if x = 1 then 0 else Complex.normSq (phi x)) =
          ∑ x : H, if x ≠ 1 then Complex.normSq (phi x) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            by_cases hx : x = 1 <;> simp [hx]
      _ = ∑ x ∈ Finset.univ.filter (fun x : H => x ≠ 1),
          Complex.normSq (phi x) := by
            exact (Finset.sum_filter (s := Finset.univ)
              (p := fun x : H => x ≠ 1)
              (f := fun x : H => Complex.normSq (phi x))).symm
      _ = ∑ x ∈ Finset.univ.erase (1 : H), Complex.normSq (phi x) := by
            congr 1
            ext x
            by_cases hx : x = 1 <;> simp [hx]
      _ = (∑ x : H, Complex.normSq (phi x)) - Complex.normSq (phi 1) := by
            exact Finset.sum_erase_eq_sub (s := Finset.univ)
              (f := fun x : H => Complex.normSq (phi x))
              (Finset.mem_univ (1 : H))
  rw [henergy, hsum, Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
  have hcard : (Nat.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  field_simp [hcard]

private theorem theorem_13_5_subgroupInKernel_conjugateOrbitConj_iff
    {K : Type u}
    [Group K]
    (H A : Subgroup K)
    [hH : H.Normal]
    [hA : A.Normal]
    (hAH : A ≤ H)
    (theta : Section1.ClassFunction H)
    (i : Section1.conjugateOrbitIndex H theta) :
    Section1.subgroupInKernel'
        (Section1.conjugateOrbitConj H theta i) (A.subgroupOf H) ↔
      Section1.subgroupInKernel' theta (A.subgroupOf H) := by
  have hconjugate_iff : ∀ x : K,
      Section1.subgroupInKernel'
          (Section1.conjugateOnNormal H theta x) (A.subgroupOf H) ↔
        Section1.subgroupInKernel' theta (A.subgroupOf H) := by
    intro x
    constructor
    · intro hker a
      have hmemA : x⁻¹ * (((a : A.subgroupOf H) : H) : K) * x ∈ A := by
        simpa using hA.conj_mem (((a : A.subgroupOf H) : H) : K)
          (Subgroup.mem_subgroupOf.mp a.property) x⁻¹
      have hmemH : x⁻¹ * (((a : A.subgroupOf H) : H) : K) * x ∈ H := hAH hmemA
      have hker' :=
        hker ⟨⟨x⁻¹ * (((a : A.subgroupOf H) : H) : K) * x, hmemH⟩,
          Subgroup.mem_subgroupOf.mpr hmemA⟩
      have hdegree :
          Section1.degree (Section1.conjugateOnNormal H theta x) =
            Section1.degree theta := by
        unfold Section1.conjugateOnNormal Section1.degree
        exact congrArg theta (Subtype.ext (by simp))
      rw [hdegree] at hker'
      simpa [Section1.conjugateOnNormal, mul_assoc] using hker'
    · intro hker a
      have hmemA : x * (((a : A.subgroupOf H) : H) : K) * x⁻¹ ∈ A := by
        simpa using hA.conj_mem (((a : A.subgroupOf H) : H) : K)
          (Subgroup.mem_subgroupOf.mp a.property) x
      have hmemH : x * (((a : A.subgroupOf H) : H) : K) * x⁻¹ ∈ H := hAH hmemA
      have hker' :=
        hker ⟨⟨x * (((a : A.subgroupOf H) : H) : K) * x⁻¹, hmemH⟩,
          Subgroup.mem_subgroupOf.mpr hmemA⟩
      have hdegree :
          Section1.degree (Section1.conjugateOnNormal H theta x) =
            Section1.degree theta := by
        unfold Section1.conjugateOnNormal Section1.degree
        exact congrArg theta (Subtype.ext (by simp))
      rw [hdegree]
      simpa [Section1.conjugateOnNormal] using hker'
  refine Quotient.inductionOn i ?_
  intro x
  exact hconjugate_iff x

private theorem theorem_13_5_subgroupRestriction_inducedCF_orthogonal_of_kernel
    {K : Type u}
    [Group K]
    [Finite K]
    (H A : Subgroup K)
    [H.Normal]
    [A.Normal]
    (hAH : A ≤ H)
    (theta psi : Section1.ClassFunction H)
    (htheta_irreducible : Section1.IsIrreducibleCharacterOnGroup theta)
    (htheta_not_kernel :
      ¬ Section1.subgroupInKernel' theta (A.subgroupOf H))
    (hpsi_irreducible : Section1.IsIrreducibleCharacterOnGroup psi)
    (hpsi_kernel : Section1.subgroupInKernel' psi (A.subgroupOf H)) :
    Section1.scalarProduct H
        (Section1.subgroupRestriction H (Section1.inducedCF H theta)) psi = 0 := by
  classical
  rcases htheta_irreducible with ⟨n, rho, hrho_irreducible, htheta⟩
  subst theta
  letI orbitFintype : Fintype (Section1.conjugateOrbitIndex H rho.character) :=
    Quotient.fintype (Section1.conjugateOrbitSetoid H rho.character)
  have horbit_zero : ∀ i : Section1.conjugateOrbitIndex H rho.character,
      Section1.scalarProduct H
        (Section1.conjugateOrbitConj H rho.character i) psi = 0 := by
    intro i
    have horbit_irreducible :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.conjugateOrbitConj H rho.character i) := by
      refine ⟨n, Section1.conjugateOrbitRepresentation H rho i, ?_, ?_⟩
      · letI : Representation.IsIrreducible rho := hrho_irreducible
        exact Section1.irreducible_conjugateRepresentation H rho (Quotient.out i)
      · exact Section1.conjugateOrbitConj_representationCharacter H rho i
    have horbit_ne : Section1.conjugateOrbitConj H rho.character i ≠ psi := by
      intro heq
      apply htheta_not_kernel
      apply (theorem_13_5_subgroupInKernel_conjugateOrbitConj_iff
        H A hAH rho.character i).mp
      simpa [heq] using hpsi_kernel
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      horbit_irreducible hpsi_irreducible horbit_ne
  let orbitSum : Section1.ClassFunction H := fun h =>
    ∑ i : Section1.conjugateOrbitIndex H rho.character,
      Section1.conjugateOrbitConj H rho.character i h
  have horbitSum_zero : Section1.scalarProduct H orbitSum psi = 0 := by
    simpa [orbitSum, horbit_zero] using Section1.scalarProduct_fintype_sum_left
      (fun i : Section1.conjugateOrbitIndex H rho.character =>
        Section1.conjugateOrbitConj H rho.character i) psi
  have hrestriction :
      Section1.subgroupRestriction H (Section1.inducedCF H rho.character) =
        (H.relIndex (Section1.inertiaSubgroup H rho.character) : ℂ) • orbitSum := by
    rw [Section1.proposition_1_5_a_orbit_relIndex_canonical H rho]
    ext h
    apply congrArg (fun z : ℂ =>
      (H.relIndex (Section1.inertiaSubgroup H rho.character) : ℂ) * z)
    apply Finset.sum_congr
    · ext i
      simp
    · intro i _hi
      rfl
  rw [hrestriction, Section1.scalarProduct_smul_left, horbitSum_zero, mul_zero]

private theorem theorem_13_5_restriction_inducedCF_orthogonal_kernelConstituent
    {K : Type u}
    [Group K]
    [Finite K]
    (H M P : Subgroup K)
    (phiM : Section1.ClassFunction M)
    (phiH alpha : Section1.ClassFunction H)
    (theta : Section1.ClassFunction (H.subgroupOf M))
    (hres : classFunctionRestrictionData H M phiM phiH)
    (hPH : P ≤ H)
    (hHnormal : (H.subgroupOf M).Normal)
    (hPnormal : (P.subgroupOf M).Normal)
    (htheta_irreducible : Section1.IsIrreducibleCharacterOnGroup theta)
    (htheta_not_kernel : ¬ Section1.subgroupInKernel' theta
      ((P.subgroupOf M).subgroupOf (H.subgroupOf M)))
    (hphiM : phiM = Section1.inducedCF (H.subgroupOf M) theta)
    (halpha : virtualCharacterKernelConstituentData H P alpha) :
    Section1.scalarProduct H phiH alpha = 0 := by
  classical
  rcases hres with ⟨hHM, hres⟩
  let e : H.subgroupOf M ≃* H := Subgroup.subgroupOfEquivOfLe hHM
  let phiHsub : Section1.ClassFunction (H.subgroupOf M) :=
    Section6.theorem_6_8_transportClassFunction e.symm phiH
  let alphaSub : Section1.ClassFunction (H.subgroupOf M) :=
    Section6.theorem_6_8_transportClassFunction e.symm alpha
  have hphiHsub :
      phiHsub = Section1.subgroupRestriction (H.subgroupOf M) phiM := by
    ext x
    simpa [phiHsub, e, Section6.theorem_6_8_transportClassFunction,
      Section1.subgroupRestriction] using hres (e x)
  have hPHsub : P.subgroupOf M ≤ H.subgroupOf M := by
    intro x hx
    change ((x : M) : K) ∈ H
    exact hPH (by simpa [Subgroup.mem_subgroupOf] using hx)
  letI : (H.subgroupOf M).Normal := hHnormal
  letI : (P.subgroupOf M).Normal := hPnormal
  rcases halpha with ⟨halpha_virtual, halpha_kernel⟩
  have halpha_class : Section1.IsClassFunction alpha :=
    Section1.isVirtualCharacter_isClassFunction halpha_virtual
  rcases Theory.Character.irreducible_characters_form_basis (G := H) with
    ⟨ι, hι, chi, hchi, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let psi : ι → Section1.ClassFunction H :=
    fun i => Section1.ofConjClassFunction (chi i)
  have hpsi_irreducible : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (psi i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hchi.1 i)
  have hcoeff_int : ∀ i,
      ∃ z : ℤ, Section1.scalarProduct H alpha (psi i) = (z : ℂ) := by
    intro i
    exact Section3.scalarProduct_isVirtualCharacter_eq_int halpha_virtual
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hpsi_irreducible i))
  let coeff := Section3.irreducibleBasisCoeff alpha hcoeff_int
  have halpha_decomp : Section1.evalCoeff psi coeff = alpha := by
    simpa [psi, coeff] using
      (Section3.irreducibleBasis_evalCoeff_coeff hchi b hb alpha
        halpha_class hcoeff_int)
  let psiSub : ι → Section1.ClassFunction (H.subgroupOf M) := fun i =>
    Section6.theorem_6_8_transportClassFunction e.symm (psi i)
  have hpsiSub_irreducible : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (psiSub i) := by
    intro i
    exact Section6.theorem_6_8_transportClassFunction_irreducible e.symm
      (hpsi_irreducible i)
  have halphaSub_decomp :
      alphaSub = ∑ i : ι, (coeff i : ℂ) • psiSub i := by
    ext x
    have hdecomp_at := congrArg
      (fun f : Section1.ClassFunction H => f (e x)) halpha_decomp
    simpa [alphaSub, psiSub, Section6.theorem_6_8_transportClassFunction,
      Section1.evalCoeff] using hdecomp_at.symm
  rw [← Section6.theorem_6_8_scalarProduct_transportClassFunction e.symm phiH alpha]
  change Section1.scalarProduct (H.subgroupOf M) phiHsub alphaSub = 0
  rw [hphiHsub, hphiM, halphaSub_decomp]
  have hsum_pointwise :
      (∑ i : ι, (coeff i : ℂ) • psiSub i) =
        (fun x => ∑ i : ι, (((coeff i : ℂ) • psiSub i) x)) := by
    ext x
    simp
  rw [hsum_pointwise]
  rw [Section1.scalarProduct_fintype_sum_right]
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases hcoeff_zero : coeff i = 0
  · rw [hcoeff_zero, Int.cast_zero, zero_smul]
    unfold Section1.scalarProduct
    simp
  have hscalar_ne : Section1.scalarProduct H alpha (psi i) ≠ 0 := by
    intro hscalar_zero
    have hspec := Section3.irreducibleBasisCoeff_spec alpha hcoeff_int i
    have hcast : ((coeff i : ℤ) : ℂ) = 0 := by
      simpa [coeff, psi, hscalar_zero] using hspec.symm
    exact hcoeff_zero (Int.cast_eq_zero.mp hcast)
  have hpsi_kernel :
      Section1.subgroupInKernel' (psi i) (P.subgroupOf H) :=
    halpha_kernel (psi i) (hpsi_irreducible i) hscalar_ne
  have hpsiSub_kernel : Section1.subgroupInKernel' (psiSub i)
      ((P.subgroupOf M).subgroupOf (H.subgroupOf M)) := by
    intro a
    have haP : ((e (a : H.subgroupOf M) : H) : K) ∈ P := by
      change ((((a : (P.subgroupOf M).subgroupOf (H.subgroupOf M)) :
        H.subgroupOf M) : M) : K) ∈ P
      exact Subgroup.mem_subgroupOf.mp a.property
    let aPH : P.subgroupOf H :=
      ⟨e (a : H.subgroupOf M), Subgroup.mem_subgroupOf.mpr haP⟩
    have hkernel_at := hpsi_kernel aPH
    simpa [psiSub, aPH, e, Section6.theorem_6_8_transportClassFunction,
      Section1.degree] using hkernel_at
  have horthogonal :=
    theorem_13_5_subgroupRestriction_inducedCF_orthogonal_of_kernel
      (H.subgroupOf M) (P.subgroupOf M) hPHsub theta (psiSub i)
      htheta_irreducible htheta_not_kernel (hpsiSub_irreducible i)
      hpsiSub_kernel
  rw [Section1.scalarProduct_smul_right, horthogonal, mul_zero]

private theorem theorem_13_5_support_energy_punctured_subgroup_eq
    {K : Type u}
    [Group K]
    [Finite K]
    (H : Subgroup K)
    (phiK : Section1.ClassFunction K)
    (phiH : Section1.ClassFunction H)
    (hagree : ∀ x : H, (x : K) ≠ 1 → phiK (x : K) = phiH x) :
    Section7.supportEnergy (Section7.puncturedSubgroupSet H) phiK =
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) phiH := by
  classical
  unfold Section7.supportEnergy Section7.subgroupSupportEnergy
  have hfiltered :
      (∑ g : K, if g ∈ Section7.puncturedSubgroupSet H then
          Complex.normSq (phiK g) else 0) =
        ∑ g ∈ Finset.univ.filter (fun g : K => g ∈ H),
          if g ∈ Section7.puncturedSubgroupSet H then
            Complex.normSq (phiK g) else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro g _hg
    by_cases hgH : g ∈ H
    · simp [hgH]
    · have hgsharp : g ∉ Section7.puncturedSubgroupSet H := by
        intro hg
        exact hgH hg.1
      simp [hgH, hgsharp]
  rw [hfiltered]
  rw [Finset.sum_subtype
    (s := Finset.univ.filter (fun g : K => g ∈ H))
    (p := fun g : K => g ∈ H)
    (f := fun g : K => if g ∈ Section7.puncturedSubgroupSet H then
      Complex.normSq (phiK g) else 0) (by simp)]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hx : (x : K) ∈ Section7.puncturedSubgroupSet H
  · rw [if_pos hx, if_pos hx, hagree x hx.2]
  · rw [if_neg hx, if_neg hx]

private noncomputable def theorem_13_5_crossSum
    {K : Type u}
    [Group K]
    [Finite K]
    (H : Subgroup K)
    (A : Set K)
    (phi psi : Section1.ClassFunction H) : ℂ := by
  classical
  exact ∑ x : H, if (x : K) ∈ A then phi x * star (psi x) else 0

private theorem theorem_13_5_crossSum_punctured_eq_card_mul_scalarProduct_sub_one
    {K : Type u}
    [Group K]
    [Finite K]
    (H : Subgroup K)
    (phi psi : Section1.ClassFunction H) :
    theorem_13_5_crossSum H (Section7.puncturedSubgroupSet H) phi psi =
      (Nat.card H : ℂ) * Section1.scalarProduct H phi psi -
        phi 1 * star (psi 1) := by
  classical
  unfold theorem_13_5_crossSum Section1.scalarProduct
  have hpunctured :
      (∑ x : H, if (x : K) ∈ Section7.puncturedSubgroupSet H then
          phi x * star (psi x) else 0) =
        (∑ x : H, phi x * star (psi x)) - phi 1 * star (psi 1) := by
    calc
      (∑ x : H, if (x : K) ∈ Section7.puncturedSubgroupSet H then
          phi x * star (psi x) else 0) =
          ∑ x : H, if x ≠ 1 then phi x * star (psi x) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            by_cases hx : x = 1
            · simp [Section7.puncturedSubgroupSet, hx]
            · have hxK : (x : K) ≠ 1 := by
                intro h
                exact hx (Subtype.ext h)
              simp [Section7.puncturedSubgroupSet, hx, hxK]
      _ = ∑ x ∈ Finset.univ.filter (fun x : H => x ≠ 1),
          phi x * star (psi x) := by
            exact (Finset.sum_filter (s := Finset.univ)
              (p := fun x : H => x ≠ 1)
              (f := fun x : H => phi x * star (psi x))).symm
      _ = ∑ x ∈ Finset.univ.erase (1 : H), phi x * star (psi x) := by
            congr 1
            ext x
            by_cases hx : x = 1 <;> simp [hx]
      _ = (∑ x : H, phi x * star (psi x)) - phi 1 * star (psi 1) := by
            exact Finset.sum_erase_eq_sub (s := Finset.univ)
              (f := fun x : H => phi x * star (psi x))
              (Finset.mem_univ (1 : H))
  rw [hpunctured]
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  congr 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _hx
    rfl

private theorem theorem_13_5_subgroup_energy_cast_add
    {K : Type u}
    [Group K]
    [Finite K]
    (H : Subgroup K)
    (A : Set K)
    (r : ℂ)
    (phi psi : Section1.ClassFunction H)
    (hr : star r = r) :
    ((Section7.subgroupSupportEnergy H A
        (fun x => r * phi x + psi x) : ℝ) : ℂ) =
      r ^ 2 * (Section7.subgroupSupportEnergy H A phi : ℂ) +
        r * theorem_13_5_crossSum H A phi psi +
        r * theorem_13_5_crossSum H A psi phi +
        (Section7.subgroupSupportEnergy H A psi : ℂ) := by
  classical
  letI : DecidablePred (fun x : K => x ∈ H) := Classical.decPred _
  letI : Fintype H := H.instFintypeSubtypeMemOfDecidablePred
  have hcast : ∀ f : Section1.ClassFunction H,
      ((∑ x : H, if (x : K) ∈ A then Complex.normSq (f x) else 0 : ℝ) : ℂ) =
        ∑ x : H, if (x : K) ∈ A then f x * star (f x) else 0 := by
    intro f
    calc
      ((∑ x : H, if (x : K) ∈ A then Complex.normSq (f x) else 0 : ℝ) : ℂ) =
          ∑ x : H, ((if (x : K) ∈ A then Complex.normSq (f x) else 0 : ℝ) : ℂ) := by
            simp
      _ = ∑ x : H, if (x : K) ∈ A then f x * star (f x) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        by_cases hx : (x : K) ∈ A
        · simp only [hx, if_pos]
          calc
            ((Complex.normSq (f x) : ℝ) : ℂ) = star (f x) * f x :=
              Complex.normSq_eq_conj_mul_self
            _ = f x * star (f x) := by rw [mul_comm]
        · simp [hx]
  unfold Section7.subgroupSupportEnergy theorem_13_5_crossSum
  change ((∑ x : H, if (x : K) ∈ A then
    Complex.normSq (r * phi x + psi x) else 0 : ℝ) : ℂ) = _
  rw [hcast (fun x => r * phi x + psi x), hcast phi, hcast psi]
  calc
    (∑ x : H, if (x : K) ∈ A then
        (r * phi x + psi x) * star (r * phi x + psi x) else 0) =
      ∑ x : H, (
        r ^ 2 * (if (x : K) ∈ A then phi x * star (phi x) else 0) +
          r * (if (x : K) ∈ A then phi x * star (psi x) else 0) +
          r * (if (x : K) ∈ A then psi x * star (phi x) else 0) +
          (if (x : K) ∈ A then psi x * star (psi x) else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        by_cases hx : (x : K) ∈ A
        · simp [hx, hr]
          ring
        · simp [hx]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem theorem_13_5_isMulCommutative_sup_of_le_centralizer
    {G : Type u} [Group G]
    {A Y : Subgroup G}
    (hAcomm : IsMulCommutative A)
    (hYcomm : IsMulCommutative Y)
    (hYleCentA : Y ≤ Subgroup.centralizer (A : Set G)) :
    IsMulCommutative (A ⊔ Y : Subgroup G) := by
  classical
  let D : Subgroup G := A ⊔ Y
  let AD : Subgroup D := A.subgroupOf D
  let YD : Subgroup D := Y.subgroupOf D
  have hA_norm_Y : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'Y : y' ∈ Y := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy'Y) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'Y
  haveI : YD.Normal := by
    simpa [D, YD] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := Y) hA_norm_Y)
  have hAD_YD_top : AD ⊔ YD = ⊤ := by
    calc
      AD ⊔ YD = D.subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := A) (A' := Y) (B := D) (by simp [D]) (by simp [D])
      _ = ⊤ := by simp
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxTop : x ∈ AD ⊔ YD := by simp [hAD_YD_top]
  have hyTop : y ∈ AD ⊔ YD := by simp [hAD_YD_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := x)).1 hxTop with
    ⟨aD, haD, bD, hbD, hxab⟩
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := y)).1 hyTop with
    ⟨cD, hcD, dD, hdD, hycd⟩
  let a : G := aD
  let b : G := bD
  let c : G := cD
  let d : G := dD
  have haA : a ∈ A := by simpa [a, AD, Subgroup.mem_subgroupOf] using haD
  have hbY : b ∈ Y := by simpa [b, YD, Subgroup.mem_subgroupOf] using hbD
  have hcA : c ∈ A := by simpa [c, AD, Subgroup.mem_subgroupOf] using hcD
  have hdY : d ∈ Y := by simpa [d, YD, Subgroup.mem_subgroupOf] using hdD
  have hx_eq : (x : G) = a * b := by
    have hval := congrArg (fun z : D => (z : G)) hxab
    simpa [a, b] using hval.symm
  have hy_eq : (y : G) = c * d := by
    have hval := congrArg (fun z : D => (z : G)) hycd
    simpa [c, d] using hval.symm
  have hac : a * c = c * a :=
    setLike_mul_comm (s := A) haA hcA
  have hbd : b * d = d * b :=
    setLike_mul_comm (s := Y) hbY hdY
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hYleCentA hbY) c hcA).symm
  have had : a * d = d * a :=
    Subgroup.mem_centralizer_iff.mp (hYleCentA hdY) a haA
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [hx_eq, hy_eq]
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by simp [mul_assoc]
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by simp [mul_assoc]
    _ = c * (d * a) * b := by rw [had]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

public theorem theorem_13_5_H_subgroupOf_isMulCommutative
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) (_ : H ≤ Smax) :
    IsMulCommutative (H.subgroupOf Smax) := by
  have hsourceOrig := hsource
  have h13_2 := theorem_13_2
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  rcases h13_2 with
    ⟨_hMF, _htype, _hq_lt_p, hUcomm, _hfrob, hPelem, _hPcard, _hu_bound,
      _hcoherent, _hbook, _hA0, _hnorm⟩
  have hPcomm : IsMulCommutative P := hPelem.toIsMulCommutative
  have hCeq : C = subgroupCentralizerIn U P := by
    exact hsourceOrig.2.2.2.2.2.1
  have hCcomm : IsMulCommutative C := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : ((x : C) : G) ∈ subgroupCentralizerIn U P := by
      rw [← hCeq]
      exact x.property
    have hy : ((y : C) : G) ∈ subgroupCentralizerIn U P := by
      rw [← hCeq]
      exact y.property
    apply Subtype.ext
    exact setLike_mul_comm (s := U)
      hx.1 hy.1
  have hCleCentP : C ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    have hx' : x ∈ subgroupCentralizerIn U P := by
      rw [← hCeq]
      exact hx
    exact hx'.2
  have hHcomm : IsMulCommutative H := by
    rw [hH]
    exact theorem_13_5_isMulCommutative_sup_of_le_centralizer
      hPcomm hCcomm hCleCentP
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  exact setLike_mul_comm (s := H)
    (show (((x : H.subgroupOf Smax) : Smax) : G) ∈ H from x.property)
    (show (((y : H.subgroupOf Smax) : Smax) : G) ∈ H from y.property)

private theorem theorem_13_5_inducedFamilyNotation_insert_principal_of_punctured
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hS : Section7.puncturedInducedFamily H S) :
    Section7.inducedFamilyNotation H
      (insert (Section1.inducedCF H (Section1.principalCharacter H)) S) := by
  classical
  intro χ
  constructor
  · intro hχ
    rw [Finset.mem_insert] at hχ
    rcases hχ with hχ | hχ
    · refine ⟨Section1.principalCharacter H,
        Section3.principalCharacter_isIrreducibleCharacterOnGroup, ?_⟩
      simp [hχ]
    · rcases (hS χ).mp hχ with ⟨θ, hθirr, _hθne, hχeq⟩
      exact ⟨θ, hθirr, hχeq⟩
  · rintro ⟨θ, hθirr, hχeq⟩
    rw [Finset.mem_insert]
    by_cases hθ : θ = Section1.principalCharacter H
    · left
      rw [hχeq, hθ]
    · right
      exact (hS χ).mpr ⟨θ, hθirr, hθ, hχeq⟩

private theorem theorem_13_5_inducedFamilyEnumeration_with_base
    {L : Type u} [Group L] [Finite L]
    (T : Finset (Section1.ClassFunction L))
    (ζ0 : Section1.ClassFunction L)
    (hζ0T : ζ0 ∈ T)
    (hdegree : ∀ ζ : Section1.ClassFunction L, ζ ∈ T →
      Section1.degree ζ = Section1.degree ζ0) :
    ∃ n : ℕ, ∃ η : Fin (n + 1) → Section1.ClassFunction L,
      Section7.inducedFamilyEnumeration T η (fun _ : Fin n => (1 : ℂ)) ∧
        η 0 = ζ0 := by
  classical
  let R : Finset (Section1.ClassFunction L) := T.erase ζ0
  let n : ℕ := Fintype.card {ζ : Section1.ClassFunction L // ζ ∈ R}
  let restEquiv : Fin n ≃ {ζ : Section1.ClassFunction L // ζ ∈ R} :=
    (Fintype.equivFin _).symm
  let η : Fin (n + 1) → Section1.ClassFunction L :=
    Fin.cases ζ0 (fun i : Fin n => (restEquiv i).1)
  have hηmem : ∀ i : Fin (n + 1), η i ∈ T := by
    intro i
    cases i using Fin.cases with
    | zero => simpa [η] using hζ0T
    | succ i =>
        exact (Finset.mem_erase.mp (restEquiv i).2).2
  have henum :
      Section7.inducedFamilyEnumeration T η (fun _ : Fin n => (1 : ℂ)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro ζ
      constructor
      · intro hζT
        by_cases hζ : ζ = ζ0
        · exact ⟨0, by simp [η, hζ]⟩
        · have hζR : ζ ∈ R := by simp [R, hζ, hζT]
          let x : {ζ : Section1.ClassFunction L // ζ ∈ R} := ⟨ζ, hζR⟩
          refine ⟨Fin.succ (restEquiv.symm x), ?_⟩
          simp [η, x]
      · rintro ⟨i, rfl⟩
        exact hηmem i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => rfl
          | succ j =>
              exfalso
              have hjne : (restEquiv j).1 ≠ ζ0 :=
                (Finset.mem_erase.mp (restEquiv j).2).1
              exact hjne (by simpa [η] using hij.symm)
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exfalso
              have hine : (restEquiv i).1 ≠ ζ0 :=
                (Finset.mem_erase.mp (restEquiv i).2).1
              exact hine (by simpa [η] using hij)
          | succ j =>
              apply congrArg Fin.succ
              apply restEquiv.injective
              apply Subtype.ext
              simpa [η] using hij
    · intro i
      simp only [one_mul]
      calc
        Section1.degree (η (Fin.succ i)) = Section1.degree ζ0 :=
          hdegree _ (hηmem (Fin.succ i))
        _ = Section1.degree (η 0) := by simp [η]
  exact ⟨n, η, henum, by simp [η]⟩

private theorem theorem_13_5_transportClassFunction_isCharacter
    {K L : Type u} [Group K] [Finite K] [Group L] [Finite L]
    (e : K ≃* L) {χ : Section1.ClassFunction K}
    (hχ : Section1.IsCharacter χ) :
    Section1.IsCharacter (Section6.theorem_6_8_transportClassFunction e χ) := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, hχeq⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance,
    ρ.comp e.symm.toMonoidHom, ?_⟩
  ext x
  simp [Section6.theorem_6_8_transportClassFunction, hχeq,
    Representation.character]

private theorem theorem_13_5_isVirtualCharacter_int_smul
    {K : Type u} [Group K] [Finite K]
    (z : ℤ) {phi : Section1.ClassFunction K}
    (hphi : Theory.Character.IsVirtualCharacter phi) :
    Theory.Character.IsVirtualCharacter ((z : ℂ) • phi) := by
  classical
  rcases hphi with ⟨r, m, n, rho, rfl⟩
  refine ⟨r, fun i => z * m i, n, rho, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum,
    mul_assoc]

private theorem theorem_13_5_isVirtualCharacter_fintype_int_sum
    {K : Type u} {I : Type v} [Group K] [Finite K] [Fintype I]
    (z : I → ℤ) (phi : I → Section1.ClassFunction K)
    (hphi : ∀ i, Theory.Character.IsVirtualCharacter (phi i)) :
    Theory.Character.IsVirtualCharacter (∑ i : I, (z i : ℂ) • phi i) := by
  classical
  have hsum : ∀ s : Finset I,
      Theory.Character.IsVirtualCharacter (∑ i ∈ s, (z i : ℂ) • phi i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using Section3.isVirtualCharacter_sub
          (G := K) (χ := Section1.principalCharacter K)
          (ψ := Section1.principalCharacter K)
          Section3.isVirtualCharacter_principalCharacter
          Section3.isVirtualCharacter_principalCharacter
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact Section3.isVirtualCharacter_add
          (theorem_13_5_isVirtualCharacter_int_smul (z i) (hphi i)) ih
  simpa using hsum Finset.univ

private theorem theorem_13_5_integer_sum_character_kernelConstituentData
    {K : Type u} {I : Type v} [Group K] [Finite K] [Fintype I]
    (H P : Subgroup K)
    (z : I → ℤ) (beta : I → Section1.ClassFunction H)
    (hbetaChar : ∀ i, Section1.IsCharacter (beta i))
    (hbetaKer : ∀ i,
      Section1.subgroupInKernel' (beta i) (P.subgroupOf H)) :
    virtualCharacterKernelConstituentData H P
      (∑ i : I, (z i : ℂ) • beta i) := by
  classical
  have hbetaVirt : ∀ i, Theory.Character.IsVirtualCharacter (beta i) :=
    fun i => Section5.isVirtualCharacter_of_isCharacter (hbetaChar i)
  refine ⟨theorem_13_5_isVirtualCharacter_fintype_int_sum z beta hbetaVirt, ?_⟩
  intro theta hthetaIrr hscalar
  by_contra hthetaNotKer
  apply hscalar
  have hsumPointwise :
      (∑ i : I, (z i : ℂ) • beta i) =
        (fun x => ∑ i : I, (((z i : ℂ) • beta i) x)) := by
    ext x
    simp
  rw [hsumPointwise]
  rw [Section1.scalarProduct_fintype_sum_left]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [Section1.scalarProduct_smul_left]
  have hthetaBeta : Section1.scalarProduct H theta (beta i) = 0 := by
    by_contra hne
    exact hthetaNotKer
      (hypothesis_13_1_subgroupInKernel_of_irreducible_constituent_of_kernel_character
        (P.subgroupOf H) theta (beta i) hthetaIrr (hbetaChar i)
        (hbetaKer i) hne)
  have hbetaTheta : Section1.scalarProduct H (beta i) theta = 0 := by
    rw [← Section1.scalarProduct_star_swap (beta i) theta, hthetaBeta]
    simp
  rw [hbetaTheta, mul_zero]

private theorem theorem_13_5_normalized_induced_restriction_kernel_package
    {G : Type u} [Group G] [Finite G]
    (H M P : Subgroup G)
    (hHM : H ≤ M) (hPH : P ≤ H)
    (hHnormal : (H.subgroupOf M).Normal)
    (hPnormal : (P.subgroupOf M).Normal)
    (η : Section1.ClassFunction M)
    (θ : Section1.ClassFunction (H.subgroupOf M))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ
      ((P.subgroupOf M).subgroupOf (H.subgroupOf M)))
    (hη : η = Section1.inducedCF (H.subgroupOf M) θ) :
    ∃ β : Section1.ClassFunction H,
      Section1.IsCharacter β ∧
        Section1.subgroupInKernel' β (P.subgroupOf H) ∧
        ∀ x : H,
          β x = (Section5.cfNormSq η : ℂ)⁻¹ * η ⟨(x : G), hHM x.property⟩ := by
  classical
  let HS : Subgroup M := H.subgroupOf M
  let PS : Subgroup M := P.subgroupOf M
  have hPHS : PS ≤ HS := by
    intro x hx
    exact hPH hx
  letI : HS.Normal := hHnormal
  letI : PS.Normal := hPnormal
  have hθchar : Section1.IsCharacter θ :=
    Section6.theorem_6_8_isCharacter_of_irreducible hθirr
  rcases hθirr with ⟨m, θrep, hθrepirr, hθeq⟩
  subst θ
  let orbitRep := Section1.conjugateOrbitSumRepresentation HS θrep
  let orbitChar : Section1.ClassFunction HS := orbitRep.character
  let e : HS ≃* H := Subgroup.subgroupOfEquivOfLe hHM
  let β : Section1.ClassFunction H :=
    Section6.theorem_6_8_transportClassFunction e orbitChar
  have horbitChar : Section1.IsCharacter orbitChar := by
    exact ⟨_, inferInstance, inferInstance, inferInstance, orbitRep, rfl⟩
  have hβchar : Section1.IsCharacter β :=
    theorem_13_5_transportClassFunction_isCharacter e horbitChar
  have hηchar : Section1.IsCharacter η := by
    rw [hη]
    exact Section1.isCharacter_inducedCF_of_isCharacter HS θrep.character
      hθchar
  let r : ℕ := HS.relIndex (Section1.inertiaSubgroup HS θrep.character)
  have hr : (r : ℂ) ≠ 0 := by
    have hrNat : r ≠ 0 := by
      dsimp [r]
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    exact_mod_cast hrNat
  have hself : Section1.scalarProduct M η η = (r : ℂ) := by
    rw [hη]
    simpa [HS, r] using
      (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        HS θrep hθrepirr)
  have hnorm : (Section5.cfNormSq η : ℂ) = (r : ℂ) := by
    exact (Section5.scalarProduct_self_eq_cfNormSq_of_character hηchar).symm.trans hself
  have hres :
      Section1.subgroupRestriction HS η =
        (fun z : HS => (r : ℂ) * orbitChar z) := by
    rw [hη]
    simpa [HS, r, orbitChar, orbitRep,
      Section1.character_conjugateOrbitSumRepresentation] using
      (Section1.proposition_1_5_a_orbit_relIndex_canonical HS θrep)
  have hβeval : ∀ x : H,
      β x = (Section5.cfNormSq η : ℂ)⁻¹ * η ⟨(x : G), hHM x.property⟩ := by
    intro x
    have hx := congrFun hres (e.symm x)
    change η (e.symm x : HS) = (r : ℂ) * orbitChar (e.symm x) at hx
    change orbitChar (e.symm x) = _
    rw [hnorm]
    have he : (e.symm x : M) = ⟨(x : G), hHM x.property⟩ := Subtype.ext rfl
    rw [← he, hx]
    field_simp [hr]
  have hindKer : Section1.subgroupInKernel' η PS := by
    rw [hη]
    exact (Section1.proposition_1_6_a HS PS hPHS θrep).mp hθker
  have hβker : Section1.subgroupInKernel' β (P.subgroupOf H) := by
    intro x
    have hxP : ((e.symm (x : H) : HS) : M) ∈ PS := by
      exact x.property
    have hker := hindKer ⟨(e.symm (x : H) : M), hxP⟩
    have hβone := hβeval (1 : H)
    have hβx := hβeval (x : H)
    have hxM_val : (e.symm (x : H) : M) = ⟨(x : G), hHM (x : H).property⟩ := Subtype.ext rfl
    have h1M_val : (1 : M) = ⟨(1 : G), hHM (Subgroup.one_mem H)⟩ := Subtype.ext rfl
    have h1e : (e.symm (1 : H) : M) = (1 : M) := by simp
    unfold Section1.degree
    rw [hβx, hβone]
    simpa [Section1.degree, hxM_val, h1M_val, h1e] using congrArg
      (fun z : ℂ => (Section5.cfNormSq η : ℂ)⁻¹ * z) hker
  exact ⟨β, hβchar, hβker, hβeval⟩

private theorem theorem_13_5_expansion_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (ζ1H : Section1.ClassFunction H)
    (χ : Section1.ClassFunction G)
    (a : ℂ)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hhyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 χ a)
    (_hres : classFunctionRestrictionData H Smax ζ1 ζ1H) :
    ∃ α : Section1.ClassFunction H,
      virtualCharacterKernelConstituentData H P α ∧
        (∃ z : ℤ, a = (z : ℂ)) ∧
          ∀ x : H, (x : G) ≠ 1 →
            χ (x : G) =
              (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x + α x := by
  classical
  letI : Fintype Smax := Fintype.ofFinite Smax
  letI : Fintype (H.subgroupOf Smax) := Fintype.ofFinite (H.subgroupOf Smax)
  rcases _hhyp with
    ⟨hH, hS1, hζ0S1, hζ1S1, hζ01, hχvirt, ha, hzero⟩
  have hHS : H ≤ Smax := hS1.1
  have hPH : P ≤ H := hS1.2.1
  have hsourceFields := _hsource
  rcases hsourceFields with
    ⟨_hcaseB, hptypeS, _htypeT, _hp, _hq, hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _htail⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hptypeS
  have hHnormal : (H.subgroupOf Smax).Normal := by
    have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
      simpa [hfit] using section8FittingSubgroup_normal_in Smax
    simpa [hH] using hPCnormal
  rcases hptypeS with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfitDef, _hfitDer,
      _hW2le, _hW2cyc, _hW2ne, _hcent, _hnorm⟩
  rcases hMF with ⟨⟨_hPSmax, hPnormal, _hPnil, _hPHall⟩, _hPmax⟩
  letI : (H.subgroupOf Smax).Normal := hHnormal
  letI : IsMulCommutative (H.subgroupOf Smax) :=
    theorem_13_5_H_subgroupOf_isMulCommutative
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        p q u v c d _hsource hH hHS
  rcases Section12.exists_puncturedInducedFamily (H.subgroupOf Smax) with
    ⟨S, hS⟩
  let T : Finset (Section1.ClassFunction Smax) :=
    insert (Section7.principalInducedCharacter Smax H) S
  have hTnotation : Section7.inducedFamilyNotation (H.subgroupOf Smax) T := by
    dsimp [T]
    exact theorem_13_5_inducedFamilyNotation_insert_principal_of_punctured
      (H := H.subgroupOf Smax) (S := S) hS
  rcases (hS1.2.2 ζ0).mp hζ0S1 with
    ⟨θ0, hθ0irr, hθ0notker, hζ0ind⟩
  rcases (hS1.2.2 ζ1).mp hζ1S1 with
    ⟨θ1, hθ1irr, _hθ1notker, hζ1ind⟩
  have hζ0T : ζ0 ∈ T :=
    (hTnotation ζ0).mpr ⟨θ0, hθ0irr, hζ0ind⟩
  have hζ1T : ζ1 ∈ T :=
    (hTnotation ζ1).mpr ⟨θ1, hθ1irr, hζ1ind⟩
  have hTdegree : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ T →
      Section1.degree ζ = Section1.degree ζ0 := by
    intro ζ hζT
    rcases (hTnotation ζ).mp hζT with ⟨θ, hθirr, hζind⟩
    have hθdeg : Section1.degree θ = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθirr
    have hθ0deg : Section1.degree θ0 = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθ0irr
    calc
      Section1.degree ζ =
          (Subgroup.index (H.subgroupOf Smax) : ℂ) * Section1.degree θ := by
            rw [hζind, Section1.degree_inducedClassFunction]
      _ = (Subgroup.index (H.subgroupOf Smax) : ℂ) := by rw [hθdeg, mul_one]
      _ = (Subgroup.index (H.subgroupOf Smax) : ℂ) * Section1.degree θ0 := by
            rw [hθ0deg, mul_one]
      _ = Section1.degree ζ0 := by
            rw [hζ0ind, Section1.degree_inducedClassFunction]
  rcases theorem_13_5_inducedFamilyEnumeration_with_base T ζ0 hζ0T hTdegree with
    ⟨n, η, henum, hη0⟩
  have hη1index : ∃ i : Fin n, η (Fin.succ i) = ζ1 := by
    rcases (henum.1 ζ1).mp hζ1T with ⟨j, hj⟩
    cases j using Fin.cases with
    | zero =>
        exfalso
        exact hζ01 (hj.trans hη0).symm
    | succ i => exact ⟨i, hj.symm⟩
  rcases hη1index with ⟨i1, hηi1⟩
  let A : Set G := Section7.puncturedSubgroupSet H
  let K : G → Subgroup G := fun _ => ⊥
  have hAnonempty : A.Nonempty := by
    dsimp [A]
    by_contra hnone
    apply hθ0notker
    intro x
    have hxone :
        (((((x : (P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)) :
          H.subgroupOf Smax) : Smax) : G)) = 1 := by
      by_contra hxne
      apply hnone
      exact ⟨((((x : (P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)) :
        H.subgroupOf Smax) : Smax) : G),
        (x : H.subgroupOf Smax).property, hxne⟩
    change θ0 (x : H.subgroupOf Smax) = θ0 1
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hxone
  have hAneOne : ∀ x : G, x ∈ A → x ≠ 1 := by
    intro x hx
    exact hx.2
  have hTI16 : section16TISubsetWithNormalizer A Smax := by
    simpa [A] using
      (section13_theorem_13_2_H_punctured_tiNormalizer_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
          p q u v c d _hsource hH)
  have hTI2 : Section2.IsTISubsetWithNormalizer A Smax :=
    Section8.section2_IsTISubsetWithNormalizer_of_section16
      hAneOne hAnonempty hTI16
  have h71 : Section2.Hypothesis2 A Smax K := by
    simpa [K] using (Section2.proposition_2_3 A Smax hAnonempty).mp hTI2
  have h76 : Section7.hypothesis_7_6_statement A Smax H K T :=
    ⟨hHS, hHnormal, h71, by rfl, hTnotation⟩
  let τind : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G :=
    Section1.inducedCFLinear Smax
  have hτind : Section7.agreesWithDadeTransform A Smax K τind := by
    refine ⟨h71.subset_L, ?_⟩
    intro phi hphi
    dsimp [τind]
    exact (section13_dadeTransform_eq_inducedCFLinear_of_section16TI
      A Smax K hTI16 h71 phi hphi).symm
  have hbasis : Section7.projectionBasisPackage A Smax H η (fun _ : Fin n => 1) :=
    Section7.projectionBasisPackage_of_inducedFamilyEnumeration_source_bridge
      h76 henum
  let coeff : Fin n → ℂ := fun i =>
    Section1.scalarProduct G
      (τind (η (Fin.succ i) - η 0)) χ
  have hcoeffPackage :
      Section7.projectionCoefficientPackage η (fun _ : Fin n => 1)
        τind χ coeff := by
    intro i
    simp [coeff]
  have hχclass : Section1.IsClassFunction χ :=
    Section1.isVirtualCharacter_isClassFunction hχvirt
  have h77 := Section7.theorem_7_7 A Smax H K T η
    (fun _ : Fin n => 1) τind χ coeff
      h76 hτind henum hbasis hχclass hcoeffPackage
  rcases theorem_13_2_agreesWithInductionOnBookAZero
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d _hsource with
    ⟨_Ms, A0book, H_A0, hA0hyp, _hMsChoice, _hA0TI, _hMsSharp,
      hFittingSharp, _hASet, _hτDade, hbookInd⟩
  have hHleFit : H ≤ section8FittingSubgroup Smax := by
    rw [hfit, hH]
  have hA_A0 : A ⊆ A0book := by
    intro x hx
    exact hFittingSharp ⟨x, hHS hx.1⟩ ⟨hHleFit hx.1, hx.2⟩
  have hcoeffTau : ∀ i : Fin n, η (Fin.succ i) ∈ S1 →
      coeff i = Section1.scalarProduct G
        (τS (η (Fin.succ i) - ζ0)) χ := by
    intro i _hiS1
    have hcfA : Section2.CFOn Smax A
        (η (Fin.succ i) - (1 : ℂ) • η 0) := hbasis.1 i
    have hcfA' : Section2.CFOn Smax A (η (Fin.succ i) - η 0) := by
      simpa using hcfA
    have hcfA0 : Section2.CFOn Smax A0book
        (η (Fin.succ i) - η 0) := by
      refine ⟨hcfA'.1, ?_⟩
      intro x hxA0
      exact hcfA'.2 x (fun hxA => hxA0 (hA_A0 hxA))
    calc
      coeff i = Section1.scalarProduct G
          (τind (η (Fin.succ i) - η 0)) χ := rfl
      _ = Section1.scalarProduct G
          (τS (η (Fin.succ i) - η 0)) χ := by
            rw [hbookInd _ hcfA0]
      _ = Section1.scalarProduct G
          (τS (η (Fin.succ i) - ζ0)) χ := by rw [hη0]
  have hηtail_ne_zero : ∀ i : Fin n, η (Fin.succ i) ≠ ζ0 := by
    intro i heq
    have hidx : Fin.succ i = 0 := henum.2.1 (heq.trans hη0.symm)
    exact Fin.succ_ne_zero i hidx
  have hηtail_ne_one : ∀ i : Fin n, i ≠ i1 →
      η (Fin.succ i) ≠ ζ1 := by
    intro i hi heq
    apply hi
    apply Fin.succ_injective
    exact henum.2.1 (heq.trans hηi1.symm)
  have hcoeff_i1 : coeff i1 = a := by
    calc
      coeff i1 = Section1.scalarProduct G
          (τS (η (Fin.succ i1) - ζ0)) χ :=
        hcoeffTau i1 (by simpa [hηi1] using hζ1S1)
      _ = Section1.scalarProduct G (τS (ζ1 - ζ0)) χ := by rw [hηi1]
      _ = a := ha.symm
  have hcoeff_zero : ∀ i : Fin n, η (Fin.succ i) ∈ S1 →
      i ≠ i1 → coeff i = 0 := by
    intro i hiS1 hi
    rw [hcoeffTau i hiS1]
    exact hzero _ hiS1 (hηtail_ne_zero i) (hηtail_ne_one i hi)
  have hηT : ∀ j : Fin (n + 1), η j ∈ T := by
    intro j
    exact (henum.1 (η j)).mpr ⟨j, rfl⟩
  have hηvirt : ∀ j : Fin (n + 1),
      Theory.Character.IsVirtualCharacter (η j) := by
    intro j
    rcases (hTnotation (η j)).mp (hηT j) with ⟨θ, hθirr, hηind⟩
    rw [hηind]
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (H.subgroupOf Smax)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hθirr)
  have hcoeffInt : ∀ i : Fin n, ∃ zi : ℤ, coeff i = (zi : ℂ) := by
    intro i
    have hdiffVirt : Theory.Character.IsVirtualCharacter
        (η (Fin.succ i) - η 0) :=
      Section3.isVirtualCharacter_sub (hηvirt (Fin.succ i)) (hηvirt 0)
    have hindVirt : Theory.Character.IsVirtualCharacter
        (τind (η (Fin.succ i) - η 0)) := by
      change Theory.Character.IsVirtualCharacter
        (Section1.inducedCF Smax (η (Fin.succ i) - η 0))
      exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter Smax hdiffVirt
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hindVirt hχvirt
  choose z hz using hcoeffInt
  have hstarCoeff : ∀ i : Fin n, star (coeff i) = coeff i := by
    intro i
    rw [hz i]
    simp
  have hbetaPackage : ∀ i : Fin n,
      ∃ beta : Section1.ClassFunction H,
        Section1.IsCharacter beta ∧
          Section1.subgroupInKernel' beta (P.subgroupOf H) ∧
          (η (Fin.succ i) ∉ S1 → ∀ x : H,
            beta x = (Section5.cfNormSq (η (Fin.succ i)) : ℂ)⁻¹ *
              η (Fin.succ i) ⟨(x : G), hHS x.property⟩) := by
    intro i
    by_cases hiS1 : η (Fin.succ i) ∈ S1
    · refine ⟨Section1.principalCharacter H,
        Section6.theorem_6_8_isCharacter_of_irreducible
          Section3.principalCharacter_isIrreducibleCharacterOnGroup, ?_, ?_⟩
      · intro y
        rfl
      · intro hiNot
        exact (hiNot hiS1).elim
    · rcases (hTnotation (η (Fin.succ i))).mp (hηT (Fin.succ i)) with
        ⟨θ, hθirr, hηind⟩
      have hθker : Section1.subgroupInKernel' θ
          ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)) := by
        by_contra hθnotker
        exact hiS1 ((hS1.2.2 (η (Fin.succ i))).mpr
          ⟨θ, hθirr, hθnotker, hηind⟩)
      rcases theorem_13_5_normalized_induced_restriction_kernel_package
          H Smax P hHS hPH hHnormal hPnormal
          (η (Fin.succ i)) θ hθirr hθker hηind with
        ⟨beta, hbetaChar, hbetaKer, hbetaEval⟩
      exact ⟨beta, hbetaChar, hbetaKer, fun _hiNot => hbetaEval⟩
  choose beta hbetaChar hbetaKer hbetaEval using hbetaPackage
  let zTail : Fin n → ℤ := fun i =>
    if η (Fin.succ i) ∈ S1 then 0 else z i
  let alpha : Section1.ClassFunction H :=
    ∑ i : Fin n, (zTail i : ℂ) • beta i
  have halpha : virtualCharacterKernelConstituentData H P alpha := by
    dsimp [alpha]
    exact theorem_13_5_integer_sum_character_kernelConstituentData
      (K := G) (I := Fin n) H P zTail beta hbetaChar hbetaKer
  refine ⟨alpha, halpha, ⟨z i1, ?_⟩, ?_⟩
  · exact hcoeff_i1.symm.trans (hz i1)
  · intro x hx
    let xS : Smax := ⟨(x : G), hHS x.property⟩
    have hxA : (xS : G) ∈ A := ⟨x.property, hx⟩
    have hresx : ζ1H x = ζ1 xS := by
      rcases _hres with ⟨hHSres, hresEval⟩
      calc
        ζ1H x = ζ1 ⟨(x : G), hHSres x.property⟩ := hresEval x
        _ = ζ1 xS := congrArg ζ1 (Subtype.ext rfl)
    have hterm : ∀ i : Fin n,
        (star (coeff i) /
            (Section5.cfNormSq (η (Fin.succ i)) : ℂ)) *
              η (Fin.succ i) xS =
          (if i = i1 then
            (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x else 0) +
            (zTail i : ℂ) * beta i x := by
      intro i
      by_cases hii : i = i1
      · subst i
        have hi1S1 : η (Fin.succ i1) ∈ S1 := by
          simpa [hηi1] using hζ1S1
        rw [hstarCoeff i1, hcoeff_i1, hηi1]
        simp [zTail, hi1S1, hresx]
      · by_cases hiS1 : η (Fin.succ i) ∈ S1
        · rw [hstarCoeff i, hcoeff_zero i hiS1 hii]
          simp [zTail, hii, hiS1]
        · rw [hstarCoeff i, hz i, hbetaEval i hiS1 x]
          have hevalArg :
              (⟨(x : G), hHS x.property⟩ : Smax) = xS := Subtype.ext rfl
          rw [hevalArg]
          simp [zTail, hii, hiS1, div_eq_mul_inv]
          ring
    have hsum :
        (∑ i : Fin n,
          (star (coeff i) /
              (Section5.cfNormSq (η (Fin.succ i)) : ℂ)) *
                η (Fin.succ i) xS) =
          (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x + alpha x := by
      calc
        (∑ i : Fin n,
            (star (coeff i) /
                (Section5.cfNormSq (η (Fin.succ i)) : ℂ)) *
                  η (Fin.succ i) xS) =
            ∑ i : Fin n,
              ((if i = i1 then
                (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x else 0) +
                (zTail i : ℂ) * beta i x) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  exact hterm i
        _ = (∑ i : Fin n, if i = i1 then
              (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x else 0) +
            ∑ i : Fin n, (zTail i : ℂ) * beta i x := by
              rw [Finset.sum_add_distrib]
        _ = (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x + alpha x := by
              simp [alpha]
    have hprojection : Section7.dadeProjection Smax K χ xS = χ (x : G) := by
      have hbotDefault : ((default : (⊥ : Subgroup G)) : G) = 1 :=
        Subgroup.mem_bot.mp (default : (⊥ : Subgroup G)).property
      simp [Section7.dadeProjection, Section2.dadeAveragingFunction, K, xS,
        hbotDefault]
    calc
      χ (x : G) = Section7.dadeProjection Smax K χ xS := hprojection.symm
      _ = ∑ i : Fin n,
          (star (coeff i) /
              (Section5.cfNormSq (η (Fin.succ i)) : ℂ)) *
                η (Fin.succ i) xS := h77.1 xS hxA
      _ = (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x + alpha x := hsum

private theorem theorem_13_5_squareSumFormula_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (ζ1H α : Section1.ClassFunction H)
    (χ : Section1.ClassFunction G)
    (a : ℂ)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hhyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 χ a)
    (_hres : classFunctionRestrictionData H Smax ζ1 ζ1H)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_ha : ∃ z : ℤ, a = (z : ℂ))
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      χ (x : G) =
        (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x + α x) :
    theorem_13_5_squareSumFormula Smax H ζ1 ζ1H α χ a := by
  classical
  have hsource := _hsource
  have hres := _hres
  rcases _hhyp with
    ⟨hH, hS1, _hζ0mem, hζ1mem, _hζ01, _hχvirt, _ha_def, _hothers⟩
  have hHS : H ≤ Smax := hS1.1
  have hPH : P ≤ H := hS1.2.1
  rcases (hS1.2.2 ζ1).mp hζ1mem with
    ⟨theta, htheta_irreducible, htheta_not_kernel, hζ1_induced⟩
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _htail⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hptypeS
  have hHnormal : (H.subgroupOf Smax).Normal := by
    have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
      simpa [hfit] using section8FittingSubgroup_normal_in Smax
    simpa [hH] using hPCnormal
  rcases hptypeS with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfitDef, _hfitDer,
      _hW2le, _hW2cyc, _hW2ne, _hcent, _hnorm⟩
  rcases hMF with ⟨⟨_hPSmax, hPnormal, _hPnil, _hPHall⟩, _hPmax⟩
  letI : (H.subgroupOf Smax).Normal := hHnormal
  have hζ1support :
      Section1.supportedOn ζ1 (H.subgroupOf Smax : Set Smax) := by
    rw [Section1.supportedOn_iff]
    intro x hx
    rw [hζ1_induced]
    exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
      (H.subgroupOf Smax) theta hx
  have horthogonal : Section1.scalarProduct H ζ1H α = 0 :=
    theorem_13_5_restriction_inducedCF_orthogonal_kernelConstituent
      H Smax P ζ1 ζ1H α theta hres hPH hHnormal hPnormal
      htheta_irreducible htheta_not_kernel hζ1_induced _hα
  have htheta_virtual : Theory.Character.IsVirtualCharacter theta :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      htheta_irreducible
  have hζ1virtual : Theory.Character.IsVirtualCharacter ζ1 := by
    rw [hζ1_induced]
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (H.subgroupOf Smax) htheta_virtual
  have htheta_degree_ne : Section1.degree theta ≠ 0 :=
    Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup theta
      htheta_irreducible
  have hindex_ne : (Subgroup.index (H.subgroupOf Smax) : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf Smax))
  have hζ1_degree_ne : Section1.degree ζ1 ≠ 0 := by
    rw [hζ1_induced, Section1.degree_inducedClassFunction]
    exact mul_ne_zero hindex_ne htheta_degree_ne
  have hζ1_ne : ζ1 ≠ 0 := by
    intro hzero
    apply hζ1_degree_ne
    simp [hzero, Section1.degree]
  have hnorm_ne_real : Section5.cfNormSq ζ1 ≠ 0 := by
    intro hzero
    exact hζ1_ne (Section5.cfNormSq_eq_zero hzero)
  have hnorm_ne : (Section5.cfNormSq ζ1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnorm_ne_real
  rcases theorem_13_5_virtualCharacter_one_eq_int hζ1virtual with
    ⟨zetaOne, hζ1_one⟩
  rcases theorem_13_5_virtualCharacter_one_eq_int _hα.1 with
    ⟨alphaOne, hα_one⟩
  rcases _ha with ⟨aInt, ha_int⟩
  rcases hres with ⟨_hHSres, hres_eval⟩
  have hζ1H_one : ζ1H 1 = ζ1 1 := by
    have htemp := hres_eval (1 : H)
    have hone : (⟨(1 : G), _hHSres (Subgroup.one_mem H)⟩ : Smax) = (1 : Smax) :=
      Subtype.ext (by simp)
    simpa [hone] using htemp
  have hstar_a : star a = a := by
    rw [ha_int]
    simp
  have hstar_ζ1 : star (ζ1 1) = ζ1 1 := by
    rw [hζ1_one]
    simp
  have hstar_ζ1H : star (ζ1H 1) = ζ1H 1 := by
    rw [hζ1H_one, hstar_ζ1]
  have hstar_α : star (α 1) = α 1 := by
    rw [hα_one]
    simp
  let b : ℂ := a / (Section5.cfNormSq ζ1 : ℂ)
  have hstar_b : star b = b := by
    simp [b, hstar_a]
  have henergy_restrict :
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) χ =
        Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H)
          (fun x => b * ζ1H x + α x) := by
    exact theorem_13_5_support_energy_punctured_subgroup_eq H χ
      (fun x => b * ζ1H x + α x) (by
        intro x hx
        simpa [b] using _hexp x hx)
  have hraw_energy :
      (Nat.card H : ℝ) * Section5.cfNormSq ζ1H =
        (Nat.card Smax : ℝ) * Section5.cfNormSq ζ1 :=
    theorem_13_5_subgroup_restriction_raw_energy_eq_ambient
      H Smax ζ1 ζ1H _hres hζ1support
  have hpunctured_energy :=
    theorem_13_5_punctured_energy_eq_card_mul_cfNormSq_sub_one H ζ1H
  have hζ1_energy_real :
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) ζ1H =
        (Nat.card Smax : ℝ) * Section5.cfNormSq ζ1 -
          Complex.normSq (ζ1H 1) := by
    linarith
  have hnorm_ζ1H_one :
      ((Complex.normSq (ζ1H 1) : ℝ) : ℂ) = (ζ1 1) ^ 2 := by
    rw [hζ1H_one]
    calc
      ((Complex.normSq (ζ1 1) : ℝ) : ℂ) = star (ζ1 1) * ζ1 1 :=
        Complex.normSq_eq_conj_mul_self
      _ = (ζ1 1) ^ 2 := by rw [hstar_ζ1]; ring
  have hζ1_energy :
      (Section7.subgroupSupportEnergy H
          (Section7.puncturedSubgroupSet H) ζ1H : ℂ) =
        (Nat.card Smax : ℂ) * (Section5.cfNormSq ζ1 : ℂ) -
          (ζ1 1) ^ 2 := by
    rw [hζ1_energy_real]
    push_cast
    rw [hnorm_ζ1H_one]
  have horthogonal_swap : Section1.scalarProduct H α ζ1H = 0 := by
    calc
      Section1.scalarProduct H α ζ1H =
          star (Section1.scalarProduct H ζ1H α) := by
            symm
            exact Section1.scalarProduct_star_swap α ζ1H
      _ = 0 := by rw [horthogonal]; simp
  have hcross_left :
      theorem_13_5_crossSum H (Section7.puncturedSubgroupSet H) ζ1H α =
        -ζ1H 1 * α 1 := by
    rw [theorem_13_5_crossSum_punctured_eq_card_mul_scalarProduct_sub_one,
      horthogonal, mul_zero, zero_sub, hstar_α]
    ring
  have hcross_right :
      theorem_13_5_crossSum H (Section7.puncturedSubgroupSet H) α ζ1H =
        -ζ1H 1 * α 1 := by
    rw [theorem_13_5_crossSum_punctured_eq_card_mul_scalarProduct_sub_one,
      horthogonal_swap, mul_zero, zero_sub, hstar_ζ1H]
    ring
  have henergy_expand := theorem_13_5_subgroup_energy_cast_add
    H (Section7.puncturedSubgroupSet H) b ζ1H α hstar_b
  unfold theorem_13_5_squareSumFormula
  calc
    (Section7.supportEnergy (Section7.puncturedSubgroupSet H) χ : ℂ) =
        (Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H)
          (fun x => b * ζ1H x + α x) : ℂ) := by
            exact_mod_cast henergy_restrict
    _ = b ^ 2 *
          (Section7.subgroupSupportEnergy H
            (Section7.puncturedSubgroupSet H) ζ1H : ℂ) +
        b * theorem_13_5_crossSum H (Section7.puncturedSubgroupSet H) ζ1H α +
        b * theorem_13_5_crossSum H (Section7.puncturedSubgroupSet H) α ζ1H +
        (Section7.subgroupSupportEnergy H
          (Section7.puncturedSubgroupSet H) α : ℂ) := henergy_expand
    _ = (a ^ 2 / (Section5.cfNormSq ζ1 : ℂ)) *
          ((Nat.card Smax : ℂ) - (ζ1 1) ^ 2 /
            (Section5.cfNormSq ζ1 : ℂ)) -
        2 * a * ζ1H 1 * α 1 / (Section5.cfNormSq ζ1 : ℂ) +
        (Section7.subgroupSupportEnergy H
          (Section7.puncturedSubgroupSet H) α : ℂ) := by
            rw [hζ1_energy, hcross_left, hcross_right]
            dsimp [b]
            field_simp [hnorm_ne]
            ring

private theorem theorem_13_5_kernelConstituent_lower_bound_of_const_on_subgroup
    {G : Type u}
    [Group G]
    [Finite G]
    (H P : Subgroup G)
    (α : Section1.ClassFunction H)
    (hPH : P ≤ H)
    (hconst : ∀ x : P, α ⟨(x : G), hPH x.property⟩ = α 1) :
    ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  classical
  let e : P → H := fun x => ⟨(x : G), hPH x.property⟩
  let n : ℝ := Complex.normSq (α 1)
  have he_inj : Function.Injective e := by
    intro x y hxy
    ext
    exact congrArg (fun z : H => (z : G)) hxy
  have himage_subset : (Finset.univ.image e) ⊆ (Finset.univ : Finset H) := by
    intro x _hx
    simp
  have hnonneg_out :
      ∀ x ∈ (Finset.univ : Finset H), x ∉ Finset.univ.image e →
        0 ≤
          (if (x : G) ∈ Section7.puncturedSubgroupSet H then
            Complex.normSq (α x) else 0) := by
    intro x _hx _hxnot
    split
    · exact Complex.normSq_nonneg (α x)
    · norm_num
  have hle_image :
      (∑ x ∈ Finset.univ.image e,
          (if (x : G) ∈ Section7.puncturedSubgroupSet H then
            Complex.normSq (α x) else 0)) ≤
        ∑ x ∈ (Finset.univ : Finset H),
          (if (x : G) ∈ Section7.puncturedSubgroupSet H then
            Complex.normSq (α x) else 0) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg_out
  have himage_sum :
      (∑ x ∈ Finset.univ.image e,
          (if (x : G) ∈ Section7.puncturedSubgroupSet H then
            Complex.normSq (α x) else 0)) =
        ∑ x : P, if (x : G) = 1 then 0 else n := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx1 : (x : G) = 1
      · simp [e, n, hx1, Section7.puncturedSubgroupSet]
      · have he_mem : ((e x : G) ∈ Section7.puncturedSubgroupSet H) := by
          exact ⟨(e x).property, hx1⟩
        have hval : α (e x) = α 1 := hconst x
        simp [e, n, hx1, he_mem, hval]
    · intro x _hx y _hy hxy
      exact he_inj hxy
  have hcard_filter :
      (Finset.univ.filter (fun x : P => (x : G) ≠ 1)).card =
        Nat.card P - 1 := by
    rw [Nat.card_eq_fintype_card]
    have hcompl := Fintype.card_subtype_compl (fun x : P => (x : G) = 1)
    rw [← Fintype.card_subtype (fun x : P => (x : G) ≠ 1)]
    rw [hcompl]
    simp
  have hcard_sum :
      ∑ x : P, (if (x : G) = 1 then 0 else n) =
        ((Nat.card P - 1 : ℕ) : ℝ) * n := by
    have hsum_filter :
        (∑ x : P, if (x : G) = 1 then 0 else n) =
          ∑ x ∈ Finset.univ.filter (fun x : P => (x : G) ≠ 1), n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx1 : (x : G) = 1 <;> simp [hx1]
    rw [hsum_filter, Finset.sum_const, nsmul_eq_mul, hcard_filter]
  rw [himage_sum, hcard_sum] at hle_image
  unfold Section7.subgroupSupportEnergy
  simpa [n] using hle_image

public theorem theorem_13_5_virtualCharacterKernelConstituent_subgroupInKernel
    {G : Type u}
    [Group G]
    [Finite G]
    (H P : Subgroup G)
    (α : Section1.ClassFunction H)
    (hα : virtualCharacterKernelConstituentData H P α) :
    Section1.subgroupInKernel' α (P.subgroupOf H) := by
  classical
  rcases hα with ⟨hvirt, hker⟩
  have hαclass : Section1.IsClassFunction α :=
    Section1.isVirtualCharacter_isClassFunction hvirt
  rcases Theory.Character.irreducible_characters_form_basis (G := H) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let ψ : ι → Section1.ClassFunction H := fun i => Section1.ofConjClassFunction (χ i)
  have hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
  have hcoeff_int : ∀ i,
      ∃ z : ℤ, Section1.scalarProduct H α (ψ i) = (z : ℂ) := by
    intro i
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hvirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hψirr i))
  let coeff := Section3.irreducibleBasisCoeff α hcoeff_int
  have hdecomp : Section1.evalCoeff ψ coeff = α := by
    simpa [ψ, coeff] using
      (Section3.irreducibleBasis_evalCoeff_coeff hχ b hb α hαclass hcoeff_int)
  have hsumker : Section1.subgroupInKernel' (Section1.evalCoeff ψ coeff)
      (P.subgroupOf H) := by
    intro a
    change (Section1.evalCoeff ψ coeff) a = (Section1.evalCoeff ψ coeff) 1
    change ((∑ i : ι, (coeff i : ℂ) • ψ i) : Section1.ClassFunction H) a =
      ((∑ i : ι, (coeff i : ℂ) • ψ i) : Section1.ClassFunction H) 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    by_cases hzero : coeff i = 0
    · simp [hzero]
    · have hsp_ne : Section1.scalarProduct H α (ψ i) ≠ 0 := by
        intro hsp0
        have hspec := Section3.irreducibleBasisCoeff_spec α hcoeff_int i
        have hspec0 : (0 : ℂ) = ((coeff i : ℤ) : ℂ) := by
          simpa [coeff, ψ, hsp0] using hspec
        have hcast : ((coeff i : ℤ) : ℂ) = 0 := hspec0.symm
        exact hzero (Int.cast_eq_zero.mp hcast)
      have hψker : Section1.subgroupInKernel' (ψ i) (P.subgroupOf H) :=
        hker (ψ i) (hψirr i) hsp_ne
      have hψa1 : ψ i a = ψ i 1 := by
        simpa [Section1.subgroupInKernel', Section1.degree] using hψker a
      simp [hψa1]
  exact Section1.subgroupInKernel'_of_eq hdecomp hsumker

/-- Checked PF `(13.5)(c)` step: the virtual character `α` is constant on
`P`, because every irreducible constituent with nonzero coefficient has `P`
in its kernel. -/
private theorem theorem_13_5_kernelConstituent_const_on_P_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H P C : Subgroup G)
    (α : Section1.ClassFunction H)
    (hPH : P ≤ H)
    (_hH : H = P ⊔ C)
    (hα : virtualCharacterKernelConstituentData H P α) :
    ∀ x : P, α ⟨(x : G), hPH x.property⟩ = α 1 := by
  intro x
  let xH : H := ⟨(x : G), hPH x.property⟩
  have hxmem : xH ∈ P.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact x.property
  have hker := theorem_13_5_virtualCharacterKernelConstituent_subgroupInKernel H P α hα
  simpa [xH, Section1.subgroupInKernel', Section1.degree] using hker ⟨xH, hxmem⟩

private theorem theorem_13_5_kernelConstituent_lower_bound_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H P C : Subgroup G)
    (α : Section1.ClassFunction H)
    (hH : H = P ⊔ C)
    (hα : virtualCharacterKernelConstituentData H P α) :
    ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  have hPH : P ≤ H := by
    rw [hH]
    exact le_sup_left
  exact theorem_13_5_kernelConstituent_lower_bound_of_const_on_subgroup H P α hPH
    (theorem_13_5_kernelConstituent_const_on_P_source H P C α hPH hH hα)

public theorem theorem_13_5
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (ζ1H : Section1.ClassFunction H)
    (χ : Section1.ClassFunction G)
    (a : ℂ)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 χ a →
      classFunctionRestrictionData H Smax ζ1 ζ1H →
        ∃ α : Section1.ClassFunction H,
          virtualCharacterKernelConstituentData H P α ∧
            (∀ x : H, (x : G) ≠ 1 →
              χ (x : G) =
                (a / (Section5.cfNormSq ζ1 : ℂ)) * ζ1H x + α x) ∧
            theorem_13_5_squareSumFormula Smax H ζ1 ζ1H α χ a ∧
            ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
              Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  intro hsource hhyp hres
  rcases theorem_13_5_expansion_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT
      ζ0 ζ1 ζ1H χ a p q u v c d hsource hhyp hres with
    ⟨α, hα, ha, hexp⟩
  refine ⟨α, hα, hexp, ?_, ?_⟩
  · exact theorem_13_5_squareSumFormula_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT
      ζ0 ζ1 ζ1H α χ a p q u v c d hsource hhyp hres hα ha hexp
  · exact theorem_13_5_kernelConstituent_lower_bound_source H P C α hhyp.1 hα
end CFSG.Section13
