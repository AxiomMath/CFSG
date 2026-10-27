module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import Certificates.Certificate1952
import all CFSG.LocalAnalysis.StandardType.GGL45NtLattice
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public section

namespace CFSG.StandardType.LieCore

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.HardMathSupport.Timmesfeld.Torality (familyStabilizerSubgroup)
open CFSG.HardMathSupport.C14Lattice (familyReflectionGroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (MonomialToralAt)
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.HardMathSupport.Timmesfeld.Torality (familyChar kernelRoots_familyChar
  mem_familyStabilizerSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (conj_pow_eq_one' rootDiagUnit_pow')
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
  (exists_conj_le_monomial_familyCentralizer_bar
    exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (monomialToralAt_exc monomialToralAt_exc_of_ne_E8
    monomialToralAt_E6_five monomialToralAt_E7_five)
open CFSG.HardMathSupport.C14Lattice (familyStabilizer_le_reflection not_dvd_or_sylowCert)

private theorem lieInd_kernelWeylGroup_familyChar {τ : Tag} {K : Type} [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ) : kernelWeylGroup (familyChar a) = familyReflectionGroup a := by
  rw [familyReflectionGroup, kernelWeylGroup, kernelRoots_familyChar]

private theorem lieInd_exists_family
    {τ : Tag} {p : ℕ} {L : Type} [Field L] {A : Subgroup (ModGL τ L)}
    (hexp : ∀ x ∈ A, x ^ p = 1) (C : ModGL τ L) (S : Finset A)
    (hCS : ∀ y ∈ S, C * (y : ModGL τ L) * C⁻¹ ∈ torusGroup τ L) :
    ∃ aS : {y : A // y ∈ S} → Fin τ.rank → Lˣ,
      (∀ y : {y : A // y ∈ S}, C * (y.1 : ModGL τ L) * C⁻¹ = rootDiagUnit τ (aS y)) ∧
        ∀ y j, aS y j ^ p = 1 := by
  choose aS haS using fun y : {y : A // y ∈ S} =>
    exists_rootDiagUnit_eq_of_mem_torusGroup (hCS y.1 y.2)
  refine ⟨aS, haS, fun y j => ?_⟩
  have h : rootDiagUnit τ (aS y ^ p) = rootDiagUnit τ 1 := by
    rw [rootDiagUnit_pow', rootDiagUnit_one, ← haS y, conj_pow_eq_one' C (hexp _ y.1.2)]
  simpa using congrFun (rootDiagUnit_injective h) j

private theorem lieInd_exists_conj_mem_torusGroup
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hmon : MonomialToralAt τ p) {L : Type} [Field L]
    [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {ι : Type} [Fintype ι] {a : ι → Fin τ.rank → Lˣ}
    (hstab : familyStabilizerSubgroup a ≤ familyReflectionGroup a)
    {B : Subgroup (ModGL τ L)} (hB : B ≤ adjointGroup τ L) (hBfin : (B : Set (ModGL τ L)).Finite)
    (hBa : ∀ x ∈ B, ∀ i, rootDiagUnit τ (a i) * x = x * rootDiagUnit τ (a i))
    (hexp : ∀ x ∈ B, x ^ p = 1) {y : ModGL τ L} (hy : y ∈ B) :
    ∃ g ∈ adjointGroup τ L, (∀ i, rootDiagUnit τ (a i) * g = g * rootDiagUnit τ (a i)) ∧
      g * y * g⁻¹ ∈ torusGroup τ L := by
  have hLp : ringChar L ≠ p := by rw [ringChar.eq L ℓ]; exact hℓ
  have hW : ∀ w : WeylGroup τ, (∀ i, w ∈ rootCharStabilizer (a i)) →
      w ∈ kernelWeylGroup (familyChar a) := fun w hw => by
    rw [lieInd_kernelWeylGroup_familyChar]
    exact hstab (mem_familyStabilizerSubgroup.2 hw)
  obtain ⟨z, hz, hzd, hzN⟩ :=
    exists_conj_le_monomial_familyCentralizer_bar hℓ halg a hB hBfin hBa hexp
  have hna : ∀ i, rootDiagUnit τ (a i) * (z * y * z⁻¹) = z * y * z⁻¹ * rootDiagUnit τ (a i) :=
    fun i => (Commute.mul_right (Commute.mul_right (hzd i) (hBa y hy i))
      (Commute.inv_right (hzd i))).eq
  obtain ⟨g, hg, hgd, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer hmon
    hLp hW (hzN y hy) hna (conj_pow_eq_one' z (hexp y hy))
  refine ⟨g * z, mul_mem hg hz, fun i => (Commute.mul_right (hgd i) (hzd i)).eq, ?_⟩
  rw [show g * z * y * (g * z)⁻¹ = g * (z * y * z⁻¹) * g⁻¹ by group]
  exact hgn

private theorem lieInd_insert
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hmon : MonomialToralAt τ p) {L : Type} [Field L]
    [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    (hfam : ∀ (ι : Type) [Finite ι] (a : ι → Fin τ.rank → Lˣ), (∀ i j, a i j ^ p = 1) →
      familyStabilizerSubgroup a ≤ familyReflectionGroup a)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L) (hAfin : (A : Set (ModGL τ L)).Finite)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    [DecidableEq A] {S : Finset A} {C : ModGL τ L} (hC : C ∈ adjointGroup τ L)
    (hCS : ∀ y ∈ S, C * (y : ModGL τ L) * C⁻¹ ∈ torusGroup τ L) (x : A) :
    ∃ C' ∈ adjointGroup τ L, ∀ y ∈ insert x S, C' * (y : ModGL τ L) * C'⁻¹ ∈ torusGroup τ L := by
  obtain ⟨aS, haS, hap⟩ := lieInd_exists_family hexp C S hCS
  set B := A.map (MulAut.conj C).toMonoidHom
  have hB : B ≤ adjointGroup τ L := by
    rintro _ ⟨w, hw, rfl⟩
    exact mul_mem (mul_mem hC (hA hw)) (inv_mem hC)
  have hBfin : (B : Set (ModGL τ L)).Finite := hAfin.image _
  have hBa : ∀ z ∈ B, ∀ y, rootDiagUnit τ (aS y) * z = z * rootDiagUnit τ (aS y) := by
    rintro _ ⟨w, hw, rfl⟩ y
    rw [← haS y]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (Commute.map (hcomm _ y.1.2 w hw) (MulAut.conj C)).eq
  have hBexp : ∀ z ∈ B, z ^ p = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact conj_pow_eq_one' C (hexp w hw)
  obtain ⟨g, hg, hgd, hgx⟩ := lieInd_exists_conj_mem_torusGroup hmon hℓ halg (hfam _ aS hap) hB
    hBfin hBa hBexp (y := C * (x : ModGL τ L) * C⁻¹) ⟨x, x.2, rfl⟩
  refine ⟨g * C, mul_mem hg hC, fun y hy => ?_⟩
  rw [show g * C * (y : ModGL τ L) * (g * C)⁻¹ = g * (C * (y : ModGL τ L) * C⁻¹) * g⁻¹ by group]
  rcases Finset.mem_insert.1 hy with rfl | hyS
  · exact hgx
  · rw [haS ⟨y, hyS⟩, ← hgd ⟨y, hyS⟩, mul_inv_cancel_right]
    exact rootDiagUnit_mem_torusGroup _

private theorem lieInd_claim
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hmon : MonomialToralAt τ p) {L : Type} [Field L]
    [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    (hfam : ∀ (ι : Type) [Finite ι] (a : ι → Fin τ.rank → Lˣ), (∀ i j, a i j ^ p = 1) →
      familyStabilizerSubgroup a ≤ familyReflectionGroup a)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L) (hAfin : (A : Set (ModGL τ L)).Finite)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1) (S : Finset A) :
    ∃ C ∈ adjointGroup τ L, ∀ y ∈ S, C * (y : ModGL τ L) * C⁻¹ ∈ torusGroup τ L := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert x S _ ih =>
    obtain ⟨C, hC, hCS⟩ := ih
    exact lieInd_insert hmon hℓ halg hfam hA hAfin hcomm hexp hC hCS x

theorem isToralSubgroup_of_familyStabilizer_le
    {τ : Tag} {p : ℕ} [Fact p.Prime]
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ p) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    (hfam : ∀ (ι : Type) [Finite ι] (a : ι → Fin τ.rank → Lˣ), (∀ i j, a i j ^ p = 1) →
      familyStabilizerSubgroup a ≤ familyReflectionGroup a)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L) (hfin : Finite A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1) :
    IsToralSubgroup τ L A := by
  have : Fintype A := Fintype.ofFinite A
  obtain ⟨C, hC, hCA⟩ := lieInd_claim hmon hℓ halg hfam hA (Set.toFinite _) hcomm hexp
    Finset.univ
  refine ⟨C⁻¹, inv_mem hC, fun x hx => ?_⟩
  rw [inv_inv]
  exact hCA ⟨x, hx⟩ (Finset.mem_univ _)

theorem isToralSubgroup_of_nonTorsion_of_ne_E8
    {τ : Tag} (hne : τ ≠ .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3)
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L) (hfin : Finite A)
    (hel : IsElemAbelian p A) : IsToralSubgroup τ L A := by
  have : Fact p.Prime := ⟨hp⟩
  exact isToralSubgroup_of_familyStabilizer_le
    (monomialToralAt_exc_of_ne_E8 monomialToralAt_E6_five monomialToralAt_E7_five hne hp hp2)
    hℓ halg
    (fun _ _ _ ha => familyStabilizer_le_reflection hp
      (not_dvd_or_sylowCert τ hp hp2 h3 (fun h => (hne h).elim)) ha)
    hA hfin (fun x hx y hy => congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hel.2

theorem isToralSubgroup_of_nonTorsion
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L) (hfin : Finite A)
    (hel : IsElemAbelian p A) : IsToralSubgroup τ L A := by
  have : Fact p.Prime := ⟨hp⟩
  have hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    cases τ <;> simp
  exact isToralSubgroup_of_familyStabilizer_le
    (monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ hp hp2) hℓ halg
    (fun _ _ _ ha => familyStabilizer_le_reflection hp (not_dvd_or_sylowCert τ hp hp2 h3 h5) ha)
    hA hfin (fun x hx y hy => congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hel.2

end CFSG.StandardType.LieCore

end
