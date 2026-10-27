module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Blueprint.Catalog
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem SUid_eq_gramSU_idGram (h : UnitaryFieldData p f F) (n : ℕ) :
    CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution F p f) n =
      gramSU h (idGram F n) := by
  have hF : Nat.card F = (p ^ f) ^ 2 := by rw [h.card, Nat.mul_comm 2 f, pow_mul]
  exact (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n).trans
    (unitarySU_eq_gramSU h n)

@[expose] noncomputable def unitaryCover (h : UnitaryFieldData p f F) (n : ℕ) :
    Su F p f n →* primeFormP h (idGram F n) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram F n)) n)).comp
    (MulEquiv.subgroupCongr (SUid_eq_gramSU_idGram h n)).toMonoidHom

theorem unitaryCover_surjective (h : UnitaryFieldData p f F) (n : ℕ) :
    Function.Surjective (unitaryCover h n) := by
  intro y
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
    (normOneScalars h (gramSU h (idGram F n)) n) y
  refine ⟨(MulEquiv.subgroupCongr (SUid_eq_gramSU_idGram h n)).symm s, ?_⟩
  simp [unitaryCover]

theorem coe_mem_center_of_mem_ker_unitaryCover (h : UnitaryFieldData p f F) {n : ℕ}
    {x : Su F p f n} (hx : x ∈ (unitaryCover h n).ker) :
    (x : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
  have hx1 : unitaryCover h n x = 1 := MonoidHom.mem_ker.mp hx
  rw [unitaryCover, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx1
  change (MulEquiv.subgroupCongr (SUid_eq_gramSU_idGram h n)) x ∈
    normOneScalars h (gramSU h (idGram F n)) n at hx1
  obtain ⟨c, -, -, hg⟩ := (mem_normOneScalars).mp hx1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨c, ?_⟩
  rw [← hg, MulEquiv.subgroupCongr_apply]

theorem ker_unitaryCover_le_center (h : UnitaryFieldData p f F) (n : ℕ) :
    (unitaryCover h n).ker ≤ Subgroup.center (Su F p f n) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' := coe_mem_center_of_mem_ker_unitaryCover h hx
  rw [Subgroup.mem_center_iff] at hx'
  simpa only [Subgroup.coe_mul] using hx' (y : GL (Fin n) F)

theorem coe_mem_center_of_unitaryCover_eq (h : UnitaryFieldData p f F) {n : ℕ}
    {x y : Su F p f n} (hxy : unitaryCover h n x = unitaryCover h n y) :
    ((x⁻¹ * y : Su F p f n) : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
  apply coe_mem_center_of_mem_ker_unitaryCover h
  simp [MonoidHom.mem_ker, hxy]

theorem coe_mem_primeFormUnitary (h : UnitaryFieldData p f F) {n : ℕ} (x : Su F p f n) :
    (x : GL (Fin n) F) ∈ primeFormUnitary h (idGram F n) := by
  have hx : (x : GL (Fin n) F) ∈ gramSU h (idGram F n) := by
    rw [← SUid_eq_gramSU_idGram h n]
    exact x.2
  exact ((mem_gramSU_iff_unitary (h := h)).mp hx).1

theorem primeFormConjHom_coe (h : UnitaryFieldData p f F) {n : ℕ} (x : Su F p f n) :
    primeFormConjHom h (idGram F n) ⟨(x : GL (Fin n) F), coe_mem_primeFormUnitary h x⟩ =
      MulAut.conj (unitaryCover h n x) := by
  let e := SUid_eq_gramSU_idGram h n
  let s : gramSU h (idGram F n) := (MulEquiv.subgroupCongr e) x
  have hcoe : (s : GL (Fin n) F) = (x : GL (Fin n) F) := MulEquiv.subgroupCongr_apply e x
  have hcov : unitaryCover h n x = (s : primeFormP h (idGram F n)) := rfl
  have hA : (⟨(x : GL (Fin n) F), coe_mem_primeFormUnitary h x⟩ :
      primeFormUnitary h (idGram F n)) = ⟨(s : GL (Fin n) F), s.2.1⟩ :=
    Subtype.ext hcoe.symm
  rw [hcov, hA, primeFormConjHom_eq_conj]

theorem conj_mem_SUid (h : UnitaryFieldData p f F) {n : ℕ} (A : primeFormUnitary h (idGram F n))
    (x : Su F p f n) :
    (A : GL (Fin n) F) * (x : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹ ∈
      CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution F p f) n := by
  have hx : (x : GL (Fin n) F) ∈ gramSU h (idGram F n) := by
    rw [← SUid_eq_gramSU_idGram h n]
    exact x.2
  have hconj := conj_mem_gramSU h (idGram F n) A.2 hx
  rw [← SUid_eq_gramSU_idGram h n] at hconj
  exact hconj

theorem primeFormConjHom_unitaryCover (h : UnitaryFieldData p f F) {n : ℕ}
    (A : primeFormUnitary h (idGram F n)) (x : Su F p f n) :
    primeFormConjHom h (idGram F n) A (unitaryCover h n x) =
      unitaryCover h n ⟨(A : GL (Fin n) F) * (x : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹,
        conj_mem_SUid h A x⟩ := by
  let e := SUid_eq_gramSU_idGram h n
  have hcov : ∀ y : Su F p f n,
      unitaryCover h n y = ((MulEquiv.subgroupCongr e) y : primeFormP h (idGram F n)) :=
    fun y => rfl
  rw [hcov x, hcov ⟨_, conj_mem_SUid h A x⟩, primeFormConjHom_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem lieModel_primeFormP_idGram (h : UnitaryFieldData p f F) {n : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    CFSG.Blueprint.LieModel (primeFormP h (idGram F n)) .PSU n p f := by
  have hF : Nat.card F = (p ^ f) ^ 2 := by rw [h.card, Nat.mul_comm 2 f, pow_mul]
  let e : primeFormP h (idGram F n) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU n (p ^ f) F) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h
      (CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram (n := n) (K := F)))).trans
      (unitaryPSUEquiv h (by omega))
  refine Or.inl ⟨by decide, ⟨h.prime, h.one_le, hn, ?_⟩, F, inferInstance, inferInstance,
    hF, ⟨e⟩⟩
  intro he
  exact hq (by simpa using he)

omit [Finite F] [Fact (Nat.Prime p)] [CharP F p] in
theorem isSimpleGroup_primeFormP_idGram (h : UnitaryFieldData p f F) {n : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) : IsSimpleGroup (primeFormP h (idGram F n)) :=
  CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h hn hq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
