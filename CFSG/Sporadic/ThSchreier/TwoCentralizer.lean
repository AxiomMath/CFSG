
module

public import CFSG.Sporadic.ThSchreier.TwoCentralizerBase1

public import CFSG.Sporadic.ThSchreier.OrbitCheck819
public import CFSG.Sporadic.Th.Max3.Packet
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819
public meta import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public import Certificates.Certificate2324
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.PacketInputs
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem twoC0_mem : twoC0 ∈ localH :=
  wordG_mem _ (pairLetters_mem _ localX_mem_H localY_mem_H) _

@[expose] noncomputable def twoG : J := transporterV * twoK * transporterV⁻¹

@[expose] noncomputable def twoR : J := twoG * a * twoG⁻¹

@[expose] noncomputable def twoM1 : Subgroup J := M.map (MulAut.conj twoG).toMonoidHom

theorem isRows_hLetter (l : ℤ) : IsRows (hLetterRows l) (pairLetters localX localY l) := by
  unfold hLetterRows pairLetters
  by_cases h1 : l = 1
  · simp only [h1, true_or, ite_true]
    exact isRows_localX
  · by_cases h2 : l = -1
    · simp only [h2, or_true, ite_true, show (-1 : ℤ) ≠ 1 by decide, ite_false]
      exact isRows_localX_inv
    · simp only [h1, h2, or_self, ite_false]
      by_cases h3 : l = 2
      · simp only [h3, ite_true]
        exact isRows_localY
      · simp only [h3, ite_false]
        exact isRows_localY_inv

theorem isRows_hRows (w : List ℤ) : IsRows (hRows w) (wordG (pairLetters localX localY) w) :=
  isRows_signedRows isRows_hLetter w

private theorem native_two_facts :
    eqRows (mulRows (hRows centWord0) rowsT) (mulRows rowsT (hRows centWord0)) = true ∧
    eqRows (mulRows (hRows centWord1) rowsT) (mulRows rowsT (hRows centWord1)) = true ∧
    (∀ R ∈ twoRowsList, eqRows (mulRows R (invRows R)) idRows = true ∧
      (invRows R).size = 248 ∧ ∀ r ∈ invRows R, r.wf = true) ∧
    twoRowsList.length = 10 ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord0) rowsLX = true ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord1) rowsLY = true ∧
    eqRows rowsTwoR rowsE217 = true ∧ eqRows rowsTwoR idRows = false ∧
    eqRows rowsTwoR rowsZ = false :=
  Certificates.certificate2324

theorem isRows_kInv : IsRows (hRows (invWord kWord)) twoK⁻¹ := by
  have h := isRows_hRows (invWord kWord)
  rw [wordG_invWord localX localY kWord kWord_letters] at h
  exact h

theorem forall₂_twoRows4 : List.Forall₂ IsRows twoRows4 twoU4 := by
  refine List.Forall₂.cons (isRows_hRows _) (List.Forall₂.cons (isRows_hRows _)
    (List.Forall₂.cons ((isRows_hRows _ |>.mul (isRows_hRows _)).mul isRows_kInv)
    (List.Forall₂.cons ((isRows_hRows _ |>.mul (isRows_hRows _)).mul isRows_kInv)
    List.Forall₂.nil)))

theorem forall₂_twoRowsList : List.Forall₂ IsRows twoRowsList twoList :=
  foldl_forall₂ strongWords twoRows4 twoU4 forall₂_twoRows4 native_two_facts.2.2.1

theorem twoList_length : twoList.length = 10 := by
  rw [← forall₂_twoRowsList.length_eq]
  exact native_two_facts.2.2.2.1

theorem origWords_eq : wordG (tupleLetters twoList) origWord0 = localX ∧
    wordG (tupleLetters twoList) origWord1 = localY := by
  obtain ⟨-, -, hinv, -, h0, h1, -⟩ := native_two_facts
  have hR := isRows_tupleRows forall₂_twoRowsList hinv
  exact ⟨(isRows_signedRows hR origWord0).eq_of_eqRows isRows_localX h0,
    (isRows_signedRows hR origWord1).eq_of_eqRows isRows_localY h1⟩

theorem twoC_comm : twoC0 * involT = involT * twoC0 ∧ twoC1 * involT = involT * twoC1 := by
  obtain ⟨h0, h1, -⟩ := native_two_facts
  exact ⟨((isRows_hRows _).mul isRows_rowsT).eq_of_eqRows (isRows_rowsT.mul (isRows_hRows _)) h0,
    ((isRows_hRows _).mul isRows_rowsT).eq_of_eqRows (isRows_rowsT.mul (isRows_hRows _)) h1⟩

theorem localH_le_twoH4 : localH ≤ twoH4 := by
  rw [localH, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← origWords_eq.1]
    exact wordG_mem _ (tupleLetters_mem twoList_mem_twoH4) _
  · rw [← origWords_eq.2]
    exact wordG_mem _ (tupleLetters_mem twoList_mem_twoH4) _

theorem localH_eq_twoH4 : localH = twoH4 := by
  refine le_antisymm localH_le_twoH4 ?_
  rw [twoH4, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact twoC0_mem
  · exact twoC1_mem
  · exact localH.mul_mem (localH.mul_mem twoK_mem twoC0_mem) (localH.inv_mem twoK_mem)
  · exact localH.mul_mem (localH.mul_mem twoK_mem twoC1_mem) (localH.inv_mem twoK_mem)

theorem isRows_twoG : IsRows rowsTwoG twoG :=
  (isRows_rowsV.mul (isRows_hRows _)).mul isRows_rowsVInv

theorem isRows_twoGInv : IsRows rowsTwoGInv twoG⁻¹ := by
  have h := (isRows_rowsV.mul isRows_kInv).mul isRows_rowsVInv
  have e : transporterV * twoK⁻¹ * transporterV⁻¹ = twoG⁻¹ := by
    rw [twoG]
    group
  rw [e] at h
  exact h

theorem isRows_twoR : IsRows rowsTwoR twoR := (isRows_twoG.mul isRows_a).mul isRows_twoGInv

theorem isRows_E217 : IsRows rowsE217 (zP * qP 2 * qP 3 * qP 5 * qP 6) :=
  ((((Packet.isRows_signedWord _).mul (Packet.isRows_signedWord _)).mul
    (Packet.isRows_signedWord _)).mul (Packet.isRows_signedWord _)).mul
    (Packet.isRows_signedWord _)

theorem twoR_eq : twoR = EP 217 := by
  rw [EP_217]
  exact isRows_twoR.eq_of_eqRows isRows_E217 native_two_facts.2.2.2.2.2.2.1

theorem twoR_mul_self : twoR * twoR = 1 := by
  rw [twoR]
  have h : twoG * a * twoG⁻¹ * (twoG * a * twoG⁻¹) = twoG * (a * a) * twoG⁻¹ := by group
  rw [h, AllConj.a_mul_self, mul_one, mul_inv_cancel]

theorem twoR_ne_one : twoR ≠ 1 :=
  isRows_twoR.ne_of_eqRows IsRows.one native_two_facts.2.2.2.2.2.2.2.1

theorem twoR_ne_z : twoR ≠ z :=
  isRows_twoR.ne_of_eqRows isRows_z native_two_facts.2.2.2.2.2.2.2.2

theorem twoR_mem_Q : twoR ∈ Q := (mem_Q_iff_EP twoR).2 ⟨217, twoR_eq.symm⟩

theorem twoR_not_mem_zpowers : twoR ∉ Subgroup.zpowers z := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, z_mul_self]
  have e : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
  · rw [e, hk2, zpow_zero] at hk
    exact twoR_ne_one hk.symm
  · rw [e, hk2, zpow_one] at hk
    exact twoR_ne_z hk.symm

theorem ctuc_Th_two_centralizer_data :
    twoC0 = wordG (pairLetters localX localY) centWord0 ∧
    twoC1 = wordG (pairLetters localX localY) centWord1 ∧
    twoK = localY * localY * localX * localY ∧ twoG = transporterV * twoK * transporterV⁻¹ ∧
    twoR = twoG * a * twoG⁻¹ ∧ twoM1 = M.map (MulAut.conj twoG).toMonoidHom ∧
    twoList.length = 10 ∧ twoList.take 4 = twoU4 ∧
    (∀ i < 6, twoList.take (i + 5) =
      twoStep (twoList.take (i + 4)) (strongWords.getD i [])) ∧
    (∀ i < 6, ∀ l ∈ strongWords.getD i [], l ≠ 0 ∧ l.natAbs ≤ i + 4) ∧
    (∀ l ∈ origWord0, l ≠ 0 ∧ l.natAbs ≤ 10) ∧ (∀ l ∈ origWord1, l ≠ 0 ∧ l.natAbs ≤ 10) ∧
    ∀ u ∈ twoList, u ∈ localH := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, twoList_length, ?_, ?_, by decide, by decide, by decide,
    fun u hu => localH_eq_twoH4 ▸ twoList_mem_twoH4 u hu⟩
  · simp [twoK, kWord, wordG, pairLetters, mul_assoc]
  · simp [twoList, strongWords, twoStep, twoU4]
  · intro i hi
    interval_cases i <;> simp [twoList, strongWords, twoStep, twoU4]

theorem ctuc_Th_two_centralizer_local_generation :
    twoC0 * involT = involT * twoC0 ∧ twoC1 * involT = involT * twoC1 ∧
    localH = Subgroup.closure {twoC0, twoC1, twoK * twoC0 * twoK⁻¹, twoK * twoC1 * twoK⁻¹} ∧
    twoR = EP 217 ∧ ∃ h : twoR ∈ Q, (⟨twoR, h⟩ : Q) ∉ Subgroup.center Q ∧ orderOf twoR = 2 := by
  refine ⟨twoC_comm.1, twoC_comm.2, localH_eq_twoH4, twoR_eq, twoR_mem_Q, ?_,
    orderOf_eq_prime (by rw [sq]; exact twoR_mul_self) twoR_ne_one⟩
  rw [center_Q, Subgroup.mem_subgroupOf]
  exact twoR_not_mem_zpowers

end CFSG.Sporadic.ThSchreier
