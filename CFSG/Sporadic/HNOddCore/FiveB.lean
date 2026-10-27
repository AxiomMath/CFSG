module

public import CFSG.Sporadic.HNOddCore.FiveA
public import CFSG.Sporadic.HNOddCore.OddA
public import Certificates.Certificate2085
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate16041

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem map_getElem! {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (A : Array α)
    {j : ℕ} (hj : j < A.size) : (A.map f)[j]! = f A[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos A j hj]

theorem five_small_parts :
    natChainOK natStrongArr = true ∧ a6NatOK natStrongArr = true ∧
    iOrbitOK = true ∧ aOrbitsOK = true ∧ labelsOK natStrongArr = true ∧
    gammaOK orb7 orb42 = true ∧ fiberOK = true ∧ pairsOK = true := by
  have h := five_small_cert
  unfold fiveSmallChecks fiveSmallChecksN at h
  rw [← natStrongArr_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem a6_parts :
    FAData.a6Words.size = 4 ∧ ∀ k < 4, plettersOK 17 FAData.a6Words[k]! = true ∧
    ∀ i < 6, ((natImgs natStrongArr FAData.a6Words)[k]!)[i]! = i := by
  have h := five_small_parts.2.1
  unfold a6NatOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have := allBelowN_spec h.2 hk
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1, fun i hi => by simpa using allBelowN_spec this.2 hi⟩

theorem aWords_size :
    FAData.aWords.size = 5 := fa_nat_parts.2.2.2.2.1

theorem aWords_letters
    {j : ℕ} (hj : j < 5) : plettersOK 17 FAData.aWords[j]! = true :=
  (fa_nat_parts.2.2.2.2.2 j hj).1

theorem fJ_comm_aGen
    {j : ℕ} (hj : j < 5) : fJ * aGenJ j = aGenJ j * fJ :=
  five_comm_aGen hj

theorem fJ_comm_g5 :
    fJ * g5J = g5J * fJ := five_comm_g5

theorem fJ_comm_commJ :
    fJ * commJ = commJ * fJ := by
  have ha := fJ_comm_aGen (j := 0) (by norm_num)
  have hai : fJ * (aGenJ 0)⁻¹ = (aGenJ 0)⁻¹ * fJ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ha, ← mul_assoc, inv_mul_cancel, one_mul]
  have hgi : fJ * g5J⁻¹ = g5J⁻¹ * fJ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, fJ_comm_g5, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [commJ, show FAData.iCommIdx = 0 from rfl]
  calc fJ * ((aGenJ 0)⁻¹ * g5J⁻¹ * aGenJ 0 * g5J)
      = (fJ * (aGenJ 0)⁻¹) * g5J⁻¹ * aGenJ 0 * g5J := by group
    _ = (aGenJ 0)⁻¹ * (fJ * g5J⁻¹) * aGenJ 0 * g5J := by rw [hai]; group
    _ = (aGenJ 0)⁻¹ * g5J⁻¹ * (fJ * aGenJ 0) * g5J := by rw [hgi]; group
    _ = (aGenJ 0)⁻¹ * g5J⁻¹ * aGenJ 0 * (fJ * g5J) := by rw [ha]; group
    _ = (aGenJ 0)⁻¹ * g5J⁻¹ * aGenJ 0 * g5J * fJ := by rw [fJ_comm_g5]; group

theorem fJ_comm_iGen
    (k : ℕ) : fJ * iGen k = iGen k * fJ := by
  unfold iGen
  split_ifs with h
  · exact fJ_comm_aGen h
  · exact fJ_comm_commJ

theorem fFixed_getElem! {k : ℕ} : FAData.fFixed.toArray[k]! = FAData.fFixed.getD k 0 :=
  toArray_getElem! _ k

theorem omList :
    PtList hnsData.n FAData.fFixed.toArray where
  lt k hk := by
    rw [fFixed_getElem!]
    exact fFixed_lt k (by simpa [fFixed_length] using hk)
  inj k hk l hl he := by
    rw [fFixed_getElem!, fFixed_getElem!] at he
    exact fFixed_inj k (by simpa [fFixed_length] using hk) l (by simpa [fFixed_length] using hl) he

theorem fFixed_size :
    FAData.fFixed.toArray.size = 50 := by simp [fa_data_sizes.2.2.2.2.2.2.2.2.1]

@[expose] def omPt
    (k : Fin 50) : X := omList.pt ⟨k, by rw [fFixed_size]; exact k.2⟩

theorem fix_fJ
    (x : X) : fJ • x = x ↔ ∃ k : Fin 50, omPt k = x := by
  rw [five_fix]
  constructor
  · intro hx
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hx
    have hi50 : i < 50 := by rw [← fa_data_sizes.2.2.2.2.2.2.2.2.1]; exact hi
    refine ⟨⟨i, hi50⟩, Fin.ext ?_⟩
    rw [omPt, PtList.pt_val]
    simp only [List.getElem!_toArray]
    rw [getElem!_pos _ i hi, hie]
  · rintro ⟨k, rfl⟩
    rw [omPt, PtList.pt_val]
    simp only [List.getElem!_toArray]
    rw [getElem!_pos _ (k : ℕ) (by rw [fa_data_sizes.2.2.2.2.2.2.2.2.1]; exact k.2)]
    exact List.getElem_mem _

end CFSG.Sporadic.HNOddCore
