module

public import CFSG.Sporadic.ONOddCore.MinusCheck
public import CFSG.Sporadic.Schreier.ONVectorOrder

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON CFSG.Sporadic.ON.Native
open CFSG.Certificates CFSG.ONSchreier.CArrays

@[expose] def sigmaPerm : Equiv.Perm (Fin N) := permOfArr N sigmaArr

theorem sigmaArr_eq : sigmaArr = sigmaT := by
  show _ = sigmaTab vectorOrbit (posOf (indexOf vectorOrbit.keys) nPts)
  rw [vectorOrbit_def]
  rfl

theorem minus_facts :
    let invs := allInvSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray
    let Ls := cLevels nPts Data.baseList.toArray
      (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray)
    let base := Data.baseList.toArray
    let k0 := Ls[0]!.pos[sigmaArr[base[0]!]!]!
    let x1 := trInvApp invs[0]! Ls[0]! Ls[0]!.pts.size k0 sigmaArr[base[1]!]!
    let k1 := Ls[1]!.pos[x1]!
    pisInv nPts sigmaArr sigmaArr = true ∧ k0 < Ls[0]!.pts.size ∧ k1 < Ls[1]!.pts.size ∧
      trInvApp invs[1]! Ls[1]! Ls[1]!.pts.size k1
        (trInvApp invs[0]! Ls[0]! Ls[0]!.pts.size k0 sigmaArr[base[2]!]!) = 81515 ∧
      ¬ Ls[2]!.pos[81515]! < Ls[2]!.pts.size ∧ base[2]! = 100817 := by
  have h := minus_cert
  simp only [minusOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem prep_sigma :
    PRep N sigmaArr sigmaPerm := (prep_permOfArr minus_facts.1).1

theorem vv_sigmaPerm
    (i : Fin N) : vv (sigmaPerm i) = -vv i := by
  rw [← prep_sigma i, sigmaArr_eq]
  exact vv_sigmaT i.isLt

theorem qon_base_val
    {i : ℕ} (hi : i < QON.baseCount) :
    ((QON.base.get ⟨i, hi⟩ : Fin N) : ℕ) = Data.baseList.toArray[i]! :=
  qon_arrays.base_val ⟨i, hi⟩

theorem sigma_val
    (x : Fin N) : ((sigmaPerm x : Fin N) : ℕ) = sigmaArr[(x : ℕ)]! :=
  (prep_sigma x).symm

theorem transversal_at
    {i : ℕ} (hi : i < QON.baseCount) {z : Fin N}
    (hk : (lev N qonStrongArrs Data.baseList.toArray i).pos[(z : ℕ)]! <
      (lev N qonStrongArrs Data.baseList.toArray i).pts.size) :
    QON.transversal? ⟨i, hi⟩ z = some (levT QON qonStrongArrs Data.baseList.toArray i
      ((lev N qonStrongArrs Data.baseList.toArray i).pos[(z : ℕ)]!)) := by
  have hF := chainFacts qon_chain_cert.1
  have hpt := (qon_arrays.levelFacts hF hi).pts_pos z z.isLt hk
  have hz : levPts QON qonStrongArrs Data.baseList.toArray i
      ((lev N qonStrongArrs Data.baseList.toArray i).pos[(z : ℕ)]!) = z := by
    apply Fin.ext
    rw [qon_arrays.levPts_val hF hi hk, hpt]
  have h := qon_arrays.transversal_of_lt hF hi hk
  rw [hz] at h
  exact h

theorem levT_inv_val
    {i : ℕ} (hi : i < QON.baseCount) {k : ℕ}
    (hk : k < (lev N qonStrongArrs Data.baseList.toArray i).pts.size) (x : Fin N) :
    (((levT QON qonStrongArrs Data.baseList.toArray i k)⁻¹ x : Fin N) : ℕ) =
      trInvApp (invsOf N qonStrongArrs Data.baseList.toArray)[i]!
        (lev N qonStrongArrs Data.baseList.toArray i)
        (lev N qonStrongArrs Data.baseList.toArray i).pts.size k x :=
  (qon_arrays.trInvApp_eq (chainFacts qon_chain_cert.1) hi _ k hk hk x x.isLt).symm

theorem sigma_sift :
    ∃ (h0 : 0 < QON.baseCount) (h1 : 1 < QON.baseCount) (h2 : 2 < QON.baseCount)
      (t₀ t₁ : Equiv.Perm (Fin N)),
      QON.transversal? ⟨0, h0⟩ (sigmaPerm (QON.base.get ⟨0, h0⟩)) = some t₀ ∧
      QON.transversal? ⟨1, h1⟩ ((t₀⁻¹ * sigmaPerm) (QON.base.get ⟨1, h1⟩)) = some t₁ ∧
      ((QON.base.get ⟨2, h2⟩ : Fin N) : ℕ) = 100817 ∧
      (((t₁⁻¹ * (t₀⁻¹ * sigmaPerm)) (QON.base.get ⟨2, h2⟩) : Fin N) : ℕ) = 81515 ∧
      QON.transversal? ⟨2, h2⟩ ((t₁⁻¹ * (t₀⁻¹ * sigmaPerm)) (QON.base.get ⟨2, h2⟩)) = none := by
  have hf := minus_facts
  dsimp only at hf
  obtain ⟨-, hk0, hk1, hx2, hnot, hb2⟩ := hf
  have h29 := qon_baseCount
  have h0 : 0 < QON.baseCount := by omega
  have h1 : 1 < QON.baseCount := by omega
  have h2 : 2 < QON.baseCount := by omega
  have hz0 : ((sigmaPerm (QON.base.get ⟨0, h0⟩) : Fin N) : ℕ) =
      sigmaArr[Data.baseList.toArray[0]!]! := by
    rw [sigma_val, qon_base_val]
  have ht0 := transversal_at h0 (z := sigmaPerm (QON.base.get ⟨0, h0⟩)) (by rw [hz0]; exact hk0)
  set t₀ := levT QON qonStrongArrs Data.baseList.toArray 0
    ((lev N qonStrongArrs Data.baseList.toArray 0).pos[((sigmaPerm (QON.base.get ⟨0, h0⟩) :
      Fin N) : ℕ)]!) with ht₀
  have hz1 : (((t₀⁻¹ * sigmaPerm) (QON.base.get ⟨1, h1⟩) : Fin N) : ℕ) =
      trInvApp (invsOf N qonStrongArrs Data.baseList.toArray)[0]!
        (lev N qonStrongArrs Data.baseList.toArray 0)
        (lev N qonStrongArrs Data.baseList.toArray 0).pts.size
        ((lev N qonStrongArrs Data.baseList.toArray 0).pos[sigmaArr[Data.baseList.toArray[0]!]!]!)
        sigmaArr[Data.baseList.toArray[1]!]! := by
    rw [Equiv.Perm.mul_apply, ht₀, levT_inv_val h0 (by rw [hz0]; exact hk0)]
    simp only [sigma_val, qon_base_val]
  have ht1 := transversal_at h1 (z := (t₀⁻¹ * sigmaPerm) (QON.base.get ⟨1, h1⟩))
    (by rw [hz1]; exact hk1)
  set t₁ := levT QON qonStrongArrs Data.baseList.toArray 1
    ((lev N qonStrongArrs Data.baseList.toArray 1).pos[(((t₀⁻¹ * sigmaPerm)
      (QON.base.get ⟨1, h1⟩) : Fin N) : ℕ)]!) with ht₁
  have hz2 : (((t₁⁻¹ * (t₀⁻¹ * sigmaPerm)) (QON.base.get ⟨2, h2⟩) : Fin N) : ℕ) = 81515 := by
    rw [← hx2, Equiv.Perm.mul_apply, ht₁, levT_inv_val h1 (by rw [hz1]; exact hk1), hz1,
      Equiv.Perm.mul_apply, ht₀, levT_inv_val h0 (by rw [hz0]; exact hk0)]
    simp only [sigma_val, qon_base_val]
  refine ⟨h0, h1, h2, t₀, t₁, ht0, ht1, by rw [qon_base_val, hb2], hz2, ?_⟩
  apply qon_arrays.transversal_eq_none (chainFacts qon_chain_cert.1) h2
  rw [hz2]
  exact hnot

theorem sigma_sift_false :
    QON.sift sigmaPerm 0 = false := by
  obtain ⟨h0, h1, h2, t₀, t₁, ht0, ht1, -, -, ht2⟩ := sigma_sift
  rw [RawSchreierDatum.sift, schreierSiftSucceeds_eq_false_iff]
  have e0 := QON.siftLevels_cons QON.orbitTables ⟨0, h0⟩
  have e1 := QON.siftLevels_cons QON.orbitTables ⟨1, h1⟩
  have e2 := QON.siftLevels_cons QON.orbitTables ⟨2, h2⟩
  simp only at e0 e1 e2
  rw [e0, e1, e2, RawSchreierDatum.orbitTables_get, RawSchreierDatum.orbitTables_get,
    RawSchreierDatum.orbitTables_get,
    schreierSiftResidual_available _ _ _ _ t₀ ht0, schreierSiftResidual_available _ _ _ _ t₁ ht1,
    schreierSiftResidual_unavailable _ _ _ _ ht2]
  simp

theorem sigma_not_mem :
    sigmaPerm ∉ Pv := by
  rw [← qon_originalSubgroup]
  exact (QON.sift_eq_false_iff_not_mem_original qon_valid sigmaPerm).1 sigma_sift_false

theorem neg_one_not_mem_J :
    (-1 : GL (Fin 154) (ZMod 3)) ∉ J := by
  intro h
  apply sigma_not_mem
  have hphi : phiV ⟨-1, h⟩ = sigmaPerm := by
    ext i
    have h1 := vv_phiV ⟨-1, h⟩ i
    have hm : Matrix.mulVec (mat (⟨-1, h⟩ : J)) (vv i) = -vv i := by
      show Matrix.mulVec ((-1 : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3))
        (vv i) = -vv i
      rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
      rfl
    rw [hm, ← vv_sigmaPerm] at h1
    exact vv_injective (phiV ⟨-1, h⟩ i).isLt (sigmaPerm i).isLt h1
  rw [← hphi, ← range_phiV]
  exact ⟨_, rfl⟩

end CFSG.Sporadic.ONOddCore
