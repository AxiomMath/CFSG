module

public import CFSG.Sporadic.HNOddCore.FiveC
public import CFSG.Sporadic.HNOddCore.Alt12
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm

theorem iSm_get
    {k : ℕ} (hk : k < 6) : iSm[k]! = (FAData.iSmall[k]!).toArray := by
  rw [iSm, map_getElem! _ _ (by rw [iSmall_size]; exact hk)]

theorem act_of_omega {g : JH} {T : List ℕ}
    (hT : ∀ t < 50, T.getD t 0 < 50)
    (hg : ∀ t < 50, ∀ x : X, x.val = FAData.fFixed.getD t 0 →
      (g • x).val = FAData.fFixed.getD (T.getD t 0) 0) :
    ∀ k : Fin FAData.fFixed.toArray.size, ∃ h : T.toArray[(k : ℕ)]! < FAData.fFixed.toArray.size,
      g • omList.pt k = omList.pt ⟨T.toArray[(k : ℕ)]!, h⟩ := by
  intro k
  have hk : (k : ℕ) < 50 := by simpa [fFixed_length] using k.2
  rw [toArray_getElem!]
  refine ⟨by simpa [fFixed_length] using hT k hk, Fin.ext ?_⟩
  rw [PtList.pt_val, fFixed_getElem!]
  exact hg k hk _ (by rw [PtList.pt_val, fFixed_getElem!])

theorem hactI :
    ∀ s < iSm.size, ∀ k : Fin FAData.fFixed.toArray.size,
    ∃ h : (iSm[s]!)[(k : ℕ)]! < FAData.fFixed.toArray.size,
      iGen s • omList.pt k = omList.pt ⟨(iSm[s]!)[(k : ℕ)]!, h⟩ := by
  intro s hs
  have hs6 : s < 6 := by
    have : iSm.size = 6 := by simp [iSm, iSmall_size]
    omega
  rw [iSm_get hs6]
  exact act_of_omega (iSmall_lt s hs6) fun t ht x hx => five_iGen_omega hs6 ht hx

theorem a6Sm_get
    {k : ℕ} (hk : k < 4) : a6Sm[k]! = (FAData.a6Small[k]!).toArray := by
  rw [a6Sm, map_getElem! _ _ (by rw [a6Small_size]; exact hk)]

theorem hactA6 :
    ∀ s < a6Sm.size, ∀ k : Fin FAData.fFixed.toArray.size,
    ∃ h : (a6Sm[s]!)[(k : ℕ)]! < FAData.fFixed.toArray.size,
      a6Gen s • omList.pt k = omList.pt ⟨(a6Sm[s]!)[(k : ℕ)]!, h⟩ := by
  intro s hs
  have hs4 : s < 4 := by
    have : a6Sm.size = 4 := by simp [a6Sm, a6Small_size]
    omega
  rw [a6Sm_get hs4]
  exact act_of_omega (a6Small_lt s hs4) fun t ht x hx => five_a6Gen_omega hs4 ht hx

end CFSG.Sporadic.HNOddCore
