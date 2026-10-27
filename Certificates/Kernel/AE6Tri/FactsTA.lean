module

public import Certificates.Kernel.AE6Tri.ChecksTA
public import CFSG.Certificates.Kernel.AE6TriSoundB
public import Certificates.Kernel.AE6Tri.FactsM

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KD.AE6TA
open CertificateChecks.KernelAE6TriTA

theorem nthD_eq {α : Type} (d : α) : ∀ (L : List α) (j : Nat), nthD L d j = L.getD j d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, j + 1 => nthD_eq d L j

theorem ml_letters : ∀ c < 8, bit 93 c = true → c ∈ taEL ∧ c ∈ ml := by decide

theorem taSI_lt : ∀ j < 6, ∀ t < 6, nthN (nthD taSI [] j) t < 168 := by decide

theorem taNodes_len : taNodes.length ≤ 30 * 11 := by
  have h := kTaLen
  rw [Nat.ble_eq, lenL_eq] at h
  exact h

theorem taNodes_ne : taNodes ≠ [] := by decide

theorem srch_all : ∀ k < 11,
    sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes (30 * k) (30 * k + 30) = true := by
  intro k hk
  interval_cases k
  · exact kTaSrch0
  · exact kTaSrch1
  · exact kTaSrch2
  · exact kTaSrch3
  · exact kTaSrch4
  · exact kTaSrch5
  · exact kTaSrch6
  · exact kTaSrch7
  · exact kTaSrch8
  · exact kTaSrch9
  · exact kTaSrch10

theorem taB_lt : ∀ x ∈ taB, x < 360 := by decide

theorem ta0_perm : ∃ ℓ : Nat → Equiv.Perm (Fin 360), LRep taLL ℓ ∧ ℓ 0 = wv gP taKw1 ∧
    (∀ c ∈ taEL, ∀ a < 168, tq taTau c a < 168 ∧ ℓ (tq taTau c a) = gP c * ℓ a * (gP c)⁻¹) ∧
    (∀ a < 168, ∃ w : List Nat, (∀ c ∈ w, c ∈ taEL) ∧ ℓ a = wv gP w * ℓ 0 * (wv gP w)⁻¹) ∧
    (∀ i < taKW.length, nthN taKI i < 168 ∧ ℓ (nthN taKI i) = wv gP (taKW.getD i [])) ∧
    (∀ i < tg0.length, nthN taTI i < 168 ∧ ℓ (nthN taTI i) = wv gP (tg0.getD i [])) ∧
    (∀ j < taTI.length, nthN taTI j < 168) ∧ prof ℓ taB taPW taPO taPS taPM (nthN taTI) ∧
    ∀ y : Nat → Nat, (∀ t < 6, y t < 168) → prof ℓ taB taPW taPO taPS taPM y →
      ∃ w : List Nat, lettersIn 93 w = true ∧ ∃ j < 6, ∀ t < 6,
        wv gP w * ℓ (nthN (nthD taSI [] j) t) * (wv gP w)⁻¹ = ℓ (y t) := by
  obtain ⟨ℓ, hℓ, h0, hτ, hw⟩ := lOK_sound gRep kTaL
  have hT := tOK_sound hℓ taB_lt kTaP
  refine ⟨ℓ, hℓ, h0, hτ, hw, vOK_sound hℓ gRep kTaK, vOK_sound hℓ gRep kTaT, hT.1, hT.2, ?_⟩
  exact sOK_sound gRep hℓ (by norm_num)
    (fun c hc hb a ha => hτ c (ml_letters c hc hb).1 a ha)
    (fun c hc hb => invB_sound gRep kTaB c (ml_letters c hc hb).2) taSI_lt taNodes_ne 11
    taNodes_len srch_all

end CertificateChecks.KernelAE6Tri

end
