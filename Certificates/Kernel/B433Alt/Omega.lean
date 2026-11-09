module

public import Certificates.Kernel.B433Alt.Chains
public import Certificates.Kernel.B433Alt.Om.N
public import Certificates.Kernel.B433Alt.Om.R
public import Certificates.Kernel.B433Alt.Om.O
public import Certificates.Kernel.B433Alt.Om.C0
public import Certificates.Kernel.B433Alt.Om.C1
public import Certificates.Kernel.B433Alt.Om.C2
public import Certificates.Kernel.B433Alt.Om.C3
public import Certificates.Kernel.B433Alt.Om.C4
public import Certificates.Kernel.B433Alt.Om.C5
public import Certificates.Kernel.B433Alt.Om.C6
public import Certificates.Kernel.B433Alt.Om.C7
public import CFSG.Certificates.Kernel.B433Alt.Group
public import CFSG.YGroups.Model233F

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration CFSG.KD.B4AN

#kc_forall_tree nc_all (fun k => CFSG.KD.B4AN.netColChk k = true) 190 CFSG.KD.B4AN.nc
#kc_forall_tree rel_all (fun i => CFSG.KD.B4AN.relPlChk i = true) 1083 CFSG.KD.B4AN.rel
#kc_forall_tree seg_all (fun k => CFSG.KD.B4AN.segK k = true) 1975 CFSG.KD.B4AN.sg
#kc_forall_tree fin_all (fun j => CFSG.KD.B4AN.finK j = true) 64 CFSG.KD.B4AN.fin

theorem tag_ok : ∀ c < 10, ∀ b < 128, CB (256 * c + b) >>> 81920 = b := by decide +kernel

@[expose] noncomputable def allNB (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => CFSG.KC.B4A.andB (f i) acc) n

theorem allNB_spec {f : ℕ → Bool} : ∀ {n : ℕ}, allNB n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    change CFSG.KC.B4A.andB (f n) (allNB n f) = true at h
    cases hfn : f n
    · rw [hfn] at h
      exact absurd h Bool.false_ne_true
    · rw [hfn] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact allNB_spec h i hi
      · exact hfn

theorem pw_lt : ∀ p < 8192, wInH (CFSG.KD.B4A.PW p) = true :=
  allNB_spec (f := fun p => wInH (CFSG.KD.B4A.PW p)) (by decide +kernel)

theorem PW_per (p : ℕ) : CFSG.KD.B4A.PW p = CFSG.KD.B4A.PW (p % 8192) := by
  rw [mod_8192]
  delta CFSG.KD.B4A.PW
  dsimp only
  rw [land_land]

theorem pw_ok (p : ℕ) : wInH (CFSG.KD.B4A.PW p) = true := by
  rw [PW_per]
  exact pw_lt _ (Nat.mod_lt _ (by norm_num))

theorem pw_len_lt : ∀ p < 8192, wLen (CFSG.KD.B4A.PW p) < 2 ^ 16 := by
  have h := allNB_spec (f := fun p => Nat.blt (wLen (CFSG.KD.B4A.PW p)) 65536) (n := 8192)
    (by decide +kernel)
  intro p hp
  have h' : Nat.blt (wLen (CFSG.KD.B4A.PW p)) 65536 = true := h p hp
  rw [show (2 : ℕ) ^ 16 = 65536 by norm_num]
  exact Nat.blt_eq.mp h'

theorem pw_len (p : ℕ) : wLen (CFSG.KD.B4A.PW p) < 2 ^ 16 := by
  rw [PW_per]
  exact pw_len_lt _ (Nat.mod_lt _ (by norm_num))

theorem om_rels : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten],
    ∀ u < 19, relPlOK MS w u = true := by
  intro w hw u hu
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hlen : (yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten]).length = 57 := by
    decide
  have hi' : i < 57 := by
    rw [hlen] at hi
    exact hi
  have hk : 19 * i + u < 1083 := by omega
  have h := rel_all (19 * i + u) hk
  unfold relPlChk at h
  have e1 : (19 * i + u) / 19 = i := by omega
  have e2 : (19 * i + u) % 19 = u := by omega
  rw [e1, e2, List.getD_eq_getElem _ _ (by unfold omRels F432W; omega)] at h
  exact h

theorem om : ∃ ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896),
    (∀ c < 10, ∀ x : Fin 412896, (ρΩ (yGen 4 3 2 c) x : ℕ) = colAt CB c x) ∧
    evalWord (yGen 4 3 2) (List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten ∈ ρΩ.ker ∧
    (∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
      omSet (netApp19 MS c E) = ρΩ (yGen 4 3 2 c) '' omSet E) ∧
    ∀ x : Fin 412896, x ∈ MulAction.orbit ρΩ.range (0 : Fin 412896) :=
  om_sound (R := 72) masks0 (fun c hc b hb => by
      have hk : 19 * c + b < 190 := by omega
      have h := nc_all (19 * c + b) hk
      unfold netColChk at h
      have e1 : (19 * c + b) / 19 = c := by omega
      have e2 : (19 * c + b) % 19 = b := by omega
      rwa [e1, e2] at h)
    tag_ok om_rels CFSG.KD.B4AN.orb0

end CertificateChecks.KernelB433

end
