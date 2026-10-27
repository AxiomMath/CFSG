module

public import Certificates.Kernel.Co2Census.TInvChecks
public import Certificates.Kernel.Co2Census.TInvLook
public import Certificates.Kernel.Co2J.Facts
public import Certificates.Kernel.Co2Cls.Final
public import Certificates.Kernel.Co2Cls.Checks
public import CFSG.Certificates.Kernel.Co2Census.Glue
public import CFSG.RankThree.Co2.TInvFacts
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.Co2TInv

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2J CFSG.KC.Co2Cls CFSG.KC.Co2TInv
  CFSG.KC.TabMatGrp CFSG.RankThree.Co2 CertificateChecks.KernelSpor.Co2J

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem census_T_mat (hc : Nat.card (matGrp sylWords) ≤ 2 ^ 18) {x : M22}
    (hx : x ∈ matGrp sylWords) (hsq : x * x = 1) (h1 : x ≠ 1) :
    ∃ c < 10, ∃ i < NCS c, ∃ g ∈ matGrp sylWords, g * MatP 22 (elemAt (CFS c) i) = x * g := by
  rw [← genMon_G] at hc hx ⊢
  exact census_T jGen jEnum jInT coord pow32 treeR invAll lift scan fus jorb look lookJ hc hx hsq
    h1

theorem recsAll : ∀ c < 10, ∀ k < NCS c,
    recC (CFS c) Co2Cls.GC 21 (Co2Syl.RP c) (NCS c) k = true := by
  intro c hc
  interval_cases c
  · exact Co2Cls.rec0
  · exact Co2Cls.rec1
  · exact Co2Cls.rec2
  · exact Co2Cls.rec3
  · exact Co2Cls.recs4
  · exact Co2Cls.rec5
  · exact Co2Cls.rec6
  · exact Co2Cls.rec7
  · exact Co2Cls.rec8
  · exact Co2Cls.recs9

theorem letters21_size : letters21.size = 21 := rfl

theorem letters21_get : ∀ k < 21, letters21[k]! = [k + 21] := by decide

theorem wordMat_letters21 {k : ℕ} (hk : k < 21) :
    wordMat letters21[k]! = MatP 22 (Co2Cls.GC k) := by
  rw [letters21_get k hk, wordMat_eq_prod, List.map_singleton, List.prod_singleton]
  exact (Co2Syl.MatP_letter (l := k + 21) (by omega)).symm

theorem Cm_eq : Cm = genMonN 21 Co2Cls.GC := by
  have hS : Set.range (fun k : Fin letters21.size => wordMat letters21[k]) =
      Set.range fun j : Fin 21 => MatP 22 (Co2Cls.GC j) := by
    ext x
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      have hk' : k < 21 := by rwa [letters21_size] at hk
      refine ⟨⟨k, hk'⟩, ?_⟩
      change MatP 22 (Co2Cls.GC k) = wordMat letters21[k]
      rw [← wordMat_letters21 hk', getElem!_pos letters21 k hk]
      rfl
    · rintro ⟨⟨k, hk⟩, rfl⟩
      have hk' : k < letters21.size := by rw [letters21_size]; exact hk
      refine ⟨⟨k, hk'⟩, ?_⟩
      change wordMat letters21[k] = MatP 22 (Co2Cls.GC k)
      rw [← wordMat_letters21 hk, getElem!_pos letters21 k hk']
  unfold Cm matGrp genMonN
  exact congrArg Submonoid.closure hS

theorem T_le_Cm : matGrp sylWords ≤ Cm := by
  rw [Cm_eq, ← Co2Cls.Final.genMonN_HT]
  exact Co2Cls.T_le

theorem tInvFacts : TInvFacts := by
  intro hc x hx hsq h1
  obtain ⟨c, hc10, i, hi, g, hg, eg⟩ := census_T_mat hc hx hsq h1
  obtain ⟨h, hh, eh⟩ := tree_conj (recsAll c hc10) i hi
  refine ⟨c, hc10, g * h, Cm.mul_mem (T_le_Cm hg) (by rw [Cm_eq]; exact hh), ?_⟩
  rw [Co2Syl.repMat_eq hc10]
  exact conj_trans eh eg

end CertificateChecks.KernelSpor.Co2TInv

end
