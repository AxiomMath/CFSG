module

public import Certificates.Kernel.Co1Three.Bind
public import Certificates.Kernel.Co1Three.BindR
public import Certificates.Kernel.Co1Three.Rest
public import Certificates.Kernel.Co1ThreeK.GlueNodes

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.KS.Raw CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem unpack_TS_A₁ : Native.aR = unpack 24 24 (TS 0) := by
  have h := CertificateChecks.KernelSporSch.Co1Packed.rows_of bindA
  rw [Array.toArray_toList] at h
  rw [CertificateChecks.KernelSporSch.Co1ThreeLocal.aR_eq, h]

theorem unpack_TS_A₂ : Native.bR = unpack 24 24 (TS 1) := by
  have h := CertificateChecks.KernelSporSch.Co1Packed.rows_of bindB
  rw [Array.toArray_toList] at h
  rw [CertificateChecks.KernelSporSch.Co1ThreeLocal.bR_eq, h]

theorem unpack_TS_a {k : Nat} (hk : k < 6) : Native.aRows k = unpack 24 24 (TS (k + 2)) := by
  have h := Nat.eq_of_beq_eq_true (CFSG.KS.SporSch.M24.MatL.allN_iff.1 elemA k hk)
  exact (congrFun CertificateChecks.KernelSporSch.Co1Elem.aRows_eq k).trans (congrArg _ h.symm)

theorem unpack_TS_root {j : Nat} (hj : j < 3) :
    Co1T.Native.rootRows j = unpack 24 24 (TS (j + 8)) := by
  have h := Nat.eq_of_beq_eq_true (CFSG.KS.SporSch.M24.MatL.allN_iff.1 rootsR j hj)
  exact (CertificateChecks.KernelCo1ThreeK.rootRows_eq hj).trans (congrArg _ h.symm)

theorem mRep_TS {R : Native.Rows} {k : Nat} {g : GL24} (hR : R = unpack 24 24 (TS k))
    (h : MRep R g) : matK (TS k) = g := by
  rw [← mRep_iff, CFSG.KS.SporSch.M24.unpackR_eq_unpack, ← hR]
  exact h

theorem matK_TS_A₁ : matK (TS 0) = A₁ :=
  mRep_TS unpack_TS_A₁ rep_A₁

theorem matK_TS_A₂ : matK (TS 1) = A₂ :=
  mRep_TS unpack_TS_A₂ rep_A₂

theorem matK_TS_a
    (i : Fin 6) : matK (TS (i.val + 2)) = a i :=
  mRep_TS (unpack_TS_a i.isLt) (a_rep i)

theorem matK_TS_root
    {j : Nat} (hj : j < 3) : matK (TS (j + 8)) = (Co1T.root j : GL24) :=
  mRep_TS (unpack_TS_root hj) (KernelCo1ThreeK.wordL_repK _)

theorem matK_TS_one : matK (TS 11) = 1 :=
  (congrArg matK (Nat.eq_of_beq_eq_true
    (@CFSG.KS.SporSch.M24.MatS.bAnd_split (canAllK TS 12) (Nat.beq (TS 11) oneK) seeds).2)).trans
    matK_oneK

theorem nodeIn_seeds :
    ∀ k < 12, NodeIn GA TS k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ (2 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 11) ∨ k = 11) with
    rfl | rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl
  · exact ⟨A₁, A₁_mem, matK_TS_A₁⟩
  · exact ⟨A₂, A₂_mem, matK_TS_A₂⟩
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
    exact ⟨a ⟨i, by omega⟩, A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ (a_mem_E _))),
      matK_TS_a ⟨i, by omega⟩⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    exact ⟨Co1T.root j, (Co1T.root j).2, matK_TS_root (by omega)⟩
  · exact ⟨1, GA.one_mem, matK_TS_one.trans (Units.val_one).symm⟩

end CertificateChecks.KernelCo1Three

end
