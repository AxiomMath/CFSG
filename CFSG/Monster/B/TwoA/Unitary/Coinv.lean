module

public import CFSG.Monster.B.TwoA.Unitary.Stab891
public import Certificates.Certificate16040

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA

@[expose] def commV :
    Submodule (ZMod 2) (Wv v0) :=
  Submodule.span (ZMod 2) {x | ∃ v ∈ sigmaPerp, ∃ g ∈ Usig, x = wAct v0 g v + v}

theorem commV_le :
    commV ≤ sigmaPerp := by
  rw [commV, Submodule.span_le]
  rintro _ ⟨v, hv, g, hg, rfl⟩
  exact sigmaPerp.add_mem (wAct_mem_sigmaPerp' g hg hv) hv
where
  wAct_mem_sigmaPerp' (g : Kstab v0) (hg : g ∈ Usig) {v : Wv v0} (hv : v ∈ sigmaPerp) :
      wAct v0 g v ∈ sigmaPerp := by
    change bW sigmaW (wAct v0 g v) = 0
    rw [← (mem_Usig.1 hg : wAct v0 g sigmaW = sigmaW), bW_wAct]
    exact hv

theorem wFr_mem_sigmaPerp :
    wFr ∈ sigmaPerp := n6vec_zero ▸ n6vec_mem_sigmaPerp 0

theorem n6vec_add_wFr_mem
    (j : Fin 891) : n6vec j + wFr ∈ commV := by
  obtain ⟨u, hu, e⟩ := exists_wAct_wFr j
  rw [← e]
  exact Submodule.subset_span ⟨wFr, wFr_mem_sigmaPerp, u, hu, rfl⟩

theorem n6Vec_one_three :
    n6VecArr[1]! = 12319 ∧ n6VecArr[3]! = 12288 :=
  Certificates.certificate16040

theorem n6vec_sum_zero : n6vec 0 + n6vec 1 + n6vec 3 = 0 := by
  have h0 : n6vec 0 = decW 31 := congrArg decW n6Vec_zero
  have h1 : n6vec 1 = decW 12319 := congrArg decW n6Vec_one_three.1
  have h3 : n6vec 3 = decW 12288 := congrArg decW n6Vec_one_three.2
  rw [h0, h1, h3, ← decW_xor, ← decW_xor, show (31 ^^^ 12319 ^^^ 12288 : ℕ) = 0 by decide,
    decW_zero]

theorem add_self_W (x : Wv v0) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem wFr_mem_commV :
    wFr ∈ commV := by
  have h1 := n6vec_add_wFr_mem 1
  have h3 := n6vec_add_wFr_mem 3
  have e : wFr = (n6vec 1 + wFr) + (n6vec 3 + wFr) := by
    have hs := n6vec_sum_zero
    rw [n6vec_zero] at hs
    calc wFr = wFr + (wFr + n6vec 1 + n6vec 3) := by rw [hs, add_zero]
      _ = (n6vec 1 + wFr) + (n6vec 3 + wFr) := by
        have hw := add_self_W wFr
        calc wFr + (wFr + n6vec 1 + n6vec 3) = (wFr + wFr) + n6vec 1 + n6vec 3 := by abel
          _ = n6vec 1 + n6vec 3 := by rw [hw, zero_add]
          _ = (n6vec 1 + wFr) + (n6vec 3 + wFr) := by
            rw [add_add_add_comm, hw, add_zero]
  rw [e]
  exact commV.add_mem h1 h3

theorem n6vec_mem_commV
    (j : Fin 891) : n6vec j ∈ commV := by
  have h := commV.add_mem (n6vec_add_wFr_mem j) wFr_mem_commV
  rwa [add_assoc, add_self_W, add_zero] at h

theorem commV_eq :
    commV = sigmaPerp := by
  refine le_antisymm commV_le ?_
  rw [← span_n6vec, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact n6vec_mem_commV j

theorem eq_sigmaPerp_of_trivial_quotient
    {X : Submodule (ZMod 2) (Wv v0)} (hX : X ≤ sigmaPerp)
    (htriv : ∀ v ∈ sigmaPerp, ∀ g ∈ Usig, wAct v0 g v + v ∈ X) : X = sigmaPerp := by
  refine le_antisymm hX ?_
  rw [← commV_eq, commV, Submodule.span_le]
  rintro _ ⟨v, hv, g, hg, rfl⟩
  exact htriv v hv g hg

theorem native_unitary_hyperplane_zero_coinvariants :
    commV = sigmaPerp ∧
    ∀ X : Submodule (ZMod 2) (Wv v0), X ≤ sigmaPerp →
      (∀ v ∈ sigmaPerp, ∀ g ∈ Usig, wAct v0 g v + v ∈ X) → X = sigmaPerp :=
  ⟨commV_eq, fun _ hX htriv => eq_sigmaPerp_of_trivial_quotient hX htriv⟩

end CFSG.Monster.B.TwoA.Unitary
