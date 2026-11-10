
module

public import CFSG.Sporadic.HNOddCore.FourPairBase
public import CFSG.Sporadic.HNOddCore.PCheckBase
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.PCheckInputs
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

def wordVal {G : Type*} [Group G] (g : ℕ → G) (w : List ℤ) : G :=
  (w.map fun l => if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹).prod

theorem wordVal_nil {G : Type*} [Group G] (g : ℕ → G) : wordVal g [] = 1 := rfl

theorem wordVal_cons {G : Type*} [Group G] (g : ℕ → G) (l : ℤ) (w : List ℤ) :
    wordVal g (l :: w) =
      (if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹) * wordVal g w := by
  simp only [wordVal, List.map_cons, List.prod_cons]

theorem map_wordVal {G K : Type*} [Group G] [Group K] (φ : G →* K) (g : ℕ → G) :
    ∀ w : List ℤ, φ (wordVal g w) = wordVal (fun i => φ (g i)) w
  | [] => map_one φ
  | l :: w => by
    rw [wordVal_cons, wordVal_cons, map_mul, map_wordVal φ g w]
    congr 1
    split_ifs
    · rfl
    · exact map_inv φ _

theorem wordVal_mem {G : Type*} [Group G] {g : ℕ → G} {K : Subgroup G} {j : ℕ}
    (hK : ∀ h < j, g h ∈ K) : ∀ w : List ℤ, plettersOK j w = true → wordVal g w ∈ K
  | [], _ => K.one_mem
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    rw [wordVal_cons]
    refine K.mul_mem ?_ (wordVal_mem hK w hw')
    split_ifs
    · exact hK _ (by omega)
    · exact K.inv_mem (hK _ (by omega))

theorem prep_pword_wordVal {n : ℕ} {S Sinv : Array (Array ℕ)} {g : ℕ → Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, PRep n S[h]! (g h)) (hSinv : ∀ h < j, PRep n Sinv[h]! (g h)⁻¹) :
    ∀ w : List ℤ, plettersOK j w = true → PRep n (pword n S Sinv w) (wordVal g w)
  | [], _ => by simpa [pword, wordVal_nil] using (prep_pid (n := n))
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have hlet := prep_pletter hS hSinv ⟨hl0, hlj⟩
    rw [pword, wordVal_cons]
    by_cases hpos : 0 < l
    · rw [ite_eq_left (decide_eq_true hpos)] at hlet
      rw [ite_eq_left hpos]
      exact prep_pcomp hlet (prep_pword_wordVal hS hSinv w hw')
    · rw [ite_eq_right (by simpa using hpos)] at hlet
      rw [ite_eq_right hpos]
      exact prep_pcomp hlet (prep_pword_wordVal hS hSinv w hw')

theorem prep_of_peq_right {n : ℕ} {t u : Array ℕ} {g : Perm (Fin n)} (h : peq n t u = true)
    (hu : PRep n u g) : PRep n t g := fun x => by
  have := allBelowN_spec h x.2
  rw [beq_iff_eq] at this
  rw [this, hu x]

def pbarPerm (i : ℕ) : Perm (Fin 800) := Monster.B.Co2.permOfArr 800 InvData.pgenPerms[i]!

abbrev ppar (k : ℕ) : ℕ := pparOf InvData.parRecs k

abbrev plab (k : ℕ) : ℕ := plabOf InvData.parRecs k

abbrev pE : Array (Array ℕ) := pEnum InvData.pgenPerms InvData.parRecs

def ePerm (k : ℕ) : Perm (Fin 800) := Monster.B.Co2.permOfArr 800 pE[k]!

abbrev Pbar : Subgroup (Perm (Fin 800)) :=
  Subgroup.closure (Set.range fun i : Fin 14 => pbarPerm i)

theorem pbarPerm_mem {i : ℕ} (hi : i < 14) : pbarPerm i ∈ Pbar :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

end CFSG.Sporadic.HNOddCore
