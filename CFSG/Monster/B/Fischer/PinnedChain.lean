
module

public import CFSG.Monster.B.Fischer.PinnedChainBase

public import CFSG.Monster.B.Fischer.PinnedChainData
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.SchreierChainOrderGenerators
public meta import CFSG.Monster.B.Fischer.PinnedChainData
public meta import CFSG.Monster.B.Co2.PermArr
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import Certificates.Certificate3039
public import Certificates.Certificate3039Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22Chain_check :
    (∀ j < 19, isInvA 3510 fi22StrongArrs[j]! fi22StrongInvs[j]! = true) ∧
    (∀ k < 2, isInvA 3510 (fi22ChainGen k) (invCand 3510 (fi22ChainGen k)) = true) ∧
    (∀ k < 2, eqA 3510 fi22StrongArrs[k]! (fi22ChainGen k) = true) ∧
    (∀ j < 19, 2 ≤ j → lettersOK j (fi22Derivation j) = true ∧
      eqA 3510 fi22StrongArrs[j]!
        (wordA 3510 fi22StrongArrs fi22StrongInvs (fi22Derivation j)) = true) ∧
    fi22ChainDerivations.length = 17 :=
  Certificates.certificate3039

theorem rep_fi22Strong {j : ℕ} (hj : j < 19) :
    Rep 3510 fi22StrongArrs[j]! (fi22StrongPerm j) := by
  have h := (rep_permOfArr (fi22Chain_check.1 j hj)).1
  rw [fi22StrongArrs_get hj] at h ⊢
  exact h

theorem rep_fi22StrongInv {j : ℕ} (hj : j < 19) :
    Rep 3510 fi22StrongInvs[j]! (fi22StrongPerm j)⁻¹ :=
  rep_inv_of_isInvA (rep_fi22Strong hj) (fi22Chain_check.1 j hj)

theorem rep_fi22Gen {k : ℕ} (hk : k < 2) : Rep 3510 (fi22ChainGen k)
    (fi22GenPerm k) :=
  (rep_permOfArr (fi22Chain_check.2.1 k hk)).1

theorem fi22Chain_original_eq (k : Fin fi22Chain.originalCount) :
    fi22Chain.strong.get (Fin.castLE fi22Chain.originalCount_le k) = fi22Chain.original.get k := by
  have hk : (k : ℕ) < 2 := k.2
  rw [fi22Chain_original_get, fi22Chain_strong_get, Fin.val_castLE]
  exact eq_of_eqA (rep_fi22Strong (by omega)) (rep_fi22Gen hk) (fi22Chain_check.2.2.1 k hk)

theorem fi22StrongPerm_word {j : ℕ} (hj : j < 19) (hj2 : 2 ≤ j) :
    fi22StrongPerm j = Quiver.SchreierGraph.evalWord (fun h : Fin j => fi22StrongPerm h)
      (toLetters j (fi22Derivation j)) := by
  obtain ⟨hl, he⟩ := fi22Chain_check.2.2.2.1 j hj hj2
  refine eq_of_eqA (rep_fi22Strong hj) ?_ he
  exact rep_wordA (gs := fi22StrongPerm) (fun h hh => rep_fi22Strong (by omega))
    (fun h hh => rep_fi22StrongInv (by omega)) _ hl

theorem fi22Chain_derivation_eq (j : Fin fi22Chain.strongCount)
    (hj : fi22Chain.originalCount ≤ j.val) :
    fi22Chain.strong.get j = fi22Chain.derivationValue j hj := by
  have hj19 : (j : ℕ) < 19 := j.2
  have hj2 : 2 ≤ (j : ℕ) := hj
  rw [RawSchreierDatum.derivationValue, schreierWordValue]
  simp only [fi22Chain_strong_get]
  exact fi22StrongPerm_word hj19 hj2

theorem fi22Chain_strong_mem (j : Fin fi22Chain.strongCount) :
    fi22Chain.strong.get j ∈ fi22P := by
  have all : ∀ a : ℕ, ∀ j : Fin fi22Chain.strongCount, j.val = a →
      fi22Chain.strong.get j ∈ fi22P := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < fi22Chain.originalCount
      · let l : Fin fi22Chain.originalCount := ⟨j.val, hj⟩
        have hcast : Fin.castLE fi22Chain.originalCount_le l = j := Fin.ext rfl
        rw [← hcast, fi22Chain_original_eq l]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList fi22Chain.original l)
      · rw [fi22Chain_derivation_eq j (Nat.le_of_not_gt hj)]
        apply schreierWordValue_mem_subgroup fi22Chain.strong.get (Nat.le_of_lt j.isLt)
          (fi22Chain.derivation j (Nat.le_of_not_gt hj)) fi22P
        intro l
        exact ih l.val (by omega) ⟨l.val, l.isLt.trans j.isLt⟩ rfl
  exact all j.val j rfl

end CFSG.Monster.B.Fischer
