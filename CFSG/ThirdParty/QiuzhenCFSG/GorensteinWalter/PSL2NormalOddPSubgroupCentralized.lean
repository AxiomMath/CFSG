module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupCentralizedOfKleinFourSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DicksonNormalOddPSmallSylowReduction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

namespace CFSG
end CFSG
open CFSG

/-!
# Centralization of normal odd-prime subgroups in odd `PSL₂`

This closes the dihedral residue of Dickson classification.  Large Sylow
`2`-subgroups use the commutator/rotation argument, while the Klein-four case
uses ambient involution fusion and the controlled involution centralizer.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- Let `M ≤ PSL₂(F)` contain a Sylow `2`-subgroup, and suppose the ambient
centralizer of its distinguished central involution lies in `M`.  Every
normal odd-prime subgroup of `M` is centralized by that involution. -/
public theorem psl2_normal_oddP_centralized_of_contains_sylow
    {F : Type u} [Field F] [Finite F]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f) (hrodd : Odd r) (hpodd : Odd p)
    (S : Sylow 2 (PSL2MatrixGroup F))
    (M P : Subgroup (PSL2MatrixGroup F))
    (hSM : (S : Subgroup (PSL2MatrixGroup F)) ≤ M)
    (hPleM : P ≤ M)
    (hPnormal : (P.subgroupOf M).Normal)
    (hPp : IsPGroup p P)
    {t : PSL2MatrixGroup F}
    (htS : t ∈ (S : Subgroup (PSL2MatrixGroup F)))
    (htcenter : (⟨t, htS⟩ : S) ∈ Subgroup.center S)
    (ht : IsInvolution t)
    (hCM : Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) ≤ M) :
    P ≤ Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hcard_one : Nat.card F = 1 := by
      simpa [hf_zero, pow_zero] using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard_one
  have hoddF : IsOddPrimePower (Nat.card F) :=
    ⟨r, f, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hf_ne_zero, hFcard⟩
  rcases psl2_normal_oddP_small_dihedral_or_centralized_of_contains_sylow
      hFcard hrodd hpodd S M P hSM hPleM hPnormal hPp htS htcenter ht with
    ⟨z, hMcard, ⟨eM⟩, ⟨eS⟩⟩ | hcentral
  · exact
      odd_subgroup_le_centralizer_of_klein_four_sylow_in_dihedral_subgroup
        (S : Subgroup (PSL2MatrixGroup F)) M P eS eM hMcard hSM hPleM
        (by
          rcases hPp.exists_card_eq with ⟨n, hn⟩
          rw [hn]
          exact hpodd.pow)
        htS ht hCM
        (fun x y hx hy =>
          psl2_involutions_conjugate_of_odd_prime_power
            F hoddF x y hx hy)
  · exact hcentral

end CFSG.GorensteinWalter
