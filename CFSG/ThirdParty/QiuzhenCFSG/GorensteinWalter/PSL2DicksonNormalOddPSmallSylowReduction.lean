module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupCentralizedOfLargeDihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DicksonNormalOddPReduction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

namespace CFSG
end CFSG
open CFSG

/-!
# Reduction of the `PSL₂` normal odd-prime problem to Sylow order four

Dickson classification leaves a dihedral subgroup model.  The large-dihedral
central-involution theorem eliminates this alternative whenever the Sylow
`2`-subgroup has order at least eight, so only a Klein-four Sylow model can
remain.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- A normal odd-prime subgroup in the Dickson setup is centralized by the
distinguished involution unless both the containing subgroup is dihedral and
the ambient Sylow `2`-subgroup is Klein four. -/
public theorem psl2_normal_oddP_small_dihedral_or_centralized_of_contains_sylow
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
    (ht : IsInvolution t) :
    (∃ z : ℕ, Nat.card M = 2 * z ∧ Nonempty (M ≃* DihedralGroup z) ∧
      Nonempty (S ≃* DihedralGroup 2)) ∨
      P ≤ Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hcard_one : Nat.card F = 1 := by
      simpa [hf_zero, pow_zero] using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard_one
  have hoddF : IsOddPrimePower (Nat.card F) :=
    ⟨r, f, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hf_ne_zero, hFcard⟩
  rcases psl2_normal_oddP_dihedral_or_centralized_of_contains_sylow
      hFcard hrodd hpodd S M P hSM hPleM hPnormal hPp htS htcenter with
    ⟨z, hMcard, ⟨eM⟩⟩ | hcentral
  · rcases psl2_odd_hasDihedralSylowTwo_model F hoddF S with
      ⟨m, hm, ⟨eS⟩⟩
    by_cases hm_one : m = 1
    · left
      subst m
      simpa using ⟨z, hMcard, Nonempty.intro eM, Nonempty.intro eS⟩
    · right
      have hm_two : 2 ≤ m := by omega
      have hPodd : Odd (Nat.card P) := by
        rcases hPp.exists_card_eq with ⟨n, hn⟩
        rw [hn]
        exact hpodd.pow
      exact
        odd_subgroup_le_centralizer_of_large_dihedral_sylow_in_dihedral_subgroup
          (S : Subgroup (PSL2MatrixGroup F)) M P hm_two eS eM hMcard
          hSM hPleM hPodd htS htcenter ht
  · exact Or.inr hcentral

end CFSG.GorensteinWalter
