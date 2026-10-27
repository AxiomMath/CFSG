module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normal odd-prime subgroups of alternating groups

For degree at least five, simplicity of the alternating group and the even
order of that group rule out nontrivial normal odd-prime subgroups.
-/

namespace CFSG.GorensteinWalter

universe u

/-- A normal odd-prime subgroup of a finite group isomorphic to `Aₙ`, for
`n ≥ 5`, is trivial. -/
public theorem normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} (hn : 5 ≤ n)
    (he : Nonempty (G ≃* alternatingGroup (Fin n)))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G) (hPnormal : P.Normal) (hPp : IsPGroup p P) :
    P = ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsimple_model : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hsimple : IsSimpleGroup G :=
    (MulEquiv.isSimpleGroup_congr he.some).mpr hsimple_model
  rcases (haveI := hPnormal; hsimple.eq_bot_or_eq_top_of_normal P) with hPbot | hPtop
  · exact hPbot
  · exfalso
    have hPcard_odd : Odd (Nat.card P) := by
      rcases hPp.exists_card_eq with ⟨m, hm⟩
      rw [hm]
      exact hpodd.pow
    have hPcard : Nat.card P = Nat.card (alternatingGroup (Fin n)) := by
      calc
        Nat.card P = Nat.card G := by
          rw [hPtop]
          exact Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv
        _ = Nat.card (alternatingGroup (Fin n)) :=
          Nat.card_congr he.some.toEquiv
    have hfour_dvd_factorial : 4 ∣ n.factorial :=
      Nat.dvd_factorial (by norm_num) (by omega)
    rcases hfour_dvd_factorial with ⟨k, hk⟩
    have htwice : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
      calc
        2 * Nat.card (alternatingGroup (Fin n)) =
            Nat.card (Equiv.Perm (Fin n)) :=
          two_mul_nat_card_alternatingGroup
        _ = n.factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rw [hk] at htwice
    have heven_model : 2 ∣ Nat.card (alternatingGroup (Fin n)) := by
      use k
      omega
    apply hPcard_odd.not_two_dvd_nat
    rwa [hPcard]

end CFSG.GorensteinWalter
