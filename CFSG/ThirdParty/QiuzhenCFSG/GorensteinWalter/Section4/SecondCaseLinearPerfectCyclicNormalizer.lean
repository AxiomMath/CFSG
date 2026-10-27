module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearSemidirectComplement
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic normalizers in perfect groups

A nontrivial prime-order subgroup cannot have a cyclic normalizer in a
perfect finite group when all Sylow subgroups for that prime are cyclic.
Burnside transfer would otherwise give a nontrivial cyclic quotient.
-/

noncomputable section
namespace CFSG.GorensteinWalter
universe u

/-- In a perfect finite group with cyclic Sylow `p`-subgroups, the
normalizer of an order-`p` subgroup is not cyclic. -/
public theorem normalizer_not_cyclic_of_perfect_of_prime_card
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (hperf : Group.IsPerfect H)
    (X : Subgroup H) (hXcard : Nat.card X = p)
    (hSylowCyc : ∀ S : Sylow p H, IsCyclic S) :
    ¬ IsCyclic (Subgroup.normalizer (X : Set H)) := by
  intro hNcyc
  have hXp : IsPGroup p X :=
    IsPGroup.of_card (n := 1) (by simpa [hXcard])
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  have hScyc : IsCyclic S := hSylowCyc S
  have hNSleNX : Subgroup.normalizer ((S : Subgroup H) : Set H) ≤
      Subgroup.normalizer (X : Set H) :=
    normalizer_le_normalizer_of_le_cyclic hScyc hXS
  have hNSleCS : Subgroup.normalizer ((S : Subgroup H) : Set H) ≤
      Subgroup.centralizer ((S : Subgroup H) : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    let nN : Subgroup.normalizer (X : Set H) := ⟨n, hNSleNX hn⟩
    let sN : Subgroup.normalizer (X : Set H) :=
      ⟨s, hNSleNX (Subgroup.le_normalizer hs)⟩
    let : IsCyclic (Subgroup.normalizer (X : Set H)) := hNcyc
    have hcomm : nN * sN = sN * nN :=
      hNcyc.isMulCommutative.is_comm.comm nN sN
    exact (congrArg Subtype.val hcomm).symm
  let tr : H →* S := MonoidHom.transferSylow S hNSleCS
  have htr : ∀ x : H, tr x = 1 :=
    MonoidHom.eq_one_of_perfect_of_cyclic hperf hScyc tr
  have hker : tr.ker = ⊤ := by
    apply top_unique
    intro x _hx
    exact htr x
  have hcomp : tr.ker.IsComplement' (S : Subgroup H) :=
    MonoidHom.ker_transferSylow_isComplement' S hNSleCS
  have hSbot : (S : Subgroup H) = ⊥ := by
    have hd := hcomp.disjoint
    rw [disjoint_iff, hker, top_inf_eq] at hd
    exact hd
  have hXbot : X = ⊥ := le_bot_iff.mp (hXS.trans (le_of_eq hSbot))
  have hXone : Nat.card X = 1 := Subgroup.card_eq_one.mpr hXbot
  rw [hXcard] at hXone
  exact (Fact.out : p.Prime).ne_one hXone

end CFSG.GorensteinWalter
