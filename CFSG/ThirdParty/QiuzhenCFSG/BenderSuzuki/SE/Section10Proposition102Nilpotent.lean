module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Algebra
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2: fixed-point-free nilpotence

This module exposes the generic Thompson/Huppert endpoint used after the
commutator subgroup has been identified.  It is deliberately independent of
the Proposition 10.2 package itself.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

/-- A centralizer-free normal complement forces the complement's kernel to
have trivial centralizer on the operator subgroup. -/
public theorem proposition102_centralizer_bot_of_normal_complement
    {X : Type*} [Group X]
    {D N C H P : Subgroup X}
    (hHleN : H ≤ N)
    (hCentNP : subgroupCentralizerIn N P = C)
    (hcompD : IsNormalComplementIn D C (H ⊔ P)) :
    subgroupCentralizerIn H P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxC : x ∈ C := by
    have hxNP : x ∈ subgroupCentralizerIn N P := ⟨hHleN hx.1, hx.2⟩
    rw [hCentNP] at hxNP
    exact hxNP
  exact Subgroup.disjoint_def.mp hcompD.disjoint_D
    (Subgroup.mem_sup_left hx.1) hxC

/-- A prime-order subgroup acting fixed-point-freely by conjugation on a
subgroup forces that subgroup to be nilpotent. -/
public theorem proposition102_nilpotent_of_prime_fixedPointFree
    {G : Type u} [Group G] [Finite G]
    (H P : Subgroup G)
    (hPnormH : P ≤ Subgroup.normalizer (H : Set G))
    (hPprime : Nat.Prime (Nat.card P))
    (hfix : subgroupCentralizerIn H P = ⊥) :
    Group.IsNilpotent H := by
  have hPne : P ≠ ⊥ := by
    intro hPbot
    exact hPprime.ne_one (by simp [hPbot])
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hxneG : (x : G) ≠ 1 := by
    intro h
    apply hxne
    exact Subtype.ext h
  have hfixed : ∀ y : G, y ∈ P → y ≠ 1 →
      Subgroup.centralizer ({y} : Set G) ⊓ H = ⊥ := by
    intro y hyP hyne
    have hyneP : (⟨y, hyP⟩ : P) ≠ 1 := by
      intro h
      exact hyne (congrArg Subtype.val h)
    have hcent := theorem_3_7_elementCentralizer_eq_bot
      H P hPprime hfix ⟨y, hyP⟩ hyneP
    simpa [elementCentralizerIn, inf_comm] using hcent
  exact
    External.huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
      H P hPnormH ⟨x, x.property, hxneG⟩ hfixed

/-- Promote a Hall subgroup of an intermediate subgroup to a Hall subgroup of
the ambient group when every prime in its support has an ambient Sylow
subgroup contained in it. -/
public theorem proposition102_hall_of_subgroupOf_and_ambient_sylows
    {G : Type*} [Group G] [Finite G]
    {D H : Subgroup G} (hHD : H ≤ D) {pi : Set Nat.Primes}
    (hHallD : IsHallSubgroup pi (H.subgroupOf D))
    (hSylow : ∀ q : Nat.Primes, q ∈ pi →
      ∃ Q : Sylow q.val G, (Q : Subgroup G) ≤ H) :
    IsHallSubgroup pi H := by
  refine isHallSubgroup_of (G := G) pi H ?_ ?_
  · intro q hqH
    apply hHallD.p_in_pi_of_p_dvd_card q
    simpa [natCard_subgroupOf_eq H D hHD] using hqH
  · intro q hqpi hqindex
    letI : Fact (Nat.Prime q.val) := ⟨q.property⟩
    obtain ⟨Q, hQH⟩ := hSylow q hqpi
    have hindex_dvd : H.index ∣ (Q : Subgroup G).index :=
      Subgroup.index_dvd_of_le hQH
    exact Q.not_dvd_index (hqindex.trans hindex_dvd)

end CFSG.BenderSuzuki
