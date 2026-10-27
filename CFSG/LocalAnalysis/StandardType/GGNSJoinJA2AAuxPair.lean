module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

theorem nsJA2_of_pairBlocks_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs J : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : (ggSuPairBlock K 2 f n a b).map ψ ≤ J) (h2 : (ggSuPairBlock K 2 f n b c).map ψ ≤ J) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 := by
  obtain ⟨ε, hrefl, hblock⟩ := ggNSDiag_position h hd
  let r : MulAut ↥Bs := ((ε (Equiv.swap a b) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)
  let r' : MulAut ↥Bs := ((ε (Equiv.swap b c) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)
  have hkey : ∀ q : MulAut ↥Bs, q ∈ ggAutomizer ψ.range Bs → q * q = 1 →
      ggRankOneIn ψ.range Bs q ≤ J → q ∈ ggAutomizer J Bs := by
    intro q hq hq2 hqJ
    obtain ⟨m, hmR, hmN, hm⟩ := ggExists_weylElt_of_mem_ggAutomizer hq hq2
    exact mem_ggAutomizer_iff.mpr ⟨m, hqJ hmR, hmN, hm⟩
  have hmem : r ∈ ggAutomizer J Bs := by
    refine hkey r (ε (Equiv.swap a b)).2 ?_ ?_
    · have hpow := (hrefl a b hab).1
      rwa [pow_two] at hpow
    · rw [hblock a b hab]
      exact h1
  have hmem' : r' ∈ ggAutomizer J Bs := by
    refine hkey r' (ε (Equiv.swap b c)).2 ?_ ?_
    · have hpow := (hrefl b c hbc).1
      rwa [pow_two] at hpow
    · rw [hblock b c hbc]
      exact h2
  refine ⟨r, hmem, r', hmem', hrefl a b hab, hrefl b c hbc, ?_⟩
  have hmul : r * r' = ((ε (Equiv.swap a b * Equiv.swap b c) :
      ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
    rw [map_mul]
    rfl
  rw [hmul, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Equiv.swap_comm a b]
  exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac).orderOf

end CFSG.StandardType

end
