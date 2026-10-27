module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.G2Core

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_perfectCore_of_le_commutator {M : Type} [Group M] {Q P : Subgroup M} (hQP : Q ≤ P)
    (h : Q ≤ ⁅Q, CFSG.Quasithin.perfectCore P⁆) : Q ≤ CFSG.Quasithin.perfectCore P := by
  have hQN : Q ≤ Subgroup.normalizer (CFSG.Quasithin.perfectCore P : Set M) :=
    hQP.trans (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P))
  exact h.trans ((Subgroup.commutator_le).2 fun q hq p hp =>
    G2.commutator_mem_of_normalizes (hQN hq) hp)

theorem posUnipotent_le_perfectCore
    (hK4 : 4 ≤ Nat.card K) (i : Fin Tag.G2.rank) :
    posUnipotent Tag.G2 K ≤ CFSG.Quasithin.perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
  have hQP : parabolicRadical Tag.G2 K {i} ≤ parabolicSubgroup Tag.G2 K {i} :=
    (parabolicRadical_le_posUnipotent {i}).trans (posUnipotent_le_parabolicSubgroup {i})
  obtain ⟨L, hLP, hL, hx, -, -⟩ := G2.leviL_data hK4 i
  have hLc := CFSG.Quasithin.le_perfectCore_of_perfect hLP hL
  rcases G2.fin_two_cases i with rfl | rfl
  · have hQ := le_perfectCore_of_le_commutator hQP (G2.generated_zero hK4)
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases G2.isRoot_pos_iff.1 hα with rfl | h
    · have h1 := hx c
      rw [G2.rootOne_gX_i0] at h1
      exact hLc h1
    · exact hQ (G2.mem_zero h c)
  · have hQ := le_perfectCore_of_le_commutator hQP (G2.generated_one hK4)
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases G2.isRoot_pos_iff.1 hα with h | rfl | h
    · exact hQ (G2.mem_one (Or.inl h) c)
    · have h1 := hx c
      rw [G2.rootOne_gX_i1] at h1
      exact hLc h1
    · exact hQ (G2.mem_one (Or.inr h) c)

end CFSG.Quasithin.Vol2.Ch10.SecB.G2Core
