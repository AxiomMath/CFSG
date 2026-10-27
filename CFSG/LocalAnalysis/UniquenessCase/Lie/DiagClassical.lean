module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairOmegaMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin CFSG.Quasithin.B69K CFSG.QuasithinUnique CFSG.ABGLocalTools

theorem uc22pdiag_invPairs_of_parabolicPair {M : Type} [Group M] [Finite M]
    (h : ∃ U : Subgroup M, IsSylowTwoOf U ⊤ ∧ ParabolicPair U) (V : Sylow 2 M) :
    uc22pdiag_InvPair M V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU, hP⟩ := h
  have hV : IsSylowTwoOf (V : Subgroup M) ⊤ := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow V
  obtain ⟨k, -, hk⟩ := (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU).exists_mem_conj
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hV)
  have hconj : U.map (MulAut.conj k).toMonoidHom = (V : Subgroup M) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have hP' := ParabolicPair.map_mulEquiv (MulAut.conj k) hP
  rw [hconj] at hP'
  obtain ⟨P₀, P₁, -, -, h0, h1, hsup, hinv⟩ := hP'
  exact ⟨P₀, P₁, h0, h1, hsup, hinv⟩

section Families

open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {M : Type} [Group M] [Finite M] [IsSimpleGroup M]

theorem uc22pdiag_all_psl4 {n : ℕ} (h : LieModel M .PSL 4 2 n) : uc22pdiag_All M :=
  uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_parabolicPair
    (pairData_of_statedPSL (le_refl 4) (h.statedClassicalModel (by decide))))

theorem uc22pdiag_all_psu4 {n : ℕ} (h : LieModel M .PSU 4 2 n) : uc22pdiag_All M :=
  uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_parabolicPair
    (pairData_of_statedPSU (le_refl 4) (h.statedClassicalModel (by decide))))

theorem uc22pdiag_all_psu5 {n : ℕ} (h : LieModel M .PSU 5 2 n) : uc22pdiag_All M :=
  uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_parabolicPair
    (pairData_of_statedPSU (by norm_num) (h.statedClassicalModel (by decide))))

theorem uc22pdiag_all_psp6 {n : ℕ} (h : LieModel M .PSp 3 2 n) : uc22pdiag_All M :=
  uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_parabolicPair
    (pairData_of_statedPSp (le_refl 3) (h.statedClassicalModel (by decide))))

theorem uc22pdiag_all_pomegaMinus8 {n : ℕ} (h : LieModel M .POmegaMinus 4 2 n) : uc22pdiag_All M :=
  uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_parabolicPair
    (pairData_of_statedPOmegaMinus (le_refl 4) (h.statedClassicalModel (by decide))))

end Families

end CFSG.LocalAnalysis.UniquenessCase.UC22
