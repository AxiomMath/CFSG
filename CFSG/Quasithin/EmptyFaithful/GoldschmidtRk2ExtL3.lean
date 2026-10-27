module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtInner
public import CFSG.Quasithin.H13.NQCatParabolicSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtDef
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.Quasithin.Rk2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.Open
open scoped commutatorElement

section Three

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem inner_Q3 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    ∀ g ∈ Q3 K j, ∃ y ∈ perfectCore (Q3 K j), ∀ x ∈ perfectCore (Q3 K j),
      ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore (Q3 K j)) :=
  inner_of_blockHom
    (blkMon (Q3 K j) (1 - (j : ℕ)) 2 (q3_blk_le j) (q3_blockLeft j) (q3_blockRight j))
    (blk3 j) (fun _ => rfl) (blk3_surjective (exists_finset_card_four_of_pow hf hf2) j)
    (blk3_ker_isPGroup ⟨f, hf⟩ j)

omit [Finite K] [CharP K 2] in
theorem isSolvable_ker_proj3 : Group.IsSolvable ↥(proj 3 K).ker := by
  refine Group.isSolvable_of_comm (fun a b => Subtype.ext ?_)
  have h1 : (a : SpecialLinearGroup (Fin 3) K) ∈ Subgroup.center _ :=
    scalars_le_center 3 K ((ker_proj 3 K).le a.2)
  exact (Subgroup.mem_center_iff.1 h1 b).symm

theorem rank2PkgExt_proj3 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    Rank2Pkg.Ext (projectiveSL 3 K) ((unitriangular 3 K).map (proj 3 K))
      (fun j : Fin 2 => (Q3 K j).map (proj 3 K)) where
  charTwo_par j :=
    CFSG.QuasithinUnique.B113Lie.Lin.charTwo_projStabilizer (n := 3) (by omega)
      (by have := j.isLt; omega)
  le_perfectCore j := by
    rw [← map_perfectCore (proj 3 K) (Q3 K j)]
    exact Subgroup.map_mono
      (CFSG.Quasithin.H13.NQCat.SL3.unitriangular_le_perfectCore
        (exists_finset_card_four_of_pow hf hf2) j)
  inner j := inner_map (proj 3 K) (inner_Q3 hf hf2 j)
  solvable_le_normalizer X hUX hX := by
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : unitriangular 3 K ≤ X.comap (proj 3 K) := fun u hu => hUX ⟨u, hu, rfl⟩
    have h2 := SzN2.sl3_le_upperTriangular_of_solvable (exists_finset_card_four_of_pow hf hf2)
      h1 (isSolvable_comap_of_ker (proj 3 K) isSolvable_ker_proj3 hX)
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 K x
    exact (normalizer_projUnitriangular (K := K) 2).ge ⟨g, h2 hx, rfl⟩

end Three

end CFSG.Quasithin.Rk2
