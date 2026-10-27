module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtInner
public import CFSG.Quasithin.H13.NQCatParabolicSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtDef

public section

namespace CFSG.Quasithin.Rk2

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin CFSG.Open
open CFSG.QuasithinUnique
open scoped commutatorElement

section Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem inner_Q2 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    ∀ g ∈ Q2 K j, ∃ y ∈ perfectCore (Q2 K j), ∀ x ∈ perfectCore (Q2 K j),
      ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore (Q2 K j)) :=
  inner_of_blockHom (blkQ j) (blkN j) (fun _ => rfl)
    (blkN_surjective (exists_finset_card_four_of_pow hf hf2) j) (blkN_ker_isPGroup ⟨f, hf⟩ j)

omit [CharP K 2] in
theorem isSolvable_ker_proj2 [CharP K 2] : Group.IsSolvable ↥(proj 2 K).ker := by
  have : Subsingleton ↥(proj 2 K).ker :=
    ⟨fun a b => Subtype.ext (proj_injective_charTwo
      ((MonoidHom.mem_ker.1 a.2).trans (MonoidHom.mem_ker.1 b.2).symm))⟩
  infer_instance

theorem rank2PkgExt_sp4 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    Rank2Pkg.Ext (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) where
  charTwo_par j := by
    fin_cases j
    · exact CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_flag_one (r := 2) (K := K)
        (by norm_num)
    · exact CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_flag_self (r := 2) (K := K)
        (by norm_num)
  le_perfectCore j := by
    rw [← map_perfectCore (proj 2 K) (Q2 K j)]
    exact Subgroup.map_mono (CFSG.Quasithin.H13.NQCat.Sp4.unipotent_le_perfectCore
      (exists_finset_card_four_of_pow hf hf2) j)
  inner j := inner_map (proj 2 K) (inner_Q2 hf hf2 j)
  solvable_le_normalizer X hUX hX := by
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : unipotent 2 K ≤ X.comap (proj 2 K) := fun u hu => hUX ⟨u, hu, rfl⟩
    have h2 := CFSG.Quasithin.H13.NQCat.Sp4.le_borelSubgroup_of_isSolvable
      (exists_finset_card_four_of_pow hf hf2) h1
      (isSolvable_comap_of_ker (proj 2 K) isSolvable_ker_proj2 hX)
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := K) x
    exact (normalizer_projUnipotent 2 (by norm_num)).ge ⟨g, h2 hx, rfl⟩

end Sp4

end CFSG.Quasithin.Rk2
