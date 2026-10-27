module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSp4

public section

namespace CFSG.Quasithin.Rk2

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin
open CFSG.QuasithinUnique

section Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem charTwo_perfectCore_projQ2 (j : Fin 2) :
    CharTwo (perfectCore ((Q2 K j).map (proj 2 K))) := by
  refine charTwo_perfectCore ?_
  fin_cases j
  · exact CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_flag_one (r := 2) (K := K)
      (by norm_num)
  · exact CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_flag_self (r := 2) (K := K)
      (by norm_num)

theorem rank2Levi_projQ2 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    Rank2Levi ((Q2 K j).map (proj 2 K)) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN := perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine ⟨K, inferInstance, inferInstance, inferInstance, f, hf, hf2,
    (blkN j).comp eN.symm.toMonoidHom, (blkN_surjective hK4 j).comp eN.symm.surjective, ?_⟩
  intro z
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
  have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : eN.symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ eN.symm.injective).mp this

theorem rank2Pkg_sp4 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    Rank2Pkg (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) where
  res := symplectic_two_residualOvergroupsAt ⟨f, hf⟩
  norm j := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [normalizer_projUnipotent 2 (by norm_num)]
    exact Subgroup.map_mono (borelSubgroup_le_Q2 j)
  levi j := rank2Levi_projQ2 hf hf2 j
  charTwo j := charTwo_perfectCore_projQ2 j

end Sp4

end CFSG.Quasithin.Rk2
