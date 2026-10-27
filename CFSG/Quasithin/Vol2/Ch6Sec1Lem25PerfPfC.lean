module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfPfB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.H13.LiePerf

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Field K] [CharP K 2] in
theorem exists_finset_four_of_card {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) :
    ∃ s : Finset K, s.card = 4 := by
  refine exists_finset_card_four ?_
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

section L3

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem benderLevi_Q3 {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) (j : Fin 2) :
    BenderLevi (Q3 K j) := by
  have hK4 := exists_finset_four_of_card hK hm
  have := sl2_isSimple hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := blk3_ker_isPGroup ⟨m, hK⟩ j
  exact Or.inr ⟨_, inferInstance, inferInstance, blk3 j, blk3_surjective hK4 j, by
    have := hk.isNilpotent
    infer_instance, m, isBenderOf_sl2 hK hm⟩

theorem injOn_proj_Q3 (j : Fin 2) :
    Set.InjOn (proj 3 K) (perfectCore (Q3 K j) : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  intro x hx y hy hxy
  have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have h1 := blk3_scalars j ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩ ((ker_proj 3 K).le hz)
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

theorem hasBenderLevi_l3 {S : Type} [Group S] [Finite S] {k : ℕ} (hk : 2 ≤ k)
    (hS : IsPSL 3 2 k S) : HasBenderLevi S := by
  intro U hU
  obtain ⟨K, _, _, _, φ, hcard, -, hres, -⟩ := even_rank_two_residual_linear hS hU
  refine ⟨_, hres, fun j => ?_⟩
  show BenderLevi (((Q3 K j).map (proj 3 K)).map φ.symm.toMonoidHom)
  exact benderLevi_map_equiv φ.symm
    (benderLevi_map (proj 3 K) (injOn_proj_Q3 j) (benderLevi_Q3 hcard hk j))

end L3

section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem benderLevi_Q2 {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) (j : Fin 2) :
    BenderLevi (Q2 K j) := by
  have hK4 := exists_finset_four_of_card hK hm
  have := sl2_isSimple hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := blkN_ker_isPGroup ⟨m, hK⟩ j
  exact Or.inr ⟨_, inferInstance, inferInstance, blkN j, blkN_surjective hK4 j, by
    have := hk.isNilpotent
    infer_instance, m, isBenderOf_sl2 hK hm⟩

theorem hasBenderLevi_sp4 {S : Type} [Group S] [Finite S] {k : ℕ} (hk : 2 ≤ k)
    (hS : IsPSp4 2 k S) : HasBenderLevi S := by
  intro U hU
  obtain ⟨K, _, _, _, φ, hcard, -, hres, -⟩ := even_rank_two_residual_symplectic hS hU
  refine ⟨_, hres, fun j => ?_⟩
  show BenderLevi (((Q2 K j).map (proj 2 K)).map φ.symm.toMonoidHom)
  exact benderLevi_map_equiv φ.symm (benderLevi_map (proj 2 K)
    (fun _ _ _ _ hxy => proj_injective_charTwo hxy) (benderLevi_Q2 hcard hk j))

end Sp4

end CFSG.Quasithin.H13.LiePerf
