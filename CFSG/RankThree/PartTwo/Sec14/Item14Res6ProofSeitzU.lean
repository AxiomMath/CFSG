module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofCentGen
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.UnitaryToralNine
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open Sec15.Proof1513Res3 in
theorem ks1517SeitzU :
    Sec15.KS1517SeitzU := by
  intro X _ _ p e _ he hiso hq2 hperf _ D hD hD9
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨ψ⟩ : Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p e) := by
    rcases hiso with ⟨h1, -⟩ | ⟨-, hψ⟩
    · omega
    · exact hψ
  set K := GaloisField p (2 * e) with hK
  have hU : UnitaryFieldData p e K := Census.unitaryFieldData_galoisField p e he
  have hq3 : 3 ∣ p ^ e + 1 := by omega
  have hnt : Nontrivial X := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have := Subgroup.card_le_card_group D
    omega
  have hpe2 : p ^ e ≠ 2 := by
    intro h2
    obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp h2
    have : Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 2 1) :=
      Sec13.isSolvable_projSU_two
    have hsolv : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
    exact Group.IsPerfect.not_isSolvable X hsolv
  set Φ : StatedProj (StatedSU 3 (p ^ e) K) ≃* CFSG.Assembly.RankThreeEven.projSU 3 p e :=
    (Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 p e)) with hΦ
  set θ : X ≃* StatedProj (StatedSU 3 (p ^ e) K) := ψ.trans Φ.symm with hθ
  set E := D.map θ.toMonoidHom with hE
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change θ x * θ y = θ y * θ x
    rw [← map_mul, ← map_mul]
    exact congrArg θ (congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hexp : ∀ a ∈ E, a ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change θ x ^ 3 = 1
    rw [← map_pow, hD.2 x hx, map_one]
  have hcard : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective θ.injective, hD9]
    norm_num
  have hgen : Subgroup.closure {k : StatedProj (StatedSU 3 (p ^ e) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
    by_cases hab : ∀ x y : unitarySU p e K 3, LieType.SeitzGeneration.piSU p e K x ∈ E →
        LieType.SeitzGeneration.piSU p e K y ∈ E → x * y = y * x
    · exact LieType.SeitzGeneration.unitaryToralNine p e K hU hq3 hpe2 E hcomm hexp hcard hab
    · push Not at hab
      exact LieType.SeitzGeneration.closure_centralizers_statedProj_su_three_nonab
        LieType.SeitzGeneration.unitaryHeisCore hU hq3 hpe2 E hcomm hexp hab
  rw [← map_closure_centralizers θ D] at hgen
  rw [eq_top_iff]
  intro k _
  have hk : θ.toMonoidHom k ∈
      (Subgroup.closure {k : X | ∃ x ∈ D, x ≠ 1 ∧ k * x = x * k}).map θ.toMonoidHom := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_map_iff_mem θ.injective).mp hk

end CFSG.RankThree.PartTwo.Sec14
