module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBlock
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.StandardType CFSG.Blueprint CFSG.ClassicalInvolution.Phan

private theorem qTwoNbrA_three_dvd_card_unitarySU {F : Type} [Field F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {t : ℕ} (ht : 4 ≤ t) :
    3 ∣ Nat.card ↥(unitarySU 2 1 F t) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKd : UnitaryFieldData 2 1 F := TableBU.unitaryFieldData_of_card hF le_rfl
  let i0 : Fin t := ⟨0, by omega⟩
  let i1 : Fin t := ⟨1, by omega⟩
  let i2 : Fin t := ⟨2, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have h1 : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  have hi02 : i0 ≠ i2 := by
    intro h
    have h1 : (0 : ℕ) = 2 := by simpa [i0, i2] using congrArg Fin.val h
    omega
  have hi12 : i1 ≠ i2 := by
    intro h
    have h1 : (1 : ℕ) = 2 := by simpa [i1, i2] using congrArg Fin.val h
    omega
  let π : Equiv.Perm (Fin t) := Equiv.swap i0 i1 * Equiv.swap i0 i2
  have hcyc : π.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hi01 hi02 hi12
  have hmem : (CFSG.RankThree.Classical.permGL π : GL (Fin t) F) ∈ unitarySU 2 1 F t := by
    rw [mem_unitarySU_iff hKd]
    exact ⟨by rw [CFSG.RankThree.Classical2.det_permGL, hcyc.sign]; simp,
      CFSG.RankThree.Classical2.permGL_unitary hKd π⟩
  let g : ↥(unitarySU 2 1 F t) := ⟨CFSG.RankThree.Classical.permGL π, hmem⟩
  have hπ3 : π ^ 3 = 1 := by
    rw [← hcyc.orderOf]
    exact pow_orderOf_eq_one π
  have hg3 : (CFSG.RankThree.Classical.permGL π : GL (Fin t) F) ^ 3 = 1 := by
    rw [← map_pow, hπ3, map_one]
  have hπi0 : π i0 = i2 := by
    show (Equiv.swap i0 i1 * Equiv.swap i0 i2) i0 = i2
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hi02.symm hi12.symm
  have hg1 : (CFSG.RankThree.Classical.permGL π : GL (Fin t) F) ≠ 1 := by
    intro hmat
    have hπinv : π⁻¹ i2 = i0 := by
      rw [← hπi0]
      simp
    have hentry : ((CFSG.RankThree.Classical.permGL π : GL (Fin t) F) :
        Matrix (Fin t) (Fin t) F) i2 i0 = 1 := by
      rw [CFSG.StandardType.TableBUE.permGL_apply, hπinv]
      simp
    have hentry2 : (1 : Matrix (Fin t) (Fin t) F) i2 i0 = 1 := by
      simpa [hmat] using hentry
    rw [Matrix.one_apply_ne (Ne.symm hi02)] at hentry2
    exact zero_ne_one hentry2
  have horderGL : orderOf (CFSG.RankThree.Classical.permGL π : GL (Fin t) F) = 3 :=
    orderOf_eq_prime hg3 hg1
  have horder : orderOf g = 3 := by
    rw [Subgroup.orderOf_mk (CFSG.RankThree.Classical.permGL π) hmem]
    exact horderGL
  have hdvd := orderOf_dvd_natCard g
  rwa [horder] at hdvd

theorem qTwoNbrA_block_model {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF : Nat.card F0 = (2 ^ 1) ^ 2) {m : ℕ} {L0 : Type} [Group L0] [Finite L0]
    (φ : ↥(unitarySU 2 1 F0 m) →* L0)
    (hφ_ker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 F0 m)) {S : Finset (Fin m)}
    (hS4 : 4 ≤ S.card) (hSm : S.card < m) :
    LieModel (↥((TableBUE.blockSU (K := F0) (n := 1) S).map φ) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := F0) (n := 1) S).map φ)) .PSU S.card 2 1 ∧
      3 ∣ Nat.card ↥((TableBUE.blockSU (K := F0) (n := 1) S).map φ) := by
  have hKd : UnitaryFieldData 2 1 F0 := TableBU.unitaryFieldData_of_card hF le_rfl
  have hcard_le : S.card ≤ m := by simpa using Finset.card_le_univ S
  have hm : 3 ≤ m := by omega
  have hmq : (m, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 : m = 3 := by simpa using congrArg Prod.fst h
    omega
  have hker : SURep.GGFrameKer φ := SURep.ggFrameKer_of_ker_le_center hF hm hmq hφ_ker
  have hlt : S.card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hSm
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨e⟩ := SURep.nonempty_map_blockSU_equiv hKd hker hi₀
  refine ⟨?_, ?_⟩
  · exact SUFacts.lieModel_quotient_center_of_mulEquiv_unitarySU hKd (by omega) (by
      intro h
      have h1 : S.card = 3 := by simpa using congrArg Prod.fst h
      omega) e
  · rw [Nat.card_congr e.toEquiv]
    exact qTwoNbrA_three_dvd_card_unitarySU hF hS4

end CFSG.StandardType.QTwo

end
