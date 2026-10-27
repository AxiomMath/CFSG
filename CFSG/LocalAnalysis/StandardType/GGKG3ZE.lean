module

public import CFSG.LocalAnalysis.StandardType.GGKG3Act

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.StandardType.GGKG3.K3dCheck CFSG.StandardType.GGKG3.K3dWeyl

private theorem kg3_e6RootVec_mem (m : Fin 72) : (e6RootVec m : Fin 6 → ℤ) ∈ k3Roots := by
  change e6RootVec m ∈ (List.range 72).map e6Certificate.root
  exact List.mem_map.mpr ⟨m, List.mem_range.mpr m.2, rfl⟩

theorem k3_mem_k3Roots {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) : (γ : Fin 6 → ℤ) ∈ k3Roots := by
  rw [isRoot_iff_exists_e6RootVec] at hγ
  obtain ⟨m, hm⟩ := hγ
  rw [← hm]
  exact kg3_e6RootVec_mem m

theorem k3Pair_single (y : Fin 6 → ZMod 7) (i : Fin 6) :
    k3Pair y (Pi.single i 1 : Fin 6 → ℤ) = y i := by
  unfold k3Pair
  simp [Pi.single_apply]

theorem k3_ZE (c : WeylGroup .E6)
    (h : ∀ y ∈ k3Ex, k3Star c y = y) : c = 1 := by
  have hinv : c⁻¹ = 1 := by
    refine ext_single fun i => ?_
    rw [one_smul]
    have hr1 : IsRoot Tag.E6 (c⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
      IsRoot.smul (isRoot_single Tag.E6 i) c⁻¹
    have hr2 : IsRoot Tag.E6 (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 i
    refine k3_Ex_sep (k3_mem_k3Roots hr1) (k3_mem_k3Roots hr2) fun y hy => ?_
    have h1 := k3Star_apply c y i
    have h2 := k3Pair_single y i
    have h3 := congrFun (h y hy) i
    exact h1.symm.trans (h3.trans h2.symm)
  exact inv_eq_one.mp hinv

theorem k3_comm_of_stable
    (c : WeylGroup .E6) (h : ∀ y ∈ k3Ex, k3Star c y ∈ k3Ex) : c * w3 = w3 * c := by
  have hz : c⁻¹ * w3 * c * w3⁻¹ = 1 := by
    refine k3_ZE _ fun y hy => ?_
    have hu1 : (2 : ZMod 7) • k3Star c y ∈ k3Ex := k3Ex_smul 2 (h y hy)
    have h42 : (4 : ZMod 7) * 2 = 1 := by decide
    calc k3Star (c⁻¹ * w3 * c * w3⁻¹) y
        = k3Star c⁻¹ (k3Star w3 (k3Star c (k3Star w3⁻¹ y))) := by
          rw [k3Star_mul, k3Star_mul, k3Star_mul]
      _ = k3Star c⁻¹ (k3Star w3 (k3Star c ((2 : ZMod 7) • y))) := by rw [k3Star_w3_inv hy]
      _ = k3Star c⁻¹ (k3Star w3 ((2 : ZMod 7) • k3Star c y)) := by rw [k3Star_smul]
      _ = k3Star c⁻¹ ((4 : ZMod 7) • ((2 : ZMod 7) • k3Star c y)) := by rw [k3Star_w3 hu1]
      _ = k3Star c⁻¹ (k3Star c y) := by rw [smul_smul, h42, one_smul]
      _ = y := k3Star_inv_star c y
  calc c * w3 = c * (c⁻¹ * w3 * c * w3⁻¹) * w3 := by rw [hz, mul_one]
    _ = w3 * c := by group

end CFSG.StandardType.GGKG3
