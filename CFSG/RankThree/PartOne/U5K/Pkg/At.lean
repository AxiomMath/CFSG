module

public import CFSG.RankThree.PartOne.U5K.Pkg.Root
public import CFSG.RankThree.PartOne.U5K.Pkg.Order
public import CFSG.RankThree.PartOne.S12.PhanAssembly
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.KF.U4Multiplier
public import CFSG.RankThree.PartOne.CTP.ExtPhan
public import CFSG.RankThree.PartOne.U5K.Pkg.Mod

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem _root_.CFSG.RankThree.PartOne.U5K.kfU5At_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : KFU5At := by
  intro G _ _ p A c L E f h15 hF hout hf hpf ⟨e⟩ t ht
  have h := h15.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  obtain ⟨h24, hrow, -⟩ := rows h15 hF hout
  obtain ⟨fL, hfL1, hpfL, hmodel⟩ := hrow
  have hcardE : Nat.card E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  obtain ⟨W⟩ := nonempty_weylIso h15 hF hout
  have hL24 : Nat.card (torusImage E L) = (4 : ℕ).factorial := by
    rw [h24]
    rfl
  obtain ⟨hKat, hKpair⟩ := kf126U4_of_multipliers hGA G p A c L E fL h hF hfL1 hpfL hmodel hcardE
  have hKall : ∀ t ∈ reflectionSet p E, KFAt p E fL t := by
    intro t ht
    obtain ⟨w, hw, hwt, -⟩ := W.exists_conj_into_L hL24 ht ht
      (W.exists_common_fixed (by norm_num) ht ht)
    exact KFAt.of_conj hw (hKat _ (conj_mem_reflectionSet hp ht hw) hwt)
  have hPall : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPair p E fL s t := by
    intro s hs t ht hst
    obtain ⟨w, hw, hws, hwt⟩ := W.exists_conj_into_L hL24 hs ht
      (W.exists_common_fixed (by norm_num) hs ht)
    have hne' : conjAut E w hw * s * (conjAut E w hw)⁻¹ ≠
        conjAut E w hw * t * (conjAut E w hw)⁻¹ := fun h' =>
      hst (mul_left_cancel (mul_right_cancel h'))
    exact KFPair.of_conj hw (hKpair _ (conj_mem_reflectionSet hp hs hw) hws _
      (conj_mem_reflectionSet hp ht hw) hwt hne')
  have hfL2 : 2 ≤ fL := by
    by_contra hlt
    have hfL : fL = 1 := by omega
    subst hfL
    have := Nat.le_of_dvd (by norm_num) hpfL
    omega
  obtain ⟨ψ, k, hk, hstab⟩ := exists_psi_k h15 hF hout
  let M := mkModel h15 hF hout ψ k hk hstab
  have hP := PhanAssembly.phan_conclusion W CTP.extPhan (by norm_num) hp hp5 h.E_elem hfL2 hpfL
    (rootLattice_le E) (rootLattice_invariant hp E) M.rootLattice_irreducible
    M.rootLattice_faithful hKall hPall
  obtain ⟨e'⟩ := projSU_of_statedClassicalModel hP
  have hfeq : fL = f := eq_of_mulEquiv_projSU_five hfL1 hf (e'.symm.trans e)
  subst hfeq
  exact hKall t ht

end CFSG.RankThree.PartOne.U5K.Pkg
