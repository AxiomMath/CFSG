module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))
variable {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n) (ψ : UK n f →* X) (p : ℕ)
  (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x)
include hn hH
variable (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
  (hB : SetD n f ψ J S J') (hF : FullD n f ψ D S) (hE : EpsD n f S J' ε)
  (heJ : IsPrimIdemIn (AdS f S) e_J)
include S J' ε e_J hB hF hE heJ

theorem nbrpmmx_J_sl
    (hcase : e_J ≠ ε ∧ Fadj n f e_J ≠ e_J ∧ ε = e_J + Fadj n f e_J ∧
      blockDegree (AdS f S) e_J < 2) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .POmegaMinus n f p ψ R Rm ∧
      ∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
        βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
        rk f e_J = kJ + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hf : 1 ≤ f := h3.admissible.2.1
  obtain ⟨hSU, hS, hodd, hJ'comp, hJ'map⟩ := hB
  obtain ⟨k, ι, β₀, hrank, hlong, hιcent, hιrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hAl,
    hAl'⟩ :=
    exists_blockModel_dualPair_POmegaMinus_explicit n f hf S hSU hS hodd heJ hn hcase.2.1
      hcase.2.2.2 (by rw [← hcase.2.2.1]; exact hE.2)
  obtain ⟨β, hβroot, hβlong, u, huA, huA'⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaMinus n (minusCoeffs_irr 2 f) hn a₁ a₂ b₁ b₂
      hQ h₁ h₂ h₀
  have heqRoot : (((ggU .POmegaMinus n f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι) :=
    nbrpom_map_spinAction_injective (huA.trans hAl.symm)
  have heqRootNeg : (((ggU .POmegaMinus n f).D.rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι) :=
    nbrpom_map_spinAction_injective (huA'.trans hAl'.symm)
  refine ⟨ggRootSub (ggU .POmegaMinus n f).D ψ β u,
    ggRootSub (ggU .POmegaMinus n f).D ψ (-β) u, ?_, ?_, ?_, k, β₀,
    longRoot_mem_roots_univ (ggU .PSL (k + 1) f).D β₀ hlong, ?_, hrank.symm⟩
  · have hBle : (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaMinus n f).D ψ β u
        = (((ggU .POmegaMinus n f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaMinus n f).D ψ (-β) u
        = (((ggU .POmegaMinus n f).D.rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inl hβlong, u, rfl, rfl⟩
  · refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ J' := by rw [hιrange]
        _ = J := hJ'map
    · intro y hy
      apply hιcent
      apply h2
      exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
    · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSL (k + 1) f).K)).toMonoidHom
            ((ggU .PSL (k + 1) f).D.rootGroup β₀) = (ggU .PSL (k + 1) f).D.rootGroup β₀ := by
        ext y; simp
      unfold ggRootSub
      rw [hconj]
      exact (congrArg (Subgroup.map ψ) heqRoot).trans
        (Subgroup.map_map ((ggU .PSL (k + 1) f).D.rootGroup β₀) ψ ι)

end CFSG.StandardType.ClassicalPosition.NbrLeaf
