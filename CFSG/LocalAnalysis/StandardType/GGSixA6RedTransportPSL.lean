module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedLiftComponent
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedPSLRankOne
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSL
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockLiftAux
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoDefs
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

open scoped commutatorElement

private theorem ggA6_transport_PSL_core_sl (m f : ℕ) (X : Type) [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (p : ℕ) (G₀ D J : Subgroup X)
    (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hDcard : Nat.card D = p ^ 2)
    (hEA : ∀ d ∈ D, ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (d, A) ∈ LinFusion.ggInducedPairs ψ)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    ∃ (P J' : Subgroup (GL (Fin (m + 1)) (GaloisField 2 f))), Odd (Nat.card P) ∧
      IsComponentOf J' (Matrix.SpecialLinearGroup.toGL.range ⊓
        Subgroup.centralizer (P : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
  let U := Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)
  let M : Subgroup U := (G₀ ⊓ Subgroup.centralizer (D : Set X)).comap ψ
  let C : Subgroup U := LayerFacts.ggCentSL ψ D
  have hMmap : M.map ψ = G₀ ⊓ Subgroup.centralizer (D : Set X) := by
    dsimp only [M]
    rw [Subgroup.map_comap_eq, hrange, inf_eq_right.mpr inf_le_left]
  have hJ0 : IsComponentOf J (M.map ψ) := hMmap ▸ hJ
  have hab : ⁅M, M⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine LayerFacts.mem_ggCentSL.mpr fun A hA => ?_
    have hxc : ψ x ∈ Subgroup.centralizer (D : Set X) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2
    have hyc : ψ y ∈ Subgroup.centralizer (D : Set X) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)).2
    obtain ⟨z, hz, hzx⟩ :=
      LayerFacts.conjSL_eq_mul_of_mem_centralizer (ψ := ψ) (E := D) hker hxc hA
    obtain ⟨w, hw, hwy⟩ :=
      LayerFacts.conjSL_eq_mul_of_mem_centralizer (ψ := ψ) (E := D) hker hyc hA
    rw [map_commutatorElement, hzx, hwy, LayerFacts.ggCommutatorElement_center_mul hz hw]
  have hmapC : C.map ψ ≤ G₀ ⊓ Subgroup.centralizer (D : Set X) := by
    have h := LayerFacts.map_ggCentSL_le (ψ := ψ) (E := D) hEA
    rwa [hrange] at h
  have hCM : C ≤ M := by
    intro c hc
    exact Subgroup.mem_comap.mpr (hmapC (Subgroup.mem_map_of_mem ψ hc))
  have hkerM : ψ.ker ≤ M := by
    intro u hu
    exact Subgroup.mem_comap.mpr
      (MonoidHom.mem_ker.mp hu ▸ Subgroup.one_mem (G₀ ⊓ Subgroup.centralizer (D : Set X)))
  obtain ⟨K, hKcomp, hKiso⟩ :=
    ggA6_lift_component (U := U) ψ hker M C hkerM hCM hab hJ0
  have hDp : IsPGroup p D := IsPGroup.of_card (n := 2) (by simpa using hDcard)
  have hPodd : Odd (Nat.card (LinTorus.inducedMatrices ψ D)) := by
    have hne := LayerFacts.natCast_card_inducedMatrices_ne_zero (ψ := ψ) (E := D) hker hp hp2 hDp
    refine Nat.not_even_iff_odd.mp fun he => hne ?_
    exact (CharP.cast_eq_zero_iff (GaloisField 2 f) 2 _).mpr (even_iff_two_dvd.mp he)
  have hCdef : C = (Subgroup.centralizer
      ((LinTorus.inducedMatrices ψ D) : Set (GL (Fin (m + 1)) (GaloisField 2 f)))).comap
      Matrix.SpecialLinearGroup.toGL := rfl
  have hKmap : C.map Matrix.SpecialLinearGroup.toGL =
      Matrix.SpecialLinearGroup.toGL.range ⊓
        Subgroup.centralizer
          ((LinTorus.inducedMatrices ψ D) : Set (GL (Fin (m + 1)) (GaloisField 2 f))) := by
    rw [hCdef, Subgroup.map_comap_eq]
  have hJcomp : IsComponentOf (K.map Matrix.SpecialLinearGroup.toGL)
      (Matrix.SpecialLinearGroup.toGL.range ⊓
        Subgroup.centralizer
          ((LinTorus.inducedMatrices ψ D) : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Matrix.SpecialLinearGroup.toGL)
      Matrix.SpecialLinearGroup.toGL_injective).mpr hKcomp
    rwa [hKmap] at h
  obtain ⟨eiso⟩ := hKiso
  refine ⟨LinTorus.inducedMatrices ψ D, K.map Matrix.SpecialLinearGroup.toGL,
    hPodd, hJcomp, ⟨?_⟩⟩
  exact eiso.trans (QuotientGroup.congr (Subgroup.center ↥K)
    (Subgroup.center ↥(K.map Matrix.SpecialLinearGroup.toGL))
    (Subgroup.equivMapOfInjective K Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective)
    (Subgroup.map_center_eq _))

section Genuine

private theorem ggA6_transport_PSL_core
    (m f : ℕ) (X : Type) [Group X]
    (ψ : (ggU .PSL (m + 1) f).K →* X) (p : ℕ) (G₀ D J : Subgroup X)
    (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hDcard : Nat.card D = p ^ 2)
    (hEA : ∀ d ∈ D, ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (d, A) ∈ LinFusion.ggInducedPairs ψ)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    ∃ (P J' : Subgroup (GL (Fin (m + 1)) (GaloisField 2 f))), Odd (Nat.card P) ∧
      IsComponentOf J' (Matrix.SpecialLinearGroup.toGL.range ⊓
        Subgroup.centralizer (P : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
  exact ggA6_transport_PSL_core_sl m f X ψ p G₀ D J hrange hker hp hp2 hDcard hEA hJ

theorem ggA6_transport_PSL
    (m f : ℕ) (X : Type) [Group X] [Finite X]
    (ψ : (ggU .PSL (m + 1) f).K →* X) (p : ℕ) (G₀ D J : Subgroup X) :
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .PSL (m + 1) 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) →
    (∀ d ∈ D, GGPsiInnerDiag (ggU .PSL (m + 1) f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    ∃ (P J' : Subgroup (GL (Fin (m + 1)) (GaloisField 2 f))), Odd (Nat.card P) ∧
      IsComponentOf J' (Matrix.SpecialLinearGroup.toGL.range ⊓
        Subgroup.centralizer (P : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
  intro hrange hker hLie hp hp2 hDN hdiag hab hD hJ
  have hadm := LieModel.admissible hLie
  rcases lt_or_ge m 2 with hm | hm
  · have h01 : m = 0 ∨ m = 1 := by omega
    rcases h01 with rfl | rfl
    · exfalso
      have h2 : 2 ≤ (0 + 1) := hadm.2.2.1
      omega
    · have hEA : ∀ d ∈ D, ∃ A : GL (Fin (1 + 1)) (GaloisField 2 f),
          (d, A) ∈ LinFusion.ggInducedPairs ψ := by
        intro d hd
        obtain ⟨A, hA⟩ := ggA6_psl_rank_one ψ hker (y := d⁻¹) (by
          show GGPsiInnerDiag (ggU .PSL 2 f).D ψ ((d⁻¹)⁻¹)
          rw [inv_inv]
          exact hdiag d hd)
        exact ⟨A⁻¹, by simpa using (LinFusion.ggInducedPairs ψ).inv_mem hA⟩
      exact ggA6_transport_PSL_core 1 f X ψ p G₀ D J hrange hker hp hp2 hD hEA hJ
  · exact ggA6_transport_PSL_core m f X ψ p G₀ D J hrange hker hp hp2 hD (by
      intro d hd
      obtain ⟨A, hA⟩ := LinFusion.exists_mem_ggInducedPairs hm ψ hker (y := d⁻¹) (by
        show GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ ((d⁻¹)⁻¹)
        rw [inv_inv]
        exact hdiag d hd)
      exact ⟨A⁻¹, by simpa using (LinFusion.ggInducedPairs ψ).inv_mem hA⟩) hJ

end Genuine

end CFSG.StandardType.A6Red
