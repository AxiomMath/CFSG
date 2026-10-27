module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafNeighbourBlockData

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

section RootVia


theorem nbrpmmx_rootVia {X : Type} [Group X] (n f : ℕ) (ψ : UK n f →* X)
    (hψ : ψ.ker ≤ Subgroup.center (UK n f)) {t : StatedLieTag} {m : ℕ}
    (ι : (ggU t m f).K →* UK n f)
    (hιcent : ∀ y, ι y ∈ Subgroup.center (UK n f) → y ∈ Subgroup.center (ggU t m f).K)
    (K' R' : Subgroup (UK n f)) (K R : Subgroup X) (hK'map : K'.map ψ = K)
    (hR'map : R'.map ψ = R) (hιrange : ι.range = K')
    (β : Fin (ggU t m f).D.rank → ℤ) (u : (ggU t m f).K)
    (hroot : (((ggU t m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R') :
    GGRootVia (ggU t m f) K R β := by
  refine ⟨ψ.comp ι, ?_, ?_, u, ?_⟩
  · rw [MonoidHom.range_comp, hιrange]
    exact hK'map
  · intro y hy
    exact hιcent y (hψ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy)))
  · rw [ggRootSub]
    have h := congrArg (Subgroup.map ψ) hroot
    rw [hR'map] at h
    rw [← h]
    exact Subgroup.map_map _ ψ ι

end RootVia

variable {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n) (ψ : UK n f →* X) (p : ℕ)
  (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x)
include hn hH
variable (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
  (hB : SetD n f ψ J S J') (hF : FullD n f ψ D S) (hE : EpsD n f S J' ε)
  (heJ : IsPrimIdemIn (AdS f S) e_J)
include S J' ε e_J hB hF hE heJ
variable (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
  (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
include heD hKG₀ hKcomp hJK
variable (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .POmegaMinus n f p ψ R Rm)
  (hKne : K ≠ J)
include hR hR0 hKne

theorem nbrpmmx_K_setup :
    ∃ (S' : Set (GL (Ix n) (GaloisField 2 f))) (K' R' : Subgroup (UK n f)) (ε' e' : Mx n f),
      S' ⊆ S ∧ SetD n f ψ K S' K' ∧ EpsD n f S' K' ε' ∧ IsPrimIdemIn (AdS f S') e' ∧
      e' * ε' = e' ∧ SplitD n f ε' e' ∧ J' ≤ K' ∧ ε * ε' = ε ∧ R'.map ψ = R ∧ R' ≤ J' ∧
      (∃ a₁ a₂ : Ix n → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
        R'.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2)) = siegelGroup (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂) ∧
      ((e' = ε' ∧ blockDegree (AdS f S') e' < 2) ∨
        (e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4) ∨
        (e' ≠ ε' ∧ blockDegree (AdS f S') e' < 2)) := by
  obtain ⟨S', K', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie⟩ :=
    nbrpmmx_neighbourBlockData n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K hKG₀
      hKcomp hJK
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  obtain ⟨-, -, -, -, hJ'map⟩ := hB
  obtain ⟨R', hR'map, hgeo⟩ := nbrpom_L1 n f p hn ψ R Rm hR0
  have hinj : Function.Injective ψ := nbrpom_injective n f hn ψ hH.2.1
  have hR'J' : R' ≤ J' := by
    intro y hy
    have hyR : ψ y ∈ R := by rw [← hR'map]; exact Subgroup.mem_map_of_mem ψ hy
    have hyJ : ψ y ∈ J'.map ψ := by rw [hJ'map]; exact hR hyR
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyJ
    rwa [hinj hzy] at hz
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have hdeg := nbrpom_L4 n f S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit' hK'ε' hR'K'
    hgeo
  exact ⟨S', K', R', ε', e', hSe, ⟨hSU', hS', hodd', hK'comp, hK'map⟩, ⟨hε', hK'ε'⟩, he', he'ε',
    hsplit', hJK', htie, hR'map, hR'J', hgeo, hdeg⟩

end CFSG.StandardType.ClassicalPosition.NbrLeaf
