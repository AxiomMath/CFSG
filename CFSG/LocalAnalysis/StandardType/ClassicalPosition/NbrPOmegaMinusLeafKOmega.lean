module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafGen
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafKSetup
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafModel
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafPlusFour
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafNeOne

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
variable (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
  (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
include heD hKG₀ hKcomp hJK
variable (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .POmegaMinus n f p ψ R Rm)
  (hKne : K ≠ J)
include hR hR0 hKne

theorem nbrpmmx_K_omega (hcase : e_J = ε ∧ blockDegree (AdS f S) e_J < 2)
    (t' : StatedLieTag) (mJ : ℕ) (βJ : Fin (ggU t' mJ f).D.rank → ℤ)
    (ht' : t' = .POmegaPlus ∨ t' = .POmegaMinus) (hmJ : 3 ≤ mJ) (hrankJ : rk f e_J = 2 * mJ) :
    ∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
      (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ mJ < mK ∧ βK ∈ (ggU t'' mK f).D.roots ∧
      GGLongRoot (ggU t'' mK f).D βK ∧ GGRootVia (ggU t'' mK f) K R βK := by
  have hψ : ψ.ker ≤ Subgroup.center (UK n f) := hH.2.1
  have hf : 1 ≤ f := (hH.2.2.1).admissible.2.1
  obtain ⟨S', K', R', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie, hR'map, hR'J',
    hgeo, hdeg⟩ := nbrpmmx_K_setup n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K
      hKG₀ hKcomp hJK R Rm hR hR0 hKne
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  obtain ⟨hSU, hS, hodd, hJ'comp, hJ'map⟩ := hB
  obtain ⟨hεE, hJ'ε⟩ := hE
  have hsplit'' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj n f e' ≠ e' ∧ ε' = e' + Fadj n f e') := hsplit'
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have he'A : e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hcomm : ∀ a b : Mx n f, a ∈ AdS f S → b ∈ AdS f S → a * b = b * a :=
    fun a b ha hb => (adjoin_comm hS a ha b hb).eq
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hadjJ : Fadj n f e_J = e_J := by rw [hcase.1]; exact hεE.2.2.2.1
  have htieJ' : e_J * ε' = e_J := by rw [hcase.1]; exact htie

  have hedge : ∀ (ι : (ggU .PSL 2 f).K →* UK n f) (β : Fin (ggU .PSL 2 f).D.rank → ℤ)
      (u : (ggU .PSL 2 f).K), β ∈ (ggU .PSL 2 f).D.roots → ι.range = K' →
      (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' →
      (∀ y, ι y ∈ Subgroup.center (UK n f) → y ∈ Subgroup.center (ggU .PSL 2 f).K) → False := by
    intro ι β u hβ hrange hroot hcent
    have hle : ι.range ≤ J' :=
      nbrpmmx_plus_four n f hf ι hcent β hβ u J' hperf (hrange ▸ hJK') (hroot.le.trans hR'J')
    have hK'J' : K' ≤ J' := hrange ▸ hle
    apply hKne
    apply le_antisymm _ hJK
    rw [← hK'map, ← hJ'map]
    exact Subgroup.map_mono hK'J'
  rcases hdeg with ⟨heq, hd⟩ | ⟨heq, hd1, hd2⟩ | ⟨hne, hd⟩
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpmmx_K_model (X := X) n f hn hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inl ⟨heq, hd⟩)
    have hvia := nbrpmmx_rootVia n f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    have hba : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans htieJ
    have hne' : e_J ≠ e' :=
      nbrpmmx_ne_one n f ψ S J' ε e_J hS heJ hcase J K hKne hJ'map S' K' ε' e' hK'map hSe hε'
        hK'ε' hJ'ε hJK' ⟨heq, hd⟩
    have hlt := rank_lt_of_mul_eq heJ.2.1 htieJ hba hne'
    rcases (htype.1 ⟨heq, hd⟩) with ⟨ht'', h3, hrk⟩ | ⟨rfl, rfl, hrk4⟩
    · exact ⟨t'', m, β, ht'', by omega, hβ, hlong, hvia⟩
    · exact (hedge ι β u hβ hrange hroot hcent).elim
  · have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    exact (notSU hSe hS hS' hodd' heJ he' htieJ hcase.2 (by omega)).elim
  · have hs3 := hsplit''.resolve_left hne
    exact (notSL (Gm n f) (gram_det n f) hSe (fun s hs => gram_iso n f (hSU s hs)) hS heJ hadjJ
      he' hs3 htieJ').elim


end CFSG.StandardType.ClassicalPosition.NbrLeaf
