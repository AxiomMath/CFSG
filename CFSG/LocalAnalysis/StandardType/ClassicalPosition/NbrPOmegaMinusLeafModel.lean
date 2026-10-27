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


theorem nbrpmmx_K_model {X : Type} [Group X] (n f : ℕ) (hn : 4 ≤ n) (hf : 1 ≤ f)
    (S' : Set (GL (Ix n) (GaloisField 2 f))) (hSU' : ∀ s ∈ S', s ∈ (ρm n f).range)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (UK n f)) (ε' e' : Mx n f)
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm n f) (AdS f S') ε')
    (he' : IsPrimIdemIn (AdS f S') e') (he'ε' : e' * ε' = e')
    (hsplit' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj n f e' ≠ e' ∧ ε' = e' + Fadj n f e'))
    (hK'ε' : IsComponentOf K' ⁅BlkC n f S' ε', BlkC n f S' ε'⁆) (hR'K' : R' ≤ K')
    (hgeo : ∃ a₁ a₂ : Ix n → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
      R'.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) = siegelGroup (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂)
    (hdeg : (e' = ε' ∧ blockDegree (AdS f S') e' < 2) ∨
      (e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4) ∨
      (e' ≠ ε' ∧ blockDegree (AdS f S') e' < 2)) :
    ∃ (t' : StatedLieTag) (m : ℕ) (ι : (ggU t' m f).K →* UK n f)
      (β : Fin (ggU t' m f).D.rank → ℤ) (u : (ggU t' m f).K),
      β ∈ (ggU t' m f).D.roots ∧ GGLongRoot (ggU t' m f).D β ∧ ι.range = K' ∧
      (∀ y, ι y ∈ Subgroup.center (UK n f) → y ∈ Subgroup.center (ggU t' m f).K) ∧
      (((ggU t' m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' ∧
      ((e' = ε' ∧ blockDegree (AdS f S') e' < 2 →
          (((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m ∧ 2 * m = rk f e') ∨
            (t' = .PSL ∧ m = 2 ∧ rk f e' = 4))) ∧
        (e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4 →
          t' = .PSU ∧ 2 * m = rk f e') ∧
        (e' ≠ ε' ∧ blockDegree (AdS f S') e' < 2 → t' = .PSL ∧ m = rk f e')) := by
  classical
  let Q := Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, hm⟩ := hgeo
  have hle : siegelGroup Q a₁ a₂ ≤ K'.map (Spin.spinAction Q) := by
    rw [← hm]
    exact Subgroup.map_mono hR'K'
  rcases hsplit' with hself | ⟨hne, hadj, heq⟩
  · have hadjE : formAdj (RingHom.id (GaloisField 2 f)) G e' = e' := by
      rw [hself]; exact hε'.2.2.2.1
    have hK'E : IsComponentOf K' ⁅(glBlockCentralizer (Spin.spinMatrix Q) S' e' :
        Subgroup (UK n f)), (glBlockCentralizer (Spin.spinMatrix Q) S' e' :
        Subgroup (UK n f))⁆ := by
      rw [hself]; exact hK'ε'
    rcases hdeg with ⟨-, hd⟩ | ⟨-, hd1, hd2⟩ | ⟨hne', -⟩
    · obtain ⟨t', m, ι, hshape, hcenter, hrange, hclos⟩ :=
        exists_blockModelClosure_selfDual_POmegaMinus_explicit n f hf S' hSU' hS' hodd' he'
          hn hadjE hd (nbrpom_hnm_minusFour n f S' K' R' e' he' hK'E hR'K' hadjE a₁ a₂ ha₁
            ha₂ hli hQ₁ hQ₂ horth hm) hK'E
      obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hclos a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hle
      refine ⟨t', m, ι, β, u, hβ, hβlong, hrange, hcenter,
        nbrpom_map_spinAction_injective (hβeq.trans hm.symm), ?_, ?_, ?_⟩
      · intro _
        exact hshape
      · intro h
        exact absurd h.2.1 (not_le.mpr hd)
      · intro h
        exact absurd hself h.1
    · have h :=
        exists_blockModelClosure_selfDualTwo_POmegaMinus_explicit n f S' hSU' hS' hodd' he'
          hn hadjE hd1 hd2 hK'E
      rw [max_eq_left hf] at h
      obtain ⟨r, ι, hrank, hcenter, hrange, hclos⟩ := h
      rw [← Matrix.toLin'_apply'] at hrank
      obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hclos a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hle
      refine ⟨.PSU, r, ι, β, u, hβ, hβlong, hrange, hcenter,
        nbrpom_map_spinAction_injective (hβeq.trans hm.symm), ?_, ?_, ?_⟩
      · intro h
        exact absurd h.2 (not_lt.mpr hd1)
      · intro _
        exact ⟨rfl, hrank⟩
      · intro h
        exact absurd hself h.1
    · exact absurd hself hne'
  · rw [heq] at hK'ε'
    rcases hdeg with ⟨hself', -⟩ | ⟨hself', -⟩ | ⟨-, hd⟩
    · exact absurd hself' hne
    · exact absurd hself' hne
    · obtain ⟨r, ι, hrank, hcenter, hrange, hclos⟩ :=
        exists_blockModelClosure_dualPair_POmegaMinus_explicit n f hf S' hSU' hS' hodd' he'
          hn hadj hd hK'ε'
      obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hclos a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hle
      refine ⟨.PSL, r + 1, ι, β, u, hβ, hβlong, hrange, hcenter,
        nbrpom_map_spinAction_injective (hβeq.trans hm.symm), ?_, ?_, ?_⟩
      · intro h
        exact absurd h.1 hne
      · intro h
        exact absurd h.1 hne
      · intro _
        exact ⟨rfl, hrank⟩

end CFSG.StandardType.ClassicalPosition.NbrLeaf
