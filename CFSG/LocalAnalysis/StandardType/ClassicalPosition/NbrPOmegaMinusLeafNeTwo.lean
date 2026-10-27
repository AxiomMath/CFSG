module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafGen

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


private lemma nbrpmmx_glBlockCentralizer_le_two {n f : ℕ}
    {S S_e : Set (GL (Ix n) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Mx n f}
    (he : IsPrimIdemIn (AdS f S) e)
    (heSe : e ∈ AdS f S_e)
    (hAe : ∀ s ∈ S, (s : Mx n f) * e ∈ AdS f S_e) :
    glBlockCentralizer (ρm n f) S_e e ≤ glBlockCentralizer (ρm n f) S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : (ρm n f) u ∈ Subgroup.centralizer S_e ⊓ glFixing (1 - e) :=
    Subgroup.mem_comap.mp hu
  have hfix : (((ρm n f) u : GL (Ix n) (GaloisField 2 f)) : Mx n f) * (1 - e) = 1 - e := hufix
  have hcomm_e : (((ρm n f) u : GL (Ix n) (GaloisField 2 f)) : Mx n f) * e =
      e * (((ρm n f) u : GL (Ix n) (GaloisField 2 f)) : Mx n f) :=
    commute_adjoin (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Mx n f) ∈ AdS f S := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hse : (s : Mx n f) * e = e * (s : Mx n f) :=
    (adjoin_comm hS (s : Mx n f) hsA e he.1).eq
  have hSme : (s : Mx n f) * e ∈ AdS f S_e := hAe s hs
  have hGSm : (((ρm n f) u : GL (Ix n) (GaloisField 2 f)) : Mx n f) * ((s : Mx n f) * e) =
      ((s : Mx n f) * e) * (((ρm n f) u : GL (Ix n) (GaloisField 2 f)) : Mx n f) :=
    commute_adjoin (S := S_e) huc hSme
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G := (((ρm n f) u : GL (Ix n) (GaloisField 2 f)) : Mx n f) with hGdef
  set Sm := (s : Mx n f) with hSmdef
  have hG : G = G * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G = (G - G * e) + G * e := by abel
      _ = (1 - e) + G * e := by rw [h]
      _ = G * e + (1 - e) := by abel
  have hSG : Sm * G = Sm * (G * e) + (Sm - Sm * e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + Sm * (1 - e) := by rw [Matrix.mul_add]
      _ = Sm * (G * e) + (Sm - Sm * e) := by rw [Matrix.mul_sub, Matrix.mul_one]
  have hGS : G * Sm = (G * e) * Sm + (Sm - Sm * e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = (G * e) * Sm + (1 - e) * Sm := by rw [Matrix.add_mul]
      _ = (G * e) * Sm + (Sm - e * Sm) := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = (G * e) * Sm + (Sm - Sm * e) := by rw [hse]
  have hkey : Sm * (G * e) = (G * e) * Sm := by
    calc Sm * (G * e) = Sm * (e * G) := by rw [hcomm_e]
      _ = (Sm * e) * G := by noncomm_ring
      _ = G * (Sm * e) := hGSm.symm
      _ = G * (e * Sm) := by rw [hse]
      _ = (G * e) * Sm := by noncomm_ring
  change Sm * G = G * Sm
  rw [hSG, hGS, hkey]

private lemma nbrpmmx_blockDegree_eq_two_of_selfDual {n f : ℕ}
    {S : Set (GL (Ix n) (GaloisField 2 f))}
    (hSU : ∀ s ∈ S, s ∈ (ρm n f).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Mx n f}
    (he : IsPrimIdemIn (AdS f S) e)
    (hadj : Fadj n f e = e)
    (h2 : 2 ≤ blockDegree (AdS f S) e)
    (h4 : blockDegree (AdS f S) e < 4) :
    blockDegree (AdS f S) e = 2 := by
  have hGdet : IsUnit (Gm n f).det := gram_det n f
  have hSG : ∀ s ∈ S, Matrix.transpose (((s : GL (Ix n) (GaloisField 2 f)) : Mx n f).map
      (RingHom.id (GaloisField 2 f))) * Gm n f *
      ((s : GL (Ix n) (GaloisField 2 f)) : Mx n f) = Gm n f := by
    intro s hs
    exact gram_iso n f (hSU s hs)
  have hpar := blockDegree_eq_one_or_even_of_formAdj_eq hGdet hS hodd hSG he hadj
  rcases hpar with h1 | heven
  · omega
  · obtain ⟨k, hk⟩ := heven
    omega


theorem nbrpmmx_ne_two {X : Type} [Group X] (n f : ℕ) (ψ : UK n f →* X)
    (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hSU : ∀ s ∈ S, s ∈ (ρm n f).range)
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm n f) (AdS f S) ε)
    (heJ : IsPrimIdemIn (AdS f S) e_J) (hcase : e_J = ε)
    (hdegJ : blockDegree (AdS f S) e_J < 4)
    (J K : Subgroup X) (hKne : K ≠ J) (hJ'map : J'.map ψ = J)
    (S' : Set (GL (Ix n) (GaloisField 2 f))) (K' : Subgroup (UK n f)) (ε' e' : Mx n f)
    (hK'map : K'.map ψ = K) (hSe : S' ⊆ S)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hSU' : ∀ s ∈ S', s ∈ (ρm n f).range)
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm n f) (AdS f S') ε')
    (he' : IsPrimIdemIn (AdS f S') e')
    (hK'ε' : IsComponentOf K' ⁅BlkC n f S' ε', BlkC n f S' ε'⁆)
    (hJ'ε : IsComponentOf J' ⁅BlkC n f S ε, BlkC n f S ε⁆) (hJK' : J' ≤ K')
    (hcaseSU : e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4) :
    e_J ≠ e' := by
  intro heq
  have heqε : ε = ε' := by rw [← hcase, heq, ← hcaseSU.1]
  have hsub : AdS f S' ≤ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe)
  have hadj' : Fadj n f e' = e' := by
    rw [hcaseSU.1]
    exact hε'.2.2.2.1
  have hdegA' : blockDegree (AdS f S') e' = 2 :=
    nbrpmmx_blockDegree_eq_two_of_selfDual hSU' hS' hodd' he' hadj' hcaseSU.2.1 hcaseSU.2.2
  have hadjJ : Fadj n f e_J = e_J := by
    rw [hcase]
    exact hε.2.2.2.1
  have hmono : blockDegree (AdS f S') e' ≤ blockDegree (AdS f S) e' :=
    Submodule.finrank_mono (Submodule.map_mono hsub)
  have h2 : 2 ≤ blockDegree (AdS f S) e_J := by
    rw [heq]
    exact le_trans hcaseSU.2.1 hmono
  have hdegJ2 : blockDegree (AdS f S) e_J = 2 :=
    nbrpmmx_blockDegree_eq_two_of_selfDual hSU hS hodd heJ hadjJ h2 hdegJ
  have hdegA'J : blockDegree (AdS f S') e_J = 2 := by
    rw [heq]
    exact hdegA'
  have heJA : e_J ∈ AdS f S' := by
    rw [heq]
    exact he'.1
  have hAe : ∀ s ∈ S, (s : Mx n f) * e_J ∈ AdS f S' := by
    intro s hs
    have hleM : (Subalgebra.toSubmodule (AdS f S')).map
        (LinearMap.mulRight (GaloisField 2 f) e_J) ≤
        (Subalgebra.toSubmodule (AdS f S)).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      Submodule.map_mono hsub
    have heqm : (Subalgebra.toSubmodule (AdS f S')).map
        (LinearMap.mulRight (GaloisField 2 f) e_J) =
        (Subalgebra.toSubmodule (AdS f S)).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      Submodule.eq_of_le_of_finrank_eq hleM (by
        show blockDegree (AdS f S') e_J = blockDegree (AdS f S) e_J
        rw [hdegA'J, hdegJ2])
    have hsM : (s : Mx n f) * e_J ∈
        (Subalgebra.toSubmodule (AdS f S)).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      ⟨s, Algebra.subset_adjoin ⟨s, hs, rfl⟩, by rw [LinearMap.mulRight_apply]⟩
    rw [← heqm] at hsM
    obtain ⟨a, ha, hae⟩ := hsM
    rw [LinearMap.mulRight_apply] at hae
    rw [← hae]
    exact Subalgebra.mul_mem _ ha heJA
  have hK'block : IsComponentOf K' ⁅BlkC n f S' ε, BlkC n f S' ε⁆ := by
    rw [heqε]
    exact hK'ε'
  have heSe : ε ∈ AdS f S' := by
    rw [heqε]
    exact hε'.1
  have hle : BlkC n f S' ε ≤ BlkC n f S ε := by
    have hprim : IsPrimIdemIn (AdS f S) ε := by
      rw [← hcase]
      exact heJ
    have hdeg : blockDegree (AdS f S) ε < 4 := by
      rw [← hcase]
      exact hdegJ
    exact nbrpmmx_glBlockCentralizer_le_two (S := S) (S_e := S') hS hprim heSe
      (fun s hs => by rw [← hcase]; exact hAe s hs)
  have hge : BlkC n f S ε ≤ BlkC n f S' ε := by
    intro u hu
    obtain ⟨huc, hufix⟩ := Subgroup.mem_comap.mp hu
    exact Subgroup.mem_comap.mpr ⟨Subgroup.centralizer_le hSe huc, hufix⟩
  have hG_eq : BlkC n f S ε = BlkC n f S' ε := le_antisymm hge hle
  have hK'blockS : IsComponentOf K' ⁅BlkC n f S ε, BlkC n f S ε⁆ :=
    hG_eq.symm ▸ hK'block
  haveI : Finite (UK n f) :=
    Finite.of_injective (ρm n f) (nbrpom_spinMatrix_injective n f)
  have hJK'' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'ε hK'blockS hJK'
  have hKJ : K = J :=
    ((hJ'map.symm.trans (congrArg (Subgroup.map ψ) hJK'')).trans hK'map).symm
  exact hKne hKJ

end CFSG.StandardType.ClassicalPosition.NbrLeaf
