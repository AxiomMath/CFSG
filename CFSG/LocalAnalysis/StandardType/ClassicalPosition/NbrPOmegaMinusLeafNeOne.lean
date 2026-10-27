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

private lemma nbrpmmx_glBlockCentralizer_le {n f : ℕ}
    {S S_e : Set (GL (Ix n) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Mx n f}
    (he : IsPrimIdemIn (AdS f S) e)
    (hdeg : blockDegree (AdS f S) e < 2)
    (heSe : e ∈ AdS f S_e) :
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
  obtain ⟨c, hc⟩ := mul_e_eq_smul he hdeg _ hsA
  have hse : (s : Mx n f) * e = e * (s : Mx n f) :=
    (adjoin_comm hS (s : Mx n f) hsA e he.1).eq
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
  have hSG : Sm * G = c • (G * e) + (Sm - c • e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + (Sm - Sm * e) := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
      _ = c • (G * e) + (Sm - c • e) := by
        rw [hc, hcomm_e, ← Matrix.mul_assoc, hc, Matrix.smul_mul]
  have hGS : G * Sm = c • (G * e) + (Sm - c • e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = G * (e * Sm) + (Sm - e * Sm) := by
        rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = c • (G * e) + (Sm - c • e) := by rw [← hse, hc, Matrix.mul_smul]
  rw [hSG, hGS]


theorem nbrpmmx_ne_one {X : Type} [Group X] (n f : ℕ) (ψ : UK n f →* X)
    (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn (AdS f S) e_J)
    (hcase : e_J = ε ∧ blockDegree (AdS f S) e_J < 2)
    (J K : Subgroup X) (hKne : K ≠ J) (hJ'map : J'.map ψ = J)
    (S' : Set (GL (Ix n) (GaloisField 2 f))) (K' : Subgroup (UK n f)) (ε' e' : Mx n f)
    (hK'map : K'.map ψ = K) (hSe : S' ⊆ S)
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm n f) (AdS f S') ε')
    (hK'ε' : IsComponentOf K' ⁅BlkC n f S' ε', BlkC n f S' ε'⁆)
    (hJ'ε : IsComponentOf J' ⁅BlkC n f S ε, BlkC n f S ε⁆) (hJK' : J' ≤ K')
    (hcaseSp : e' = ε' ∧ blockDegree (AdS f S') e' < 2) :
    e_J ≠ e' := by
  intro heq
  have heqε : ε = ε' := by rw [← hcase.1, heq, ← hcaseSp.1]
  have hK'block : IsComponentOf K' ⁅BlkC n f S' ε, BlkC n f S' ε⁆ := by
    rw [heqε]; exact hK'ε'
  have heSe : ε ∈ AdS f S' := by rw [heqε]; exact hε'.1
  have hle : BlkC n f S' ε ≤ BlkC n f S ε := by
    have hprim : IsPrimIdemIn (AdS f S) ε := by rw [← hcase.1]; exact heJ
    have hdeg : blockDegree (AdS f S) ε < 2 := by rw [← hcase.1]; exact hcase.2
    exact nbrpmmx_glBlockCentralizer_le (S := S) (S_e := S') hS hprim hdeg heSe
  have hge : BlkC n f S ε ≤ BlkC n f S' ε := by
    intro u hu
    obtain ⟨huc, hufix⟩ : (ρm n f) u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hu
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
