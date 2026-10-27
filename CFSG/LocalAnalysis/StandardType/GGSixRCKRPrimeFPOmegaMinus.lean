module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeOmegaFourMinusPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaMinusDPOne
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaMinusFixed
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaMinusSDTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlag
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] def RCKM3POmegaMinusDualPairHigh :
    Prop :=
  ∀ (n f : ℕ), 1 ≤ f → 4 ≤ n →
    ∀ (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      (∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range) →
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') → (∀ s ∈ S, Odd (orderOf s)) →
      ∀ {ε e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 f)},
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin (Spin.quadMinus n
          (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε →
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e → e * ε = e →
      e ≠ ε →
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e →
      ∀ {J' : Subgroup (ggU .POmegaMinus n f).K},
      IsComponentOf J'
        ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε :
            Subgroup (ggU .POmegaMinus n f).K),
          (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε :
            Subgroup (ggU .POmegaMinus n f).K)⁆ →
      RCKSpinFlagModel
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) J' 4

@[expose] def RCKM3POmegaMinusSelfDualHigh :
    Prop :=
  ∀ (n f : ℕ), 1 ≤ f → 4 ≤ n →
    ∀ (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      (∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range) →
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') → (∀ s ∈ S, Odd (orderOf s)) →
      ∀ {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 f)},
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin (Spin.quadMinus n
          (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e →
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e →
      4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e →
      ∀ {J' : Subgroup (ggU .POmegaMinus n f).K},
      IsComponentOf J'
        ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e :
            Subgroup (ggU .POmegaMinus n f).K),
          (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e :
            Subgroup (ggU .POmegaMinus n f).K)⁆ →
      RCKSpinFlagModel
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) J' 4

@[expose] def RCKLemmaFAtPOmegaMinusLow :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    (∃ (m g : ℕ) (φ : (ggU .POmegaMinus m g).K →* X), m < 4 ∧ 1 ≤ g ∧ φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .POmegaMinus m g).K ∧
      ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus m g).D φ b) →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → GGRootPosFlag K R

theorem rckM3_POmegaMinus_dispatch
    (hdp : RCKM3POmegaMinusDualPairHigh) (hsd : RCKM3POmegaMinusSelfDualHigh)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J B : Subgroup X}
    {d : X} (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    {m g : ℕ} (hg : 1 ≤ g) (hm : 4 ≤ m)
    (φ : ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2)) →* X)
    (hφk : φ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)))
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)) φ b)
    {s : ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2))}
    (hs : ∀ u, d⁻¹ * φ u * d = φ (s * u * s⁻¹))
    (hsodd : Odd (orderOf (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) s)))
    {ε : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (GaloisField 2 g)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 g))
      (LinearMap.toMatrix₂' (GaloisField 2 g) (QuadraticMap.polarBilin
        (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)))
      (Algebra.adjoin (GaloisField 2 g) (Units.val ''
        {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
          (minusCoeffs 2 g).2) s})) ε)
    {J' : Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2))}
    (hJ'comp : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
          (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
          {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
            (minusCoeffs 2 g).2) s} ε :
          Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
            (minusCoeffs 2 g).2))),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
          (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
          {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
            (minusCoeffs 2 g).2) s} ε :
          Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
            (minusCoeffs 2 g).2)))⁆)
    (hJ'map : J'.map φ = J) :
    RCKSpinSiegelModel (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
        (minusCoeffs 2 g).2) J' ∨
      RCKSpinFlagModel (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
        (minusCoeffs 2 g).2) J' 4 := by
  have hirr : ∀ t : GaloisField 2 g,
      t ^ 2 + (minusCoeffs 2 g).1 * t + (minusCoeffs 2 g).2 ≠ 0 := minusCoeffs_irr 2 g
  have hSsing : ∀ x ∈ ({Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (GaloisField 2 g))), ∀ x' ∈ ({Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (GaloisField 2 g))), Commute x x' := by
    intro x hx x' hx'
    rw [Set.mem_singleton_iff] at hx hx'
    subst x
    subst x'
    exact Commute.refl _
  have hSU : ∀ x ∈ ({Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (GaloisField 2 g))), x ∈ (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)).range := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨s, hx.symm⟩
  have hoddS : ∀ x ∈ ({Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (GaloisField 2 g))), Odd (orderOf x) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hsodd
  have hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
      {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
        (minusCoeffs 2 g).2) s} ε :=
    hJ'comp.1.trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
        (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂))
  obtain ⟨e, he, heε, hcases⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaMinus m g
    {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2) s} hSU hSsing hε
  rcases hcases with hee | ⟨hne, hadjne, hεe⟩
  ·
    have heε' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val ''
        {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
          (minusCoeffs 2 g).2) s})) ε := hee ▸ he
    have hadj := hε.2.2.2.1
    by_cases hd1 : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val ''
        {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
          (minusCoeffs 2 g).2) s})) ε < 2
    · exact Or.inl (rckM3_POmegaMinus_fixed m g hg hm _ hSU hSsing hoddS heε' hadj hd1
        (fun hm4 => rckF_POmegaMinus_not_omegaFourMinus hp hp2 hBab hdB hrank hirr hm φ hφk
          hdiag s hs heε' hadj hm4 hJ'G hJ'map) hJ'comp)
    by_cases hd2 : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val ''
        {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
          (minusCoeffs 2 g).2) s})) ε < 4
    · exact Or.inl (rckM3_POmegaMinus_selfDualTwo m g hm _ hSU hSsing hoddS heε' hadj
        (by omega) hd2 hJ'comp)
    · exact Or.inr (hsd m g hg hm _ hSU hSsing hoddS hε heε' (by omega) hJ'comp)
  ·
    have hJe : IsComponentOf J'
        ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
            (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
            {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
              (minusCoeffs 2 g).2) s}
            (e + formAdj (RingHom.id (GaloisField 2 g))
              (LinearMap.toMatrix₂' (GaloisField 2 g) (QuadraticMap.polarBilin
                (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
                  (minusCoeffs 2 g).2))) e) :
            Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
              (minusCoeffs 2 g).2))),
          (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
            (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
            {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
              (minusCoeffs 2 g).2) s}
            (e + formAdj (RingHom.id (GaloisField 2 g))
              (LinearMap.toMatrix₂' (GaloisField 2 g) (QuadraticMap.polarBilin
                (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
                  (minusCoeffs 2 g).2))) e) :
            Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
              (minusCoeffs 2 g).2)))⁆ := by
      rw [← hεe]
      exact hJ'comp
    by_cases hd1 : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val ''
        {Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
          (minusCoeffs 2 g).2) s})) e < 2
    · exact Or.inl (rckM3_POmegaMinus_dualPairOne m g hg hm _ hSU hSsing hoddS he hadjne hd1
        hJe)
    · exact Or.inr (hdp m g hg hm _ hSU hSsing hoddS hε he heε hne (by omega) hJ'comp)

theorem rckLemmaFAt_POmegaMinus_of
    (hIRG : RCKIntrinsicRoot)
    (hdp : RCKM3POmegaMinusDualPairHigh) (hsd : RCKM3POmegaMinusSelfDualHigh)
    (hlow : RCKLemmaFAtPOmegaMinusLow) : RCKLemmaFAt .POmegaMinus := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hA6 hRJ hRmJ hroot
  obtain ⟨m, g, φ, hg, hφr, hφk, hdiag⟩ := hmodel
  by_cases hm : 4 ≤ m
  swap
  · exact hlow X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
      ⟨m, g, φ, by omega, hg, hφr, hφk, hdiag⟩ hodd hcomp hA6 hRJ hRmJ hroot
  have hirr : ∀ s : GaloisField 2 g,
      s ^ 2 + (minusCoeffs 2 g).1 * s + (minusCoeffs 2 g).2 ≠ 0 := minusCoeffs_irr 2 g
  have hnd : (QuadraticMap.polarBilin (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadMinus_of_finite m (GaloisField 2 g) hirr
  have hj : Function.Injective (Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero (GaloisField 2 g) 2))
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hφk.trans (CFSG.StandardType.PsiDiag.SpinM.center_eq_bot hirr hm).le
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaMinus hp hp2 (hBab.2 d hdB) hirr hm φ hφr hφk (hdiag d hdB) hcomp
  have hJq := hcomp.2.2
  rw [← hJ'map] at hJq
  have hpos := hroot
  rw [← hJ'map] at hpos
  have hmod : RCKSpinFlagModel (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2) J' 0 := by
    rcases rckM3_POmegaMinus_dispatch hdp hsd hp hp2 hBab hdB hrank hg hm φ hφk hdiag hs hsodd
      hε hJ'comp hJ'map with hsieg | hfl
    · exact rckSpinFlagModel_of_siegel hnd hsieg
    · exact hfl.mono (Nat.zero_le _)
  have hflag := rckFlagAt_of_spinFlagModel hIRG hj φ hφinj hmod hJq hφr hpos
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, g, hg, hflag⟩)))

end CFSG.StandardType.RCKRP
