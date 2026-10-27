module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
import CFSG.LocalAnalysis.StandardType.KGLangTorusLinear
import CFSG.LocalAnalysis.StandardType.KGLangTorusUnitary
import CFSG.LocalAnalysis.StandardType.KGLangTorusSymplectic
import CFSG.LocalAnalysis.StandardType.KGLangTorusOmegaPlus
import CFSG.LocalAnalysis.StandardType.KGLangTorusOmegaMinus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

private theorem kgLangCFamAux_centerCoprime {p : ℕ} (hZ : KGCenterCoprimeInput)
    (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hreg : GGNbrLangRegLabel p lab) {R : Type} [Group R] (hhas : GGHasLabel lab R) :
    ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R),
      commutator (HopfCover R) = ⊤ →
      Nat.Coprime (Nat.card (Subgroup.center (HopfCover R))) p := by
  intro _ θ hcomm
  exact hZ p hp hp2 lab hlab hreg (HopfCover R) hcomm
    (largeEvenRawDatum_mono (fun R' _ _ _ ⟨e⟩ => ⟨θ.trans e⟩) hhas)

theorem kgLangTorusDatumOn_regLinear12 (hZ : KGCenterCoprimeInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) :
    KGLangTorusDatumOn fun p lab => GGNbrLangRegLinearLabel p lab ∧ GGNbrLangRest12Label p lab := by
  intro p lab hp hp2 hlab hS
  obtain ⟨hreg, hrest⟩ := hS
  have hZreg : GGNbrLangRegLabel p lab := Or.inl hreg
  have hLinCop : ¬ GGLinearCoprimeDegLabel p lab := hrest.1.2.2.2.2.1
  have hVac : ¬ GGCorFourTwoOpenVacLabel p lab := hrest.1.2.2.1
  obtain ⟨t, l, n⟩ := lab
  rcases hreg with ⟨ht, hpd⟩ | ⟨ht, hr⟩
  · rcases ht with rfl | rfl
    ·
      intro Q hQ
      have hpn : p ∣ n := by
        by_contra h
        exact hLinCop ⟨Or.inl rfl, h⟩
      have h2l : 2 ≤ l := by
        have h1 : 1 ≤ l := hlab.2.1
        by_contra h
        have hl1 : l = 1 := by omega
        exact hrest.1.2.1 (Or.inl ⟨rfl, hl1⟩)
      have hQc : LargeEvenRawDatum ⟨.A, l, n⟩
          (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
        hpc p hp hp2 ⟨.A, l, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
      dsimp only [LargeEvenRawDatum] at hQc
      obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
      have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K))
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K)) Set.univ)
          (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K))) :=
        ggRawFieldCycW_of_pCyclic hPCK
      have hhas : GGHasLabel ⟨.A, l, n⟩ (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K)) := by
        dsimp only [GGHasLabel, LargeEvenRawDatum]
        exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
      have hD := @kgLangTorusDatumCont_linear p hp hp2 (l + 1) n (by omega) hpd hpn K i1 i2 hK
        hcyc (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
      exact ⟨K, i1, i2, hK, hQK, hD⟩
    ·
      intro Q hQ
      have hpn : p ∣ n := by
        by_contra h
        exact hVac ⟨hp2, Or.inr (Or.inr ⟨Or.inl rfl, h⟩)⟩
      have h2l : 2 ≤ l := hlab.2.1
      have hQc : LargeEvenRawDatum ⟨.twA, l, n⟩
          (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
        hpc p hp hp2 ⟨.twA, l, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
      dsimp only [LargeEvenRawDatum] at hQc
      obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
      have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
            (LargeEvenGUSet (Fin (l + 1)) K (2 ^ n)))
          (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))) :=
        ggRawFieldCycW_of_pCyclic hPCK
      have hhas : GGHasLabel ⟨.twA, l, n⟩
          (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) := by
        dsimp only [GGHasLabel, LargeEvenRawDatum]
        exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
      have hD := @kgLangTorusDatumCont_unitary p hp hp2 (l + 1) n (by omega) hpd hpn K i1 i2 hK
        hcyc (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
      exact ⟨K, i1, i2, hK, hQK, hD⟩
  · rcases ht with rfl | rfl
    ·
      subst hr
      intro Q hQ
      have hpn : p ∣ n := by
        by_contra h
        exact hLinCop ⟨Or.inr ⟨rfl, rfl⟩, h⟩
      have hpd4 : ¬ p ∣ 4 := by
        intro h
        have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 2) (by simpa using h)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      have hQc : LargeEvenRawDatum ⟨.D, 3, n⟩
          (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
        hpc p hp hp2 ⟨.D, 3, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
      simp only [LargeEvenRawDatum, ↓reduceIte] at hQc
      obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
      have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) Set.univ)
          (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K))) :=
        ggRawFieldCycW_of_pCyclic hPCK
      have hhas : GGHasLabel ⟨.D, 3, n⟩ (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
        dsimp only [GGHasLabel, LargeEvenRawDatum]
        simp only [↓reduceIte]
        exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
      have hD := @kgLangTorusDatumCont_linear p hp hp2 4 n (by norm_num) hpd4 hpn K i1 i2 hK
        hcyc (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
      exact ⟨K, i1, i2, hK, hQK, hD⟩
    ·
      subst hr
      intro Q hQ
      have hpn : p ∣ n := by
        by_contra h
        exact hVac ⟨hp2, Or.inr (Or.inr ⟨Or.inr ⟨rfl, rfl⟩, h⟩)⟩
      have hpd4 : ¬ p ∣ 4 := by
        intro h
        have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 2) (by simpa using h)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      have hQc : LargeEvenRawDatum ⟨.twD, 3, n⟩
          (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
        hpc p hp hp2 ⟨.twD, 3, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
      simp only [LargeEvenRawDatum, ↓reduceIte] at hQc
      obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
      have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
            (LargeEvenGUSet (Fin 4) K (2 ^ n)))
          (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))) :=
        ggRawFieldCycW_of_pCyclic hPCK
      have hhas : GGHasLabel ⟨.twD, 3, n⟩
          (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) := by
        dsimp only [GGHasLabel, LargeEvenRawDatum]
        simp only [↓reduceIte]
        exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
      have hD := @kgLangTorusDatumCont_unitary p hp hp2 4 n (by norm_num) hpd4 hpn K i1 i2 hK
        hcyc (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
      exact ⟨K, i1, i2, hK, hQK, hD⟩

private theorem kgLangCFamAux_cycW_inn {p : ℕ} {R : Type} [Group R] (F : Set (MulAut R))
    (hcycF : IsCyclic (Subgroup.closure F)) :
    GGRawFieldCycW p R (LargeEvenInnSet R) F := by
  intro _ _
  let J : Subgroup (MulAut R) := (MulAut.conj : R →* MulAut R).range
  haveI : J.Normal := ggInnNormal R
  have hJcoe : (J : Set (MulAut R)) = LargeEvenInnSet R := rfl
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Subgroup.closure F)).mp hcycF
  have hgmem : g ∈ Subgroup.closure F := hg ▸ Subgroup.mem_zpowers g
  refine ⟨J, J ⊔ Subgroup.zpowers g, hJcoe, le_sup_left, inferInstance, ?_, ?_⟩
  · refine ⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g), fun s hs => ?_⟩
    obtain ⟨j, hj, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine ⟨-(k : ℤ), ?_⟩
    show g ^ (-(k : ℤ)) * (j * g ^ k) ∈ J
    have hconj : g ^ (-(k : ℤ)) * j * (g ^ (-(k : ℤ)))⁻¹ ∈ J :=
      (inferInstance : J.Normal).conj_mem j hj (g ^ (-(k : ℤ)))
    have he : g ^ (-(k : ℤ)) * (j * g ^ k) = g ^ (-(k : ℤ)) * j * (g ^ (-(k : ℤ)))⁻¹ := by
      group
    rw [he]; exact hconj
  · intro α hα _
    have hle : Subgroup.closure (LargeEvenInnSet R ∪ F) ≤ J ⊔ Subgroup.zpowers g := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hxI | hxF
      · exact Subgroup.mem_sup_left hxI
      · exact Subgroup.mem_sup_right (hg ▸ Subgroup.subset_closure hxF)
    exact hle hα

theorem kgLangTorusDatumOn_regClassical12 (hZ : KGCenterCoprimeInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) :
    KGLangTorusDatumOn fun p lab => GGNbrLangRegClassicalLabel lab ∧ GGNbrLangRest12Label p lab := by
  intro p lab hp hp2 hlab hS
  obtain ⟨hreg, hrest⟩ := hS
  have hZreg : GGNbrLangRegLabel p lab := Or.inr (Or.inl hreg)
  have hSpOmega : ¬ GGSpOmegaCoprimeDegLabel p lab := hrest.1.2.2.2.2.2.1
  have hVac : ¬ GGCorFourTwoOpenVacLabel p lab := hrest.1.2.2.1
  obtain ⟨t, l, n⟩ := lab
  rcases hreg with rfl | rfl | ⟨ht, h4⟩
  ·
    intro Q hQ
    have hpn : p ∣ n := by
      by_contra h
      exact hSpOmega ⟨Or.inl rfl, h⟩
    have hm : 2 ≤ l := hlab.2.1
    have hQc : LargeEvenRawDatum ⟨.B, l, n⟩
        (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
      hpc p hp hp2 ⟨.B, l, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
    dsimp only [LargeEvenRawDatum] at hQc
    obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
    have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K l))) :=
      ggRawFieldCycW_of_pCyclic hPCK
    have hhas : GGHasLabel ⟨.B, l, n⟩ (LargeEvenProj (LargeEvenSpGroup K l)) := by
      dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
    have hD := @kgLangTorusDatumCont_symplectic p hp hp2 l n hm hpn K i1 i2 hK hcyc
      (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
    refine ⟨K, i1, i2, hK, hQK, ?_⟩
    change KGLangTorusDatumCont p (LargeEvenProj (LargeEvenSpGroup K l))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K l)))
    exact hD
  ·
    intro Q hQ
    have hpn : p ∣ n := by
      by_contra h
      exact hSpOmega ⟨Or.inr (Or.inl rfl), h⟩
    have hm : 2 ≤ l := hlab.2.1
    have hQc : LargeEvenRawDatum ⟨.C, l, n⟩
        (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
      hpc p hp hp2 ⟨.C, l, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
    dsimp only [LargeEvenRawDatum] at hQc
    obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
    have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K l))) :=
      ggRawFieldCycW_of_pCyclic hPCK
    have hhas : GGHasLabel ⟨.C, l, n⟩ (LargeEvenProj (LargeEvenSpGroup K l)) := by
      dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
    have hD := @kgLangTorusDatumCont_symplectic p hp hp2 l n hm hpn K i1 i2 hK hcyc
      (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
    refine ⟨K, i1, i2, hK, hQK, ?_⟩
    change KGLangTorusDatumCont p (LargeEvenProj (LargeEvenSpGroup K l))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K l)))
    exact hD
  · rcases ht with rfl | rfl
    ·
      intro Q hQ
      have h4l : 4 ≤ l := h4
      have hpn : p ∣ n := by
        by_contra h
        exact hSpOmega ⟨Or.inr (Or.inr ⟨rfl, h4⟩), h⟩
      have hl3 : l ≠ 3 := by omega
      by_cases hD4 : GGNotD4Three p ⟨.D, l, n⟩
      · have hQc : LargeEvenRawDatum ⟨.D, l, n⟩
            (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
          hpc p hp hp2 ⟨.D, l, n⟩ hlab hD4 Q hQ
        simp only [LargeEvenRawDatum, hl3, ↓reduceIte] at hQc
        obtain ⟨K, i1, i2, hK, hQK, hPCK⟩ := hQc
        have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l)))
            (LargeEvenInnSet _)
            (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K l)))) :=
          ggRawFieldCycW_of_pCyclic hPCK
        have hhas : GGHasLabel ⟨.D, l, n⟩
            (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l))) := by
          simp only [GGHasLabel, LargeEvenRawDatum, hl3, ↓reduceIte]
          exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
        have hD := @kgLangTorusDatumCont_omegaPlus p hp hp2 l n h4l hpn K i1 i2 hK hcyc
          (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
        simp only [LargeEvenRawDatum, hl3, ↓reduceIte]
        exact ⟨K, i1, i2, hK, hQK, hD⟩
      · have hQd : LargeEvenRawDatum ⟨.D, l, n⟩ Q := hQ
        simp only [LargeEvenRawDatum, hl3, ↓reduceIte] at hQd
        obtain ⟨K, i1, i2, hK, hQK⟩ := hQd
        haveI : CharP K 2 := charP_two_of_card hK
        have hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l)))
            (LargeEvenInnSet _)
            (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K l)))) :=
          kgLangCFamAux_cycW_inn _
            (kgRawFieldCyclic_omegaPlus (K := K) (m := l) (f := n) (by omega) hK)
        have hhas : GGHasLabel ⟨.D, l, n⟩
            (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l))) := by
          simp only [GGHasLabel, LargeEvenRawDatum, hl3, ↓reduceIte]
          exact ⟨K, i1, i2, hK, ⟨MulEquiv.refl _⟩⟩
        have hD := @kgLangTorusDatumCont_omegaPlus p hp hp2 l n h4l hpn K i1 i2 hK hcyc
          (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
        simp only [LargeEvenRawDatum, hl3, ↓reduceIte]
        exact ⟨K, i1, i2, hK, hQK, hD⟩
    ·
      intro Q hQ
      have h4l : 4 ≤ l := h4
      have hpn : p ∣ n := by
        by_contra h
        exact hVac ⟨hp2, Or.inl ⟨rfl, h4, h⟩⟩
      have hm : 3 ≤ l - 1 := by omega
      have hl2 : l ≠ 2 := by omega
      have hl3 : l ≠ 3 := by omega
      have hQc : LargeEvenRawDatum ⟨.twD, l, n⟩
          (fun R _ I F => Q R I F ∧ GGRawPCyclic p R I F) :=
        hpc p hp hp2 ⟨.twD, l, n⟩ hlab (by simp [GGNotD4Three]) Q hQ
      simp only [LargeEvenRawDatum, hl2, hl3, ↓reduceIte] at hQc
      obtain ⟨K, i1, i2, hK, b, c, hbc, hQK, hPCK⟩ := hQc
      have hcyc : GGRawFieldCycW p
          (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))
          (LargeEvenInnSet _)
          (LargeEvenPhiQ (l - 1) b c
            (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))) :=
        ggRawFieldCycW_of_pCyclic hPCK
      have hhas : GGHasLabel ⟨.twD, l, n⟩
          (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) := by
        simp only [GGHasLabel, LargeEvenRawDatum, hl2, hl3, ↓reduceIte]
        exact ⟨K, i1, i2, hK, b, c, hbc, ⟨MulEquiv.refl _⟩⟩
      have hD := @kgLangTorusDatumCont_omegaMinus p hp hp2 (l - 1) n hm hpn K i1 i2 hK b c hbc
        hcyc (kgLangCFamAux_centerCoprime hZ hp hp2 hlab hZreg hhas)
      simp only [LargeEvenRawDatum, hl2, hl3, ↓reduceIte]
      exact ⟨K, i1, i2, hK, b, c, hbc, hQK, hD⟩

end CFSG.StandardType
