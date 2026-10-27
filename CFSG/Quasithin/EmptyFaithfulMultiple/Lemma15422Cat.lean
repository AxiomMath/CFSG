module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Quot
public import CFSG.Quasithin.Background.F6Cat
public import Mathlib.FieldTheory.Finite.GaloisField
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate4952
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GorensteinWalter

namespace L15422

section PSigma

variable {K : Type} [Field K]

theorem inr_conj_mem_pGammaL2PSLRange (τ : K ≃+* K) {x : PGammaL2 K}
    (hx : x ∈ pGammaL2PSLRange K) :
    SemidirectProduct.inr τ * x * (SemidirectProduct.inr τ)⁻¹ ∈ pGammaL2PSLRange K := by
  obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K x).mp hx
  refine (mem_pGammaL2PSLRange_iff K _).mpr ⟨psl2FieldAut K τ y, ?_⟩
  rw [psl2FieldAut_toPGL, SemidirectProduct.inl_aut, map_inv]

theorem range_inr_le_normalizer :
    (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range ≤
      Subgroup.normalizer (pGammaL2PSLRange K : Set (PGammaL2 K)) := by
  rintro _ ⟨τ, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨inr_conj_mem_pGammaL2PSLRange τ, fun hx => ?_⟩
  have h := inr_conj_mem_pGammaL2PSLRange τ⁻¹ hx
  have e : SemidirectProduct.inr τ⁻¹ *
      (SemidirectProduct.inr τ * x * (SemidirectProduct.inr τ)⁻¹) *
        (SemidirectProduct.inr τ⁻¹ : PGammaL2 K)⁻¹ = x := by
    rw [map_inv]
    group
  rwa [e] at h

theorem mem_pGammaL2PSLRange_of_mem {x : PGammaL2 K} (hx : x ∈ F6.PSigmaL2 K)
    (h1 : SemidirectProduct.rightHom x = 1) : x ∈ pGammaL2PSLRange K := by
  have hx' : x ∈ (((SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range ⊔
      pGammaL2PSLRange K : Subgroup (PGammaL2 K)) : Set (PGammaL2 K)) := by
    rw [sup_comm]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ range_inr_le_normalizer] at hx'
  obtain ⟨_, ⟨τ, rfl⟩, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  have hz1 : SemidirectProduct.rightHom z = 1 := by
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K z).mp hz
    exact SemidirectProduct.rightHom_inl _
  rw [map_mul, SemidirectProduct.rightHom_inr, hz1, mul_one] at h1
  rw [h1, map_one, one_mul]
  exact hz

theorem card_ringEquiv_eq_two {p : ℕ} [hp : Fact p.Prime] [Fintype K]
    (hcard : Fintype.card K = p ^ 2) :
    Nat.card (K ≃+* K) = 2 ∧ ∃ σ : K ≃+* K, σ ≠ 1 ∧ ∀ x, σ x = x ^ p := by
  have : CharP K p := charP_of_card_eq_prime_pow hcard
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hfin : Module.finrank (ZMod p) K = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rw [ZMod.card, hcard] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  let e : (K ≃+* K) ≃ (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x => by
        have h : σ.toRingHom.comp (algebraMap (ZMod p) K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun σ => by ext; rfl
      right_inv := fun σ => by ext; rfl }
  refine ⟨?_, (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K).toRingEquiv, ?_, fun x => ?_⟩
  · rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank, hfin]
  · intro h1
    have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) K
    have h2 : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K = 1 := by
      ext x
      exact congrArg (fun σ : K ≃+* K => σ x) h1
    rw [h2, orderOf_one, hfin] at hord
    omega
  · change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K x = x ^ p
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]

theorem isL2FieldExt_of_isL2FieldExtCat {p : ℕ} {W : Type} [Group W]
    (h : F6.IsL2FieldExtCat p W) : F6.IsL2FieldExt p W := by
  obtain ⟨hp, K, hK, hKf, hcard, ⟨ε⟩⟩ := h
  refine ⟨hp, K, hK, hKf, hcard, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = p ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨hAut, σ, hσ1, hσ⟩ := card_ringEquiv_eq_two hcard'
  have hPSLle : pGammaL2PSLRange K ≤ F6.PSigmaL2 K := le_sup_left
  have hinrS : ∀ τ : K ≃+* K, SemidirectProduct.inr τ ∈ F6.PSigmaL2 K := fun τ =>
    (le_sup_right : _ ≤ F6.PSigmaL2 K) ⟨τ, rfl⟩
  let ρ : W →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp ((F6.PSigmaL2 K).subtype.comp ε.toMonoidHom)
  have hρ : ∀ w, ρ w = SemidirectProduct.rightHom ((ε w : F6.PSigmaL2 K) : PGammaL2 K) :=
    fun w => rfl
  have hρs : Function.Surjective ρ := fun τ =>
    ⟨ε.symm ⟨SemidirectProduct.inr τ, hinrS τ⟩, by
      rw [hρ, MulEquiv.apply_symm_apply, SemidirectProduct.rightHom_inr]⟩
  have hNidx : ρ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρs, Subgroup.card_top, hAut]
  have hNmem : ∀ x : ρ.ker, ((ε x : F6.PSigmaL2 K) : PGammaL2 K) ∈ pGammaL2PSLRange K :=
    fun x => mem_pGammaL2PSLRange_of_mem (ε x).2 (MonoidHom.mem_ker.mp x.2)
  let ι : ρ.ker →* pGammaL2PSLRange K :=
    ((F6.PSigmaL2 K).subtype.comp (ε.toMonoidHom.comp ρ.ker.subtype)).codRestrict _ hNmem
  have hιi : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg (fun z : pGammaL2PSLRange K => (z : PGammaL2 K)) hab
    exact Subtype.ext (ε.injective (Subtype.ext h1))
  have hιs : Function.Surjective ι := by
    rintro ⟨z, hz⟩
    refine ⟨⟨ε.symm ⟨z, hPSLle hz⟩, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, hρ, MulEquiv.apply_symm_apply]
      obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K z).mp hz
      exact SemidirectProduct.rightHom_inl _
    · apply Subtype.ext
      change ((ε (ε.symm ⟨z, hPSLle hz⟩) : F6.PSigmaL2 K) : PGammaL2 K) = z
      rw [MulEquiv.apply_symm_apply]
  let e₀ : ρ.ker ≃* pGammaL2PSLRange K := MulEquiv.ofBijective ι ⟨hιi, hιs⟩
  let Ψ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
  refine ⟨ρ.ker, (e₀.trans (pGammaL2PSLRangeEquiv K).symm).trans Ψ,
    ε.symm ⟨SemidirectProduct.inr σ, hinrS σ⟩, 1, hNidx, ?_, ?_⟩
  · intro ht
    have h1 := MonoidHom.mem_ker.mp ht
    rw [hρ, MulEquiv.apply_symm_apply, SemidirectProduct.rightHom_inr] at h1
    exact hσ1 h1
  · intro n m A B hnm hA hB
    set y := (pGammaL2PSLRangeEquiv K).symm (e₀ n) with hy
    have hεn : ((ε n : F6.PSigmaL2 K) : PGammaL2 K) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      have h1 : pGammaL2PSLRangeEquiv K y = e₀ n := MulEquiv.apply_symm_apply _ _
      have h2 := congrArg (fun z : pGammaL2PSLRange K => (z : PGammaL2 K)) h1
      rw [pGammaL2PSLRangeEquiv_coe] at h2
      exact h2.symm
    have hεm : ((ε m : F6.PSigmaL2 K) : PGammaL2 K) = SemidirectProduct.inr σ *
        ((ε n : F6.PSigmaL2 K) : PGammaL2 K) * (SemidirectProduct.inr σ)⁻¹ := by
      rw [hnm, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    have hconj : SemidirectProduct.inr σ *
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) *
          (SemidirectProduct.inr σ : PGammaL2 K)⁻¹ =
        SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2FieldAut K σ y)) := by
      rw [psl2FieldAut_toPGL, SemidirectProduct.inl_aut, map_inv]
    have hem : e₀ m = pGammaL2PSLRangeEquiv K (psl2FieldAut K σ y) := by
      apply Subtype.ext
      rw [pGammaL2PSLRangeEquiv_coe, ← hconj, ← hεn, ← hεm]
      rfl
    set A' := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm A with hA'
    have hΨA' : Ψ (QuotientGroup.mk' (Subgroup.center _) A') = QuotientGroup.mk A := by
      have h1 := QuotientGroup.congr_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
        ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K).subgroupOf
          (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
        (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 K) A'
      rw [hA', MulEquiv.apply_symm_apply] at h1
      exact h1
    have hyA : y = QuotientGroup.mk' (Subgroup.center _) A' :=
      Ψ.injective (hA.trans hΨA'.symm)
    have hB' : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ p) := by
      rw [hB]
      simp
    have hBeq : CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
        (Matrix.SpecialLinearGroup.map σ.toRingHom A') = B := by
      apply Subtype.ext
      apply Units.ext
      change ((Matrix.SpecialLinearGroup.map σ.toRingHom A' : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hB']
      have hAA : (A' : Matrix (Fin 2) (Fin 2) K) =
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [hA', ← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
          MulEquiv.apply_symm_apply]
      rw [hAA]
      congr 1
      funext x
      exact hσ x
    change Ψ ((pGammaL2PSLRangeEquiv K).symm (e₀ m)) = QuotientGroup.mk B
    rw [hem, MulEquiv.symm_apply_apply, hyA, psl2FieldAut_apply, psl2RingEquiv_mk]
    have h1 := QuotientGroup.congr_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
      ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K).subgroupOf
        (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 K)
      (Matrix.SpecialLinearGroup.map σ.toRingHom A')
    rw [hBeq] at h1
    exact h1

end PSigma

end L15422

section Main

open L15422

variable {D : Type} [Group D] [Finite D] {H₁ H₂ Z' : Subgroup D}

theorem Config15422.caseEightCat_of_oriented (h : Config15422 H₁ H₂ Z')
    (hc : F6.IsF618CaseOrientedCat H₁ H₂) : IsCaseEight15422 D := by
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h1, true_or])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h2, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h3, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h4, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h5, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h6, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h7, true_or, or_true])
  · rcases h8.1 with hS | ⟨p, hp, hp8, hL⟩
    · exact Or.inl hS
    · exact Or.inr ⟨p, hp, by omega, isL2FieldExt_of_isL2FieldExtCat hL⟩
  · exfalso
    obtain ⟨-, -, -, ⟨e₂⟩⟩ := h9
    obtain ⟨v, hvZ, hv1, hvO⟩ := h.odd₂
    have hcard : Nat.card (Equiv.Perm (Fin 3) × DihedralGroup 4) = 2 ^ 4 * 3 := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, DihedralGroup.nat_card]
      rfl
    exact hv1 (eq_one_of_mem_oTwoUpper e₂ hcard perm_three_dihedral_four_cube hvO
      (h.sq_Z v hvZ))
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h10, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h11, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h12, true_or, or_true])
  · exact h.caseEight_of_oriented (by simp only [F6.IsF618CaseOriented, h13, or_true])

theorem Config15422.caseEightCat (h : Config15422 H₁ H₂ Z') (hF : F6.F618ConclusionCat H₁ H₂) :
    IsCaseEight15422 D := by
  rcases hF with hc | hc
  · exact h.caseEightCat_of_oriented hc
  · exact h.symm.caseEightCat_of_oriented hc

end Main

theorem stmt15422_of_cat
    (hF618 : F6.TheoremF618Cat) {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hSQTK : ∀ s : Setting15419 G T, CFSG.SectionRank.IsSQTKCat ↥s.I)
    (hyp : MultipleCentralizerHypothesis G T) (hnot : ¬ IsLThreeTwoOrASix G)
    (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) (h17 : Stmt15417 G T) (h19 : Stmt15419 G T)
    (h20 : Stmt15420 G T) : Stmt15422 G T :=
  L15422.stmt15422_of_caseEight hyp hnot h12 h14 h17 h19 h20 fun s _ hc =>
    hc.caseEightCat (hF618 _ _ _ hc.amalgam.toIsGoldschmidtTriple
      ⟨↥s.I, inferInstance, inferInstance, hSQTK s, ⟨MulEquiv.refl _⟩⟩)

end CFSG.Quasithin.EmptyFaithfulMultiple
