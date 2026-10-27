module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaModel
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace OrdPNsOm

theorem exists_conj_mem_centralizer_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} {n f : ℕ} (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n (GaloisField 2 f)) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (plusDatum n (GaloisField 2 f) hn) .POmegaPlus n f ψ)
    {y : G} (hyp : y ^ p = 1) (hy : GGPsiInnerDiag (plusDatum n (GaloisField 2 f) hn) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hin : ∀ c, GGPsiInnerDiag (plusDatum n (GaloisField 2 f) hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨u, rfl⟩ := hin y hy
  have hup : u ^ p = 1 := hψ (by rw [map_pow, hyp, map_one])
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
  set πe := MulEquiv.ofBijective (AutOm.spinModelPlus (K := GaloisField 2 f) hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ with hπe
  set φ : matrixDerived (coordinateQuadPlus n (GaloisField 2 f)) →* G :=
    ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφr : φ.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨πe v, by simp [hφ]⟩
  have hφu : φ (πe u) = ψ u := by simp [hφ]
  have h := exists_conj_mem_centralizer_of_model hS hnd hT φ hφinj
    (by rw [hφr, hrange]; exact Subgroup.le_normalizer)
    (fun b hb => by rw [hφr]; exact hin b (hS.innerDiag b hb)) (u := πe u)
    (by rw [← map_pow, hup, map_one])
  rwa [hφu] at h

theorem exists_conj_mem_centralizer_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {n f : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (minusDatum n hirr) .POmegaMinus n f ψ)
    {y : G} (hyp : y ^ p = 1) (hy : GGPsiInnerDiag (minusDatum n hirr) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum n hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨u, rfl⟩ := hin y hy
  have hup : u ^ p = 1 := hψ (by rw [map_pow, hyp, map_one])
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  set πe := MulEquiv.ofBijective (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ with hπe
  set φ : matrixDerived (coordinateQuadMinus n K (by omega) b c) →* G :=
    ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφr : φ.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨πe v, by simp [hφ]⟩
  have hφu : φ (πe u) = ψ u := by simp [hφ]
  have h := exists_conj_mem_centralizer_of_model hS hnd hT φ hφinj
    (by rw [hφr, hrange]; exact Subgroup.le_normalizer)
    (fun b hb => by rw [hφr]; exact hin b (hS.innerDiag b hb)) (u := πe u)
    (by rw [← map_pow, hup, map_one])
  rwa [hφu] at h

end OrdPNsOm

section Family

theorem ggOrdPInnerConjPOmegaPlusNonsplit_holds : GGOrdPInnerConjPOmegaPlusNonsplit := by
  intro G _ _ p Bs G₀ n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hS _ _ y _ hyo hy
    exact OrdPNsOm.exists_conj_mem_centralizer_plus hn hS (hyo ▸ pow_orderOf_eq_one y) hy
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ hS
    exact absurd hS.presents.1.2 (by decide)

theorem ggOrdPInnerConjPOmegaMinusNonsplit_holds : GGOrdPInnerConjPOmegaMinusNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ _ y _ hyo hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
  obtain ⟨-, hf, hn⟩ := hadm
  exact OrdPNsOm.exists_conj_mem_centralizer_minus (K := GaloisField 2 f)
    (minusCoeffs_irr 2 f) hn hS (hyo ▸ pow_orderOf_eq_one y) hy

theorem ggOrdPInnerConjAt_POmegaPlus : GGOrdPInnerConjAt .POmegaPlus :=
  ggOrdPInnerConjAt_POmegaPlus_of_nonsplit ggOrdPInnerConjPOmegaPlusNonsplit_holds

theorem ggOrdPInnerConjAt_POmegaMinus : GGOrdPInnerConjAt .POmegaMinus :=
  ggOrdPInnerConjAt_POmegaMinus_of_nonsplit ggOrdPInnerConjPOmegaMinusNonsplit_holds

end Family

end CFSG.StandardType
