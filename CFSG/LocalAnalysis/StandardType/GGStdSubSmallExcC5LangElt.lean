module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E7Index
public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwo TableBExcTwoFusion

set_option linter.unusedSectionVars false

section Omega

variable (K : Type) [Field K] [CharP K 2]

theorem exists_omega : ∃ ω : (AlgebraicClosure K)ˣ,
    (ω : AlgebraicClosure K) ^ 2 + (ω : AlgebraicClosure K) + 1 = 0 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := AlgebraicClosure K)
    (Polynomial.X ^ 2 + Polynomial.X + 1) (by
      have h : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (AlgebraicClosure K)).degree =
          2 := by compute_degree!
      rw [h]
      norm_num)
  have hx' : x ^ 2 + x + 1 = 0 := by simpa [Polynomial.IsRoot] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx'
  exact ⟨Units.mk0 x hx0, hx'⟩

@[expose] noncomputable def frobK : AlgebraicClosure K →+* AlgebraicClosure K :=
  frobenius (AlgebraicClosure K) 2

variable {K}

theorem frobK_apply (c : AlgebraicClosure K) : frobK K c = c ^ 2 :=
  frobenius_def 2 c

theorem frobK_apply_card (hK : Nat.card K = 2) (c : AlgebraicClosure K) :
    frobK K c = c ^ Nat.card K := by
  rw [hK]
  exact frobK_apply c

end Omega

section Elt

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def langG (F : OrthFrame τ d) {ω : (AlgebraicClosure K)ˣ}
    (hω : (ω : AlgebraicClosure K) ^ 2 + (ω : AlgebraicClosure K) + 1 = 0) :
    adjointGroup τ (AlgebraicClosure K) :=
  frameProd _ F (langP hω)

theorem adjointMap_frobK_langG (F : OrthFrame τ d) {ω : (AlgebraicClosure K)ˣ}
    (hω : (ω : AlgebraicClosure K) ^ 2 + (ω : AlgebraicClosure K) + 1 = 0) :
    adjointMap τ (frobK K) (langG F hω) =
      langG F hω * frameProd (AlgebraicClosure K) F (nSL 1) := by
  rw [langG, adjointMap_frameProd, map_langP hω (frobK K) (by rw [frobK_apply]),
    frameProd_mul]

theorem eq_one_of_monomial_of_frobK {m : ModGL τ (AlgebraicClosure K)}
    (hm : m ∈ monomialSubgroup τ (AlgebraicClosure K))
    (hρ : weylQuotientHom τ (AlgebraicClosure K) ⟨m, hm⟩ = 1)
    (hφ : Units.map (entrywiseHom (frobK K)) m = m) : m = 1 := by
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := AlgebraicClosure K)
  have hT : m ∈ torusGroup τ (AlgebraicClosure K) := by
    have h1 : (⟨m, hm⟩ : monomialSubgroup τ _) ∈ (weylQuotientHom τ (AlgebraicClosure K)).ker :=
      hρ
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have h0 : Units.map (entrywiseHom (frobK K)) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map (frobK K).toMonoidHom (a i) :=
    Units.ext (CFSG.LieType.Chevalley.entrywise_rootDiag (frobK K) a)
  have h1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (h0.symm.trans hφ)
  have h2 : ∀ i, a i = 1 := fun i => by
    have h3 := congrFun h1 i
    have h4 : Units.map (frobK K).toMonoidHom (a i) = a i ^ 2 :=
      Units.ext (by simp [frobK_apply])
    rw [h4] at h3
    have h5 : a i * a i = a i * 1 := by rw [mul_one, ← pow_two]; exact h3
    exact mul_left_cancel h5
  have h6 : a = 1 := funext h2
  rw [h6]
  exact rootDiagUnit_one

theorem frameProd_nSL_eq_canonicalRep (F : OrthFrame τ d)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v) :
    ∃ w : WeylGroup τ, (∀ v : Fin τ.rank → ℤ, w • v = -v) ∧
      ((frameProd (AlgebraicClosure K) F (nSL 1) : adjointGroup τ (AlgebraicClosure K)) :
        ModGL τ (AlgebraicClosure K)) = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
  obtain ⟨ω₀, hω₀⟩ := (coxeterSystem τ).wordProd_surjective
    (List.ofFn fun i => rootReflection (F.root i)).prod
  refine ⟨(coxeterSystem τ).wordProd ω₀, fun v => by rw [hω₀]; exact hw v, ?_⟩
  set L := AlgebraicClosure K with hL
  set n := frameProd L F (nSL 1) with hn
  obtain ⟨hnm, hnw⟩ := exists_frameProd_nSL_mem_monomial (L := L) F
  have hm := coe_nWord_mem_monomialSubgroup (K := L) ω₀
  set c := n * (nWord τ L ω₀)⁻¹ with hc
  have hcm : (c : ModGL τ L) ∈ monomialSubgroup τ L := mul_mem hnm (inv_mem hm)
  have hce : (⟨c, hcm⟩ : monomialSubgroup τ L) =
      ⟨_, hnm⟩ * (⟨_, hm⟩ : monomialSubgroup τ L)⁻¹ := rfl
  have hc1 : (c : ModGL τ L) = 1 := by
    refine eq_one_of_monomial_of_frobK hcm ?_ ?_
    · rw [hce, map_mul, map_inv, hnw, weylQuotientHom_nWord, hω₀, mul_inv_cancel]
    · have h1 : adjointMap τ (frobK K) n = n := by
        rw [hn, adjointMap_frameProd, map_nSL_one]
      have h2 := adjointMap_nWord (frobK K) (τ := τ) ω₀
      have h3 : adjointMap τ (frobK K) c = c := by
        rw [hc, map_mul, map_inv, h1, h2]
      have h4 := congrArg Subtype.val h3
      rw [coe_adjointMap] at h4
      exact h4
  have hnc : n = nWord τ L ω₀ := mul_inv_eq_one.mp (Subtype.ext hc1)
  rw [hnc, coe_nWord, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo]

theorem langG_frob (F : OrthFrame τ d) {ω : (AlgebraicClosure K)ˣ}
    (hω : (ω : AlgebraicClosure K) ^ 2 + (ω : AlgebraicClosure K) + 1 = 0)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v) :
    ∃ w : WeylGroup τ, (∀ v : Fin τ.rank → ℤ, w • v = -v) ∧
      Units.map (entrywiseHom (frobK K)) ((langG F hω : adjointGroup τ (AlgebraicClosure K)) :
        ModGL τ (AlgebraicClosure K)) =
      ((langG F hω : adjointGroup τ (AlgebraicClosure K)) : ModGL τ (AlgebraicClosure K)) *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
  obtain ⟨w, hwn, hnF⟩ := frameProd_nSL_eq_canonicalRep (K := K) F hw
  refine ⟨w, hwn, ?_⟩
  have h := congrArg Subtype.val (adjointMap_frobK_langG F hω)
  rw [coe_adjointMap, Subgroup.coe_mul, hnF] at h
  exact h

end Elt

end CFSG.StandardType.SmallExc

end
