module

public import CFSG.RankThree.PartOne.S15K.PSylowSL
public import CFSG.RankThree.PartOne.S15K.PSylowSp
public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

theorem eq_one_of_two_pow_eq_one {R : Type*} [CommRing R] [CharP R 2] [IsReduced R] {u : Rˣ} {k : ℕ}
    (h : u ^ (2 ^ k) = 1) : u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ((u : R) - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow (p := 2), one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  exact Units.ext (sub_eq_zero.1 (IsReduced.eq_zero _ ⟨_, h1⟩))

section Paired

variable {r : ℕ} {K : Type} [Field K]

theorem psylowSub_specialBlock_paired {ℓ f p : ℕ} [CharP K 2] (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (hP : SpPairedBlock ℓ f p x h) (hm : ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) :
    PSylowSub p (specialBlock (spForm r K) (spLin r K x) (h : K[X])) := by
  obtain ⟨φ₀, hφ₀, -⟩ := hP.factor
  let φ := (spOrbitEquiv x rfl).trans φ₀
  have hφ : ∀ (g : orbitFactor (spForm r K) (spLin r K x) (h : K[X])) (v : Fin r ⊕ Fin r → K)
      (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (φ g) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
          Module.End K (Fin r ⊕ Fin r → K)) v := fun g v hv => by
    rw [MulEquiv.trans_apply, hφ₀, spEnd_orbitEquiv]
  have hspec := specialBlock_eq_kerImage (B := spForm r K) (x := spLin r K x) (a := h) φ
    (MonoidHom.id _) hφ
  rw [MonoidHom.comp_id] at hspec
  have : CharP (AdjoinRoot (h : K[X])) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (h : K[X]))).injective 2
  have hζ' : IsPrimitiveRoot (algebraMap K (AdjoinRoot (h : K[X])) ζ) p :=
    hζ.map_of_injective (algebraMap K (AdjoinRoot (h : K[X]))).injective
  obtain ⟨e₁⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det
    (E := AdjoinRoot (h : K[X])) (W := primaryComponent (spEnd x) (h : K[X]))
  obtain ⟨e₂⟩ := nonempty_kerImage_mulEquiv (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) φ
    (blockGLDet (spEnd x) (h : K[X]))
  have e₃ : ↥(kerImage (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) φ
      (blockGLDet (spEnd x) (h : K[X]))) ≃*
      ↥(specialBlock (spForm r K) (spLin r K x) (h : K[X])) :=
    MulEquiv.subgroupCongr hspec.symm
  exact PSylowSub.of_mulEquiv ((e₁.trans e₂.symm).trans e₃) (psylowSub_specialLinear hp hζ' hm)

end Paired

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem psylowSub_specialBlock_fixed {ℓ f p : ℕ} [CharP K 2] (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {x : StatedSp r K} (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) :
    PSylowSub p (specialBlock (spForm r K) (spLin r K x) (X - 1)) := by
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hO : ({(X - 1 : K[X]), reciprocalPolynomial (X - 1 : K[X])} : Set K[X]) = {X - 1} := by
    rw [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  let Φ := (spOrbitEquiv x hO).trans φ
  have hsep : ∀ v : primaryComponent (spEnd x) (X - 1), v ≠ 0 →
      ∃ u, ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))) v u ≠ 0 := by
    intro v hv
    by_contra hcon
    push Not at hcon
    exact hv (blocks.fixed_nondegenerate.1 v hcon)
  have hSp := psylowSub_sesqUnitary_alt hp hζ
    ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))) (fun z => (spForm_isAlt (r := r) (K := K)).self_eq_zero (z : Fin r ⊕ Fin r → K)) hsep
  have hTop := hSp.top_of
  have hOrb : PSylowSub p (orbitFactor (spForm r K) (spLin r K x) (X - 1)) :=
    PSylowSub.of_mulEquiv Φ.symm hTop
  refine hOrb.of_le specialBlock_le_orbitFactor ?_
  intro g hg k hk
  refine mem_specialBlock.2 ⟨hg, orbitFactor_le_gl_centralizer hg, ?_⟩
  have : Fact (Irreducible (X - 1 : K[X])) := ⟨by simpa using irreducible_X_sub_C (1 : K)⟩
  have : CharP (AdjoinRoot (X - 1 : K[X])) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (X - 1 : K[X]))).injective 2
  have hgc : g ∈ gl_centralizer (spLin r K x) := orbitFactor_le_gl_centralizer hg
  have hpow : (⟨g, hgc⟩ : gl_centralizer (spLin r K x)) ^ (2 ^ k) = 1 :=
    Subtype.ext (by simpa using hk)
  have h1 : blockDetHom (spLin r K x) (X - 1) ⟨g, hgc⟩ ^ (2 ^ k) = 1 := by
    rw [← map_pow, hpow, map_one]
  exact eq_one_of_two_pow_eq_one h1

theorem psylowSub_spBlockGSp {ℓ f p : ℕ} [NeZero r] [CharP K 2] (hp : p.Prime) (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hℓf : 0 < ℓ ^ f) (hpq : p ∣ ℓ ^ f - 1)
    (hm : ∀ h : primaryFactors (spEnd x), ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]))
    (h : primaryFactors (spEnd x)) : PSylowSub p (spBlockGSp x (h : K[X])) := by
  have hsb : PSylowSub p (specialBlock (spForm r K) (spLin r K x) (h : K[X])) := by
    by_cases h1 : (h : K[X]) = X - 1
    · rw [h1]
      exact psylowSub_specialBlock_fixed hp hζ blocks (h1 ▸ h.2)
    · by_cases h2 : reciprocalPolynomial (h : K[X]) = h
      · obtain ⟨d, -, hpd, -⟩ := (blocks.selfDual h h1 h2).exists_half
        exact (false_of_dvd_pow_add_one hp5 hℓf hpq hpd).elim
      · exact psylowSub_specialBlock_paired hp hζ (blocks.paired h (Ne.symm h2)) (hm h)
  exact PSylowSub.of_map (gspLin r K) gspLin_injective (by rw [map_spBlockGSp]; exact hsb)

end Fixed

end CFSG.RankThree.PartOne.S15K
