module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearCentralCard
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGCoxeterPrimeSquare
public import CFSG.Mathlib.GroupTheory.Automorphism.Translations
public import CFSG.Mathlib.GroupTheory.PrimeOrderPair
public import CFSG.LocalAnalysis.StandardType.GGPGLBlockFrobeniusWord
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTwoShears
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public meta import Lean.Elab.Tactic.Omega

public section

namespace CFSG.StandardType.TypeA

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped BigOperators

theorem false_of_central_block_model_four_prime
    {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1) (hdp : d = 4 * p)
    {L : Type} [Group L] [Finite L] {ψ : L →* projectiveSL d K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) {A : Subgroup (MulAut L)} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ f ∈ Set.range (conjAut d K), ∀ l : L, f (ψ l) = ψ (a l))
    (h3 : p ^ 3 ≤ Nat.card A)
    (hcent : ∀ x ∈ (inducedSub ψ A).comap (conjAut d K), x ^ p = 1 →
      ∀ y ∈ (inducedSub ψ A).comap (conjAut d K), y * x = x * y)
    (hnt : ¬ PGLTor.IsToral ((inducedSub ψ A).comap (conjAut d K)))
    (D : PGLTor.CentralBlockModel p ((inducedSub ψ A).comap (conjAut d K)))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive A ≃+ V) (φ : Λ → MulAut A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have : Finite (MulAut (projectiveSL d K)) :=
    Finite.of_injective (fun f : MulAut (projectiveSL d K) =>
      (f : projectiveSL d K → projectiveSL d K))
      DFunLike.coe_injective
  set X := inducedSub ψ A with hX
  set G := X.comap (conjAut d K) with hGdef
  have hXA : IsElemAbelian p X := isElemAbelian_inducedSub hψ hA
  have hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨f, hfI, hf⟩ := hAI a ha
    exact induced_unique ψ hψ hf hxa ▸ hfI
  have hcardX : Nat.card X = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨f, -, hf⟩ := hAI a ha
      exact ⟨f, hf⟩)
  have hG : PGLTor.IsProjElem p G := isProjElem_comap hd0 hXA
  have hcardG : Nat.card G = Nat.card A * (Nat.card K - 1) := by
    rw [hGdef, card_comap_eq hd0 hXI, hcardX]
  have hcard : p ^ 3 * (Nat.card K - 1) ≤ Nat.card G := by
    rw [hcardG]
    exact Nat.mul_le_mul_right _ h3
  have hupper : Nat.card A ≤ p ^ 4 := by
    simpa only [hdp, Nat.mul_div_cancel _ hp.pos] using
      card_actor_le_of_central_nontoral_lifts hp hp2 hpK hd0 hψ hker hperf hA hAI hcent hnt
  let Y := D.kernel.map (conjAut d K)
  have hYX : Y ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact D.kernel_le hy
  have hYpow : ∀ b : Y, b ^ p = 1 := fun b => Subtype.ext (hXA.2 _ (hYX b.2))
  have hYcard : p < Nat.card Y := by
    have hsq := card_kernel_image_ge_sq_of_cube hp hd0 hG D hcard
    have hp' : p < p ^ 2 := by nlinarith [hp.two_le]
    exact hp'.trans_le hsq
  obtain ⟨b, c, hb, hc, hcb⟩ :=
    CFSG.GroupTheory.exists_prime_order_pair_of_card_gt hYpow hYcard
  obtain ⟨yb, hyb, heyb⟩ := Subgroup.mem_map.mp b.2
  obtain ⟨yc, hyc, heyc⟩ := Subgroup.mem_map.mp c.2
  have hquot := QuotMove.isScalarQuot_PSL (K := K) hd0
  have hscalar : ∀ u : Kˣ, conjAut d K (GeneralLinearGroup.scalar (Fin d) u) = 1 :=
    fun u => hquot.map_scalar u
  have hcast := PGLTor.isProjElem_card_cast_ne_zero hp hp2 hG
  obtain ⟨E₁, δ₁, hδ₁, hδ₁p, hδ₁b, hE₁fix, hE₁x⟩ :=
    D.exists_SL_projected_kernel_word hp hpK hG hcast (conjAut d K) hscalar hyb
  obtain ⟨E₂, δ₂, hδ₂, hδ₂p, hδ₂c, hE₂fix, hE₂x⟩ :=
    D.exists_SL_projected_kernel_word hp hpK hG hcast (conjAut d K) hscalar hyc
  have hδ₁X : conjAut d K δ₁ ∈ X := D.kernel_le hδ₁
  have hδ₂X : conjAut d K δ₂ ∈ X := D.kernel_le hδ₂
  have hind : ∀ i k : ℕ, conjAut d K δ₁ ^ i * conjAut d K δ₂ ^ k = 1 → p ∣ i ∧ p ∣ k := by
    intro i k he
    rw [hδ₁b, heyb, hδ₂c, heyc] at he
    exact CFSG.GroupTheory.dvd_exponents_of_pow_mul_pow_eq_one_of_not_mem_zpowers
      hb hc hcb (Subtype.ext he)
  let S := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →* GL (Fin d) K).range
  let e₁ : S := ⟨SpecialLinearGroup.toGL E₁, E₁, rfl⟩
  let e₂ : S := ⟨SpecialLinearGroup.toGL E₂, E₂, rfl⟩
  let x₀ : (⊤ : Subgroup (GL (Fin d) K)) := ⟨D.primitive, Subgroup.mem_top _⟩
  let d₁ : (⊤ : Subgroup (GL (Fin d) K)) := ⟨δ₁, Subgroup.mem_top _⟩
  let d₂ : (⊤ : Subgroup (GL (Fin d) K)) := ⟨δ₂, Subgroup.mem_top _⟩
  refine QuotMove.false_of_two_shears hquot hp hp5 hψ hker hperf hA ?_ hupper
    (x₀ := x₀) D.primitive.2 D.primitive_pow D.scalar_not_pow e₁ e₂ d₁ d₂
    hδ₁X hδ₂X hδ₁p hδ₂p hind hE₁x hE₂x ?_ ?_ hM hC ι φ h α hpair hlin hgen
  · intro a ha
    obtain ⟨f, ⟨z, rfl⟩, hf⟩ := hAI a ha
    exact ⟨⟨z, Subgroup.mem_top _⟩, hf⟩
  · intro y hy hyp
    have hyker : (y : GL (Fin d) K) ∈ D.kernel :=
      (D.kernel_mem_iff y hy).mpr ⟨1, by simpa using hyp⟩
    exact (hE₁fix y hyker).eq
  · intro y hy hyp
    have hyker : (y : GL (Fin d) K) ∈ D.kernel :=
      (D.kernel_mem_iff y hy).mpr ⟨1, by simpa using hyp⟩
    exact (hE₂fix y hyker).eq

theorem ggTorusWNormSC_four_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hdp : d = 4 * p) :
    GGTorusWNormSC p (projectiveSL d K) (Set.range (conjAut d K)) := by
  have hp2 : p ≠ 2 := by omega
  have hd : 5 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    hM hC hpair hlin hgen s hs
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set G := (inducedSub ψ A).comap (conjAut d K) with hGdef
  have hG : PGLTor.IsProjElem p G := isProjElem_comap hd0 (isElemAbelian_inducedSub hψ hA)
  by_cases hcent : ∀ x ∈ G, x ^ p = 1 → ∀ y ∈ G, y * x = x * y
  · by_cases ht : PGLTor.IsToral G
    · obtain ⟨A₀, hA₀⟩ := ht
      have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
        (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
          (Or.inl (by omega))).commutator_eq_top
      obtain ⟨π, hπs, hπker, hdiag⟩ := TypeANbrDvd.exists_actsDiag_model hperfSL
        (slHasSections_of_five_le hd) hψ hker hperf hAI (A₀ := A₀) fun B hB => hA₀ B hB
      exact ggWNormConcl_of_linear_diagonal hp hp2 hpK hd hπs hπker hA h3 hsc hdiag
        hM hC ι φ h α hpair hlin hgen hs
    · exfalso
      obtain ⟨D⟩ := (PGLTor.toral_or_exists_centralBlockModel hp hp2 hpK hG hcent).resolve_left ht
      exact false_of_central_block_model_four_prime hp5 hpK hdp hψ hker hperf hA hAI h3
        hcent ht D hM hC ι φ h α hpair hlin hgen
  · exfalso
    push Not at hcent
    obtain ⟨x₀, hx₀G, hx₀p, y₀, hy₀G, hne⟩ := hcent
    have hu₀1 : PGLTor.commChar hG hx₀G ⟨y₀, hy₀G⟩ ≠ 1 := fun h1 =>
      hne ((PGLTor.commChar_eq_one_iff hG hx₀G ⟨y₀, hy₀G⟩).mp h1).symm
    have hdiag : ∀ i, α i (h i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    exact false_of_noncomm_lifts hp hp5 hpK (hdp ▸ dvd_mul_left p 4) hd0 hψ hker hperf
      hA hAI hx₀G hy₀G hx₀p (PGLTor.commChar_spec hG hx₀G ⟨y₀, hy₀G⟩) hu₀1
      (PGLTor.commChar_pow_eq_one hG hx₀G ⟨y₀, hy₀G⟩) ι φ h α hdiag hlin hgen

end CFSG.StandardType.TypeA

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorusWNormSC_linear_four_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1) (hdp : d = 4 * p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) :=
  ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_four_prime hp hp5 hpK hdp)

theorem largeEvenLabelAll_wnorm_linear_four_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : lab.tag = .A)
    (hdp : lab.rank + 1 = 4 * p) (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hdp hpq ⊢
  subst tag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ GGTorusWNormSC p R I)
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_four_prime hp hp5 (by rwa [hK]) hdp

end CFSG.StandardType
