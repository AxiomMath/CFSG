module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSp
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeEndNode

public section

namespace CFSG.StandardType

namespace LineL2

open Polynomial Matrix Multiplicative CoordSL CFSG.Assembly

section Gal

variable {K : Type} [Field K] [Finite K]

theorem neg_one_mem_galExp (hK : Nat.card K = 2) {g : K[X]} [Fact (Irreducible g)]
    (hζ : AdjoinRoot.root g ^ 3 = 1) : (-1 : (ZMod 3)ˣ) ∈ galExp g hζ := by
  let := Fintype.ofFinite K
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Algebra.IsAlgebraic K (AdjoinRoot g) := Algebra.IsAlgebraic.of_finite K (AdjoinRoot g)
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g), ?_⟩
  change AdjoinRoot.root g ^ Fintype.card K = _
  rw [← Nat.card_eq_fintype_card, hK]
  have h2 : (((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 := by decide
  rw [h2]

theorem exists_irreducible_factor_cyclotomic_three (K : Type) [Field K] :
    ∃ g : K[X], Irreducible g ∧ g ∣ cyclotomic 3 K := by
  have hne : ¬ IsUnit (cyclotomic 3 K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero 3 K),
      natDegree_cyclotomic, Nat.totient_prime Nat.prime_three]
    norm_num
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero 3 K)
  exact ⟨g, hg, hgd⟩

end Gal

section Move

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_normalizer_move (hK : Nat.card K = 2)
    {E : Subgroup (SpecialLinearGroup (Fin d) K)} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : SpecialLinearGroup (Fin d) K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    {Λ : Subgroup (SpecialLinearGroup (Fin d) K)} (hΛ : Λ ≤ E) (hΛc : Nat.card Λ = 3) :
    ∃ w ∈ Subgroup.normalizer (E : Set (SpecialLinearGroup (Fin d) K)),
      ∃ e ∈ Λ, w * e * w⁻¹ ∉ Λ := by
  classical
  have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_factor_cyclotomic_three K
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (root_isPrimitiveRoot Nat.prime_three hp3 hgd).pow_eq_one
  have hC : (rootMat g).det = 1 := det_rootMat Nat.prime_three hnsplit hp3 hgd
  have hCp : rootMat g ^ 3 = 1 := rootMat_pow_eq_one Nat.prime_three hp3 hgd
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g Nat.prime_three hp3 hgd
    (Set.range fun x : E => ((x : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact congrArg (fun z : SpecialLinearGroup (Fin d) K => (z : Matrix (Fin d) (Fin d) K))
        (TableB.IsElemAbelian.comm hE x.2 y.2))
    (by
      rintro _ ⟨x, rfl⟩
      have h1 := hE.2 x x.2
      rw [← Matrix.SpecialLinearGroup.coe_pow, h1, Matrix.SpecialLinearGroup.coe_one])
  set ι := frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp with hι
  have hEk : ∀ x ∈ E, ∃ k : Fin s → ℕ, x = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
    intro x hx
    obtain ⟨k, hk⟩ := hframe _ ⟨⟨x, hx⟩, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : x * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
    rw [← h1, mul_inv_cancel_right]
  have hcomm : ∀ (k k' : Fin s → ℕ),
      (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) * (A₀ * SLNS.nsSL ε hC k' * A₀⁻¹) =
        (A₀ * SLNS.nsSL ε hC k' * A₀⁻¹) * (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) := by
    intro k k'
    calc (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) * (A₀ * SLNS.nsSL ε hC k' * A₀⁻¹)
        = A₀ * (SLNS.nsSL ε hC k * SLNS.nsSL ε hC k') * A₀⁻¹ := by group
      _ = A₀ * (SLNS.nsSL ε hC k' * SLNS.nsSL ε hC k) * A₀⁻¹ := by rw [SLNS.nsSL_comm]
      _ = (A₀ * SLNS.nsSL ε hC k' * A₀⁻¹) * (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) := by group
  have hrange : ι.range = E := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      apply hsc
      · intro e he
        obtain ⟨k, rfl⟩ := hEk e he
        rw [← ofAdd_toAdd a, hι, frameHom_apply]
        exact (hcomm k _).symm
      · exact frameHom_pow_p _ _ _ _ _ a
    · intro x hx
      obtain ⟨k, rfl⟩ := hEk x hx
      refine ⟨ofAdd fun i => (k i : ZMod 3), ?_⟩
      rw [hι, frameHom_natCast]
      rfl
  have hmove : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod 3)ˣ),
      (∀ i, η i ∈ galExp g hζ) → ∃ w ∈ Subgroup.normalizer (E : Set _), ∀ t : Fin s → ZMod 3,
        w⁻¹ * ι (ofAdd t) * w = ι (ofAdd fun i => (η i : ZMod 3) * t (π i)) := by
    intro π η hη
    obtain ⟨M, hM⟩ := exists_conj_frameHom g (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε
      hC hCp hζ π η hη
    exact ⟨SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ M,
      hrange ▸ mem_normalizer_range_of_conj π η hM, hM⟩
  by_contra hcon
  push Not at hcon
  set Φ := MulEquiv.funMultiplicative (Fin s) (ZMod 3) with hΦ
  set ι₀ : (Fin s → Multiplicative (ZMod 3)) →* SpecialLinearGroup (Fin d) K :=
    ι.comp Φ.symm.toMonoidHom with hι₀
  have hι₀apply : ∀ f, ι₀ f = ι (ofAdd fun i => toAdd (f i)) := fun f => rfl
  have hrange₀ : ι₀.range = E := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨Φ.symm f, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Φ a, by rw [hι₀apply]; simp [hΦ]⟩
  set F : Subgroup (Fin s → Multiplicative (ZMod 3)) := Λ.comap ι₀ with hF
  have hmemF : ∀ f, f ∈ F ↔ ι₀ f ∈ Λ := fun f => Iff.rfl
  have hsgn : ∀ i, ∀ f ∈ F, Function.update f i (f i)⁻¹ ∈ F := by
    intro i f hf
    obtain ⟨w, hwN, hw⟩ := hmove 1 (fun j => if j = i then -1 else 1) (fun j => by
      by_cases hj : j = i
      · simp only [hj, if_true]
        exact neg_one_mem_galExp hK hζ
      · simp only [hj, if_false]
        exact (galExp g hζ).one_mem)
    have h1 := hw fun j => toAdd (f j)
    have h2 : ι₀ (Function.update f i (f i)⁻¹) = w⁻¹ * ι₀ f * w := by
      rw [hι₀apply, hι₀apply, h1]
      congr 2
      funext j
      by_cases hj : j = i
      · subst hj
        simp
        rfl
      · simp [Function.update_of_ne hj, hj]
    rw [hmemF, h2]
    have := hcon w⁻¹ (Subgroup.inv_mem _ hwN) (ι₀ f) hf
    simpa using this
  have hperm : ∀ σ : Equiv.Perm (Fin s), ∀ f ∈ F, f ∘ ⇑σ⁻¹ ∈ F := by
    intro σ f hf
    obtain ⟨w, hwN, hw⟩ := hmove σ⁻¹ (fun _ => 1) (fun _ => (galExp g hζ).one_mem)
    have h1 := hw fun j => toAdd (f j)
    have h2 : ι₀ (f ∘ ⇑σ⁻¹) = w⁻¹ * ι₀ f * w := by
      rw [hι₀apply, hι₀apply, h1]
      congr 2
      funext j
      simp
    rw [hmemF, h2]
    have := hcon w⁻¹ (Subgroup.inv_mem _ hwN) (ι₀ f) hf
    simpa using this
  rcases NbrSp.eq_bot_or_eq_top_of_signed Nat.prime_three (by norm_num) F hsgn hperm with
    hbot | htop
  ·
    have hΛbot : Λ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨f, rfl⟩ : x ∈ ι₀.range := hrange₀ ▸ hΛ hx
      have hfF : f ∈ F := hx
      rw [hbot, Subgroup.mem_bot] at hfF
      rw [hfF, map_one]
      exact Subgroup.one_mem _
    rw [hΛbot, Subgroup.card_bot] at hΛc
    omega
  ·
    have hEΛ : E ≤ Λ := by
      intro x hx
      obtain ⟨f, rfl⟩ : x ∈ ι₀.range := hrange₀ ▸ hx
      have hfF : f ∈ F := htop ▸ Subgroup.mem_top f
      exact hfF
    have := Subgroup.card_le_of_le hEΛ
    rw [hΛc] at this
    omega

end Move

end LineL2

end CFSG.StandardType

end
