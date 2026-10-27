module

public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.A1Untwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

@[expose] def adjEmb (τ : Tag) (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] :
    adjointGroup τ K →* ModGL τ L :=
  (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype

variable {τ : Tag} {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

theorem adjEmb_apply (y : adjointGroup τ K) :
    adjEmb τ K L y = baseChangeGL (algebraMap K L) (y : ModGL τ K) :=
  rfl

theorem adjEmb_injective : Function.Injective (adjEmb τ K L) :=
  (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)

theorem adjEmb_mem (y : adjointGroup τ K) : adjEmb τ K L y ∈ adjointGroup τ L :=
  baseChangeGL_mem_adjointGroup _ y.2

theorem adjEmb_range :
    (adjEmb τ K L).range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem adjEmb_frobenius [Finite K] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (y : adjointGroup τ K) :
    Units.map (entrywiseHom Fr) (adjEmb τ K L y) = adjEmb τ K L y := by
  have : Fintype K := Fintype.ofFinite K
  have hcomp : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun c => by
    change Fr (algebraMap K L c) = algebraMap K L c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have e : Units.map (entrywiseHom Fr) (adjEmb τ K L y) = baseChangeGL Fr (adjEmb τ K L y) :=
    Units.ext rfl
  rw [e]
  change baseChangeGL Fr (baseChangeGL (algebraMap K L) (y : ModGL τ K)) =
    baseChangeGL (algebraMap K L) (y : ModGL τ K)
  rw [baseChangeGL_baseChangeGL, hcomp]

theorem sigma_untwisted_sylow (τ : Tag) (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (n : ModGL τ L) (hnC : n ∈ adjointGroup τ L)
    (Z : Subgroup (ModGL τ L))
    (hZ : Z ≤ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {N : ℕ} (hN : N ≠ 0) (hZcard : Nat.card Z = N)
    (hord : p ^ (Nat.card (adjointGroup τ K)).factorization p = p ^ N.factorization p) :
    ∃ g0 : ModGL τ L, g0 ∈ adjointGroup τ L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb τ K L).range) ∧
      ∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q →
        ∃ c : adjointGroup τ K, ∀ q ∈ Q, c * q * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g0 Z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen τ K hf L n hnC
  have hrat3 : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → (adjEmb τ K L).range.relIndex X ∣ d ∧
        (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ (adjEmb τ K L).range) ∧
        ∀ P : Subgroup (ModGL τ L), P ≤ X → ⁅P, P⁆ = P → P ≤ (adjEmb τ K L).range := by
    intro X _ hXC hXF
    rw [adjEmb_range]
    have : Algebra.IsAlgebraic K L := inferInstance
    exact finite_fixed_subgroup_rational_perfect d hτ Fr hFr X hXC hXF
  have hrat2 : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → (adjEmb τ K L).range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ (adjEmb τ K L).range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen d (adjEmb τ K L) adjEmb_injective
    (Units.map (entrywiseHom Fr)) n g0 hg0C hg0 hp hp3 hN hrat2 Z hZ hZcard hord
  exact ⟨g0, hg0C, hg0, fun P hP hPC hPF hPperf => (hrat3 P hPC hPF).2.2 P le_rfl hPperf, hconj⟩

end CFSG.RankThree.PartOne.KE
