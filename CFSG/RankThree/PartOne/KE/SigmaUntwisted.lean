module

public import CFSG.RankThree.PartOne.KE.SigmaMain
public import CFSG.RankThree.PartOne.KE.A1Untwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem sigma_untwisted_data (τ : Tag) (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hordW : ¬ p ∣ Nat.card (WeylGroup τ))
    (n : ModGL τ L) (hnC : n ∈ adjointGroup τ L) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (hZcyc : IsCyclic (subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) S))
    {N : ℕ} (hN : N ≠ 0)
    (hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) S) = N)
    (hord : p ^ (Nat.card (adjointGroup τ K)).factorization p = p ^ N.factorization p)
    (hkerZ : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a ∈ subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) S →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ S) :
    (∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q → IsCyclic Q) ∧
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL τ L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan τ L S) →
        (∀ i, P i ≤ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) →
        (∀ i, P i ≤ adjointGroup τ L) →
        (∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S,
          y ∈ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S,
          y ∈ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
          (∀ i, ∀ u ∈ P i, y * u = u * y) →
          y ∈ subtorusSigma n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) S) →
        ∀ x : adjointGroup τ K, orderOf x = p →
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup τ K))), V.Normal →
            Group.IsSolvable V → IsCyclic V := by
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
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hιC : ∀ y, ι y ∈ adjointGroup τ L := fun y => baseChangeGL_mem_adjointGroup _ y.2
  have hcomp : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun c => by
    change Fr (algebraMap K L c) = algebraMap K L c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hιΦ : ∀ y, Units.map (entrywiseHom Fr) (ι y) = ι y := fun y => by
    have e : Units.map (entrywiseHom Fr) (ι y) = baseChangeGL Fr (ι y) := Units.ext rfl
    rw [e]
    change baseChangeGL Fr (baseChangeGL (algebraMap K L) (y : ModGL τ K)) =
      baseChangeGL (algebraMap K L) (y : ModGL τ K)
    rw [baseChangeGL_baseChangeGL, hcomp]
  have hrat3 : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ι.range.relIndex X ∣ d ∧
        (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range) ∧
        ∀ P : Subgroup (ModGL τ L), P ≤ X → ⁅P, P⁆ = P → P ≤ ι.range := by
    intro X _ hXC hXF
    rw [hrange]
    have : Algebra.IsAlgebraic K L := inferInstance
    exact finite_fixed_subgroup_rational_perfect d hτ Fr hFr X hXC hXF
  have hrat2 : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ι.range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  have hZle : subtorusSigma n (Units.map (entrywiseHom Fr)) S ≤
      twistedTorusOf n (Units.map (entrywiseHom Fr)) := subtorusSigma_le_twistedTorusOf _ _ _
  obtain ⟨-, -, -, -, hpcyc, hconj⟩ := sylow_conjugacy_of_subtorus d ι hι
    (Units.map (entrywiseHom Fr)) n g0 hg0C hg0 hp hp3 hN hrat2 _ hZle hZcyc hZcard hord
  refine ⟨hpcyc, fun P hPfin hPq hPQ hPR hPadj hPnorm hPcent => ?_⟩
  exact sigma_solvable_normal_cyclic ι hι hιC (Units.map (entrywiseHom Fr)) hιΦ n g0 hg0C hg0
    (fun P hP hPC hPF hPp => (hrat3 P hPC hPF).2.2 P le_rfl hPp) hp hordW hS hSn (hZ := hZcyc)
    hconj hkerZ P hPfin hPq hPQ hPR hPadj hPnorm hPcent

end CFSG.RankThree.PartOne.KE
