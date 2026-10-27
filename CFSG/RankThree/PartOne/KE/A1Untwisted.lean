module

public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem lang_conjugator_gen (τ : Tag) (K : Type) [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL τ L) (hn : n ∈ adjointGroup τ L) :
    ∃ g0 : ModGL τ L, g0 ∈ adjointGroup τ L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).1 τ
  obtain ⟨g, hg⟩ := hLang ⟨n, hn⟩
  refine ⟨(g : ModGL τ L), g.2, ?_⟩
  rw [← hS g]
  have h1 : S g = g * ⟨n, hn⟩ := by rw [hg, mul_inv_cancel_left]
  rw [h1]
  rfl

theorem a1_untwisted_data (τ : Tag) (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hordW : ¬ p ∣ Nat.card (WeylGroup τ))
    (n : ModGL τ L) (hnC : n ∈ adjointGroup τ L) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hZcyc : IsCyclic (subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) θ))
    {N : ℕ} (hN : N ≠ 0)
    (hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) θ) = N)
    (hord : p ^ (Nat.card (adjointGroup τ K)).factorization p = p ^ N.factorization p)
    (hkerZ : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a ∈ subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) θ →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ {θ, -θ}) :
    (∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q → IsCyclic Q) ∧
      ∀ (S : Subgroup (SL2 L)) [Finite S],
        (∀ B : SL2 L, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f))
            (rootSL2 τ L θ B) * n⁻¹ = rootSL2 τ L θ B ↔ B ∈ S) →
        CFSG.IsQuasisimple S →
        Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
          Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
            (Matrix.GeneralLinearGroup.scalar (Fin 2)).range →
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
  have hZle : subtorusA1 n (Units.map (entrywiseHom Fr)) θ ≤
      twistedTorusOf n (Units.map (entrywiseHom Fr)) := subtorusA1_le_twistedTorusOf _ _ _
  obtain ⟨-, -, -, -, hpcyc, hconj⟩ := sylow_conjugacy_of_subtorus d ι hι
    (Units.map (entrywiseHom Fr)) n g0 hg0C hg0 hp hp3 hN hrat2 _ hZle hZcyc hZcard hord
  refine ⟨hpcyc, fun S _ hS1 hS2 hS3 => ?_⟩
  exact a1_solvable_normal_cyclic ι hι hιC (Units.map (entrywiseHom Fr)) hιΦ n g0 hg0C hg0
    (fun P hP hPC hPF hPp => (hrat3 P hPC hPF).2.2 P le_rfl hPp) hp hordW hθ (hZ := hZcyc) hconj
    hkerZ S hS1 hS2 hS3

end CFSG.RankThree.PartOne.KE
