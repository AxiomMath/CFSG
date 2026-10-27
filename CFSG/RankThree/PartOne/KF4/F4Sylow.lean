module

public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem sigma_untwisted_sylow_F4
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (n : ModGL .F4 L)
    (hnC : n ∈ adjointGroup .F4 L) (Z : Subgroup (ModGL .F4 L))
    (hZ : Z ≤ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {N : ℕ} (hN : N ≠ 0) (hZcard : Nat.card Z = N)
    (hord : p ^ (Nat.card (adjointGroup .F4 K)).factorization p = p ^ N.factorization p) :
    ∃ g0 : ModGL .F4 L, g0 ∈ adjointGroup .F4 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL .F4 L), Finite P → P ≤ adjointGroup .F4 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .F4 K L).range) ∧
      ∀ Q : Subgroup (adjointGroup .F4 K), IsPGroup p Q →
        ∃ c : adjointGroup .F4 K, ∀ q ∈ Q,
          c * q * c⁻¹ ∈ subtorusImage (adjEmb .F4 K L) g0 Z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL .F4 K) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen .F4 K hf L n hnC
  have hrat3 : ∀ (X : Subgroup (ModGL .F4 L)) [Finite X], X ≤ adjointGroup .F4 L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → (adjEmb .F4 K L).range.relIndex X ∣ 1 ∧
        (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL .F4 L), P ≤ X → IsPGroup p P →
          P ≤ (adjEmb .F4 K L).range) ∧
        ∀ P : Subgroup (ModGL .F4 L), P ≤ X → ⁅P, P⁆ = P → P ≤ (adjEmb .F4 K L).range := by
    intro X _ hXC hXF
    have hXle : X ≤ (adjEmb .F4 K L).range := by
      rw [adjEmb_range]
      intro x hx
      have : Algebra.IsAlgebraic K L := inferInstance
      rw [← (G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl) K L Fr hFr).1]
      exact ⟨hXC hx, hXF x hx⟩
    exact ⟨Nat.dvd_one.2 (Subgroup.relIndex_eq_one.2 hXle),
      fun _ _ _ P hPX _ => hPX.trans hXle, fun P hPX _ => hPX.trans hXle⟩
  have hrat2 : ∀ (X : Subgroup (ModGL .F4 L)) [Finite X], X ≤ adjointGroup .F4 L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → (adjEmb .F4 K L).range.relIndex X ∣ 1 ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL .F4 L), P ≤ X → IsPGroup p P →
          P ≤ (adjEmb .F4 K L).range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (adjEmb .F4 K L) adjEmb_injective
    (Units.map (entrywiseHom Fr)) n g0 hg0C hg0 hp hp3 hN hrat2 Z hZ hZcard hord
  exact ⟨g0, hg0C, hg0, fun P hP hPC hPF hPperf => (hrat3 P hPC hPF).2.2 P le_rfl hPperf, hconj⟩

end CFSG.RankThree.PartOne.KF4
