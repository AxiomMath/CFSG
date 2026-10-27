module

public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KE6.Phi6Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_untwisted_sylow subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix

theorem e6_six_frame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ g0 : ModGL .E6 L, g0 ∈ adjointGroup .E6 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi6N L ∧
      (∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .E6 K L).range) ∧
      ∀ Q : Subgroup (adjointGroup .E6 K), IsPGroup p Q → ∃ c : adjointGroup .E6 K, ∀ y ∈ Q,
        g0⁻¹ * adjEmb .E6 K L (c * y * c⁻¹) * g0 ∈
          twistedTorus (phi6N L) (iterateFrobenius L ℓ f) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hq0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [hK, Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hTcard, -⟩ := natCard_phi6Torus (L := L) hFr hq0
  have hN : ((Nat.card K ^ 2 - Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + Nat.card K + 1) : ℕ) ≠
      0 := by positivity
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E6 3 (Or.inl ⟨rfl, rfl⟩) K hf
    hK L hp hp3 (phi6N L) (canonicalRep_mem_adjointGroup _ L _) (twistedTorus (phi6N L) Fr)
    le_rfl hN hTcard (e6Six_ordProj K hp hp3 hpq)
  refine ⟨g0, hg0C, hg0, hperf, fun Q hQ => ?_⟩
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact ⟨c, fun y hy => (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)⟩

end CFSG.RankThree.PartOne.KE6
