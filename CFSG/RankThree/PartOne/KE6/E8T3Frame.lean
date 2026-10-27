module

public import CFSG.RankThree.PartOne.KE6.E8T3Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley

theorem e8T3_frame {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (n : ModGL .E8 L)
    (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = e8T3We ε) :
    ∃ g0 : ModGL .E8 L, g0 ∈ adjointGroup .E8 L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .E8 K L).range) ∧
      ∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q →
        ∃ c : adjointGroup .E8 K, ∀ q ∈ Q, c * q * c⁻¹ ∈ subtorusImage (adjEmb .E8 K L) g0
          (twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hcard := natCard_e8T3Torus hε n hnm hnW hFr hℓq
  have hN : (e8T3D ε (Nat.card K)) ^ 4 ≠ 0 := pow_ne_zero 4 (e8T3D_ne_zero hε _)
  exact sigma_untwisted_sylow .E8 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC _ le_rfl hN
    hcard (e8T3_ordProj hε K hp hp3 hpf)

end CFSG.RankThree.PartOne.KE6
