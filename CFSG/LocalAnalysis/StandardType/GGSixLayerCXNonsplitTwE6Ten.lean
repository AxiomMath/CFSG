module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6TenData

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

namespace TwE6Nonsplit

section TenZpowers


theorem mem_zpowers_twE6_of_ten {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 10).eval ((2 ^ f : ℕ) : ℤ))
    (a b : twistedE6RootGroup K σ) (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) : b ∈ Subgroup.zpowers a := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc := (twE6_ten_data (ℓ := 2) Nat.prime_two hf K hK σ hσ hp hp5 hpf).1
  exact ExcNonsplit.mem_zpowers_of_pSubgroups_cyclic hp hcyc (orderOf_eq_prime ha ha1) hb hab

end TenZpowers

section TenMarking


theorem not_ggNbrClauseFiveMarking_of_isComponentOf_twE6_of_ten {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 10).eval ((2 ^ f : ℕ) : ℤ))
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    (a : twistedE6RootGroup K σ) (ha : orderOf a = p)
    (X : Subgroup (twistedE6RootGroup K σ))
    (hX : IsComponentOf X (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ)))) :
    ¬ GGNbrClauseFiveMarking p a X := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h4, ⟨e⟩⟩ :=
    twE6_ten_structure (ℓ := 2) hf K hK σ hσ hp hp5 hpf a ha X hX
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    rw [hf1] at h4
    norm_num at h4
  have hkcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact ExcNonsplit.not_ggNbrClauseFiveMarking_of_sl_two_centralizing hkcard hf2 hp hp2 hq1 hq2 e
    hX.1

end TenMarking

end TwE6Nonsplit

end CFSG.StandardType
