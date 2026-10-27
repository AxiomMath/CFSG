module

public import CFSG.Permutation.FiveTransitive.StabilizerSylowFusion
public import CFSG.Permutation.FiveTransitive.UniqueSquareNormalizer

public section

namespace CFSG

namespace FiveTransitive.CentralizerSylowFusion

private theorem eq_of_normalizer_centralizes
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (q z : G) (hconj : ∃ g : G, g * q * g⁻¹ = z)
    (P : Sylow p (Subgroup.centralizer ({q} : Set G)))
    (hPz : (P : Subgroup (Subgroup.centralizer ({q} : Set G))).map
      (Subgroup.centralizer ({q} : Set G)).subtype ≤
        Subgroup.centralizer ({z} : Set G))
    (hNz : ∀ g : G, g ∈ Subgroup.normalizer
      (((P : Subgroup (Subgroup.centralizer ({q} : Set G))).map
        (Subgroup.centralizer ({q} : Set G)).subtype) : Set G) →
      g * z = z * g) : q = z := by
  let : MulAction G G := MulAction.compHom G ConjAct.toConjAct.toMonoidHom
  have hc (x : G) : MulAction.stabilizer G x = Subgroup.centralizer ({x} : Set G) := by
    ext g
    change g * x * g⁻¹ = x ↔ g ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  revert P
  rw [← hc q, ← hc z]
  intro P hPz hNz
  apply StabilizerSylowFusion.eq_of_normalizer_fixes q z hconj P hPz
  intro g hg
  change g * z * g⁻¹ = z
  exact mul_inv_eq_iff_eq_mul.mpr (hNz g hg)

theorem eq_square_of_unique_square
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (q a : G) (hconj : ∃ g : G, g * q * g⁻¹ = a ^ 2)
    (P : Sylow p (Subgroup.centralizer ({q} : Set G)))
    (ha : a ∈ (P : Subgroup (Subgroup.centralizer ({q} : Set G))).map
      (Subgroup.centralizer ({q} : Set G)).subtype)
    (ha2 : a ^ 2 ≠ 1)
    (hsquares : ∀ x : G, x ∈
      (P : Subgroup (Subgroup.centralizer ({q} : Set G))).map
        (Subgroup.centralizer ({q} : Set G)).subtype →
      x ^ 2 = 1 ∨ x ^ 2 = a ^ 2) : q = a ^ 2 := by
  exact eq_of_normalizer_centralizes q (a ^ 2) hconj P
    (UniqueSquareNormalizer.le_centralizer _ a ha ha2 hsquares)
    (UniqueSquareNormalizer.normalizer_centralizes _ a ha ha2 hsquares)

end FiveTransitive.CentralizerSylowFusion

end CFSG
