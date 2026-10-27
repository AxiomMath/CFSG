module

public import CFSG.LieType.Universal.Catalog
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal

@[expose] def RCKLemmaHTI (M : LieUniversal) (β : Fin M.D.rank → ℤ) : Prop :=
  ∀ x ∈ M.D.rootGroup β, x ≠ 1 → ∀ k : M.K, k * x * k⁻¹ ∈ M.D.rootGroup β →
    k ∈ Subgroup.normalizer (M.D.rootGroup β : Set M.K)

@[expose] def RCKLemmaHLevi (M : LieUniversal) (β : Fin M.D.rank → ℤ) : Prop :=
  ∀ x ∈ M.D.rootGroup β, x ≠ 1 →
    Subgroup.normalizer (M.D.rootGroup β : Set M.K) ⊓ Subgroup.centralizer {x} ≤
      Subgroup.centralizer (M.D.rootGroup β : Set M.K)

@[expose] def RCKLemmaHCent (M : LieUniversal) (β : Fin M.D.rank → ℤ) : Prop :=
  ∀ x ∈ M.D.rootGroup β, x ≠ 1 →
    Subgroup.centralizer {x} ≤ Subgroup.centralizer (M.D.rootGroup β : Set M.K)

theorem rck_lemmaH_of_parts {M : LieUniversal} {β : Fin M.D.rank → ℤ}
    (hTI : RCKLemmaHTI M β) (hL : RCKLemmaHLevi M β) :
    ∀ x ∈ M.D.rootGroup β, x ≠ 1 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer (M.D.rootGroup β : Set M.K) := by
  intro x hx hx1 k hk
  have hkx : k * x * k⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hk, mul_inv_cancel_right]
  exact hL x hx hx1 ⟨hTI x hx hx1 k (by rw [hkx]; exact hx), hk⟩

end CFSG.StandardType.RCKC1
