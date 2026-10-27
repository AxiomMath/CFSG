module

public import CFSG.LocalAnalysis.StandardType.SolvableOrSimpleDerived

public section

namespace CFSG.StandardType.SylowOvergroup

theorem card_eq_pow_factorization {p a k : ℕ} [Fact p.Prime] {N : ℕ} (hN : N = p ^ a * k)
    (hk : ¬ p ∣ k) : p ^ a = p ^ N.factorization p := by
  have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero p)
  have hp0 : p ^ a ≠ 0 := pow_ne_zero a (Fact.out : p.Prime).ne_zero
  rw [hN, Nat.factorization_mul hp0 hk0, Finsupp.add_apply,
    (Fact.out : p.Prime).factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hk, add_zero]

variable {Q : Type} [Group Q]

theorem solvableOrSimpleDerived_of_sylow_le {G P : Subgroup Q} [Finite ↥G] {p m a k : ℕ}
    [Fact p.Prime] (hPG : P ≤ G) (hP : Nat.card ↥P = p ^ a) (hG : Nat.card ↥G = p ^ a * k)
    (hk : ¬ p ∣ k)
    (h : ∀ Y : Subgroup Q, P ≤ Y → Y ≤ G → Y ≠ G → SolvableOrSimpleDerived m ↥Y) :
    ∀ X : Subgroup ↥G, X ≠ ⊤ → ¬ p ∣ X.index → SolvableOrSimpleDerived m ↥X := by
  intro X hX1 hX
  let S : Sylow p ↥G := Sylow.ofCard (P.subgroupOf G) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hP]
    exact card_eq_pow_factorization hG hk)
  have hS : (S : Subgroup ↥G) = P.subgroupOf G := Sylow.coe_ofCard _ _
  refine forall_of_sylow_le S (fun Y => SolvableOrSimpleDerived m ↥Y) ?_ ?_ hX1 hX
  · intro g Y hY
    exact SolvableOrSimpleDerived.of_mulEquiv
      (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
      hY
  · intro Y hSY hYtop
    have hPY : P ≤ Y.map G.subtype := by
      intro x hx
      have hxG : x ∈ G := hPG hx
      refine ⟨⟨x, hxG⟩, hSY ?_, rfl⟩
      rw [hS]
      exact hx
    have hne : Y.map G.subtype ≠ G := by
      intro heq
      apply hYtop
      have htop : (⊤ : Subgroup ↥G).map G.subtype = G := by
        rw [Subgroup.map_top G.subtype, Subgroup.range_subtype]
      exact (Subgroup.map_subtype_inj (H := G)).mp (heq.trans htop.symm)
    exact SolvableOrSimpleDerived.of_mulEquiv
      (Subgroup.equivMapOfInjective Y G.subtype G.subtype_injective).symm
      (h _ hPY (Subgroup.map_subtype_le Y) hne)

end CFSG.StandardType.SylowOvergroup
