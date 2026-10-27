
module

public import CFSG.Sporadic.Schreier.J4SAutBase
public import CFSG.Sporadic.Schreier.J4SKernelBase
public import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFiveBase
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_dvd_card_outer_of_sylow_bound {G : Type*} [Group G] [Finite G] {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) (S : Sylow q G) (V H : Subgroup G)
    (hVS : V ≤ S) (hSH : (S : Subgroup G) ≤ H) (hVq : IsPGroup q V)
    (hN : Subgroup.normalizer (V : Set G) = H) (hC : Subgroup.centralizer (V : Set G) ⊓ H ≤ V)
    (hCp : ¬ p ∣ Nat.card (pointwiseFixingAut H))
    (hAut : IsPGroup q (MulAut (S : Subgroup G))) : ¬ p ∣ Nat.card (Outer G) := by
  have hb := CFSG.GroupActions.self_centralizing_local_core_Sylow_automorphism_outer_prime_bound
    hpq S V H hVS hSH hVq hN hC hCp
  have : Finite (MulAut (S : Subgroup G)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (S : Subgroup G)))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hAut
  have h0 : (Nat.card (MulAut (S : Subgroup G))).factorization p = 0 := by
    rw [hk]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).1 (hp.out.dvd_of_dvd_pow h))
  rw [h0, pow_zero, Nat.dvd_one] at hb
  intro hdvd
  have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
  have hpos := hp.out.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
  have h1 : p ^ 1 ≤ p ^ (Nat.card (Outer G)).factorization p :=
    Nat.pow_le_pow_right hp.out.pos hpos
  rw [hb, pow_one] at h1
  exact absurd h1 (by have := hp.out.one_lt; omega)

theorem card_outer_congr {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    Nat.card (Outer G) = Nat.card (Outer G') :=
  Nat.card_congr (equivalence e).toEquiv

end CFSG.Sporadic.J4Schreier
