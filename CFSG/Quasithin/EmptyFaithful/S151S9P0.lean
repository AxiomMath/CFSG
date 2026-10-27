module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

structure HSRuModel {H : Type} [Group H] (P K R : Subgroup H) (e : ℕ) : Prop where
  le : P ≤ K
  uniq : ∀ X : Subgroup H, P ≤ X → Nat.card ↥X = Nat.card ↥K → X = K
  perf : ⁅K, K⁆ = K
  R_le : R ≤ K
  R_normal : (R.subgroupOf K).Normal
  R_two : IsPGroup 2 ↥R
  R_card : Nat.card ↥R = 2 ^ e
  R_he : 5 ≤ e ∧ e < 13 ∧ ¬ 9 ∣ e
  R_order4 : ∃ x ∈ R, x ^ 2 ≠ 1
  R_cent : ∀ k ∈ K, (∀ r ∈ R, k * r = r * k) → k ∈ R
  R_comm : ⁅R, K⁆ = R
  quot : ∃ a : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), Function.Surjective a ∧ a.ker = R.subgroupOf K
  notC : ∀ w ∈ centerOf P, w ≠ 1 → ∃ k ∈ K, k * w ≠ w * k

@[expose] def HSRuModelFor (H : Type) [Group H] : Prop :=
  ∀ P : Subgroup H, IsSylowTwoOf P ⊤ → ∃ (K R : Subgroup H) (e : ℕ), HSRuModel P K R e

@[expose] def Input15122HSModel : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSporadic .HS H → HSRuModelFor H

@[expose] def Input15122RuModel : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSporadic .Ru H → HSRuModelFor H

variable {G : Type} [Group G]

@[expose] def liftK (L : Subgroup G) {H : Type} [Group H] (π : ↥L →* H) (Kb : Subgroup H) : Subgroup G :=
  (⁅Kb.comap π, Kb.comap π⁆).map L.subtype

@[expose] def liftR (L : Subgroup G) {H : Type} [Group H] (π : ↥L →* H) (Kb Rb : Subgroup H) : Subgroup G :=
  liftK L π Kb ⊓ (Rb.comap π).map L.subtype

structure LiftCtx (L S : Subgroup G) {H : Type} [Group H] (π : ↥L →* H) (P Kb Rb : Subgroup H) (e : ℕ) : Prop where
  hLq : CFSG.Open.IsQuasisimple ↥L
  hZ : IsPGroup 2 ↥(Subgroup.center ↥L)
  hπ : Function.Surjective π
  hker : π.ker = CFSG.pCore 2 ↥L
  hS2 : IsPGroup 2 ↥S
  hSN : S ≤ Subgroup.normalizer (L : Set G)
  hsyl : IsSylowTwoOf (S ⊓ L) L
  hnc : ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G)
  hP : P = ((S ⊓ L).subgroupOf L).map π
  hm : HSRuModel P Kb Rb e

structure ExclHyp (K S : Subgroup G) (e : ℕ) : Prop where
  elt : ∃ x ∈ c134Q (K ⊔ S) K, x ^ 2 ≠ 1
  tors : ∃ T : Subgroup G, T ≤ c134CQ (K ⊔ S) K ∧ T ≤ centerOf (c134Q (K ⊔ S) K) ∧
    Nat.card ↥(c134Q (K ⊔ S) K) = 2 ^ e * Nat.card ↥T
  he : 5 ≤ e ∧ e < 13 ∧ ¬ 9 ∣ e

end HSRuLoc

end CFSG.Quasithin
