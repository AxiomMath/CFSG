module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dat
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417

namespace E9P2.Sec

section Data

variable {G : Type} [Group G]

structure BetaData (T H PQ : Subgroup G) {V : Type} [CommGroup V] [Finite V]
    (β : ↥H →* MulAut V) : Prop where
  ker_eq : β.ker = (pCoreOf 2 H).subgroupOf H
  str : E9Z4Str β.range ((T.subgroupOf H).map β) ((PQ.subgroupOf H).map β)
  QT : pCoreOf 2 H ≤ T
  TH : T ≤ H
  PQH : PQ ≤ H
  QPQ : pCoreOf 2 H ≤ PQ

end Data

section Basic

variable {G : Type} [Group G] {T H PQ : Subgroup G} {V : Type} [CommGroup V] [Finite V]
  {β : ↥H →* MulAut V}

namespace BetaData

theorem beta_eq_one_iff (hb : BetaData T H PQ β) (x : ↥H) : β x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [← MonoidHom.mem_ker, hb.ker_eq, Subgroup.mem_subgroupOf]

theorem card_map (hb : BetaData T H PQ β) {A : Subgroup G} (hAH : A ≤ H) :
    Nat.card ((A.subgroupOf H).map β) = (pCoreOf 2 H).relIndex A := by
  rw [← Subgroup.relIndex_ker, hb.ker_eq, Subgroup.relIndex_subgroupOf hAH]

theorem relIndex_PQ (hb : BetaData T H PQ β) : (pCoreOf 2 H).relIndex PQ = 9 := by
  rw [← hb.card_map hb.PQH]
  exact hb.str.card_P

theorem relIndex_T (hb : BetaData T H PQ β) : (pCoreOf 2 H).relIndex T = 4 := by
  rw [← hb.card_map hb.TH]
  exact hb.str.card_Tb

theorem comm_PQ (hb : BetaData T H PQ β) {y z : G} (hy : y ∈ PQ) (hz : z ∈ PQ) :
    y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 H := by
  have hy' : β ⟨y, hb.PQH hy⟩ ∈ (PQ.subgroupOf H).map β :=
    ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hz' : β ⟨z, hb.PQH hz⟩ ∈ (PQ.subgroupOf H).map β :=
    ⟨_, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have hc := hb.str.comm_P _ hy' _ hz'
  have h1 : β (⟨y, hb.PQH hy⟩ * ⟨z, hb.PQH hz⟩ * ⟨y, hb.PQH hy⟩⁻¹ * ⟨z, hb.PQH hz⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact (hb.beta_eq_one_iff _).mp h1

theorem pow_three_PQ (hb : BetaData T H PQ β) {y : G} (hy : y ∈ PQ) : y ^ 3 ∈ pCoreOf 2 H := by
  have hy' : β ⟨y, hb.PQH hy⟩ ∈ (PQ.subgroupOf H).map β :=
    ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have h1 : β (⟨y, hb.PQH hy⟩ ^ 3) = 1 := by
    rw [map_pow]
    exact hb.str.exp_P _ hy'
  exact (hb.beta_eq_one_iff _).mp h1

theorem exists_quot_four (hb : BetaData T H PQ β) :
    ∃ φ : ↥T →* Multiplicative (ZMod 4), Function.Surjective φ ∧
      ∀ x : ↥T, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  classical
  have hcyc : IsCyclic ↥((T.subgroupOf H).map β) := hb.str.cyclic_Tb
  have hcard : Nat.card ↥((T.subgroupOf H).map β) = Nat.card (Multiplicative (ZMod 4)) := by
    rw [hb.str.card_Tb]
    simp
  let ψ : ↥T →* ↥((T.subgroupOf H).map β) :=
    (β.comp (Subgroup.inclusion hb.TH)).codRestrict _ fun x =>
      ⟨⟨x, hb.TH x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  let e : ↥((T.subgroupOf H).map β) ≃* Multiplicative (ZMod 4) := mulEquivOfCyclicCardEq hcard
  refine ⟨e.toMonoidHom.comp ψ, e.surjective.comp hψ, fun x => ?_⟩
  have h1 : e (ψ x) = 1 ↔ ψ x = 1 := by
    rw [← map_one e]
    exact e.injective.eq_iff
  have h2 : ψ x = 1 ↔ β ⟨x, hb.TH x.2⟩ = 1 := by
    rw [← Subtype.coe_inj]
    rfl
  exact h1.trans (h2.trans (hb.beta_eq_one_iff _))

end BetaData

end Basic

section Bridge

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem exists_betaData (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V) (β : ↥H →* MulAut V), BetaData T H PQ β := by
  classical
  have hcls : ClassAutShapeStmt := classAutShapeStmt
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  obtain ⟨hsplit, -, -⟩ := shape_splitting h35 S hred h98
  exact ⟨_, inferInstance, inferInstance, resBeta (rhoH h98.toHypF91),
    ⟨ker_resBeta_eq h98.toHypF91 hsplit, e9z4Str_of_shape hcls h35 S hred hshape h98,
      S.pCoreOf_le_T hH, hH.1.1, hred.le, hred.lt.le⟩⟩

end Bridge

end E9P2.Sec

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9_pq_section (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    (pCoreOf 2 H).relIndex PQ = 9 ∧
      (∀ y ∈ PQ, ∀ z ∈ PQ, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 H) ∧ ∀ y ∈ PQ, y ^ 3 ∈ pCoreOf 2 H := by
  obtain ⟨V, _, _, β, hb⟩ := E9P2.Sec.exists_betaData h35 S hred hshape
  exact ⟨hb.relIndex_PQ, fun y hy z hz => hb.comm_PQ hy hz, fun y hy => hb.pow_three_PQ hy⟩

theorem e9_quot_four (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    ∃ φ : ↥T →* Multiplicative (ZMod 4), Function.Surjective φ ∧
      ∀ x : ↥T, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  obtain ⟨V, _, _, β, hb⟩ := E9P2.Sec.exists_betaData h35 S hred hshape
  exact hb.exists_quot_four

end Main

end CFSG.Quasithin
