module

public import CFSG.Walter.J1.CardEq
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.Walter.J1 CFSG.QuasithinUnique

@[expose] noncomputable def jankoHypOfMulEquiv {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] (h : JankoHyp G) (e : G' ≃* G) : JankoHyp G' where
  isSimpleGroup := by
    have := h.isSimpleGroup
    exact e.isSimpleGroup
  abelian_sylow := by
    intro P
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S, hS⟩ := (P.isPGroup'.map e.toMonoidHom).exists_le_sylow
    have hSab := h.abelian_sylow S
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : e a ∈ (S : Subgroup G) := hS ⟨a, a.2, rfl⟩
    have h2 : e b ∈ (S : Subgroup G) := hS ⟨b, b.2, rfl⟩
    have h3 := congrArg Subtype.val (hSab.is_comm.comm ⟨e a, h1⟩ ⟨e b, h2⟩)
    simp only [Subgroup.coe_mul] at h3
    rw [← map_mul, ← map_mul] at h3
    exact Subtype.ext (e.injective h3)
  t := e.symm h.t
  orderOf_t := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_t
  F := h.F.map e.symm.toMonoidHom
  le_centralizer := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  t_not_mem := by
    rintro ⟨x, hx, hxt⟩
    apply h.t_not_mem
    have : x = h.t := e.symm.injective hxt
    rwa [← this]
  centralizer_eq := by
    have := CFSG.centralizer_singleton_map e.symm h.t
    rw [← this, h.centralizer_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  iso := (Subgroup.equivMapOfInjective h.F e.symm.toMonoidHom e.symm.injective).symm.trans h.iso

variable {A : Type} [Group A] [Finite A] {Q : Subgroup A}

@[expose] noncomputable def sylowOf {T : Subgroup A} (hT : IsSylowTwoOf T Q) : Sylow 2 ↥Q :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (hT.2.1.comap_subtype : IsPGroup 2 ↥(T.subgroupOf Q)).toSylow hT.2.2

omit [Finite A] in
theorem coe_sylowOf {T : Subgroup A} (hT : IsSylowTwoOf T Q) :
    ((sylowOf hT : Sylow 2 ↥Q) : Subgroup ↥Q) = T.subgroupOf Q := rfl

variable (hJ : JankoHyp ↥Q)
include hJ

theorem comm_of_mem_sylow {T : Subgroup A} (hT : IsSylowTwoOf T Q) {a b : A} (ha : a ∈ T)
    (hb : b ∈ T) : a * b = b * a := by
  have := (hJ.abelian_sylow (sylowOf hT)).is_comm.comm
    ⟨⟨a, hT.1 ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩ ⟨⟨b, hT.1 hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
  exact congrArg (fun z : ↥((sylowOf hT : Sylow 2 ↥Q) : Subgroup ↥Q) => ((z : ↥Q) : A)) this

theorem card_of_sylow {T : Subgroup A} (hT : IsSylowTwoOf T Q) : Nat.card T = 8 := by
  have := hJ.card_sylow' (sylowOf hT)
  rwa [coe_sylowOf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv] at this

theorem eq_bot_of_le_normalizer {T K : Subgroup A} (hT : IsSylowTwoOf T Q) (hKQ : K ≤ Q)
    (hK : Odd (Nat.card K)) (hTK : T ≤ Subgroup.normalizer (K : Set A)) : K = ⊥ := by
  have h1 : K.subgroupOf Q = ⊥ := by
    refine hJ.eq_bot_of_sylow_le_normalizer (sylowOf hT) ?_ ?_
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKQ).toEquiv]
    · intro t ht
      rw [coe_sylowOf, Subgroup.mem_subgroupOf] at ht
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hTK ht) k
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hKQ hx⟩ : ↥Q) ∈ K.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hx
  rw [h1, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem orderOf_of_mem_normalizer {T : Subgroup A} (hT : IsSylowTwoOf T Q) {x : A} (hxQ : x ∈ Q)
    (hxN : x ∈ Subgroup.normalizer (T : Set A)) (hodd : Odd (orderOf x)) :
    orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 7 := by
  have hN : (⟨x, hxQ⟩ : ↥Q) ∈
      Subgroup.normalizer (((sylowOf hT : Sylow 2 ↥Q) : Subgroup ↥Q) : Set ↥Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    rw [coe_sylowOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hxN k
  have := hJ.orderOf_mem_normalizer (sylowOf hT) hN
  rw [Subgroup.orderOf_mk] at this
  rcases this with h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)
  · exact Or.inr (Or.inl h1)
  · rw [h1] at hodd
    exact absurd hodd (by decide)
  · exact Or.inr (Or.inr h1)

theorem false_of_seven_three {a b : A} (ha : a ∈ Q) (hb : b ∈ Q) (ha7 : orderOf a = 7)
    (hb3 : orderOf b = 3) (hab : a * b = b * a) : False := by
  have h1 : (⟨a, ha⟩ : ↥Q) = 1 := hJ.eq_one_of_coprime_of_commute (x := ⟨b, hb⟩)
    (by rw [Subgroup.orderOf_mk, ha7]; norm_num)
    (Or.inr (Or.inl (by rw [Subgroup.orderOf_mk, hb3])))
    (Subtype.ext hab)
  have h2 : a = 1 := congrArg Subtype.val h1
  rw [h2, orderOf_one] at ha7
  omega

theorem card_dvd_three_of_isPGroup {X : Subgroup A} (hXQ : X ≤ Q) (hX : IsPGroup 3 ↥X) :
    Nat.card X ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have h1 : Nat.card X ∣ 175560 := hJ.card_eq ▸ Subgroup.card_dvd_of_le hXQ
  rw [hk] at h1 ⊢
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 3 ^ 2 ∣ 175560 := (pow_dvd_pow 3 (by omega)).trans h1
    revert this
    decide
  interval_cases k <;> norm_num

end CFSG.Quasithin.H13.NQCat.C2
