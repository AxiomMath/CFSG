module

public import CFSG.RankThree.PartOne.SolD3.Struct
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitInputs
public import CFSG.GH74.Defs

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.GH74
open CFSG.ComponentClassification.HSFLit
open scoped commutatorElement

structure Cfg3 (G : Type) [Group G] [Finite G] (M X : Subgroup G) (a : G) : Prop where
  h : Hyp3 G M X
  hb : Blk3 X a
  Rab : ∀ r ∈ rOf M X, ∀ r' ∈ rOf M X, r * r' = r' * r
  Rsyl : ∀ c ∈ Subgroup.centralizer (X : Set G),
    (∃ j : ℕ, c ^ (2 ^ j) = 1) → c ∈ rOf M X

namespace Cfg3

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {a : G} (c : Cfg3 G M X a)
include c

theorem decomp_unique {w w' r r' : G} (hw : w ∈ pCoreOf 2 X) (hw' : w' ∈ pCoreOf 2 X)
    (hr : r ∈ rOf M X) (hr' : r' ∈ rOf M X) (heq : w * r = w' * r') : w = w' ∧ r = r' := by
  have h1 : w'⁻¹ * w = r' * r⁻¹ := by
    calc w'⁻¹ * w = w'⁻¹ * (w * r) * r⁻¹ := by group
      _ = w'⁻¹ * (w' * r') * r⁻¹ := by rw [heq]
      _ = r' * r⁻¹ := by group
  have hW : w'⁻¹ * w ∈ pCoreOf 2 X := (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hw') hw
  have hR : w'⁻¹ * w ∈ rOf M X := h1 ▸ (rOf M X).mul_mem hr' ((rOf M X).inv_mem hr)
  have h2 : w'⁻¹ * w = 1 := Hyp3.W_inf_C c.hb hW hR.2
  have hww : w = w' := by
    calc w = w' * (w'⁻¹ * w) := by group
      _ = w' := by rw [h2, mul_one]
  refine ⟨hww, ?_⟩
  subst hww
  exact mul_left_cancel heq

theorem Q_comm {q q' : G} (hq : q ∈ pCoreOf 2 M) (hq' : q' ∈ pCoreOf 2 M) : q * q' = q' * q := by
  obtain ⟨w, hw, r, hr, rfl⟩ := c.h.q_eq_W_mul_R c.hb hq
  obtain ⟨w', hw', r', hr', rfl⟩ := c.h.q_eq_W_mul_R c.hb hq'
  have h1 := c.hb.comm w hw w' hw'
  have h2 := c.Rab r hr r' hr'
  have e1 : r * w' = w' * r := (Hyp3.W_comm_R hw' hr).symm
  have e2 : w * r' = r' * w := Hyp3.W_comm_R hw hr'
  calc w * r * (w' * r') = w * (r * w') * r' := by group
    _ = w * (w' * r) * r' := by rw [e1]
    _ = (w * w') * (r * r') := by group
    _ = (w' * w) * (r' * r) := by rw [h1, h2]
    _ = w' * (w * r') * r := by group
    _ = w' * (r' * w) * r := by rw [e2]
    _ = w' * r' * (w * r) := by group

theorem card_Q : Nat.card ↥(pCoreOf 2 M) = 4 * Nat.card ↥(rOf M X) := by
  have hWQ : pCoreOf 2 X ≤ pCoreOf 2 M := c.h.W_le_Q
  have hRQ : rOf M X ≤ pCoreOf 2 M := inf_le_left
  let f : ↥(pCoreOf 2 X) × ↥(rOf M X) → ↥(pCoreOf 2 M) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), (pCoreOf 2 M).mul_mem (hWQ p.1.2) (hRQ p.2.2)⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨w, hw⟩, ⟨r, hr⟩⟩ ⟨⟨w', hw'⟩, ⟨r', hr'⟩⟩ heq
      have h1 := c.decomp_unique hw hw' hr hr' (congrArg Subtype.val heq)
      obtain ⟨h2, h3⟩ := h1
      subst h2
      subst h3
      rfl
    · intro q
      obtain ⟨w, hw, r, hr, hq⟩ := c.h.q_eq_W_mul_R c.hb q.2
      exact ⟨(⟨w, hw⟩, ⟨r, hr⟩), Subtype.ext hq.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, c.hb.card]

theorem two_elt_centralizing_mem_Q {S : Subgroup G} (hS : IsPGroup 2 S) (hSM : S ≤ M) {s : G}
    (hs : s ∈ S) (hsW : ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ = w) : s ∈ pCoreOf 2 M := by
  obtain ⟨w, hw, hwC⟩ := c.h.exists_mul_centralizer c.hb (hSM hs) hsW
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hsw : s * w = w * s := by
    have := hsW w hw
    calc s * w = (s * w * s⁻¹) * s := by group
      _ = w * s := by rw [this]
  have hcomm : Commute (w⁻¹) s := (show Commute s w from hsw).symm.inv_left
  have hw2 : (w⁻¹) ^ 2 = 1 := by
    have := c.hb.sq w hw
    calc (w⁻¹) ^ 2 = (w * w)⁻¹ := by group
      _ = 1 := by rw [this]; simp
  have hc2 : (w⁻¹ * s) ^ (2 ^ (k + 1)) = 1 := by
    rw [hcomm.mul_pow]
    have e1 : s ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
    have e2 : (w⁻¹) ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ', pow_mul, hw2, one_pow]
    rw [e1, e2, one_mul]
  have hcR : w⁻¹ * s ∈ rOf M X := c.Rsyl _ hwC ⟨k + 1, hc2⟩
  have : s = w * (w⁻¹ * s) := by group
  rw [this]
  exact (pCoreOf 2 M).mul_mem (c.h.W_le_Q hw) hcR.1

theorem card_S_le {S : Subgroup G} (hS : IsPGroup 2 S) (hSM : S ≤ M) (hQS : pCoreOf 2 M ≤ S) :
    Nat.card ↥S ≤ 2 * Nat.card ↥(pCoreOf 2 M) := by
  have hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X :=
    fun s hs w hw => c.h.W_normalized (hSM hs) hw
  have h1 := card_le_two_mul_card_centralizer c.hb hS hSn
  have h2 : (Subgroup.centralizer (pCoreOf 2 X : Set G) ⊓ S : Subgroup G) = pCoreOf 2 M := by
    apply le_antisymm
    · intro s hs
      refine c.two_elt_centralizing_mem_Q hS hSM (Subgroup.mem_inf.1 hs).2 ?_
      intro w hw
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hs).1 w hw
      calc s * w * s⁻¹ = (w * s) * s⁻¹ := by rw [this]
        _ = w := by group
    · intro q hq
      refine Subgroup.mem_inf.2 ⟨?_, hQS hq⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := c.h.q_comm_W c.hb hq w hw
      calc w * q = (q * w * q⁻¹) * q := by rw [this]
        _ = q * w := by group
  rw [h2] at h1
  exact h1

theorem not_centralizes_of_not_mem_Q {S : Subgroup G} (hS : IsPGroup 2 S) (hSM : S ≤ M) {s : G}
    (hs : s ∈ S) (hsQ : s ∉ pCoreOf 2 M) : ¬ ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ = w :=
  fun h => hsQ (c.two_elt_centralizing_mem_Q hS hSM hs h)

end Cfg3

section IndexTwo

variable {G : Type} [Group G] [Finite G]

theorem index_two_of_lt {S Q : Subgroup G} (hQS : Q ≤ S) (hne : Q ≠ S)
    (hle : Nat.card ↥S ≤ 2 * Nat.card ↥Q) : (Q.subgroupOf S).index = 2 := by
  have h1 : (Q.subgroupOf S).index * Nat.card ↥(Q.subgroupOf S) = Nat.card ↥S :=
    Subgroup.index_mul_card _
  have h2 : Nat.card ↥(Q.subgroupOf S) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
  have h3 : (Q.subgroupOf S).index ≠ 1 := by
    intro h
    apply hne
    have htop : Q.subgroupOf S = ⊤ := Subgroup.index_eq_one.1 h
    refine le_antisymm hQS fun x hx => ?_
    have : (⟨x, hx⟩ : ↥S) ∈ Q.subgroupOf S := by rw [htop]; trivial
    exact this
  have hpos : 0 < Nat.card ↥Q := Nat.card_pos
  have h0 : (Q.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h2] at h1
  by_contra hne2
  have hge : 3 ≤ (Q.subgroupOf S).index := by omega
  have : 3 * Nat.card ↥Q ≤ (Q.subgroupOf S).index * Nat.card ↥Q := Nat.mul_le_mul_right _ hge
  omega

omit [Finite G] in
theorem inv_mul_mem_of_index_two {S Q : Subgroup G} (hidx : (Q.subgroupOf S).index = 2)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hun : u ∉ Q) (hvn : v ∉ Q) : u⁻¹ * v ∈ Q := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := Q.subgroupOf S) hidx
    (a := (⟨u, hu⟩ : S)⁻¹) (b := ⟨v, hv⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false hun hvn)
  exact Subgroup.mem_subgroupOf.1 key

end IndexTwo

namespace Cfg3

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {a : G} (c : Cfg3 G M X a)
include c

theorem card_le_four_of_inf_R {K : Subgroup G} (hKQ : K ≤ pCoreOf 2 M)
    (hKR : K ⊓ rOf M X = ⊥) : Nat.card ↥K ≤ 4 := by
  have hq : ∀ k : ↥K, ∃ w ∈ pCoreOf 2 X, ∃ r ∈ rOf M X, (k : G) = w * r :=
    fun k => c.h.q_eq_W_mul_R c.hb (hKQ k.2)
  choose f hfW hfr using hq
  let g : ↥K → ↥(pCoreOf 2 X) := fun k => ⟨f k, hfW k⟩
  have hinj : Function.Injective g := by
    intro k₁ k₂ hk
    have hf : f k₁ = f k₂ := congrArg Subtype.val hk
    obtain ⟨r₁, hr₁, h₁⟩ := hfr k₁
    obtain ⟨r₂, hr₂, h₂⟩ := hfr k₂
    have hmem : (k₁ : G)⁻¹ * (k₂ : G) ∈ K := K.mul_mem (K.inv_mem k₁.2) k₂.2
    have hR : (k₁ : G)⁻¹ * (k₂ : G) ∈ rOf M X := by
      have : (k₁ : G)⁻¹ * (k₂ : G) = r₁⁻¹ * r₂ := by
        rw [h₁, h₂, hf]
        group
      rw [this]
      exact (rOf M X).mul_mem ((rOf M X).inv_mem hr₁) hr₂
    have h1 : (k₁ : G)⁻¹ * (k₂ : G) ∈ K ⊓ rOf M X := Subgroup.mem_inf.2 ⟨hmem, hR⟩
    rw [hKR, Subgroup.mem_bot] at h1
    exact Subtype.ext (by
      calc (k₁ : G) = (k₁ : G) * 1 := (mul_one _).symm
        _ = (k₁ : G) * ((k₁ : G)⁻¹ * (k₂ : G)) := by rw [h1]
        _ = (k₂ : G) := by group)
  have := Nat.card_le_card_of_injective g hinj
  rw [c.hb.card] at this
  exact this

theorem card_le_two_of_inf_R {K : Subgroup G} (hKQ : K ≤ pCoreOf 2 M)
    (hKR : K ⊓ rOf M X = ⊥) {y : G} (hy : y ∈ M) (hyK : ∀ k ∈ K, y * k * y⁻¹ = k) {c₀ : G}
    (hfix : ∀ w ∈ pCoreOf 2 X, y * w * y⁻¹ = w → w = 1 ∨ w = c₀) : Nat.card ↥K ≤ 2 := by
  have hq : ∀ k : ↥K, ∃ w ∈ pCoreOf 2 X, ∃ r ∈ rOf M X, (k : G) = w * r :=
    fun k => c.h.q_eq_W_mul_R c.hb (hKQ k.2)
  choose f hfW hfr using hq
  have hfk : ∀ k : ↥K, y * f k * y⁻¹ = f k := by
    intro k
    obtain ⟨r, hr, hkr⟩ := hfr k
    have h1 := hyK k k.2
    rw [hkr] at h1
    have hyw : y * f k * y⁻¹ ∈ pCoreOf 2 X := c.h.W_normalized hy (hfW k)
    have hyr : y * r * y⁻¹ ∈ rOf M X := c.h.R_normalized hy hr
    have h2 : (y * f k * y⁻¹) * (y * r * y⁻¹) = f k * r := by
      calc (y * f k * y⁻¹) * (y * r * y⁻¹) = y * (f k * r) * y⁻¹ := by group
        _ = f k * r := h1
    exact (c.decomp_unique hyw (hfW k) hyr hr h2).1
  have hmem : ∀ k : ↥K, f k ∈ ({1, c₀} : Set G) := by
    intro k
    rcases hfix _ (hfW k) (hfk k) with h | h
    · simp [h]
    · simp [h]
  let g : ↥K → ↥({1, c₀} : Set G) := fun k => ⟨f k, hmem k⟩
  have hinj : Function.Injective g := by
    intro k₁ k₂ hk
    have hf : f k₁ = f k₂ := congrArg Subtype.val hk
    obtain ⟨r₁, hr₁, h₁⟩ := hfr k₁
    obtain ⟨r₂, hr₂, h₂⟩ := hfr k₂
    have hmem' : (k₁ : G)⁻¹ * (k₂ : G) ∈ K := K.mul_mem (K.inv_mem k₁.2) k₂.2
    have hR : (k₁ : G)⁻¹ * (k₂ : G) ∈ rOf M X := by
      have : (k₁ : G)⁻¹ * (k₂ : G) = r₁⁻¹ * r₂ := by
        rw [h₁, h₂, hf]
        group
      rw [this]
      exact (rOf M X).mul_mem ((rOf M X).inv_mem hr₁) hr₂
    have h1 : (k₁ : G)⁻¹ * (k₂ : G) ∈ K ⊓ rOf M X := Subgroup.mem_inf.2 ⟨hmem', hR⟩
    rw [hKR, Subgroup.mem_bot] at h1
    exact Subtype.ext (by
      calc (k₁ : G) = (k₁ : G) * 1 := (mul_one _).symm
        _ = (k₁ : G) * ((k₁ : G)⁻¹ * (k₂ : G)) := by rw [h1]
        _ = (k₂ : G) := by group)
  have h1 := Nat.card_le_card_of_injective g hinj
  have h2 : Nat.card ↥({1, c₀} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by simp)
  exact h1.trans h2

theorem gen4_of_card_R_two (hHar : HaradaInput) (hcard : Nat.card ↥(rOf M X) = 2) :
    SectionalTwoRankLE G 4 := by
  have hcQ : Nat.card ↥(pCoreOf 2 M) = 8 := by rw [c.card_Q, hcard]
  have : IsMulCommutative ↥(pCoreOf 2 M) :=
    ⟨⟨fun x y => Subtype.ext (c.Q_comm x.2 y.2)⟩⟩
  have hsq : ∀ x ∈ pCoreOf 2 M, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨w, hw, r, hr, rfl⟩ := c.h.q_eq_W_mul_R c.hb hx
    have hw2 : w * w = 1 := c.hb.sq w hw
    have hr2 : r * r = 1 := by
      have := pow_card_eq_one' (G := ↥(rOf M X)) (x := ⟨r, hr⟩)
      rw [hcard] at this
      have h' : r ^ 2 = 1 := congrArg Subtype.val this
      simpa [pow_two] using h'
    have e1 : r * w = w * r := (Hyp3.W_comm_R hw hr).symm
    calc (w * r) ^ 2 = (w * r) * (w * r) := pow_two _
      _ = w * (r * w) * r := by group
      _ = w * (w * r) * r := by rw [e1]
      _ = (w * w) * (r * r) := by group
      _ = 1 := by rw [hw2, hr2, one_mul]
  have hEA : CFSG.Open.IsElemAbelian 2 (pCoreOf 2 M) := ⟨inferInstance, hsq⟩
  have hEA' : IsElementaryAbelian 2 (pCoreOf 2 M) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).2 hEA
  have hcent : Subgroup.centralizer ((pCoreOf 2 M : Subgroup G) : Set G) = pCoreOf 2 M := by
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _ hx
      rw [c.h.normalizer_Q_eq c.hb] at hxN
      exact c.h.charTwo M c.h.maxLocal.1 (Subgroup.mem_inf.2 ⟨hxN, hx⟩)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (c.Q_comm hy hx)
  intro P hP
  exact hHar.2 G (pCoreOf 2 M) hEA' hcQ hcent P hP

end Cfg3

end CFSG.RankThree.PartOne.SolD3
