module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Split

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def InO2NormPre (M Q Z Z0 : Subgroup G) [(Q.subgroupOf M).Normal] (x : G) : Prop :=
  ∃ hx : x ∈ M, ∃ y ∈ pCore 2 ↥(MbarPrime M Q Z Z0),
    ((y : Hbar M Q Z) : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hx⟩


@[expose] def Step713XActsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, InO2NormPre M Q Z Z0 x →
      (∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t) ∧
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) ∧
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t)

@[expose] def Step713CoprimeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, InO2NormPre M Q Z Z0 x → x ∉ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      ∃ x' : G, InO2NormPre M Q Z Z0 x' ∧ x' ∉ hc.CN t ∧
        ∀ m ∈ hc.CN t, ∃ z ∈ Z0, ⁅m, x'⁆ * ⁅z, x'⁆⁻¹ ∈ Q

@[expose] def Step713CentralNStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, InO2NormPre M Q Z Z0 x → x ∉ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      (∀ m ∈ hc.CN t, ⁅m, x⁆ ∈ Q) → False

@[expose] def Step713CentreFixStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, InO2NormPre M Q Z Z0 x →
      (∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ hc.CN t) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      ∀ z ∈ Z0, ⁅z, x⁆ ∈ Q

theorem step713O2Hard_of_steps (h1 : Step713XActsStatement) (h2 : Step713CoprimeStatement)
    (h3 : Step713CentralNStatement) (h4 : Step713CentreFixStatement) :
    Step713O2HardStatement := by
  intro G _ _ M Q Z B _ hc n t hs hn4 Z0 hZ0 y hy
  have hyK : ((y : Hbar M Q Z) : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
    Subgroup.mem_subgroupOf.mp y.2
  obtain ⟨x, hxK, hxy⟩ := Subgroup.mem_map.mp hyK
  have hxO : InO2NormPre M Q Z Z0 (x : G) := ⟨x.2, y, hy, hxy.symm⟩
  by_cases hxN : (x : G) ∈ hc.CN t
  ·
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hxN, hxy⟩
  · exfalso
    obtain ⟨hR, hV, hW⟩ := h1 G M Q Z B hc n t hs hn4 Z0 hZ0 x hxO
    obtain ⟨x', hx'O, hx'N, hrel⟩ :=
      h2 G M Q Z B hc n t hs hn4 Z0 hZ0 x hxO hxN hR hV hW
    obtain ⟨hR', hV', hW'⟩ := h1 G M Q Z B hc n t hs hn4 Z0 hZ0 x' hx'O
    have hcen := h4 G M Q Z B hc n t hs hn4 Z0 hZ0 x' hx'O hR' hV' hW'
    have hcN : ∀ m ∈ hc.CN t, ⁅m, x'⁆ ∈ Q := by
      intro m hm
      obtain ⟨z, hz, hmz⟩ := hrel m hm
      have h := Q.mul_mem hmz (hcen z hz)
      rwa [inv_mul_cancel_right] at h
    exact h3 G M Q Z B hc n t hs hn4 Z0 hZ0 x' hx'O hx'N hR' hV' hW' hcN

end CFSG.RankThree.GF2n.Stroth80
