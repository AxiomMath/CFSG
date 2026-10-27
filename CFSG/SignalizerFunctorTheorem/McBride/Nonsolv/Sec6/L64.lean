module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Interface
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem commutator_sSup_msig
    (h : Counterexample p A θ) :
    ⁅(sSup (Msig p A θ) : Subgroup G), (sSup (Msig p A θ) : Subgroup G)⁆ =
      sSup (Msig p A θ) := by
  set W : Subgroup G := sSup (Msig p A θ) with hW
  by_contra hne
  have hle : ⁅W, W⁆ ≤ W := Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem hg₁ hg₂) (W.inv_mem hg₁)) (W.inv_mem hg₂)
  have hnorm : (⁅W, W⁆.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun g hg =>
      mem_normalizer_commutator (Subgroup.le_normalizer hg)
  have hAN : A ≤ Subgroup.normalizer ((⁅W, W⁆ : Subgroup G) : Set G) :=
    fun a ha => mem_normalizer_commutator (h.normalizes_sSup_msig ha)
  have hbot := h.inf_eq_bot_of_normal hle hnorm hAN hne
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  apply h.not_isSolvable_apply ha ha1
  refine Group.isSolvable_of_comm fun x y => ?_
  have hxW : (x : G) ∈ W := h.apply_le_sSup_msig ha ha1 x.2
  have hyW : (y : G) ∈ W := h.apply_le_sSup_msig ha ha1 y.2
  have hc : ⁅(x : G), (y : G)⁆ ∈ θ a ⊓ ⁅W, W⁆ := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.commutator_mem_commutator hxW hyW⟩
    rw [commutatorElement_def]
    exact (θ a).mul_mem ((θ a).mul_mem ((θ a).mul_mem x.2 y.2) ((θ a).inv_mem x.2))
      ((θ a).inv_mem y.2)
  rw [hbot a ha ha1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact Subtype.ext hc

theorem exists_minimal_central (h : Counterexample p A θ)
    (hne : zOf (sSup (Msig p A θ)) ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≤ zOf (sSup (Msig p A θ)) ∧ Z ≠ ⊥ ∧
      A ≤ Subgroup.normalizer (Z : Set G) ∧
      ∀ Z' : Subgroup G, Z' ≤ Z → A ≤ Subgroup.normalizer (Z' : Set G) → Z' = ⊥ ∨ Z' = Z := by
  let S : Set (Subgroup G) := {Z | Z ≤ zOf (sSup (Msig p A θ)) ∧ Z ≠ ⊥ ∧
    A ≤ Subgroup.normalizer (Z : Set G)}
  have hS : S.Nonempty :=
    ⟨zOf (sSup (Msig p A θ)), le_rfl, hne,
      fun a ha => mem_normalizer_zOf (h.normalizes_sSup_msig ha)⟩
  obtain ⟨Z, hZS, hZmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min S hS
  refine ⟨Z, hZS.1, hZS.2.1, hZS.2.2, fun Z' hle hA' => ?_⟩
  by_cases hbot : Z' = ⊥
  · exact Or.inl hbot
  · right
    by_contra hneq
    exact hZmin Z' ⟨hle.trans hZS.1, hbot, hA'⟩ (lt_of_le_of_ne hle hneq)

theorem ne_sSup_of_le_zOf
    (h : Counterexample p A θ) {Z : Subgroup G}
    (hZ : Z ≤ zOf (sSup (Msig p A θ))) : Z ≠ sSup (Msig p A θ) := by
  intro heq
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  apply h.not_isSolvable_apply ha ha1
  refine Group.isSolvable_of_comm fun x y => ?_
  have hxW : (x : G) ∈ zOf (sSup (Msig p A θ)) := hZ (heq ▸ h.apply_le_sSup_msig ha ha1 x.2)
  have hyW : (y : G) ∈ sSup (Msig p A θ) := h.apply_le_sSup_msig ha ha1 y.2
  exact Subtype.ext ((mem_zOf_iff.mp hxW).2 y hyW).symm

theorem lemma_6_4
    (h : Counterexample p A θ) : zOf (sSup (Msig p A θ)) = ⊥ := by
  by_contra hne
  obtain ⟨Z, hZc, hZ1, hZA, hZmin⟩ := h.exists_minimal_central hne
  have hperf := h.commutator_sSup_msig
  obtain ⟨m, hcard, hm⟩ := h.exists_card_quotient hZc hZA hZ1
  have hZW : Z ≤ sSup (Msig p A θ) := hZc.trans (zOf_le _)
  have : Z.Normal := h.normal_of_le_zOf hZc hZA
  by_cases hpZ : p ∣ Nat.card Z
  ·
    exfalso
    have : Fact p.Prime := ⟨h.prime⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpZ
    set W : Subgroup G := sSup (Msig p A θ) with hWdef
    have hperfW : commutator ↥W = ⊤ := by
      apply Subgroup.map_injective W.subtype_injective
      rw [Subgroup.map_subtype_commutator, hperf, Subgroup.map_top, Subgroup.range_subtype]
    let w₀ : ↥W := ⟨(z : G), hZW z.2⟩
    have hw₀ : orderOf w₀ = p := by
      have h1 : orderOf (w₀ : G) = orderOf w₀ := Subgroup.orderOf_coe w₀
      have h2 : orderOf (z : G) = orderOf z := Subgroup.orderOf_coe z
      rw [← h1]
      exact h2.trans hz
    have hdvd : p ∣ (Subgroup.center ↥W).index :=
      hw₀ ▸ orderOf_dvd_of_pow_eq_one (pow_index_center_eq_one hperfW w₀)
    have hcenter : Nat.card Z ∣ Nat.card (Subgroup.center ↥W) := by
      have h1 : Nat.card Z ∣ Nat.card (zOf W) := Subgroup.card_dvd_of_le hZc
      have h2 : Nat.card (zOf W) = Nat.card (Subgroup.center ↥W) :=
        Subgroup.card_map_of_injective W.subtype_injective
      exact h2 ▸ h1
    obtain ⟨c, hc⟩ := hcenter
    have hidx : (Subgroup.center ↥W).index ∣ m := by
      have hmul := Subgroup.card_mul_index (Subgroup.center ↥W)
      have hpos : 0 < Nat.card Z := Nat.card_pos
      have h3 : Nat.card Z * (c * (Subgroup.center ↥W).index) = Nat.card Z * m := by
        rw [← hcard, ← hmul, hc]
        ring
      exact Dvd.intro_left c (Nat.eq_of_mul_eq_mul_left hpos h3)
    exact h.prime.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hm (hdvd.trans hidx))
  · have hcopZ : Nat.Coprime p (Nat.card Z) := (Nat.Prime.coprime_iff_not_dvd h.prime).mpr hpZ
    have hWp : Nat.Coprime p (Nat.card (sSup (Msig p A θ) : Subgroup G)) := by
      rw [hcard]
      exact hcopZ.mul_right hm
    refine false_of_perfect_central_extension h.prime θ h.elemAbelian h.rank_three_le
      h.normalizes_sSup_msig hWp hperf hZW
      (fun z hz w hw => ((mem_zOf_iff.mp (hZc hz)).2 w hw).symm)
      hZ1 hZA ?_ hZmin ?_ ?_ (h.hypB_map_sSup hZc hZA hZ1)
    · refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
      have haZ : a ∈ zOf (sSup (Msig p A θ)) := hZc ha.2
      have := h.inf_centralizer_sSup_eq_bot
      rw [Subgroup.eq_bot_iff_forall] at this
      exact this a (Subgroup.mem_inf.mpr ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (mem_zOf_iff.mp haZ).2 w hw⟩)
    · intro b hb hb1
      refine ⟨h.apply_le_sSup_msig hb hb1, ?_, fun w hw => ?_⟩
      · exact h.inf_eq_bot_of_normal hZW ((inferInstance : Z.Normal).subgroupOf _) hZA
          (h.ne_sSup_of_le_zOf hZc) b hb hb1
      · exact h.exists_mul_of_mem_centralizer hZc hZA hZ1 hb hb1 hw.1 hw.2
    · intro M hMW hMn hMA hMne b hb hb1
      exact h.inf_eq_bot_of_normal hMW hMn hMA hMne b hb hb1

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
