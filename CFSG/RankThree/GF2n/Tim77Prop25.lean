module

public import CFSG.RankThree.GF2n.Tim77Prop24Roots
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.CGT.Timmesfeld75.Sec3Root

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem tim77_2_5_rel {V N Hs : Subgroup G} (hV : Assembly.IsElemAbelian 2 V) (hTI : IsTI V)
    (hN : Hs ≤ Subgroup.normalizer (N : Set G)) (hNc : IsMulCommutative N)
    (hVN : V ⊓ N ≠ ⊥) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classDIn Hs V) := by
  have key : ∀ d ∈ classDIn Hs V, ∀ e ∈ classDIn Hs V,
      (orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e))) ∧
        (orderOf (d * e) = 4 → (d * e) ^ 2 ∈ classDIn Hs V) := by
    intro d hd e he
    obtain ⟨hd1, g, hg, hdg⟩ := hd
    obtain ⟨he1, h, hh, heh⟩ := he
    have hsq : (d * e) ^ 2 = 1 → (orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨
        Odd (orderOf (d * e))) ∧ (orderOf (d * e) = 4 → (d * e) ^ 2 ∈ classDIn Hs V) := by
      intro h2
      refine ⟨(orderOf_eq_two_or_odd h2).imp_right Or.inr, fun h4 => ?_⟩
      have := orderOf_dvd_of_pow_eq_one h2
      rw [h4] at this
      exact absurd this (by decide)
    have hAel : Assembly.IsElemAbelian 2 (conjSubgroup g V) := isElemAbelian_conjSubgroup hV g
    have hBel : Assembly.IsElemAbelian 2 (conjSubgroup h V) := isElemAbelian_conjSubgroup hV h
    by_cases hAB : conjSubgroup g V = conjSubgroup h V
    · have hde : d * e ∈ conjSubgroup g V := (conjSubgroup g V).mul_mem hdg (hAB ▸ heh)
      exact hsq (hAel.2 _ hde)
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (inf_comm V N ▸ hVN : N ⊓ V ≠ ⊥)
    obtain ⟨hxN, hxV⟩ := Subgroup.mem_inf.mp hx
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hconjN : ∀ k ∈ Hs, k * x * k⁻¹ ∈ N := fun k hk =>
      (Subgroup.mem_normalizer_iff.mp (hN hk) x).mp hxN
    have hconjne : ∀ k : G, k * x * k⁻¹ ≠ 1 := fun k h => hx1' (by
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = 1 := by rw [h]; group)
    have hmem : ∀ k : G, k * x * k⁻¹ ∈ conjSubgroup k V := fun k => by
      rw [mem_conjSubgroup, show k⁻¹ * (k * x * k⁻¹) * k = x by group]
      exact hxV
    have hcomm : (g * x * g⁻¹) * (h * x * h⁻¹) = (h * x * h⁻¹) * (g * x * g⁻¹) :=
      congrArg Subtype.val (hNc.is_comm.comm ⟨_, hconjN g hg⟩ ⟨_, hconjN h hh⟩)
    have hnorm : g * x * g⁻¹ ∈ Subgroup.normalizer (conjSubgroup h V : Set G) :=
      mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hTI h) (hmem h) (hconjne h) hcomm
    have hLne : conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G) ≠ ⊥ := by
      intro hbot
      have : g * x * g⁻¹ ∈ conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G) :=
        Subgroup.mem_inf.mpr ⟨hmem g, hnorm⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hconjne g this
    have hkk : conjSubgroup (g * h⁻¹) (conjSubgroup h V) = conjSubgroup g V := by
      rw [conjSubgroup_conjSubgroup, show g * h⁻¹ * h = g by group]
    by_cases hle : conjSubgroup g V ≤ Subgroup.normalizer (conjSubgroup h V : Set G)
    · have habel := tim77_2_3 hBel (isTI_conjSubgroup hTI h) (g := g * h⁻¹) (hkk ▸ hle)
      rw [hkk] at habel
      have hde : d * e ∈ conjSubgroup h V ⊔ conjSubgroup g V :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right hdg) (Subgroup.mem_sup_left heh)
      exact hsq (habel.2 _ hde)
    · have S : Prop24Setup (conjSubgroup g V) (conjSubgroup h V)
          (conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G))
          (conjSubgroup h V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G))
          ((conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G)) ⊔
            (conjSubgroup h V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G))) :=
        { elem := hAel
          ti := isTI_conjSubgroup hTI g
          conj := ⟨h * g⁻¹, by
            rw [conjSubgroup_conjSubgroup, show h * g⁻¹ * g = h by group]⟩
          hL := rfl
          hLb := rfl
          hM := rfl
          ne_bot := hLne
          ne := fun h' => hle (h' ▸ inf_le_right) }
      rcases S.orderOf_mul_cases hdg heh with h2 | ⟨h4, hL | hL⟩ | hodd
      · exact ⟨Or.inl h2, fun h4 => by rw [h2] at h4; exact absurd h4 (by decide)⟩
      · refine ⟨Or.inr (Or.inl h4), fun _ => ?_⟩
        refine ⟨fun h1 => ?_, g, hg, S.L_le hL⟩
        have := orderOf_dvd_of_pow_eq_one h1
        rw [h4] at this
        exact absurd this (by decide)
      · refine ⟨Or.inr (Or.inl h4), fun _ => ?_⟩
        refine ⟨fun h1 => ?_, h, hh, S.Lb_le hL⟩
        have := orderOf_dvd_of_pow_eq_one h1
        rw [h4] at this
        exact absurd this (by decide)
      · exact ⟨Or.inr (Or.inr hodd), fun h4 => by rw [h4] at hodd; exact absurd hodd (by decide)⟩
  exact ⟨fun _ hd => orderOf_eq_two_of_mem_classDIn hV hd,
    fun d hd e he => (key d hd e he).1, fun d hd e he h4 => (key d hd e he).2 h4⟩

end CFSG.RankThree.GF2n.Tim77
