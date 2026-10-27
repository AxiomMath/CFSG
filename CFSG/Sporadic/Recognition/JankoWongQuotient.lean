module

public import CFSG.Sporadic.Recognition.JankoWongInvolutionData
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup

variable {C : Type} [Group C] [Finite C]

theorem centralizer_mk_oddCore_of_sq {w : C} (hw : w ^ 2 = 1) :
    centralizer ({(QuotientGroup.mk w : C ⧸ CFSG.oddCore C)} : Set (C ⧸ CFSG.oddCore C)) =
      (centralizer ({w} : Set C)).map (QuotientGroup.mk' (CFSG.oddCore C)) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    let α := {m : C //
      (QuotientGroup.mk' (CFSG.oddCore C)) m = (QuotientGroup.mk' (CFSG.oddCore C)) n}
    have hcard : Nat.card α = Nat.card (CFSG.oddCore C) := by
      refine Nat.card_congr
        { toFun := fun m => ⟨n⁻¹ * m.1, by
            have h := m.2
            simp only [QuotientGroup.mk'_apply] at h
            exact (QuotientGroup.eq_one_iff _).mp (by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel])⟩
          invFun := fun k => ⟨n * k.1, by
            have h1 : ((k.1 : C) : C ⧸ CFSG.oddCore C) = 1 := (QuotientGroup.eq_one_iff _).mpr k.2
            simp only [QuotientGroup.mk'_apply]
            rw [QuotientGroup.mk_mul, h1, mul_one]⟩
          left_inv := fun m => by apply Subtype.ext; simp
          right_inv := fun k => by apply Subtype.ext; simp }
    have hodd : Odd (Nat.card α) := by
      rw [hcard]; exact CFSG.ABGDGroups.odd_card_oddCore C
    let f : α → α := fun m => ⟨w * m.1 * w⁻¹, by
      have h1 : (QuotientGroup.mk' (CFSG.oddCore C)) (w * m.1 * w⁻¹) =
          (QuotientGroup.mk' (CFSG.oddCore C)) w * (QuotientGroup.mk' (CFSG.oddCore C)) m.1 *
            ((QuotientGroup.mk' (CFSG.oddCore C)) w)⁻¹ := by simp
      rw [h1, m.2]
      have : (QuotientGroup.mk' (CFSG.oddCore C)) n * (QuotientGroup.mk' (CFSG.oddCore C)) w =
          (QuotientGroup.mk' (CFSG.oddCore C)) w * (QuotientGroup.mk' (CFSG.oddCore C)) n := hy
      calc (QuotientGroup.mk' (CFSG.oddCore C)) w * (QuotientGroup.mk' (CFSG.oddCore C)) n *
            ((QuotientGroup.mk' (CFSG.oddCore C)) w)⁻¹
          = ((QuotientGroup.mk' (CFSG.oddCore C)) w * (QuotientGroup.mk' (CFSG.oddCore C)) n) *
            ((QuotientGroup.mk' (CFSG.oddCore C)) w)⁻¹ := rfl
        _ = ((QuotientGroup.mk' (CFSG.oddCore C)) n * (QuotientGroup.mk' (CFSG.oddCore C)) w) *
            ((QuotientGroup.mk' (CFSG.oddCore C)) w)⁻¹ := by rw [this]
        _ = (QuotientGroup.mk' (CFSG.oddCore C)) n := by group⟩
    have hf : ∀ m, f (f m) = m := by
      intro m
      apply Subtype.ext
      show w * (w * m.1 * w⁻¹) * w⁻¹ = m.1
      have h2 : w * w = 1 := by rw [← pow_two]; exact hw
      calc w * (w * m.1 * w⁻¹) * w⁻¹ = (w * w) * m.1 * (w * w)⁻¹ := by group
        _ = m.1 := by rw [h2]; group
    obtain ⟨m, hm⟩ := exists_fixed_of_sq_eq_one_odd hf hodd
    have := congrArg Subtype.val hm
    have h3 : w * m.1 * w⁻¹ = m.1 := this
    refine ⟨m.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_, m.2⟩
    calc m.1 * w = (w * m.1 * w⁻¹) * w := by rw [h3]
      _ = w * m.1 := by group
  · rintro ⟨m, hm, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hm
    show (QuotientGroup.mk' (CFSG.oddCore C)) m * (QuotientGroup.mk' (CFSG.oddCore C)) w =
      (QuotientGroup.mk' (CFSG.oddCore C)) w * (QuotientGroup.mk' (CFSG.oddCore C)) m
    rw [← map_mul, ← map_mul, this]

theorem card_centralizer_mk_oddCore_of_sq {w : C} (hw : w ^ 2 = 1) :
    Nat.card (centralizer ({(QuotientGroup.mk w : C ⧸ CFSG.oddCore C)} :
        Set (C ⧸ CFSG.oddCore C))) *
      Nat.card (CFSG.oddCore C ⊓ centralizer ({w} : Set C) : Subgroup C) =
      Nat.card (centralizer ({w} : Set C)) := by
  rw [centralizer_mk_oddCore_of_sq hw]
  set Zc : Subgroup C := centralizer ({w} : Set C) with hZc
  set π' : ↥Zc →* C ⧸ CFSG.oddCore C := (QuotientGroup.mk' (CFSG.oddCore C)).domRestrict Zc
    with hπ'
  have hrange : π'.range = Zc.map (QuotientGroup.mk' (CFSG.oddCore C)) :=
    MonoidHom.domRestrict_range Zc _
  have hker : π'.ker = (CFSG.oddCore C).subgroupOf Zc := by
    rw [hπ', MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π').toEquiv, hrange, hker] at h1
  have h2 : Nat.card ↥((CFSG.oddCore C).subgroupOf Zc) =
      Nat.card (CFSG.oddCore C ⊓ Zc : Subgroup C) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      CFSG.oddCore C ⊓ Zc ≤ Zc)).toEquiv
  rw [h2] at h1
  rw [h1]

end CFSG.Sporadic.Recognition.JankoWong
