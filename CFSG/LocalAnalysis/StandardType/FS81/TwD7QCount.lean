module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCountAux

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem card_zb {G : Type} [Group G] {β : G} (hord : orderOf β = 3) :
    Nat.card ↥(TwD7Q.zb β) = 3 := by
  rw [TwD7Q.zb, card_subgroupOf_eq (TwD7Q.zpowers_le_cen β), Nat.card_zpowers, hord]

private theorem zb_le_of_mem {G : Type} [Group G] {β : G} {Y : Subgroup ↥(TwD7Q.cen β)}
    (hβY : (⟨β, TwD7Q.self_mem_cen β⟩ : ↥(TwD7Q.cen β)) ∈ Y) : TwD7Q.zb β ≤ Y := by
  intro z hz
  rw [TwD7Q.zb, Subgroup.mem_subgroupOf] at hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hz' : z = (⟨β, TwD7Q.self_mem_cen β⟩ : ↥(TwD7Q.cen β)) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk.symm
  rw [hz']
  exact Subgroup.zpow_mem _ hβY k

private theorem card_map_pr_mul_three {G : Type} [Group G] [Finite G] {β : G}
    (hord : orderOf β = 3) {Y : Subgroup ↥(TwD7Q.cen β)}
    (hβY : (⟨β, TwD7Q.self_mem_cen β⟩ : ↥(TwD7Q.cen β)) ∈ Y) :
    Nat.card ↥(Y.map (TwD7Q.pr β)) * 3 = Nat.card ↥Y := by
  have hzbY : TwD7Q.zb β ≤ Y := zb_le_of_mem hβY
  have hker : ((TwD7Q.pr β).comp Y.subtype).ker = (TwD7Q.zb β).subgroupOf Y := by
    ext y
    constructor
    · intro hy
      rw [MonoidHom.mem_ker] at hy
      rw [Subgroup.mem_subgroupOf, TwD7Q.zb, Subgroup.mem_subgroupOf]
      exact (TwD7Q.pr_eq_one_iff _).mp hy
    · intro hy
      rw [MonoidHom.mem_ker]
      rw [Subgroup.mem_subgroupOf, TwD7Q.zb, Subgroup.mem_subgroupOf] at hy
      exact (TwD7Q.pr_eq_one_iff _).mpr hy
  have hcardker : Nat.card ↥(((TwD7Q.pr β).comp Y.subtype).ker) = 3 := by
    rw [hker, card_subgroupOf_eq hzbY, card_zb hord]
  have h := Subgroup.card_ker_mul_card_range ((TwD7Q.pr β).comp Y.subtype)
  rw [hcardker, MonoidHom.range_comp, Subgroup.range_subtype, Nat.mul_comm] at h
  exact h

private theorem card_normalizer_inf_centralizer_eq_three_mul_card_normalizer_quot
    {G : Type} [Group G] [Finite G] {B : Basis3 G 8} :
    Nat.card ↥(Subgroup.normalizer (B.span : Set G) ⊓ TwD7Q.cen (B.b 0 * B.b 1)) =
      3 * Nat.card ↥(Subgroup.normalizer
        (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) := by
  have hord : orderOf (B.b 0 * B.b 1) = 3 := orderOf_b_mul_b B (by decide : (0 : Fin 8) ≠ 1)
  have hβE : B.b 0 * B.b 1 ∈ B.span := beta_mem_span B
  have hEcen : B.span ≤ TwD7Q.cen (B.b 0 * B.b 1) := span_le_cen_beta B
  have hβY : (⟨B.b 0 * B.b 1, TwD7Q.self_mem_cen _⟩ : ↥(TwD7Q.cen (B.b 0 * B.b 1))) ∈
      (Subgroup.normalizer (B.span : Set G) ⊓ TwD7Q.cen (B.b 0 * B.b 1)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1)) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨Subgroup.le_normalizer hβE, TwD7Q.self_mem_cen _⟩
  have hmap : Nat.card ↥(((Subgroup.normalizer (B.span : Set G) ⊓
        TwD7Q.cen (B.b 0 * B.b 1)).subgroupOf (TwD7Q.cen (B.b 0 * B.b 1))).map
          (TwD7Q.pr (B.b 0 * B.b 1))) * 3 =
      Nat.card ↥((Subgroup.normalizer (B.span : Set G) ⊓
        TwD7Q.cen (B.b 0 * B.b 1)).subgroupOf (TwD7Q.cen (B.b 0 * B.b 1))) :=
    card_map_pr_mul_three hord hβY
  have himg : ((Subgroup.normalizer (B.span : Set G) ⊓ TwD7Q.cen (B.b 0 * B.b 1)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1))).map (TwD7Q.pr (B.b 0 * B.b 1)) =
      Subgroup.normalizer (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1))) := by
    rw [Subgroup.inf_subgroupOf_right]
    apply le_antisymm
    · rintro q ⟨x, hx, rfl⟩
      have hxN : (x : G) ∈ Subgroup.normalizer (B.span : Set G) := Subgroup.mem_subgroupOf.mp hx
      rw [B.twD7Quot_span]
      exact (TwD7Q.pr_mem_normalizer_img_iff hβE hEcen).mpr hxN
    · intro q hq
      rw [B.twD7Quot_span] at hq
      obtain ⟨x, rfl⟩ := TwD7Q.pr_surjective (B.b 0 * B.b 1) q
      exact TwD7Q.pr_mem_img ((TwD7Q.pr_mem_normalizer_img_iff hβE hEcen).mp hq)
  have hYcard : Nat.card ↥((Subgroup.normalizer (B.span : Set G) ⊓
        TwD7Q.cen (B.b 0 * B.b 1)).subgroupOf (TwD7Q.cen (B.b 0 * B.b 1))) =
      Nat.card ↥(Subgroup.normalizer (B.span : Set G) ⊓ TwD7Q.cen (B.b 0 * B.b 1)) :=
    card_subgroupOf_eq inf_le_right
  rw [himg, hYcard] at hmap
  exact hmap.symm.trans (Nat.mul_comm _ _)

private theorem card_centralizer_eq_three_mul_card_centralizer_quot
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G} {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    Nat.card ↥(Subgroup.centralizer (B.span : Set G)) =
      3 * Nat.card ↥(Subgroup.centralizer
        (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) := by
  classical
  have hord : orderOf (B.b 0 * B.b 1) = 3 := orderOf_b_mul_b B (by decide : (0 : Fin 8) ≠ 1)
  have hrecβ : RecOutTwD7 B (B.b 0) := hB.2.1.symm ▸ hrec
  have hβE : B.b 0 * B.b 1 ∈ B.span := beta_mem_span B
  have hβCE : B.b 0 * B.b 1 ∈ Subgroup.centralizer (B.span : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, rfl⟩ := B.exists_vec_eq hy
    have hβeq : B.b 0 * B.b 1 = B.vec (Pi.single 0 1 + Pi.single 1 1) := by
      rw [B.vec_add, B.vec_single, B.vec_single]
    rw [hβeq]
    exact (commute_vec B e (Pi.single 0 1 + Pi.single 1 1)).eq
  have hCEcen : Subgroup.centralizer (B.span : Set G) ≤ TwD7Q.cen (B.b 0 * B.b 1) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hx) (B.b 0 * B.b 1) hβE).symm
  have hβY : (⟨B.b 0 * B.b 1, TwD7Q.self_mem_cen _⟩ : ↥(TwD7Q.cen (B.b 0 * B.b 1))) ∈
      (Subgroup.centralizer (B.span : Set G)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1)) := by
    rw [Subgroup.mem_subgroupOf]
    exact hβCE
  have hmap : Nat.card ↥(((Subgroup.centralizer (B.span : Set G)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1))).map (TwD7Q.pr (B.b 0 * B.b 1))) * 3 =
      Nat.card ↥((Subgroup.centralizer (B.span : Set G)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1))) :=
    card_map_pr_mul_three hord hβY
  have himg : ((Subgroup.centralizer (B.span : Set G)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1))).map (TwD7Q.pr (B.b 0 * B.b 1)) =
      Subgroup.centralizer (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1))) := by
    apply le_antisymm
    · rintro q ⟨x, hx, rfl⟩
      exact (B.pr_mem_centralizer_twD7Quot_span_iff hrecβ x).mpr
        (Subgroup.mem_subgroupOf.mp hx)
    · intro q hq
      obtain ⟨x, rfl⟩ := TwD7Q.pr_surjective (B.b 0 * B.b 1) q
      exact TwD7Q.pr_mem_img (x := x)
        ((B.pr_mem_centralizer_twD7Quot_span_iff hrecβ x).mp hq)
  have hYcard : Nat.card ↥((Subgroup.centralizer (B.span : Set G)).subgroupOf
        (TwD7Q.cen (B.b 0 * B.b 1))) =
      Nat.card ↥(Subgroup.centralizer (B.span : Set G)) :=
    card_subgroupOf_eq hCEcen
  rw [himg, hYcard] at hmap
  exact hmap.symm.trans (Nat.mul_comm _ _)

theorem card_ggAutomizer_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) :
    Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) = 2903040 := by
  classical
  have hb : Nat.card ↥(Subgroup.normalizer (B.span : Set G)) =
      696729600 * Nat.card ↥(Subgroup.centralizer (B.span : Set G)) := by
    have h := card_ggAutomizer_mul_card_centralizer (G := G) (A := B.span)
    rw [hrec.1] at h
    exact h.symm
  have hc : Nat.card ↥(Subgroup.normalizer (B.span : Set G)) =
      240 * Nat.card ↥(Subgroup.normalizer (B.span : Set G) ⊓
        TwD7Q.cen (B.b 0 * B.b 1)) :=
    card_normalizer_eq_orbit_mul_centralizer hstd hB hrec
  have hnorm : Nat.card ↥(Subgroup.normalizer (B.span : Set G) ⊓
        TwD7Q.cen (B.b 0 * B.b 1)) =
      3 * Nat.card ↥(Subgroup.normalizer
        (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) :=
    card_normalizer_inf_centralizer_eq_three_mul_card_normalizer_quot (B := B)
  have hcen : Nat.card ↥(Subgroup.centralizer (B.span : Set G)) =
      3 * Nat.card ↥(Subgroup.centralizer
        (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) :=
    card_centralizer_eq_three_mul_card_centralizer_quot hB hrec
  have haut : Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) *
        Nat.card ↥(Subgroup.centralizer
          (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) =
      Nat.card ↥(Subgroup.normalizer
        (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) :=
    card_ggAutomizer_mul_card_centralizer (G := TwD7Q.Q (B.b 0 * B.b 1)) (A := B.twD7Quot.span)
  have key : (696729600 * 3) * Nat.card ↥(Subgroup.centralizer
        (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) =
      (720 * Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span)) *
        Nat.card ↥(Subgroup.centralizer
          (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) := by
    calc (696729600 * 3) * Nat.card ↥(Subgroup.centralizer
            (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1))))
        = 696729600 * (3 * Nat.card ↥(Subgroup.centralizer
            (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1))))) := by
          rw [Nat.mul_assoc]
      _ = 696729600 * Nat.card ↥(Subgroup.centralizer (B.span : Set G)) := by rw [hcen]
      _ = Nat.card ↥(Subgroup.normalizer (B.span : Set G)) := hb.symm
      _ = 240 * Nat.card ↥(Subgroup.normalizer (B.span : Set G) ⊓
            TwD7Q.cen (B.b 0 * B.b 1)) := hc
      _ = 240 * (3 * Nat.card ↥(Subgroup.normalizer
            (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1))))) := by rw [hnorm]
      _ = 240 * (3 * (Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) *
            Nat.card ↥(Subgroup.centralizer
              (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))))) := by rw [← haut]
      _ = (720 * Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span)) *
            Nat.card ↥(Subgroup.centralizer
              (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) := by ring
  haveI : Nonempty ↥(Subgroup.centralizer
      (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) := ⟨1⟩
  have hpos : 0 < Nat.card ↥(Subgroup.centralizer
      (B.twD7Quot.span : Set (TwD7Q.Q (B.b 0 * B.b 1)))) := Nat.card_pos
  have hfinal : 696729600 * 3 = 720 * Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) :=
    Nat.mul_right_cancel hpos key
  rw [show (696729600 * 3 : ℕ) = 720 * 2903040 by norm_num] at hfinal
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 720) hfinal.symm

end CFSG.StandardType.FrameRoute.FS81
