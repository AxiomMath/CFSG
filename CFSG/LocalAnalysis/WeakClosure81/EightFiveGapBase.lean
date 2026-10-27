module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.CGT.Timmesfeld75.OddCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

section CentralInSylow

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem centralInSylow_map (φ : X →* Y) (hφ : Function.Surjective φ) (S : Subgroup X)
    (h : CentralInSylow X S) : CentralInSylow Y (S.map φ) := by
  obtain ⟨P, hSP, hcen⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨P.mapSurjective hφ, Subgroup.map_mono hSP, ?_⟩
  intro y hy z hz
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
  simpa only [map_mul] using congrArg φ (hcen s hs p hp)

end CentralInSylow

section BarSituationTwo

theorem odd_card_center_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) :=
  CFSG.CGT.Timmesfeld75.odd_card_center fun N hN hN2 => by
    rw [eq_bot_iff, ← h]
    exact le_sSup ⟨hN, hN2⟩

private theorem w85g_orderOf_map_eq_two {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hodd : Odd (Nat.card f.ker)) {x : G} (hx : orderOf x = 2) :
    orderOf (f x) = 2 := by
  have hdvd : orderOf (f x) ∣ orderOf x := orderOf_map_dvd f x
  rw [hx] at hdvd
  have hne : f x ≠ 1 := by
    intro h1
    have hmem : x ∈ f.ker := MonoidHom.mem_ker.mpr h1
    have hxdvd : orderOf x ∣ Nat.card f.ker := Subgroup.orderOf_dvd_natCard f.ker hmem
    rw [hx] at hxdvd
    exact (by decide : ¬ Odd 2) (Odd.of_dvd_nat hodd hxdvd)
  have hne1 : orderOf (f x) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

private theorem w85g_image_conjugatesOfSet_singleton {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (a : G) :
    f '' Group.conjugatesOfSet ({a} : Set G) = {y : H | IsConj (f a) y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨b, hb, hconj⟩ := hx
    rw [Set.mem_singleton_iff] at hb
    obtain rfl : b = a := hb
    rw [isConj_iff] at hconj
    obtain ⟨c, hc⟩ := hconj
    simp only [Set.mem_setOf_eq]
    exact isConj_iff.mpr ⟨f c, by rw [← hc]; simp [map_mul]⟩
  · intro hy
    rw [Set.mem_setOf_eq, isConj_iff] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨a', ha'⟩ := hf c
    refine ⟨a' * a * a'⁻¹, ?_, ?_⟩
    · rw [Group.mem_conjugatesOfSet_iff]
      exact ⟨a, rfl, isConj_iff.mpr ⟨a', rfl⟩⟩
    · rw [map_mul, map_mul, map_inv, ha']
      exact hc

theorem barSituation_map_two {X Y : Type} [Group X] [Finite X] [Group Y] {S : Subgroup X}
    (hS : BarSituation X S) (h2 : Nat.card S = 2) (φ : X →* Y) (hφ : Function.Surjective φ)
    (hodd : Odd (Nat.card φ.ker)) :
    ∃ d : Y, d * d = 1 ∧ d ≠ 1 ∧ S.map φ = Subgroup.zpowers d ∧
      CFSG.Timmesfeld.Bridge.Asc72.IsOddTranspClass {y : Y | IsConj d y} := by
  obtain ⟨s, hs, hs_ne⟩ : ∃ s : X, s ∈ S ∧ s ≠ 1 := by
    have hSne : S ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h2
      omega
    obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
    exact ⟨s, hs, fun h => hs1 (Subtype.ext h)⟩
  have hord : orderOf s = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (hS.elemAbelian.2 s hs) hs_ne
  have hSeq : S = Subgroup.zpowers s := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers s) (K := S) ?_ ?_).symm
    · exact Subgroup.zpowers_le.mpr hs
    · rw [h2, Nat.card_zpowers, hord]
  have hmapS : S.map φ = Subgroup.zpowers (φ s) := by
    rw [hSeq, MonoidHom.map_zpowers]
  have hdd : φ s * φ s = 1 := by
    rw [← map_mul, ← pow_two, hS.elemAbelian.2 s hs, map_one]
  have hd1 : φ s ≠ 1 := by
    intro h1
    have h2o : orderOf (φ s) = 2 := w85g_orderOf_map_eq_two φ hodd hord
    rw [h1, orderOf_one] at h2o
    exact (by decide : ¬ (1 = 2)) h2o
  have hD0 : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp
      (Group.conjugatesOfSet ({s} : Set X)) :=
    (hS.oddTransp h2).mono (Group.conjugatesOfSet_mono (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hs, hs_ne⟩))
  have hne : ∀ x ∈ Group.conjugatesOfSet ({s} : Set X), φ x ≠ 1 := by
    intro x hx hx1
    have hxord : orderOf x = 2 := hD0.1 x hx
    have h2o : orderOf (φ x) = 2 := w85g_orderOf_map_eq_two φ hodd hxord
    rw [hx1, orderOf_one] at h2o
    exact (by decide : ¬ (1 = 2)) h2o
  have himg : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp
      (φ '' Group.conjugatesOfSet ({s} : Set X)) := hD0.image φ hne
  have himageS : (S.map φ : Set Y) = φ '' (S : Set X) := by
    ext y
    simp [Subgroup.mem_map]
  have hmapNormal : Subgroup.normalClosure (φ '' (S : Set X)) = ⊤ := by
    have h := congrArg (Subgroup.map φ) hS.normalClosure_eq_top
    rwa [Subgroup.map_normalClosure (S : Set X) φ hφ,
      Subgroup.map_top_of_surjective φ hφ] at h
  have hnc_zpow : Subgroup.normalClosure
      ((Subgroup.zpowers (φ s) : Subgroup Y) : Set Y) = ⊤ := by
    rw [← hmapS, himageS]
    exact hmapNormal
  have hnc_sing : Subgroup.normalClosure
      ((Subgroup.zpowers (φ s) : Subgroup Y) : Set Y)
      = Subgroup.normalClosure ({φ s} : Set Y) := by
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      intro x hx
      exact (Subgroup.zpowers_le.mpr
        (Subgroup.subset_normalClosure (Set.mem_singleton (φ s)))) hx
    · apply Subgroup.normalClosure_mono
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_zpowers (φ s)
  have hnc_D : Subgroup.normalClosure ({φ s} : Set Y)
      = Subgroup.closure {y : Y | IsConj (φ s) y} := by
    rw [Subgroup.normalClosure]
    congr 1
    ext x
    simp [Group.mem_conjugatesOfSet_iff]
  have hclosure : Subgroup.closure {y : Y | IsConj (φ s) y} = ⊤ := by
    rw [← hnc_D, ← hnc_sing, hnc_zpow]
  refine ⟨φ s, hdd, hd1, hmapS, ⟨⟨φ s, rfl⟩, ?_, hclosure⟩⟩
  rw [w85g_image_conjugatesOfSet_singleton φ hφ s] at himg
  exact himg

end BarSituationTwo

end CFSG.LocalAnalysis.WeakClosure81

end
