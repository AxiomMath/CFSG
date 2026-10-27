module

public import CFSG.OddTranspositions.SevenFourEight.SecondKindConclusion
import CFSG.OddTranspositions.SizeBound
import CFSG.OddTranspositions.SevenThreeConclusion
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.OddTranspositions.O4CloseReduction

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_commute_DalphaStar
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) :
    ∃ x ∈ DalphaStar D hC.alpha, ∃ y ∈ DalphaStar D hC.alpha, x ≠ y ∧ Commute x y := by
  classical
  have _ := hmin
  by_contra hW
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have hL : LocalSecond D := localSecond_of_forall_secondKind hsecond
  have hW1 : ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c :=
    sixSeven hC (QZ.faithfulOnBlocks_of_localSecond hC hrad hL)
      (fun u _ v _ w h => hsecond u w v h)
  have hu : hC.d ∈ D := hC.hd
  have hcomm2 : ∀ {P : Subgroup G}, IsPGroup 2 P → ∀ a ∈ D, ∀ b ∈ D, a * b ∈ P →
      Commute a b := by
    intro P hP a ha b hb hab
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨a * b, hab⟩
    rw [Subgroup.orderOf_mk] at hk
    have h2 : orderOf (a * b) ∣ 2 := by
      rcases hD.2 a ha b hb with h | h
      · exact h
      · rw [hk] at h ⊢
        rcases k with _ | k
        · simp
        · exfalso
          obtain ⟨r, hr⟩ := h
          rw [pow_succ] at hr
          omega
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one (hD.mul_self_eq_one ha)
      (hD.mul_self_eq_one hb)).mpr (orderOf_dvd_iff_pow_eq_one.mp h2)
  have h3 : ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = 3 := by
    intro w hw
    obtain ⟨hwD, hwu, -⟩ := mem_Gamma_iff.mp (show w ∈ Gamma hC from hw)
    obtain ⟨v, hv, hvw⟩ := exists_DalphaStar_not_commute hC (show w ∈ Gamma hC from hw)
    have hvD : v ∈ D := (hC.DalphaStar_subset_commute hv).1
    have hvu : Commute v hC.d := (hC.DalphaStar_subset_commute hv).2
    have hvne : v ≠ hC.d := by
      have hvE := hv
      rw [hC.DalphaStar_alpha] at hvE
      exact (CFSG.Timmesfeld.Bridge.OddLocal.subset_commSet hN hC.hE hvE).2.2
    have htri : IsTriangle D hC.d w v :=
      ⟨hu, hvD, hwD, fun h => hvne h.symm, hvu.symm, fun h => hwu h.symm, hvw⟩
    have h4 : orderOf (hC.d * v * w) = 4 := hsecond _ _ _ htri
    have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({hC.d, w} : Set G) → IsTriangle D hC.d x v →
        ¬ IsThirdKind hC.d x v := by
      intro x _ _ hx hthird
      have h4' : orderOf (hC.d * v * x) = 4 := hsecond _ x _ hx
      obtain ⟨n, hnodd, _hn1, hord⟩ := hthird
      have hn2 : n = 2 := by omega
      rw [hn2] at hnodd
      obtain ⟨m, hm⟩ := hnodd
      omega
    set Q : Subgroup G := conjClosure (Subgroup.closure ({hC.d, w} : Set G)) (hC.d * v) with hQ
    set S : Subgroup G := Subgroup.zpowers hC.d ⊔ Q with hSdef
    have hS2 : IsPGroup 2 S := isPGroup_sup_zpowers_Q hD hN htri h4 hno
    have huS : hC.d ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hvS : v ∈ S := by
      have huvQ : hC.d * v ∈ Q := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
      have : v = hC.d * (hC.d * v) := by
        rw [← mul_assoc, hD.mul_self_eq_one hu, one_mul]
      rw [this]
      exact S.mul_mem huS (Subgroup.mem_sup_right huvQ)
    have hsub : ((S : Set G) ∩ D) ⊆ {hC.d, v} := by
      rintro x ⟨hxS, hxD⟩
      have hxu : Commute x hC.d := hcomm2 hS2 x hxD _ hu (S.mul_mem hxS huS)
      by_cases hxd : x = hC.d
      · exact Or.inl hxd
      refine Or.inr ?_
      have hxα : x ∉ hC.alpha := fun hxα => hxd (hW1 _ hxα _ hC.d_mem_alpha hxu)
      have hxDs : x ∈ DalphaStar D hC.alpha := by
        rcases (Set.ext_iff.mp hC.eq_alpha_union x).mp hxD with (h | h) | h
        · exact (hxα h).elim
        · exact h
        · exact ((mem_Gamma_iff.mp (show x ∈ Gamma hC from h)).2.1 hxu).elim
      have hxv : Commute x v := hcomm2 hS2 x hxD v hvD (S.mul_mem hxS hvS)
      by_contra hxv'
      exact hW ⟨x, hxDs, v, hv, hxv', hxv⟩
    have hcard : Nat.card (((S : Set G) ∩ D : Set G)) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    have hle : orderOf (hC.d * w) ≤ 3 := by
      by_contra hgt
      have h3S : 3 ≤ Nat.card (((S : Set G) ∩ D : Set G)) :=
        three_le_card_inter_D hD hN htri h4 hno (by omega)
      omega
    have hodd : Odd (orderOf (hC.d * w)) := hD.odd_of_not_commute hu hwD (fun h => hwu h.symm)
    have hne1 : orderOf (hC.d * w) ≠ 1 := by
      intro h
      have e := hD.eq_of_mul_eq_one hu (orderOf_eq_one_iff.mp h)
      rw [← e] at hwu
      exact hwu (Commute.refl _)
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨w, hw, hw3⟩ := sevenThree hC hrad hL h3 hnot3
  exact hw3 (h3 w hw)

end CFSG.OddTranspositions

end
