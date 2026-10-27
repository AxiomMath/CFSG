module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalCent
public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalProd

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace TwoLocalSetting

variable {G : Type} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem card_center {a : G} (ha : a ∈ D) (h5 : 5 ≤ (rootLines D a).ncard) :
    Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) = 2 := by
  rw [S.centralizer_nCore ha h5, inf_eq_right.2 ((Subgroup.zpowers_le).2 (S.self_mem ha)),
    Nat.card_zpowers, S.root.orderOf_eq_two ha]

theorem list_prod_mem_zpowers [DecidableEq G] {a : G} (ha : a ∈ D)
    (h5 : 5 ≤ (rootLines D a).ncard) {l : List G} (hl : ∀ y ∈ l, y ∈ D ∧ Commute a y ∧ y ≠ a)
    (hnd : l.Nodup) (hnc : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ Commute x y) (hodd : Odd l.length)
    (hcov : ∀ z ∈ D, Commute a z → z ≠ a → ∃ y ∈ l, Commute z y) :
    l.prod ∈ Subgroup.zpowers a := by
  rw [← S.centralizer_nCore ha h5, Subgroup.mem_centralizer_iff]
  intro m hm
  have hcen : ∀ e ∈ D, Commute e a → Commute l.prod e := by
    intro e he hea
    by_cases hea' : e = a
    · rw [hea']
      refine Commute.list_prod_left _ _ fun y hy => (hl y hy).2.1.symm
    · exact (S.list_prod_commute ha hl hnd hnc hodd hcov he hea.symm hea').symm
  exact ((S.forall_commute_nCore_iff ha).2 hcen m hm).symm.eq

theorem toList_prod_mem_zpowers [DecidableEq G] {a : G} (ha : a ∈ D)
    (h5 : 5 ≤ (rootLines D a).ncard) {P : Finset G} (hPk : P.card = (rootLines D a).ncard)
    (hP : ∀ x ∈ P, x ∈ D ∧ Commute a x ∧ x ≠ a) (hnc : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ Commute x y)
    (hcov : ∀ x ∈ D, Commute a x → x ≠ a → x ∈ P ∨ a * x ∈ P) :
    P.toList.prod ∈ Subgroup.zpowers a := by
  have hL := S.lineSetting
  obtain ⟨m, hm⟩ := hL.exists_ncard_rootLines ha
  have hodd : Odd P.toList.length := by
    rw [Finset.length_toList, hPk, hm]
    have hm2 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      omega
    exact (Nat.even_pow.2 ⟨even_two, hm2⟩).add_one
  refine S.list_prod_mem_zpowers ha h5 (fun y hy => hP y (Finset.mem_toList.1 hy))
    P.nodup_toList (fun x hx y hy => hnc x (Finset.mem_toList.1 hx) y (Finset.mem_toList.1 hy))
    hodd fun z hz haz hza => ?_
  rcases hcov z hz haz hza with h | h
  · exact ⟨z, Finset.mem_toList.2 h, Commute.refl z⟩
  · exact ⟨a * z, Finset.mem_toList.2 h, haz.symm.mul_right (Commute.refl z)⟩

theorem card_nCore {a : G} (ha : a ∈ D) (h5 : 5 ≤ (rootLines D a).ncard) :
    Nat.card (nCore D a) = 2 ^ (rootLines D a).ncard := by
  classical
  have := S.hyp.finite
  have hD := S.root
  set k := (rootLines D a).ncard
  refine le_antisymm ?_ ?_
  · obtain ⟨P, hPk, hP, hnc, hcov⟩ := S.exists_transversal ha
    have ht := S.toList_prod_mem_zpowers ha h5 hPk hP hnc hcov
    have hne : P.toList ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [Finset.length_toList, hPk] at this
      simp at this
      omega
    obtain ⟨x₀, rest, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hnd : (x₀ :: rest).Nodup := hrest ▸ P.nodup_toList
    have hmemP : ∀ y ∈ x₀ :: rest, y ∈ P := fun y hy =>
      Finset.mem_toList.1 (by rw [hrest]; exact hy)
    set N := Subgroup.closure (insert a (rest.toFinset : Set G))
    have hrestN : rest.prod ∈ N := N.list_prod_mem fun y hy =>
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (by simpa using hy))
    have haN : a ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)
    have hx₀N : x₀ ∈ N := by
      have ht' : x₀ * rest.prod ∈ Subgroup.zpowers a := by
        rw [hrest, List.prod_cons] at ht
        exact ht
      have hzN : x₀ * rest.prod ∈ N := by
        rcases (mem_zpowers_iff_of_mul_self (hD.mul_self_eq_one ha)).1 ht' with h | h <;> rw [h]
        · exact N.one_mem
        · exact haN
      have e : x₀ = x₀ * rest.prod * rest.prod⁻¹ := by group
      rw [e]
      exact N.mul_mem hzN (N.inv_mem hrestN)
    have hle : nCore D a ≤ N := by
      rw [S.nCore_eq_closure_insert ha hP hcov, Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact haN
      · have hy' : y ∈ x₀ :: rest := by rw [← hrest]; exact Finset.mem_toList.2 hy
        rcases List.mem_cons.1 hy' with rfl | hy''
        · exact hx₀N
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (by simpa using hy''))
    have hcard := S.card_closure_insert_le ha rest.toFinset fun y hy => by
      have hyP := hmemP y (List.mem_cons_of_mem _ (by simpa using hy))
      exact ⟨S.mem_nCore ha (hP y hyP).1 (hP y hyP).2.1.symm, hD.mul_self_eq_one (hP y hyP).1⟩
    have hlen : rest.toFinset.card = k - 1 := by
      rw [List.toFinset_card_of_nodup (List.nodup_cons.1 hnd).2]
      have := congrArg List.length hrest
      rw [Finset.length_toList, hPk, List.length_cons] at this
      omega
    rw [hlen, show k - 1 + 1 = k by omega] at hcard
    exact (Subgroup.card_le_of_le hle).trans hcard
  · have h := S.two_pow_mul_card_center_le ha
    rw [S.card_center ha h5, ← pow_succ, show k - 1 + 1 = k by omega] at h
    exact h

theorem mul_five_mem {a : G} (ha : a ∈ D) (h5 : (rootLines D a).ncard = 5)
    {x₁ x₂ x₃ x₄ x₅ : G} (hx : ∀ x ∈ [x₁, x₂, x₃, x₄, x₅], x ∈ D ∧ Commute a x ∧ x ≠ a)
    (hnc : [x₁, x₂, x₃, x₄, x₅].Pairwise fun x y => ¬ Commute x y) :
    x₁ * x₂ * x₃ * x₄ * x₅ = 1 ∨ x₁ * x₂ * x₃ * x₄ * x₅ = a := by
  classical
  set l := [x₁, x₂, x₃, x₄, x₅] with hl
  have hsymm : Std.Symm (fun x y : G => ¬ Commute x y) := ⟨fun x y h h' => h h'.symm⟩
  have hnc' : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ Commute x y := fun x hx y hy hxy =>
    hnc.forall hx hy hxy
  have hnd : l.Nodup :=
    List.Pairwise.imp (fun {x y} (h : ¬ Commute x y) (hxy : x = y) => h (hxy ▸ Commute.refl x)) hnc
  have hcov : ∀ z ∈ D, Commute a z → z ≠ a → ∃ y ∈ l, Commute z y := by
    intro z hz haz hza
    by_contra hno
    push Not at hno
    have hzl : z ∉ l := fun h => hno z h (Commute.refl z)
    have hnd' : (z :: l).Nodup := List.nodup_cons.2 ⟨hzl, hnd⟩
    have hQ : ∀ x ∈ ((z :: l).toFinset : Set G), x ∈ D ∧ Commute a x ∧ x ≠ a := by
      intro x hxQ
      rcases List.mem_cons.1 (by simpa using hxQ) with rfl | hx'
      · exact ⟨hz, haz, hza⟩
      · exact hx x hx'
    have hpair : ((z :: l).toFinset : Set G).Pairwise fun x y => ¬ Commute x y := by
      intro x hx y hy hxy
      rcases List.mem_cons.1 (by simpa using hx) with rfl | hx' <;>
        rcases List.mem_cons.1 (by simpa using hy) with rfl | hy'
      · exact absurd rfl hxy
      · exact hno y hy'
      · exact fun h => hno x hx' h.symm
      · exact hnc' x hx' y hy' hxy
    have hle := S.ncard_le_of_pairwise ha hQ hpair
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', h5] at hle
    simp [hl] at hle
  have hprod := S.list_prod_mem_zpowers ha (by omega) hx hnd hnc' ⟨2, by simp [hl]⟩ hcov
  have e : l.prod = x₁ * x₂ * x₃ * x₄ * x₅ := by simp [hl, mul_assoc]
  rw [e] at hprod
  exact (mem_zpowers_iff_of_mul_self (S.root.mul_self_eq_one ha)).1 hprod

end TwoLocalSetting

end CFSG.Timmesfeld.Bridge
