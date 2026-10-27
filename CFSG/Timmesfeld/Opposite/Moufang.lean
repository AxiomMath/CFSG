module

public import CFSG.Timmesfeld.RootSubgroupClosure
public import CFSG.Timmesfeld.RankOne.Lift

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem rootGroup_eq_iff [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) : rootGroup D x = rootGroup D y ↔ rootSet D x = rootSet D y := by
  refine ⟨fun h => ?_, fun h => by rw [rootGroup, rootGroup, h]⟩
  have hyx : y ∈ rootSet D x :=
    mem_rootSet_of_mem_rootGroup hclass hx hy (h ▸ rootSet_subset_rootGroup D y
      (mem_rootSet_self hy))
  exact (rootSet_eq_of_mem hyx).symm

theorem map_conj_rootGroup_eq_iff [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : ¬ Commute a b)
    (hodd : Odd (orderOf (a * b))) :
    (rootGroup D a).map (MulAut.conj b).toMonoidHom =
        (rootGroup D b).map (MulAut.conj a).toMonoidHom ↔ orderOf (a * b) = 3 := by
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hainv : a⁻¹ = a := hD.inv_eq ha
  have hbinv : b⁻¹ = b := hD.inv_eq hb
  have hbab : b * a * b⁻¹ ∈ D := conj_mem_of_isClass hclass b ha
  have haba : a * b * a⁻¹ ∈ D := conj_mem_of_isClass hclass a hb
  rw [← rootGroup_conj hclass, ← rootGroup_conj hclass, rootGroup_eq_iff hclass hbab haba]
  constructor
  · intro h
    have hmem : a * b * a⁻¹ ∈ rootSet D (b * a * b⁻¹) := h ▸ mem_rootSet_self haba
    have hc := commute_of_mem_rootSet hbab (mem_rootSet_self hbab) hmem
    have h6 : (b * a) ^ 6 = 1 := by
      have := (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hbab)
        (hD.mul_self_eq_one haba)).1 hc
      rw [hainv, hbinv] at this
      rw [← this, show b * a * b * (a * b * a) = (b * a) ^ 3 by simp [pow_succ, mul_assoc],
        ← pow_mul]
    have hdvd := orderOf_dvd_of_pow_eq_one h6
    rw [orderOf_mul_comm_eq] at hdvd
    have hne1 : orderOf (a * b) ≠ 1 := by
      intro h1
      apply hab
      have : a * b = 1 := orderOf_eq_one_iff.mp h1
      have hba : b = a⁻¹ := eq_inv_of_mul_eq_one_right this
      rw [hba, hainv]
    have hle : orderOf (a * b) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hodd
    generalize orderOf (a * b) = n at *
    interval_cases n <;> omega
  · intro h3
    have h := pow_orderOf_eq_one (a * b)
    rw [h3] at h
    have hbr : a * b * a⁻¹ = b * a * b⁻¹ := by
      rw [hainv, hbinv]
      have h' : a * b * a * (b * a * b) = 1 := by
        rw [← h]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [eq_inv_of_mul_eq_one_left h', mul_inv_rev, mul_inv_rev, hainv, hbinv, mul_assoc]
    rw [hbr]

theorem map_conj_subgroupOf {H X : Subgroup G} (x : X) :
    (H.subgroupOf X).map (MulAut.conj x).toMonoidHom =
      (H.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf X := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by simp⟩
  · rintro ⟨h, hh, hy⟩
    have hhX : h ∈ X := by
      have : h = (x : G)⁻¹ * y * x := by rw [← hy]; group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem x.2) y.2) x.2
    exact ⟨⟨h, hhX⟩, hh, Subtype.ext (by simpa using hy)⟩

theorem card_subgroupOf_of_le {H X : Subgroup G} (h : H ≤ X) :
    Nat.card (H.subgroupOf X) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

variable [Finite G]

theorem isElemAbRankOne_of_moufang (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hcD : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c)))
    (hM : ∀ a ∈ rootSet D d, ∃ b ∈ rootSet D c, orderOf (a * b) = 3)
    (hM' : ∀ b ∈ rootSet D c, ∃ a ∈ rootSet D d, orderOf (a * b) = 3) :
    IsElemAbRankOne ((rootGroup D d).subgroupOf (rootGroup D d ⊔ rootGroup D c))
      ((rootGroup D c).subgroupOf (rootGroup D d ⊔ rootGroup D c)) := by
  set A := rootGroup D d
  set B := rootGroup D c
  set X := A ⊔ B
  have hpair : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D c, orderOf (a * b) = 3 →
      A.map (MulAut.conj b).toMonoidHom = B.map (MulAut.conj a).toMonoidHom := by
    intro a ha b hb h3
    obtain ⟨hodd', hc'⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hcD ha hb hodd hdc
    have := (map_conj_rootGroup_eq_iff hclass hD ha.1 hb.1 hc' hodd').2 h3
    rwa [rootGroup_eq_of_mem ha, rootGroup_eq_of_mem hb] at this
  have hmemT : ∀ x : X, x ∈ A.subgroupOf X → x ≠ 1 → (x : G) ∈ rootSet D d := by
    intro x hx hx1
    rcases (mem_rootGroup_iff_of_rootClosure hD hrc hd).1 hx with h | h
    · exact absurd (Subtype.ext h) hx1
    · exact h
  have hmemR : ∀ x : X, x ∈ B.subgroupOf X → x ≠ 1 → (x : G) ∈ rootSet D c := by
    intro x hx hx1
    rcases (mem_rootGroup_iff_of_rootClosure hD hrc hcD).1 hx with h | h
    · exact absurd (Subtype.ext h) hx1
    · exact h
  refine ⟨codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup A B), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hAB
    rw [Subgroup.subgroupOf_inj, inf_of_le_left le_sup_left, inf_of_le_left le_sup_right] at hAB
    have h1 : d ∈ A := rootSet_subset_rootGroup D d (mem_rootSet_self hd)
    rw [hAB] at h1
    have hdc' : d ∈ rootSet D c := mem_rootSet_of_mem_rootGroup hclass hcD hd h1
    exact hdc (commute_of_mem_rootSet hcD hdc' (mem_rootSet_self hcD))
  · intro a ha a' ha'
    exact Subtype.ext (commute_of_mem_rootGroup hd ha ha').eq
  · intro a ha
    exact Subtype.ext (mul_self_eq_one_of_mem_rootGroup hD hd ha)
  · intro a ha ha1
    obtain ⟨b, hb, h3⟩ := hM _ (hmemT a ha ha1)
    have hbX : b ∈ X := Subgroup.mem_sup_right (rootSet_subset_rootGroup D c hb)
    refine ⟨⟨b, hbX⟩, rootSet_subset_rootGroup D c hb, fun h => ?_, ?_⟩
    · exact hD.ne_one hb.1 (congrArg Subtype.val h)
    · rw [map_conj_subgroupOf, map_conj_subgroupOf, hpair _ (hmemT a ha ha1) b hb h3]
  · intro b hb hb1
    obtain ⟨a, ha, h3⟩ := hM' _ (hmemR b hb hb1)
    have haX : a ∈ X := Subgroup.mem_sup_left (rootSet_subset_rootGroup D d ha)
    refine ⟨⟨a, haX⟩, rootSet_subset_rootGroup D d ha, fun h => ?_, ?_⟩
    · exact hD.ne_one ha.1 (congrArg Subtype.val h)
    · rw [map_conj_subgroupOf, map_conj_subgroupOf, hpair a ha _ (hmemR b hb hb1) h3]

theorem exists_mulEquiv_SL2_of_moufang {G : Type} [Group G] [Finite G] {D : Set G}
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c)))
    (hM : ∀ a ∈ rootSet D d, ∃ b ∈ rootSet D c, orderOf (a * b) = 3)
    (hM' : ∀ b ∈ rootSet D c, ∃ a ∈ rootSet D d, orderOf (a * b) = 3)
    (hq : 4 ≤ Nat.card (rootGroup D d)) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (rootGroup D d) = 2 ^ n ∧
      ∃ φ : ↥(rootGroup D d ⊔ rootGroup D c) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        ((rootGroup D d).subgroupOf (rootGroup D d ⊔ rootGroup D c)).map φ.toMonoidHom =
            upperUnipotent (GaloisField 2 n) ∧
          ((rootGroup D c).subgroupOf (rootGroup D d ⊔ rootGroup D c)).map φ.toMonoidHom =
            lowerUnipotent (GaloisField 2 n) := by
  have h := isElemAbRankOne_of_moufang hclass hD hrc hd hcD hdc hodd hM hM'
  have hcard := card_subgroupOf_of_le (le_sup_left : rootGroup D d ≤ rootGroup D d ⊔ rootGroup D c)
  rw [← hcard] at hq ⊢
  exact rankOne_mulEquiv_SL2 h hq

theorem card_sup_rootGroup_eq_six_of_moufang {G : Type} [Group G] [Finite G] {D : Set G}
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c)))
    (hM : ∀ a ∈ rootSet D d, ∃ b ∈ rootSet D c, orderOf (a * b) = 3)
    (hM' : ∀ b ∈ rootSet D c, ∃ a ∈ rootSet D d, orderOf (a * b) = 3)
    (hq : Nat.card (rootGroup D d) = 2) :
    Nat.card ↥(rootGroup D d ⊔ rootGroup D c) = 6 := by
  have h := isElemAbRankOne_of_moufang hclass hD hrc hd hcD hdc hodd hM hM'
  have hcard := card_subgroupOf_of_le (le_sup_left : rootGroup D d ≤ rootGroup D d ⊔ rootGroup D c)
  exact rankOne_two h (hcard.trans hq)

end CFSG.Timmesfeld
