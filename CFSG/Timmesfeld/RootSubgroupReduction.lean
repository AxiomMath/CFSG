module

public import CFSG.Timmesfeld.RootSubgroupKernel
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem mem_closure_pair_conj_of_odd {t c : G} (ht : t * t = 1) (hc : c * c = 1)
    (hodd : Odd (orderOf (t * c))) : t ∈ Subgroup.closure ({c, t * c * t⁻¹} : Set G) := by
  obtain ⟨k, hk⟩ := hodd
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  set H := Subgroup.closure ({c, t * c * t⁻¹} : Set G)
  have hcH : c ∈ H := Subgroup.subset_closure (by simp)
  have hc'H : t * c * t⁻¹ ∈ H := Subgroup.subset_closure (by simp)
  have hsq : c * (t * c * t⁻¹) = (c * t) ^ 2 := by rw [htinv, pow_two]; group
  have hct : orderOf (c * t) = 2 * k + 1 := by rw [orderOf_mul_comm_eq, hk]
  have hpow : ((c * t) ^ 2) ^ (k + 1) = c * t := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hct,
      pow_orderOf_eq_one, one_mul]
  have hctH : c * t ∈ H := by
    rw [← hpow, ← hsq]
    exact H.pow_mem (H.mul_mem hcH hc'H) _
  have : t = c * (c * t) := by rw [← mul_assoc, hc, one_mul]
  rw [this]
  exact H.mul_mem hcH hctH

theorem conj_mem_rootSet_of_orderOf_eq_three (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a b c : G} (ha : a ∈ D) (hb : b ∈ rootSet D a) (hc : c ∈ D)
    (h3a : orderOf (a * c) = 3) (h3b : orderOf (b * c) = 3) :
    a * b * c * (a * b)⁻¹ ∈ rootSet D c := by
  have hb' : b ∈ D := hb.1
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb'
  have hc2 := hD.mul_self_eq_one hc
  have hainv : a⁻¹ = a := hD.inv_eq ha
  have hbinv : b⁻¹ = b := hD.inv_eq hb'
  have hcinv : c⁻¹ = c := hD.inv_eq hc
  have braid : ∀ {x : G}, x * x = 1 → orderOf (x * c) = 3 → x * c * x = c * x * c := by
    intro x hx2 h3
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have h : x * c * x * (c * x * c) = 1 := by
      rw [← pow_orderOf_eq_one (x * c), h3]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, hxinv, hcinv, mul_assoc]
  have hba := braid ha2 h3a
  have hbb := braid hb2 h3b
  have hab : Commute a b := commute_of_mem_rootSet ha (mem_rootSet_self ha) hb
  have h1 : a * c * a * (a * c)⁻¹ = c := by
    rw [mul_inv_rev, hainv, hcinv, show a * c * a * (c * a) = a * c * a * c * a by group, hba]
    rw [show c * a * c * c * a = c * a * (c * c) * a by group, hc2, mul_one, mul_assoc, ha2,
      mul_one]
  have h2 : a * c * b * (a * c)⁻¹ = a * b * c * (a * b)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hainv, hcinv, hbinv,
      show a * c * b * (c * a) = a * (c * b * c) * a by group, ← hbb]
    rw [show a * (b * c * b) * a = a * b * c * (b * a) by group, ← hab.eq]
  have hmem : a * c * b * (a * c)⁻¹ ∈ rootSet D (a * c * a * (a * c)⁻¹) := by
    rw [rootSet_conj hclass]
    exact ⟨b, hb, rfl⟩
  rwa [h1, h2] at hmem

theorem exists_opposite_not_commute [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {d : G} (hd : d ∈ D) : ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) := by
  obtain ⟨c, hc, h1, hodd⟩ := exists_opposite hclass hD hO2 hd
  refine ⟨c, hc, fun hdc => ?_, hodd⟩
  have h2 := orderOf_dvd_of_pow_eq_one
    ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hc)).1 hdc)
  have h3 : orderOf (d * c) ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  rcases hodd with ⟨k, hk⟩
  omega

theorem mul_mem_rootSet_of_forall_fixes [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {d a b : G} (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b)
    (hOS : ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
      ∃ e ∈ insert 1 (rootSet D d), a * b * e * c * (a * b * e)⁻¹ ∈ rootSet D c)
    (hSemi : ∀ w ∈ rootGroup D d, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
      w * c * w⁻¹ ∈ rootSet D c → FixesOpposite D d w) :
    a * b ∈ rootSet D d := by
  obtain ⟨c, hc, hnc, hodd⟩ := exists_opposite_not_commute hclass hD hO2 hd
  obtain ⟨e, he, hfix⟩ := hOS c hc hnc hodd
  have heW : e ∈ rootGroup D d := by
    rcases he with rfl | he
    · exact (rootGroup D d).one_mem
    · exact rootSet_subset_rootGroup D d he
  have hw : a * b * e ∈ rootGroup D d :=
    (rootGroup D d).mul_mem ((rootGroup D d).mul_mem (rootSet_subset_rootGroup D d ha)
      (rootSet_subset_rootGroup D d hb)) heW
  have h1 : a * b * e = 1 :=
    eq_one_of_fixesOpposite hclass hD hO2 hd (hSemi _ hw c hc hnc hodd hfix)
  have he2 : e * e = 1 := mul_self_eq_one_of_mem_rootGroup hD hd heW
  have hab' : a * b = e := by
    have : a * b = (a * b * e) * e := by rw [mul_assoc, he2, mul_one]
    rw [this, h1, one_mul]
  rcases he with rfl | he
  · exfalso
    apply hab
    have : a * b = 1 := hab'
    have hbinv : b⁻¹ = b := hD.inv_eq hb.1
    rw [← hbinv]
    exact eq_inv_of_mul_eq_one_left this
  · rwa [hab']

theorem exists_rootSubgroup_of_closed (hD : IsRootInvolutionSet D) {d : G}
    (hclosed : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∈ rootSet D d) :
    ∃ A : Subgroup G, (A : Set G) = insert 1 (rootSet D d) ∧ ∀ a ∈ A, a * a = 1 := by
  have hmul : ∀ x ∈ insert (1 : G) (rootSet D d), ∀ y ∈ insert (1 : G) (rootSet D d),
      x * y ∈ insert (1 : G) (rootSet D d) := by
    rintro x (rfl | hx) y (rfl | hy)
    · exact Or.inl (mul_one 1)
    · rw [one_mul]; exact Or.inr hy
    · rw [mul_one]; exact Or.inr hx
    · by_cases hxy : x = y
      · subst hxy; exact Or.inl (hD.mul_self_eq_one hx.1)
      · exact Or.inr (hclosed x hx y hy hxy)
  have hinv : ∀ x ∈ insert (1 : G) (rootSet D d), x⁻¹ ∈ insert (1 : G) (rootSet D d) := by
    rintro x (rfl | hx)
    · exact Or.inl inv_one
    · rw [hD.inv_eq hx.1]; exact Or.inr hx
  refine ⟨{ carrier := insert 1 (rootSet D d)
            mul_mem' := fun hx hy => hmul _ hx _ hy
            one_mem' := Or.inl rfl
            inv_mem' := fun hx => hinv _ hx }, rfl, ?_⟩
  rintro x (rfl | hx)
  · exact mul_one 1
  · exact hD.mul_self_eq_one hx.1

theorem ncard_rootSet_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g d : G) :
    (rootSet D (g * d * g⁻¹)).ncard = (rootSet D d).ncard := by
  rw [rootSet_conj hclass, Set.ncard_image_of_injective _ (fun x y hxy => by simpa using hxy)]

theorem ncard_rootSet_eq (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) : (rootSet D e).ncard = (rootSet D d).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hclass hd he)
  exact ncard_rootSet_conj hclass g d

end CFSG.Timmesfeld
