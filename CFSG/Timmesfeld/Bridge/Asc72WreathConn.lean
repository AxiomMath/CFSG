module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Closure.MinCex
import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki Equiv SemidirectProduct

namespace WreathConn

variable {f n : ℕ}

theorem permAct_apply {ι L : Type*} [Group L] (σ : Perm ι) (h : ι → L) (i : ι) :
    permAct ι L σ h i = h (σ⁻¹ i) := rfl

theorem permAct_symm_apply {ι L : Type*} [Group L] (σ : Perm ι) (h : ι → L) (i : ι) :
    (permAct ι L σ).symm h i = h (σ i) := rfl

theorem conj_inr_right (c : L2Wreath f n) (s : Perm (Fin n)) :
    (c * inr s * c⁻¹).right = c.right * s * c.right⁻¹ := by
  simp

theorem conj_inr_left (c : L2Wreath f n) (s : Perm (Fin n)) (k : Fin n) :
    (c * inr s * c⁻¹).left k =
      c.left k * (c.left ((c.right * s * c.right⁻¹)⁻¹ k))⁻¹ := by
  simp [permAct_apply, permAct_symm_apply, Perm.mul_apply]

theorem isConj_inr_swap_iff {a b : Fin n} (hab : a ≠ b) (x : L2Wreath f n) :
    IsConj (inr (swap a b)) x ↔ ∃ i j : Fin n, i ≠ j ∧ x.right = swap i j ∧
      (∀ k, k ≠ i → k ≠ j → x.left k = 1) ∧ x.left j = (x.left i)⁻¹ := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    have hr : c.right * swap a b * c.right⁻¹ = swap (c.right a) (c.right b) :=
      (swap_apply_apply c.right a b).symm
    refine ⟨c.right a, c.right b, c.right.injective.ne hab, by rw [conj_inr_right, hr], ?_, ?_⟩
    · intro k hka hkb
      rw [conj_inr_left, hr, swap_inv, swap_apply_of_ne_of_ne hka hkb, mul_inv_cancel]
    · rw [conj_inr_left, conj_inr_left, hr, swap_inv, swap_apply_left, swap_apply_right,
        mul_inv_rev, inv_inv]
  · rintro ⟨i, j, hij, hr, hsupp, hj⟩
    obtain ⟨σ, hσ⟩ := isConj_iff.1 (Perm.isConj_swap hab hij)
    refine isConj_iff.2 ⟨⟨Pi.mulSingle i (x.left i), σ⟩, SemidirectProduct.ext ?_ ?_⟩
    · funext k
      rw [conj_inr_left]
      simp only [hσ, swap_inv]
      by_cases hki : k = i
      · rw [hki, swap_apply_left, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm, inv_one,
          mul_one]
      by_cases hkj : k = j
      · rw [hkj, swap_apply_right, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm, one_mul,
          hj]
      · rw [swap_apply_of_ne_of_ne hki hkj, mul_inv_cancel, hsupp k hki hkj]
    · rw [conj_inr_right]
      exact hσ.trans hr.symm

theorem commute_of_disjoint {x y : L2Wreath f n} {i j k l : Fin n}
    (hx : x.right = swap i j) (hxl : ∀ m, m ≠ i → m ≠ j → x.left m = 1)
    (hy : y.right = swap k l) (hyl : ∀ m, m ≠ k → m ≠ l → y.left m = 1)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) : Commute x y := by
  have hd : Perm.Disjoint (swap i j) (swap k l) := fun m => by
    by_cases hmi : m = i
    · exact Or.inr (hmi ▸ swap_apply_of_ne_of_ne hik hil)
    by_cases hmj : m = j
    · exact Or.inr (hmj ▸ swap_apply_of_ne_of_ne hjk hjl)
    exact Or.inl (swap_apply_of_ne_of_ne hmi hmj)
  refine SemidirectProduct.ext ?_ ?_
  · funext m
    simp only [mul_left, Pi.mul_apply, permAct_apply, hx, hy, swap_inv]
    by_cases hmi : m = i
    · rw [hmi, swap_apply_left, swap_apply_of_ne_of_ne hik hil, hyl _ hjk hjl, hyl _ hik hil,
        mul_one, one_mul]
    by_cases hmj : m = j
    · rw [hmj, swap_apply_right, swap_apply_of_ne_of_ne hjk hjl, hyl _ hik hil, hyl _ hjk hjl,
        mul_one, one_mul]
    rw [swap_apply_of_ne_of_ne hmi hmj, hxl m hmi hmj, one_mul]
    by_cases hmk : m = k
    · rw [hmk, swap_apply_left, hxl _ (Ne.symm hil) (Ne.symm hjl), mul_one]
    by_cases hml : m = l
    · rw [hml, swap_apply_right, hxl _ (Ne.symm hik) (Ne.symm hjk), mul_one]
    rw [swap_apply_of_ne_of_ne hmk hml, hxl m hmi hmj, mul_one]
  · simp only [mul_right, hx, hy]
    exact hd.commute

theorem exists_pair_avoid_of_five_le (h5 : 5 ≤ n) {i j k l : Fin n}
    (h : i = k ∨ i = l ∨ j = k ∨ j = l) :
    ∃ p q : Fin n, p ≠ q ∧ p ≠ i ∧ p ≠ j ∧ p ≠ k ∧ p ≠ l ∧ q ≠ i ∧ q ≠ j ∧ q ≠ k ∧ q ≠ l := by
  have hS : ({i, j, k, l} : Finset (Fin n)).card ≤ 3 := by
    rcases h with h | h | h | h
    · rw [Finset.card_insert_of_mem (by simp [h])]
      exact Finset.card_le_three
    · rw [Finset.card_insert_of_mem (by simp [h])]
      exact Finset.card_le_three
    all_goals
      calc _ ≤ ({j, k, l} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
        _ = ({k, l} : Finset (Fin n)).card + 1 := by
          rw [Finset.card_insert_of_mem (by simp [h])]
        _ ≤ 3 := by
          have := Finset.card_le_two (a := k) (b := l)
          omega
  have hc : 1 < ({i, j, k, l}ᶜ : Finset (Fin n)).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hc
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp hq
  exact ⟨p, q, hpq, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2⟩

theorem reach_of_five_le (h5 : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) {x y : L2Wreath f n}
    (hx : IsConj (inr (swap a b)) x) (hy : IsConj (inr (swap a b)) y) :
    Reach {g : L2Wreath f n | IsConj (inr (swap a b)) g} x y := by
  obtain ⟨i, j, -, hxr, hxl, -⟩ := (isConj_inr_swap_iff hab x).1 hx
  obtain ⟨k, l, -, hyr, hyl, -⟩ := (isConj_inr_swap_iff hab y).1 hy
  by_cases h : i = k ∨ i = l ∨ j = k ∨ j = l
  · obtain ⟨p, q, hpq, hpi, hpj, hpk, hpl, hqi, hqj, hqk, hql⟩ :=
      exists_pair_avoid_of_five_le h5 h
    have hz : IsConj (inr (swap a b)) (inr (swap p q) : L2Wreath f n) :=
      MonoidHom.map_isConj inr (Perm.isConj_swap hab hpq)
    have hzl : ∀ m, m ≠ p → m ≠ q → (inr (swap p q) : L2Wreath f n).left m = 1 :=
      fun _ _ _ => rfl
    exact reach_trans (reach_of_commute hx hz (commute_of_disjoint hxr hxl rfl hzl
      hpi.symm hqi.symm hpj.symm hqj.symm))
      (reach_of_commute hz hy (commute_of_disjoint rfl hzl hyr hyl hpk hpl hqk hql))
  · simp only [not_or] at h
    exact reach_of_commute hx hy (commute_of_disjoint hxr hxl hyr hyl h.1 h.2.1 h.2.2.1 h.2.2.2)

theorem isConj_two_mk (c : PSL2Model f) :
    IsConj (inr (swap 0 1)) (⟨![c, c⁻¹], swap 0 1⟩ : L2Wreath f 2) :=
  (isConj_inr_swap_iff (by decide) _).2
    ⟨0, 1, by decide, rfl, fun k h0 h1 => by fin_cases k <;> simp_all, by simp⟩

theorem eq_two_mk {x : L2Wreath f 2} (hx : IsConj (inr (swap 0 1)) x) :
    x = ⟨![x.left 0, (x.left 0)⁻¹], swap 0 1⟩ := by
  obtain ⟨i, j, hij, hr, -, hj⟩ := (isConj_inr_swap_iff (by decide) x).1 hx
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine SemidirectProduct.ext (funext fun m => ?_) hr
    fin_cases m <;> simp_all
  · refine SemidirectProduct.ext (funext fun m => ?_) (hr.trans (swap_comm _ _))
    fin_cases m <;> simp_all
  · exact absurd rfl hij

theorem commute_two_mk {c t : PSL2Model f} (ht : t * t = 1) :
    Commute (⟨![c, c⁻¹], swap 0 1⟩ : L2Wreath f 2) ⟨![t * c, (t * c)⁻¹], swap 0 1⟩ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine SemidirectProduct.ext ?_ ?_
  · funext m
    fin_cases m <;> simp [permAct_apply, mul_assoc, ht']
  · rfl

theorem closure_mul_self_eq_one_eq_top (hf : 2 ≤ f) :
    Subgroup.closure {t : PSL2Model f | t * t = 1} = ⊤ := by
  have hB : IsBenderGroup (PSL2Model f) := .isPSL2 f hf (MulEquiv.refl _)
  have := IsBenderGroup.isSimpleGroup hB
  obtain ⟨Q⟩ : Nonempty (Sylow 2 (PSL2Model f)) := inferInstance
  have h4 := IsBenderGroup.four_le_card_center hB Q
  have : Nontrivial (Subgroup.center (Q : Subgroup (PSL2Model f))) :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (Q : Subgroup (PSL2Model f)))
  have hzc : ∀ y ∈ Q, Commute ((z : Q) : PSL2Model f) y := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)).symm
  have hzz := IsBenderGroup.mul_self_eq_one_of_commute hB Q (z : Q).2 hzc
  have hz1 : ((z : Q) : PSL2Model f) ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hsub : Group.conjugatesOfSet {t : PSL2Model f | t * t = 1} ⊆
      {t : PSL2Model f | t * t = 1} := fun x hx => by
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hax
    have ha' : a * a = 1 := ha
    show c * a * c⁻¹ * (c * a * c⁻¹) = 1
    rw [show c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ by group, ha', mul_one,
      mul_inv_cancel]
  have htop : Subgroup.normalClosure {t : PSL2Model f | t * t = 1} = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun h => hz1 ?_
    have hmem := Subgroup.subset_normalClosure (s := {t : PSL2Model f | t * t = 1}) hzz
    rw [h] at hmem
    exact Subgroup.mem_bot.1 hmem
  rw [eq_top_iff, ← htop]
  exact Subgroup.closure_mono hsub

theorem reach_of_two (hf : 2 ≤ f) {x y : L2Wreath f 2} (hx : IsConj (inr (swap 0 1)) x)
    (hy : IsConj (inr (swap 0 1)) y) :
    Reach {g : L2Wreath f 2 | IsConj (inr (swap 0 1)) g} x y := by
  have key : ∀ c : PSL2Model f, Reach {g : L2Wreath f 2 | IsConj (inr (swap 0 1)) g}
      (inr (swap 0 1)) ⟨![c, c⁻¹], swap 0 1⟩ := by
    intro c
    have hc : c ∈ Subgroup.closure {t : PSL2Model f | t * t = 1} := by
      rw [closure_mul_self_eq_one_eq_top hf]
      trivial
    induction hc using Subgroup.closure_induction_left with
    | one =>
      have h1 : (⟨![1, 1⁻¹], swap 0 1⟩ : L2Wreath f 2) = inr (swap 0 1) := by
        refine SemidirectProduct.ext (funext fun m => ?_) rfl
        fin_cases m <;> simp
      rw [h1]
      exact reach_refl _
    | mul_left t ht c _ ih =>
      exact reach_trans ih
        (reach_of_commute (isConj_two_mk c) (isConj_two_mk (t * c)) (commute_two_mk ht))
    | inv_mul_cancel t ht c _ ih =>
      rw [inv_eq_of_mul_eq_one_right ht]
      exact reach_trans ih
        (reach_of_commute (isConj_two_mk c) (isConj_two_mk (t * c)) (commute_two_mk ht))
  have h1 := key (x.left 0)
  have h2 := key (y.left 0)
  rw [← eq_two_mk hx] at h1
  rw [← eq_two_mk hy] at h2
  exact reach_trans (reach_symm h1) h2

end WreathConn

theorem reach_wreathClass {f n : ℕ} (hf : 2 ≤ f) (hn : n = 2 ∨ 5 ≤ n) (x y : L2Wreath f n)
    (hx : IsConj (SemidirectProduct.inr (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) x)
    (hy : IsConj (SemidirectProduct.inr (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) y) :
    Reach {g | IsConj (SemidirectProduct.inr
      (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) g} x y := by
  rcases hn with rfl | h5
  · exact WreathConn.reach_of_two hf hx hy
  · exact WreathConn.reach_of_five_le h5 (by simp [Fin.ext_iff]) hx hy

end CFSG.Timmesfeld.Bridge.Asc72
