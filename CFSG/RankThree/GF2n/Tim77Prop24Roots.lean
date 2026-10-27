module

public import CFSG.RankThree.GF2n.Tim77Prop24Conj

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

theorem orderOf_mul_mul_inv (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa using this

theorem orderOf_eq_two_or_odd {x : G} (hx : x ^ 2 = 1) : orderOf x = 2 ∨ Odd (orderOf x) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx) with h | h
  · exact Or.inr (h ▸ odd_one)
  · exact Or.inl h

theorem orderOf_eq_four {x : G} (h2 : x ^ 2 ≠ 1) (h4 : (x ^ 2) ^ 2 = 1) : orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one]) (by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul]
    exact h4)
  rw [h]
  norm_num

variable [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

omit [Finite G] in
theorem M_le_normalizer_A : M ≤ Subgroup.normalizer (A : Set G) :=
  S.hM ▸ sup_le (S.L_le.trans Subgroup.le_normalizer) fun _ hx => (S.mem_Lb.mp hx).2

omit [Finite G] in
theorem comm_conj {k u v : G} (hu : u ∈ conjSubgroup k A) (hv : v ∈ conjSubgroup k A) :
    u * v = v * u := by
  have h := S.comm_A (mem_conjSubgroup.mp hu) (mem_conjSubgroup.mp hv)
  have e1 : u * v = k * ((k⁻¹ * u * k) * (k⁻¹ * v * k)) * k⁻¹ := by group
  have e2 : v * u = k * ((k⁻¹ * v * k) * (k⁻¹ * u * k)) * k⁻¹ := by group
  rw [e1, e2, h]

omit [Finite G] in
theorem sq_conj {k u : G} (hu : u ∈ conjSubgroup k A) : u * u = 1 := by
  have h := S.sq_A (mem_conjSubgroup.mp hu)
  calc u * u = k * ((k⁻¹ * u * k) * (k⁻¹ * u * k)) * k⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem M_le_normalizer_conj {k : G} (hk : k ∈ A ⊔ Ab) :
    M ≤ Subgroup.normalizer (conjSubgroup k A : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff]
  have hn : k⁻¹ * m * k ∈ Subgroup.normalizer (A : Set G) := by
    apply S.M_le_normalizer_A
    have := (Subgroup.mem_normalizer_iff.mp (S.sup_le_normalizer_M ((A ⊔ Ab).inv_mem hk)) m).mp hm
    simpa using this
  rw [← conjSubgroup_mul, show m * k = k * (k⁻¹ * m * k) by group, conjSubgroup_mul,
    conjSubgroup_eq_self_iff.mpr hn]

theorem mul_mem_A_of_sq {t m : G} (ht : t ∈ A) (htL : t ∉ L) (hm : m ∈ M)
    (h2 : (t * m) * (t * m) = 1) : t * m ∈ A := by
  have hmm : m * m = 1 := by rw [← sq]; exact S.isElemAbelian_M.2 m hm
  have h1 : (t * m)⁻¹ = t * m := inv_eq_of_mul_eq_one_right h2
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hmm, inv_eq_of_mul_eq_one_right (S.sq_A ht)] at h1
  exact A.mul_mem ht (S.L_le (S.mem_L_of_commute_M ht htL hm h1.symm))

theorem inf_normalizer_conj_eq {k : G} (hk : k ∈ A ⊔ Ab) (hne : conjSubgroup k A ≠ A) :
    A ⊓ Subgroup.normalizer (conjSubgroup k A : Set G) = L := by
  refine le_antisymm (fun a ha => ?_)
    (le_inf S.L_le (S.L_le_M.trans (S.M_le_normalizer_conj hk)))
  obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
  by_contra haL
  have hkN : k⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    S.sup_le_normalizer_M ((A ⊔ Ab).inv_mem hk)
  have hkN' : k ∈ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M hk
  have haa : a * a = 1 := S.sq_A haA
  have key : ∀ y ∈ conjSubgroup k A, y ∉ M → a * y * a⁻¹ * y⁻¹ ∈ M → False := by
    intro y hy hyM hc
    have e : k⁻¹⁻¹ * (k⁻¹ * y * k) * k⁻¹ = y := by group
    have hx : k⁻¹ * y * k ∈ A := mem_conjSubgroup.mp hy
    have hxL : k⁻¹ * y * k ∉ L := fun h => hyM (by
      have := (Subgroup.mem_normalizer_iff.mp hkN' _).mp (S.L_le_M h)
      rwa [show k * (k⁻¹ * y * k) * k⁻¹ = y by group] at this)
    have hyA := S.conj_mem_of_commutator_mem hkN haA haL hx hxL (by rwa [e])
    rw [e] at hyA
    have hy1 : y ≠ 1 := fun h => hyM (h ▸ M.one_mem)
    apply hne
    refine conjSubgroup_eq_of_isTI S.ti fun hbot => hy1 ?_
    have : y ∈ A ⊓ conjSubgroup k A := Subgroup.mem_inf.mpr ⟨hyA, hy⟩
    rwa [hbot, Subgroup.mem_bot] at this
  obtain ⟨x₀, hx₀, hx₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨y₀, hy₀⟩ : ∃ y, y = k * x₀ * k⁻¹ := ⟨_, rfl⟩
  have hy₀V : y₀ ∈ conjSubgroup k A := by
    rw [mem_conjSubgroup, hy₀, show k⁻¹ * (k * x₀ * k⁻¹) * k = x₀ by group]
    exact hx₀
  have hy₀X : y₀ ∈ A ⊔ Ab := by
    rw [hy₀]
    exact (A ⊔ Ab).mul_mem ((A ⊔ Ab).mul_mem hk (Subgroup.mem_sup_left hx₀)) ((A ⊔ Ab).inv_mem hk)
  have hy₀M : y₀ ∉ M := fun h => hx₀L (S.inf_M ▸ Subgroup.mem_inf.mpr ⟨hx₀, by
    have := (Subgroup.mem_normalizer_iff.mp hkN _).mp h
    rwa [hy₀, show k⁻¹ * (k * x₀ * k⁻¹) * k⁻¹⁻¹ = x₀ by group] at this⟩)
  by_cases hc₀ : a * y₀ * a⁻¹ * y₀⁻¹ ∈ M
  · exact key y₀ hy₀V hy₀M hc₀
  have hya : a * y₀ * a⁻¹ ∈ conjSubgroup k A := (Subgroup.mem_normalizer_iff.mp haN y₀).mp hy₀V
  have hy₀inv : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right (S.sq_conj hy₀V)
  refine key (y₀ * (a * y₀ * a⁻¹)) ((conjSubgroup k A).mul_mem hy₀V hya) (fun h => hc₀ ?_) ?_
  · have := (Subgroup.mem_normalizer_iff.mp (S.sup_le_normalizer_M ((A ⊔ Ab).inv_mem hy₀X))
      _).mp h
    have e : a * y₀ * a⁻¹ * y₀⁻¹ = y₀⁻¹ * (y₀ * (a * y₀ * a⁻¹)) * y₀⁻¹⁻¹ := by
      calc a * y₀ * a⁻¹ * y₀⁻¹ = a * y₀ * a⁻¹ * y₀ := by rw [hy₀inv]
        _ = y₀⁻¹ * (y₀ * (a * y₀ * a⁻¹)) * y₀⁻¹⁻¹ := by group
    rw [e]
    exact this
  · have e : a * (y₀ * (a * y₀ * a⁻¹)) * a⁻¹ = y₀ * (a * y₀ * a⁻¹) := by
      calc a * (y₀ * (a * y₀ * a⁻¹)) * a⁻¹ = (a * y₀ * a⁻¹) * ((a * a) * y₀ * (a * a)⁻¹) := by
            group
        _ = (a * y₀ * a⁻¹) * y₀ := by rw [haa, one_mul, inv_one, mul_one]
        _ = y₀ * (a * y₀ * a⁻¹) := (S.comm_conj hy₀V hya).symm
    rw [e, mul_inv_cancel]
    exact M.one_mem

theorem setup_conj {k : G} (hk : k ∈ A ⊔ Ab) (hne : conjSubgroup k A ≠ A) :
    Prop24Setup A (conjSubgroup k A) L (conjSubgroup k L) (L ⊔ conjSubgroup k L) where
  elem := S.elem
  ti := S.ti
  conj := ⟨k, rfl⟩
  hL := (S.inf_normalizer_conj_eq hk hne).symm
  hLb := by
    have hne' : conjSubgroup k⁻¹ A ≠ A := fun h => hne (by
      rw [conjSubgroup_eq_self_iff] at h ⊢
      simpa using (Subgroup.normalizer _).inv_mem h)
    rw [← S.inf_normalizer_conj_eq ((A ⊔ Ab).inv_mem hk) hne', conjSubgroup_inf]
    congr 1
    rw [conjSubgroup, Subgroup.map_equiv_normalizer_eq, ← conjSubgroup, ← conjSubgroup_mul,
      mul_inv_cancel, conjSubgroup_one]
  hM := rfl
  ne_bot := S.ne_bot
  ne := S.ne

theorem orderOf_mul_of_mem_L {l b : G} (hl : l ∈ L) (hl1 : l ≠ 1) (hb : b ∈ Ab) (hbL : b ∉ Lb) :
    orderOf (l * b) = 4 ∧ (l * b) ^ 2 ∈ Lb := by
  have hll : l * l = 1 := S.sq_A (S.L_le hl)
  have hbb : b * b = 1 := S.sq_Ab hb
  have hc : b * l * b⁻¹ * l⁻¹ ∈ Lb := S.commutator_mem_Lb hb hl
  rw [inv_eq_of_mul_eq_one_right hbb, inv_eq_of_mul_eq_one_right hll] at hc
  have hsq : (l * b) ^ 2 = b * l * b * l := by
    have h := S.comm_M (S.L_le_M hl) (S.Lb_le_M hc)
    calc (l * b) ^ 2 = l * (b * l * b * l) * l⁻¹ := by rw [sq]; group
      _ = b * l * b * l := by rw [h, mul_inv_cancel_right]
  have h2 : (l * b) ^ 2 ≠ 1 := by
    intro h
    apply hbL
    rw [hsq] at h
    have h' : (b * l)⁻¹ = b * l := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h)
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hll, inv_eq_of_mul_eq_one_right hbb] at h'
    exact S.mem_Lb_of_commute hb (S.L_le hl) hl1 h'.symm
  refine ⟨orderOf_eq_four h2 (by rw [hsq]; exact S.isElemAbelian_M.2 _ (S.Lb_le_M hc)), ?_⟩
  rw [hsq]
  exact hc

theorem orderOf_mul_of_mem_Lb {a lb : G} (ha : a ∈ A) (haL : a ∉ L) (hlb : lb ∈ Lb)
    (hlb1 : lb ≠ 1) : orderOf (a * lb) = 4 ∧ (a * lb) ^ 2 ∈ L := by
  obtain ⟨h4, hL⟩ := S.symm.orderOf_mul_of_mem_L hlb hlb1 ha haL
  have e : a * lb = a * (lb * a) * a⁻¹ := by group
  have hsq : (a * lb) ^ 2 = (lb * a) ^ 2 := by
    rw [e, conj_pow, S.comm_A ha (S.L_le hL), mul_inv_cancel_right]
  refine ⟨?_, by rw [hsq]; exact hL⟩
  rw [e, orderOf_mul_mul_inv]
  exact h4

theorem orderOf_mul_cases {a b : G} (ha : a ∈ A) (hb : b ∈ Ab) :
    orderOf (a * b) = 2 ∨ (orderOf (a * b) = 4 ∧ ((a * b) ^ 2 ∈ L ∨ (a * b) ^ 2 ∈ Lb)) ∨
      Odd (orderOf (a * b)) := by
  have haa := S.sq_A ha
  have hbb := S.sq_Ab hb
  by_cases haL : a ∈ L <;> by_cases hbL : b ∈ Lb
  · have hc := S.comm_L_Lb haL hbL
    have h : (a * b) ^ 2 = 1 := by
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; group
        _ = a * (a * b) * b := by rw [← hc]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    rcases orderOf_eq_two_or_odd h with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inr h2)
  · by_cases ha1 : a = 1
    · rw [ha1, one_mul]
      refine Or.inl (orderOf_eq_prime (by rw [sq]; exact hbb) fun h => hbL (h ▸ Lb.one_mem))
    · exact Or.inr (Or.inl ((S.orderOf_mul_of_mem_L haL ha1 hb hbL).imp_right Or.inr))
  · by_cases hb1 : b = 1
    · rw [hb1, mul_one]
      refine Or.inl (orderOf_eq_prime (by rw [sq]; exact haa) fun h => haL (h ▸ L.one_mem))
    · exact Or.inr (Or.inl ((S.orderOf_mul_of_mem_Lb ha haL hbL hb1).imp_right Or.inl))
  · exact Or.inr (Or.inr (S.odd_orderOf_mul ha haL hb hbL))

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77
