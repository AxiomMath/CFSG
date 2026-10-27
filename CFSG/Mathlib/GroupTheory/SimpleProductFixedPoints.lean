module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace CFSG.SimpleProductFixedPoints

private lemma eq_of_subgroup_eq {K : Type*} [Group K] {ι : Type*} (S : ι → Subgroup K)
    (hnab : ∀ i, ∃ x ∈ S i, ∃ y ∈ S i, x * y ≠ y * x)
    (hind : ∀ i, S i ⊓ ⨆ j : {j // j ≠ i}, S j = ⊥)
    {a b : ι} (h : S a = S b) : a = b := by
  by_contra hab
  have hle : S a ≤ ⨆ j : {j // j ≠ a}, S j := by
    rw [h]
    exact le_iSup (fun j : {j // j ≠ a} => S j) ⟨b, Ne.symm hab⟩
  have hbot : S a = ⊥ := by
    rw [← inf_eq_left.mpr hle, hind a]
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab a
  rw [hbot] at hx hy
  exact hxy (by rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy])

private def orb {ι : Type*} [DecidableEq ι] (π : ι → ι) (i : ι) : Finset ι :=
  {i, π i, π (π i)}

private lemma orb_mem_iff {ι : Type*} [DecidableEq ι] (π : ι → ι) (i k : ι) :
    k ∈ orb π i ↔ k = i ∨ k = π i ∨ k = π (π i) := by
  simp [orb]

private lemma orb_mem_self {ι : Type*} [DecidableEq ι] (π : ι → ι) (i : ι) : i ∈ orb π i := by
  simp [orb]

private lemma orb_mem_of_mem {ι : Type*} [DecidableEq ι] (π : ι → ι)
    (hπ3 : ∀ i, π (π (π i)) = i) {i k : ι} (hk : k ∈ orb π i) : π k ∈ orb π i := by
  obtain h | h | h := (orb_mem_iff π i k).mp hk
  · rw [h]
    exact (orb_mem_iff π i (π i)).mpr (Or.inr (Or.inl rfl))
  · rw [h]
    exact (orb_mem_iff π i (π (π i))).mpr (Or.inr (Or.inr rfl))
  · rw [h]
    exact (orb_mem_iff π i (π (π (π i)))).mpr (Or.inl (hπ3 i))

private lemma orb_eq_of_mem {ι : Type*} [DecidableEq ι] (π : ι → ι)
    (hπ3 : ∀ i, π (π (π i)) = i) {i k : ι} (hk : k ∈ orb π i) :
    orb π k = orb π i := by
  apply Finset.Subset.antisymm
  · intro m hm
    obtain h | h | h := (orb_mem_iff π k m).mp hm
    · rw [h]; exact hk
    · rw [h]; exact orb_mem_of_mem π hπ3 hk
    · rw [h]; exact orb_mem_of_mem π hπ3 (orb_mem_of_mem π hπ3 hk)
  · have hi : i ∈ orb π k := by
      obtain h | h | h := (orb_mem_iff π i k).mp hk
      · rw [h]; exact orb_mem_self π i
      · rw [h]; exact (orb_mem_iff π (π i) i).mpr (Or.inr (Or.inr (hπ3 i).symm))
      · rw [h]; exact (orb_mem_iff π (π (π i)) i).mpr (Or.inr (Or.inl (hπ3 i).symm))
    intro m hm
    obtain h | h | h := (orb_mem_iff π i m).mp hm
    · rw [h]; exact hi
    · rw [h]; exact orb_mem_of_mem π hπ3 hi
    · rw [h]; exact orb_mem_of_mem π hπ3 (orb_mem_of_mem π hπ3 hi)

private lemma orb_disjoint_of_not_mem {ι : Type*} [DecidableEq ι] (π : ι → ι)
    (hπ3 : ∀ i, π (π (π i)) = i) {i i' : ι} (hi : i' ∉ orb π i) :
    Disjoint (orb π i) (orb π i') := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  have h1 : orb π k = orb π i := orb_eq_of_mem π hπ3 hk
  have h2 : orb π k = orb π i' := orb_eq_of_mem π hπ3 hk'
  have : orb π i' = orb π i := h2 ▸ h1
  exact hi (this ▸ orb_mem_self π i')

private lemma map_toMonoidHom_mul {K : Type*} [Group K] (f g : MulAut K) (H : Subgroup K) :
    H.map (f * g).toMonoidHom = (H.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private lemma mem_sup_of_commute {K : Type*} [Group K] {A B : Subgroup K}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : K} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, a * b = x) ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, B.one_mem, mul_one y⟩
      · exact ⟨1, A.one_mem, y, hy, one_mul y⟩
    · exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
    · rintro x y _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂)) := by group
        _ = a₁ * ((a₂ * b₁) * b₂) := by group
        _ = a₁ * ((b₁ * a₂) * b₂) := by rw [hAB a₂ ha₂ b₁ hb₁]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
    · rintro x _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
        _ = (a * b)⁻¹ := by rw [hAB a ha b hb]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

private lemma finset_sup_normal {K : Type*} [Group K] {ι : Type*} [DecidableEq ι]
    (S : ι → Subgroup K) (h : ∀ k, (S k).Normal) (s : Finset ι) : (s.sup S).Normal := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; infer_instance
  | insert j t hjt ih =>
      rw [Finset.sup_insert]
      exact @Subgroup.sup_normal K _ (S j) (t.sup S) (h j) ih

private lemma finset_sup_inf_finset_sup_eq_bot {K : Type*} [Group K] {ι : Type*}
    [DecidableEq ι] (S : ι → Subgroup K) (hSnorm : ∀ k, (S k).Normal)
    (hind : ∀ i, S i ⊓ ⨆ j : {j // j ≠ i}, S j = ⊥) :
    ∀ s t : Finset ι, Disjoint s t → s.sup S ⊓ t.sup S = ⊥ := by
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro t _
    simp
  · intro j s' hjs ih t hdisj
    rw [Finset.sup_insert]
    have hj_t : j ∉ t := (Finset.disjoint_left.mp hdisj) (Finset.mem_insert_self j s')
    have hdisj' : Disjoint s' t := by
      rw [Finset.disjoint_left] at hdisj ⊢
      intro a ha hat
      exact hdisj (Finset.mem_insert_of_mem ha) hat
    rw [← le_bot_iff]
    intro x hx
    obtain ⟨hxsup, hxt⟩ := Subgroup.mem_inf.mp hx
    have hnormal : (s'.sup S).Normal := finset_sup_normal S hSnorm s'
    obtain ⟨y, hySj, z, hz, rfl⟩ :=
      (@Subgroup.mem_sup_of_normal_right K _ (S j) (s'.sup S) hnormal x).mp hxsup
    rw [Subgroup.mem_bot]
    have hle : t.sup S ⊔ s'.sup S ≤ ⨆ k : {k // k ≠ j}, S k := by
      apply sup_le
      · apply Finset.sup_le
        intro k hk
        exact le_iSup (fun k : {k // k ≠ j} => S k) ⟨k, fun h => hj_t (h ▸ hk)⟩
      · apply Finset.sup_le
        intro k hk
        exact le_iSup (fun k : {k // k ≠ j} => S k) ⟨k, fun h => hjs (h ▸ hk)⟩
    have hy_bot : y ∈ (⊥ : Subgroup K) := by
      rw [← hind j]
      refine ⟨hySj, ?_⟩
      have hy_eq : y = (y * z) * z⁻¹ := by group
      rw [hy_eq]
      exact hle (Subgroup.mul_mem_sup hxt ((s'.sup S).inv_mem hz))
    have hy1 : y = 1 := Subgroup.mem_bot.mp hy_bot
    have hz_bot : z ∈ (⊥ : Subgroup K) := by
      rw [← ih t hdisj']
      exact ⟨hz, by simpa [hy1] using hxt⟩
    have hz1 : z = 1 := Subgroup.mem_bot.mp hz_bot
    rw [hy1, hz1, one_mul]

private lemma mem_J_of_pow_three {K : Type*} [Group K] {O J : Subgroup K}
    (hOJ : O ⊓ J = ⊥) (hcom : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x)
    (hO : Nat.Coprime (Nat.card O) 3) {x : K} (hx : x ∈ O ⊔ J) (hx3 : x ^ 3 = 1) :
    x ∈ J := by
  obtain ⟨o, ho, j, hj, rfl⟩ := (mem_sup_of_commute hcom).mp hx
  have hcomm : o * j = j * o := hcom o ho j hj
  have h3 : o ^ 3 * j ^ 3 = 1 := by
    rw [← Commute.mul_pow hcomm 3]
    exact hx3
  have ho3 : o ^ 3 = 1 := by
    have ho3J : o ^ 3 ∈ J := by
      have : o ^ 3 = (j ^ 3)⁻¹ := mul_eq_one_iff_eq_inv.mp h3
      rw [this]
      exact J.inv_mem (J.pow_mem hj 3)
    have ho3O : o ^ 3 ∈ O := O.pow_mem ho 3
    have : o ^ 3 ∈ (⊥ : Subgroup K) := by rw [← hOJ]; exact ⟨ho3O, ho3J⟩
    exact Subgroup.mem_bot.mp this
  have h1 : orderOf o = 1 :=
    Nat.eq_one_of_dvd_coprimes hO
      (by rw [← Subgroup.orderOf_mk o ho]; exact orderOf_dvd_natCard _)
      (orderOf_dvd_iff_pow_eq_one.mpr ho3)
  have ho1 : o = 1 := orderOf_eq_one_iff.mp h1
  rw [ho1, one_mul]
  exact hj

private lemma mul_three_rearrange {K : Type*} [Group K] {A B C : Subgroup K}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    {a₁ a₂ : K} (_ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    {b₁ b₂ : K} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    {c₁ c₂ : K} (hc₁ : c₁ ∈ C) (_hc₂ : c₂ ∈ C) :
    (a₁ * b₁ * c₁) * (a₂ * b₂ * c₂) = (a₁ * a₂) * (b₁ * b₂) * (c₁ * c₂) := by
  calc (a₁ * b₁ * c₁) * (a₂ * b₂ * c₂)
      = a₁ * b₁ * (c₁ * a₂) * b₂ * c₂ := by group
    _ = a₁ * b₁ * (a₂ * c₁) * b₂ * c₂ := by rw [← hAC a₂ ha₂ c₁ hc₁]
    _ = a₁ * (b₁ * a₂) * c₁ * b₂ * c₂ := by group
    _ = a₁ * (a₂ * b₁) * c₁ * b₂ * c₂ := by rw [← hAB a₂ ha₂ b₁ hb₁]
    _ = a₁ * a₂ * b₁ * (c₁ * b₂) * c₂ := by group
    _ = a₁ * a₂ * b₁ * (b₂ * c₁) * c₂ := by rw [← hBC b₂ hb₂ c₁ hc₁]
    _ = (a₁ * a₂) * (b₁ * b₂) * (c₁ * c₂) := by group

private lemma mul_three_rotate {K : Type*} [Group K] {A B C : Subgroup K}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (_hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    {a b c : K} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) :
    b * c * a = a * b * c := by
  calc b * c * a = b * (c * a) := by group
    _ = b * (a * c) := by rw [← hAC a ha c hc]
    _ = b * a * c := by group
    _ = a * b * c := by rw [← hAB a ha b hb]

private lemma three_factor_unique {K : Type*} [Group K] {A B C : Subgroup K}
    (_hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (_hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (_hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hA : A ⊓ (B ⊔ C) = ⊥) (hB : B ⊓ (A ⊔ C) = ⊥)
    {a₁ a₂ : K} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    {b₁ b₂ : K} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    {c₁ c₂ : K} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (h : a₁ * b₁ * c₁ = a₂ * b₂ * c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have hA' : a₂⁻¹ * a₁ ∈ A := A.mul_mem (A.inv_mem ha₂) ha₁
  have hbc : b₁ * c₁ ∈ B ⊔ C := Subgroup.mul_mem_sup hb₁ hc₁
  have hBC' : b₂ * c₂ * (b₁ * c₁)⁻¹ ∈ B ⊔ C :=
    (B ⊔ C).mul_mem (Subgroup.mul_mem_sup hb₂ hc₂) ((B ⊔ C).inv_mem hbc)
  have hkey : a₂⁻¹ * a₁ = b₂ * c₂ * (b₁ * c₁)⁻¹ := by
    calc a₂⁻¹ * a₁
        = a₂⁻¹ * (a₁ * b₁ * c₁) * (b₁ * c₁)⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂ * c₂) * (b₁ * c₁)⁻¹ := by rw [h]
      _ = b₂ * c₂ * (b₁ * c₁)⁻¹ := by group
  have ha_eq : a₂⁻¹ * a₁ = 1 := by
    have : a₂⁻¹ * a₁ ∈ (⊥ : Subgroup K) := by
      rw [← hA]
      exact ⟨hA', hkey ▸ hBC'⟩
    exact Subgroup.mem_bot.mp this
  have ha : a₁ = a₂ := by
    calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
      _ = a₂ * 1 := by rw [ha_eq]
      _ = a₂ := by group
  have h' := h
  rw [ha] at h'
  have hbc_eq : b₁ * c₁ = b₂ * c₂ := by
    apply mul_left_cancel (a := a₂)
    rw [← mul_assoc, ← mul_assoc]
    exact h'
  have hbkey : b₂⁻¹ * b₁ = c₂ * c₁⁻¹ := by
    calc b₂⁻¹ * b₁ = b₂⁻¹ * (b₁ * c₁) * c₁⁻¹ := by group
      _ = b₂⁻¹ * (b₂ * c₂) * c₁⁻¹ := by rw [hbc_eq]
      _ = c₂ * c₁⁻¹ := by group
  have hBCbot : B ⊓ C = ⊥ := bot_unique (le_trans (inf_le_inf_left B le_sup_right) (le_of_eq hB))
  have hb_eq1 : b₂⁻¹ * b₁ = 1 := by
    have : b₂⁻¹ * b₁ ∈ (⊥ : Subgroup K) := by
      rw [← hBCbot]
      exact ⟨B.mul_mem (B.inv_mem hb₂) hb₁, hbkey ▸ C.mul_mem hc₂ (C.inv_mem hc₁)⟩
    exact Subgroup.mem_bot.mp this
  have hb : b₁ = b₂ := by
    calc b₁ = b₂ * (b₂⁻¹ * b₁) := by group
      _ = b₂ * 1 := by rw [hb_eq1]
      _ = b₂ := by group
  have hc2 : c₂ * c₁⁻¹ = 1 := hbkey ▸ hb_eq1
  have hc : c₁ = c₂ := by
    have : c₂ = c₁ := by
      calc c₂ = c₂ * c₁⁻¹ * c₁ := by group
        _ = 1 * c₁ := by rw [hc2]
        _ = c₁ := by group
    exact this.symm
  exact ⟨ha, hb, hc⟩

private lemma exists_fixed_three_element_aux {K : Type*} [Group K] [Finite K] (β : MulAut K)
    (hβ : β ^ 3 = 1) {S : Subgroup K} (hS : ∀ x ∈ S, β x ∈ S) (h3 : 3 ∣ Nat.card S) :
    ∃ x ∈ S, x ≠ 1 ∧ x ^ 3 = 1 ∧ β x = x := by
  classical
  have hfin : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun x => ⟨β (x : K), hS (x : K) x.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext x
    change f (f (f x)) = x
    apply Subtype.ext
    change β (β (β (x : K))) = (x : K)
    have h := congrArg (fun g : MulAut K => g (x : K)) hβ
    simpa [MulAut.mul_apply, pow_succ, pow_one] using h
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    show f ^ 3 ^ 1 = 1
    rw [pow_one]
    exact hf3)
  have h3' : 3 ∣ Fintype.card S := by rw [← Nat.card_eq_fintype_card]; exact h3
  have h3fix : 3 ∣ Fintype.card f.fixedPoints := by
    rw [← Nat.modEq_zero_iff_dvd]
    exact hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3')
  let Fix : Subgroup S :=
    { carrier := f.fixedPoints
      mul_mem' := fun {x y} hx hy => by
        change f (x * y) = x * y
        rw [show f (x * y) = f x * f y from Subtype.ext (map_mul β (x : K) (y : K)), hx, hy]
      one_mem' := by
        change f 1 = 1
        exact Subtype.ext (map_one β)
      inv_mem' := fun {x} hx => by
        change f x⁻¹ = x⁻¹
        rw [show f x⁻¹ = (f x)⁻¹ from Subtype.ext (map_inv β (x : K)), hx] }
  have h3Fix : 3 ∣ Nat.card Fix := by
    have h3fix' : 3 ∣ Nat.card (f.fixedPoints : Set S) := by
      rw [Nat.card_eq_fintype_card]
      exact h3fix
    exact h3fix'
  obtain ⟨y, hyorder⟩ := exists_prime_orderOf_dvd_card' (G := Fix) 3 h3Fix
  have hxord : orderOf (y : K) = 3 := by
    rw [Subgroup.orderOf_coe (y : S), Subgroup.orderOf_coe y, hyorder]
  refine ⟨(y : K), (y : S).2, ?_, ?_, ?_⟩
  · intro h
    have : orderOf (y : K) = 1 := by rw [h, orderOf_one]
    rw [hxord] at this
    exact absurd this (by decide)
  · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hxord])
  · have h : f (y : S) = (y : S) := y.2
    show β ((y : S) : K) = ((y : S) : K)
    exact congrArg (fun z : S => (z : K)) h

theorem simple_or_cube {K : Type} [Group K] [Finite K] (β : MulAut K) (hβ : β ^ 3 = 1)
    (ι : Type) [Finite ι] (S : ι → Subgroup K) (hS : ∀ i, IsSimpleGroup (S i))
    (hnab : ∀ i, ∃ x ∈ S i, ∃ y ∈ S i, x * y ≠ y * x) (h3 : ∀ i, 3 ∣ Nat.card (S i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x)
    (hind : ∀ i, S i ⊓ ⨆ j : {j // j ≠ i}, S j = ⊥) (hsup : ⨆ i, S i = ⊤)
    (hperm : ∀ i, ∃ j, (S i).map β.toMonoidHom = S j) {O J : Subgroup K}
    (hfix : ∀ x : K, x ∈ O ⊔ J ↔ β x = x) (hOJ : O ⊓ J = ⊥)
    (hcom : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x) (hO : Nat.Coprime (Nat.card O) 3)
    (hJ : IsSimpleGroup J) (hJn : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) :
    IsSimpleGroup K ∨
      ∃ S₀ S₁ S₂ : Subgroup K, Nonempty (↥S₀ ≃* ↥J) ∧ Nonempty (↥S₁ ≃* ↥J) ∧
        Nonempty (↥S₂ ≃* ↥J) ∧ (∀ x ∈ S₀, ∀ y ∈ S₁, x * y = y * x) ∧
        (∀ x ∈ S₀, ∀ y ∈ S₂, x * y = y * x) ∧ (∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) ∧
        S₀ ⊓ S₁ = ⊥ ∧ (S₀ ⊔ S₁) ⊓ S₂ = ⊥ ∧ S₀ ⊔ S₁ ⊔ S₂ = ⊤ := by
  classical
  choose π hπ using hperm
  have hπ3' : ∀ i, π (π (π i)) = i := by
    intro i
    apply eq_of_subgroup_eq S hnab hind
    have hcomp3 : (S i).map ((β ^ 3 : MulAut K).toMonoidHom) = S i := by
      rw [hβ]
      exact Subgroup.map_id (K := S i)
    have hpow : (S i).map ((β ^ 3 : MulAut K).toMonoidHom) = S (π (π (π i))) := by
      have hp : (β ^ 3 : MulAut K) = β * (β * β) := by
        show β ^ (2 + 1) = β * (β * β)
        rw [pow_succ]
        show β ^ (1 + 1) * β = β * (β * β)
        rw [pow_succ, pow_one, mul_assoc]
      rw [hp, map_toMonoidHom_mul, map_toMonoidHom_mul, hπ i, hπ (π i), hπ (π (π i))]
    exact hpow.symm.trans hcomp3
  have hS_normal : ∀ k, (S k).Normal := by
    intro k
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← hsup]
    apply iSup_le
    intro j
    by_cases hjk : j = k
    · subst hjk; exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (S k : Set K))
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hcomm j k hjk y hy h hh).symm
  have hJne : J ≠ ⊥ := by
    intro hJbot
    obtain ⟨x, hxJ, y, hyJ, hxy⟩ := hJn
    rw [hJbot, Subgroup.mem_bot] at hxJ hyJ
    exact hxy (by rw [hxJ, hyJ])
  let Kf : ι → Subgroup K := fun i => (orb π i).sup S
  have hKf_eq : ∀ i, Kf i = S i ⊔ S (π i) ⊔ S (π (π i)) := by
    intro i
    change (orb π i).sup S = S i ⊔ S (π i) ⊔ S (π (π i))
    simp only [orb, Finset.sup_insert, Finset.sup_singleton]
    ac_rfl
  have hKf_map : ∀ i, (Kf i).map β.toMonoidHom = Kf i := by
    intro i
    rw [hKf_eq i]
    simp only [Subgroup.map_sup, hπ, hπ3']
    ac_rfl
  have hKf_normal : ∀ i, (Kf i).Normal := fun i =>
    finset_sup_normal S hS_normal (orb π i)
  have hKf_inv : ∀ i, ∀ x ∈ Kf i, β x ∈ Kf i := by
    intro i x hx
    have h : β x ∈ (Kf i).map β.toMonoidHom := Subgroup.mem_map_of_mem β.toMonoidHom hx
    rwa [hKf_map i] at h
  have h3Kf : ∀ i, 3 ∣ Nat.card (Kf i) := by
    intro i
    exact (h3 i).trans (Subgroup.card_dvd_of_le (Finset.le_sup (orb_mem_self π i)))
  have step3 : ∀ i, J ≤ Kf i := by
    intro i
    obtain ⟨x, hxKf, hxne, hx3, hxfix⟩ :=
      exists_fixed_three_element_aux β hβ (hKf_inv i) (h3Kf i)
    have hxF : x ∈ O ⊔ J := (hfix x).mpr hxfix
    have hxJ : x ∈ J := mem_J_of_pow_three hOJ hcom hO hxF hx3
    have hxN : (⟨x, hxJ⟩ : J) ∈ (Kf i).subgroupOf J := Subgroup.mem_comap.mpr hxKf
    have hxNne : (⟨x, hxJ⟩ : J) ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥J _ hJ ((Kf i).subgroupOf J)
        ((hKf_normal i).subgroupOf J) with hbot | htop
    · rw [hbot, Subgroup.mem_bot] at hxN
      exact absurd hxN hxNne
    · intro y hyJ
      have hmem : (⟨y, hyJ⟩ : J) ∈ (Kf i).subgroupOf J := by rw [htop]; trivial
      exact Subgroup.mem_comap.mp hmem
  have hne_ι : Nonempty ι := by
    by_contra h
    have hEmpty : IsEmpty ι := not_nonempty_iff.mp h
    have hbot : (⨆ i, S i : Subgroup K) = ⊥ :=
      bot_unique (iSup_le fun i => (hEmpty.false i).elim)
    have htop_bot : (⊤ : Subgroup K) = ⊥ := by rw [← hsup, hbot]
    have hsub : Subsingleton K := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup K) := by rw [← htop_bot]; trivial
      have hb : b ∈ (⊥ : Subgroup K) := by rw [← htop_bot]; trivial
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    obtain ⟨x, hxJ, y, hyJ, hxy⟩ := hJn
    exact hxy (hsub.elim (x * y) (y * x))
  let i₀ : ι := Classical.choice hne_ι
  have h_all : ∀ i, i ∈ orb π i₀ := by
    intro i
    by_contra hi
    have hdisj : Disjoint (orb π i₀) (orb π i) := orb_disjoint_of_not_mem π hπ3' hi
    have hbot : Kf i₀ ⊓ Kf i = ⊥ := finset_sup_inf_finset_sup_eq_bot S hS_normal hind _ _ hdisj
    have hJle : J ≤ (⊥ : Subgroup K) := (le_inf (step3 i₀) (step3 i)).trans (le_of_eq hbot)
    exact hJne (bot_unique hJle)
  have htop : Kf i₀ = ⊤ := by
    change (orb π i₀).sup S = ⊤
    rw [← hsup]
    apply le_antisymm
    · apply Finset.sup_le; intro i _; exact le_iSup S i
    · apply iSup_le; intro i; exact Finset.le_sup (h_all i)
  by_cases hfixpt : π i₀ = i₀
  · left
    have hsingle : Kf i₀ = S i₀ := by
      rw [hKf_eq i₀]
      simp [hfixpt]
    have hS0_top : S i₀ = ⊤ := hsingle.symm.trans htop
    have htop_simple : IsSimpleGroup (⊤ : Subgroup K) := by
      rw [← hS0_top]; exact hS i₀
    exact (MulEquiv.isSimpleGroup_congr (Subgroup.topEquiv (G := K))).mp htop_simple
  · right
    have hne1 : i₀ ≠ π i₀ := fun h => hfixpt h.symm
    have hne2 : π (π i₀) ≠ i₀ := by
      intro h
      apply hfixpt
      have h1 : π (π (π i₀)) = π i₀ := congrArg π h
      rw [hπ3' i₀] at h1
      exact h1.symm
    have hne3 : π (π i₀) ≠ π i₀ := by
      intro h
      apply hfixpt
      have h1 : π (π (π i₀)) = π (π i₀) := congrArg π h
      rw [hπ3' i₀] at h1
      exact (h1.trans h).symm
    have hne2' : i₀ ≠ π (π i₀) := fun h => hne2 h.symm
    have hne3' : π i₀ ≠ π (π i₀) := fun h => hne3 h.symm
    have hcomm01 : ∀ x ∈ S i₀, ∀ y ∈ S (π i₀), x * y = y * x :=
      fun x hx y hy => hcomm i₀ (π i₀) hne1 x hx y hy
    have hcomm02 : ∀ x ∈ S i₀, ∀ y ∈ S (π (π i₀)), x * y = y * x :=
      fun x hx y hy => hcomm i₀ (π (π i₀)) hne2' x hx y hy
    have hcomm12 : ∀ x ∈ S (π i₀), ∀ y ∈ S (π (π i₀)), x * y = y * x :=
      fun x hx y hy => hcomm (π i₀) (π (π i₀)) hne3' x hx y hy
    have hA_bot : S i₀ ⊓ (S (π i₀) ⊔ S (π (π i₀))) = ⊥ := by
      apply bot_unique
      calc S i₀ ⊓ (S (π i₀) ⊔ S (π (π i₀)))
          ≤ S i₀ ⊓ ⨆ k : {k // k ≠ i₀}, S k :=
            inf_le_inf_left _ (sup_le
              (le_iSup (fun k : {k // k ≠ i₀} => S k) ⟨π i₀, hne1.symm⟩)
              (le_iSup (fun k : {k // k ≠ i₀} => S k) ⟨π (π i₀), hne2⟩))
        _ = ⊥ := hind i₀
    have hB_bot : S (π i₀) ⊓ (S i₀ ⊔ S (π (π i₀))) = ⊥ := by
      apply bot_unique
      calc S (π i₀) ⊓ (S i₀ ⊔ S (π (π i₀)))
          ≤ S (π i₀) ⊓ ⨆ k : {k // k ≠ π i₀}, S k :=
            inf_le_inf_left _ (sup_le
              (le_iSup (fun k : {k // k ≠ π i₀} => S k) ⟨i₀, hne1⟩)
              (le_iSup (fun k : {k // k ≠ π i₀} => S k) ⟨π (π i₀), hne3⟩))
        _ = ⊥ := hind (π i₀)
    have h01_bot : S i₀ ⊓ S (π i₀) = ⊥ := by
      apply bot_unique
      calc S i₀ ⊓ S (π i₀) ≤ S i₀ ⊓ ⨆ k : {k // k ≠ i₀}, S k :=
            inf_le_inf_left _ (le_iSup (fun k : {k // k ≠ i₀} => S k) ⟨π i₀, hne1.symm⟩)
        _ = ⊥ := hind i₀
    have h012_bot : (S i₀ ⊔ S (π i₀)) ⊓ S (π (π i₀)) = ⊥ := by
      apply bot_unique
      calc (S i₀ ⊔ S (π i₀)) ⊓ S (π (π i₀))
          ≤ (⨆ k : {k // k ≠ π (π i₀)}, S k) ⊓ S (π (π i₀)) :=
            inf_le_inf_right _ (sup_le
              (le_iSup (fun k : {k // k ≠ π (π i₀)} => S k) ⟨i₀, hne2'⟩)
              (le_iSup (fun k : {k // k ≠ π (π i₀)} => S k) ⟨π i₀, hne3'⟩))
        _ = ⊥ := by rw [inf_comm, hind (π (π i₀))]
    have hABC_top : S i₀ ⊔ S (π i₀) ⊔ S (π (π i₀)) = ⊤ :=
      (hKf_eq i₀).symm.trans htop
    have hβa_mem : ∀ {a : K}, a ∈ S i₀ → β a ∈ S (π i₀) := by
      intro a ha
      have h : β a ∈ (S i₀).map β.toMonoidHom := Subgroup.mem_map_of_mem β.toMonoidHom ha
      rwa [hπ i₀] at h
    have hββa_mem : ∀ {a : K}, a ∈ S i₀ → β (β a) ∈ S (π (π i₀)) := by
      intro a ha
      have h : β (β a) ∈ (S (π i₀)).map β.toMonoidHom :=
        Subgroup.mem_map_of_mem β.toMonoidHom (hβa_mem ha)
      rwa [hπ (π i₀)] at h
    have hφF : ∀ a : S i₀, (a : K) * β (a : K) * β (β (a : K)) ∈ O ⊔ J := by
      intro a
      rw [hfix]
      have hβ3a : β (β (β (a : K))) = (a : K) := by
        have h := congrArg (fun f : MulAut K => f (a : K)) hβ
        simpa [MulAut.mul_apply, pow_succ, pow_one] using h
      calc β ((a : K) * β (a : K) * β (β (a : K)))
          = β (a : K) * β (β (a : K)) * β (β (β (a : K))) := by simp only [map_mul]
        _ = β (a : K) * β (β (a : K)) * (a : K) := by rw [hβ3a]
        _ = (a : K) * β (a : K) * β (β (a : K)) :=
              mul_three_rotate hcomm01 hcomm02 hcomm12 a.2 (hβa_mem a.2) (hββa_mem a.2)
    let φ : S i₀ →* ↥(O ⊔ J) :=
      { toFun := fun a => ⟨(a : K) * β (a : K) * β (β (a : K)), hφF a⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          have h1 := mul_three_rearrange hcomm01 hcomm02 hcomm12 a.2 b.2
            (hβa_mem a.2) (hβa_mem b.2) (hββa_mem a.2) (hββa_mem b.2)
          simp only [Subgroup.coe_mul, map_mul]
          rw [← h1]) }
    have hφ_inj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro a ha
      rw [MonoidHom.mem_ker] at ha
      have ha' : (a : K) * β (a : K) * β (β (a : K)) = 1 := by
        have h := congrArg (fun x : ↥(O ⊔ J) => (x : K)) ha
        exact h
      have ha_eq : (a : K) = (β (a : K) * β (β (a : K)))⁻¹ := by
        calc (a : K)
            = (a : K) * β (a : K) * β (β (a : K)) * (β (a : K) * β (β (a : K)))⁻¹ := by
              group
          _ = 1 * (β (a : K) * β (β (a : K)))⁻¹ := by rw [ha']
          _ = (β (a : K) * β (β (a : K)))⁻¹ := by group
      have hamem : (a : K) ∈ S i₀ ⊓ (S (π i₀) ⊔ S (π (π i₀))) := by
        refine ⟨a.2, ?_⟩
        rw [ha_eq]
        exact (S (π i₀) ⊔ S (π (π i₀))).inv_mem
          (Subgroup.mul_mem_sup (hβa_mem a.2) (hββa_mem a.2))
      have ha1 : (a : K) = 1 := by
        have h : (a : K) ∈ (⊥ : Subgroup K) := by rw [← hA_bot]; exact hamem
        exact Subgroup.mem_bot.mp h
      exact Subtype.ext ha1
    have hCA : (S (π (π i₀))).map β.toMonoidHom = S i₀ := by
      rw [hπ (π (π i₀)), hπ3' i₀]
    have hφ_surj : Function.Surjective φ := by
      intro z
      have hzF : β (z : K) = z := (hfix (z : K)).mp z.2
      have hzcube : (z : K) ∈ S i₀ ⊔ S (π i₀) ⊔ S (π (π i₀)) := by
        rw [hABC_top]; trivial
      obtain ⟨y, hy, c, hc, hyc⟩ := Subgroup.mem_sup_of_normal_right.mp hzcube
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have hz : (z : K) = a * b * c := by rw [← hyc, ← hab]
      have hβz : β a * β b * β c = a * b * c := by
        have h1 : β (a * b * c) = β a * β b * β c := by simp only [map_mul]
        calc β a * β b * β c = β (a * b * c) := h1.symm
          _ = β (z : K) := by rw [hz]
          _ = (z : K) := hzF
          _ = a * b * c := hz
      have hβa : β a ∈ S (π i₀) := by
        have h : β a ∈ (S i₀).map β.toMonoidHom := Subgroup.mem_map_of_mem β.toMonoidHom ha
        rwa [hπ i₀] at h
      have hβb : β b ∈ S (π (π i₀)) := by
        have h : β b ∈ (S (π i₀)).map β.toMonoidHom :=
          Subgroup.mem_map_of_mem β.toMonoidHom hb
        rwa [hπ (π i₀)] at h
      have hβc : β c ∈ S i₀ := by
        have h : β c ∈ (S (π (π i₀))).map β.toMonoidHom :=
          Subgroup.mem_map_of_mem β.toMonoidHom hc
        rwa [hCA] at h
      have hrot : β c * β a * β b = a * b * c :=
        (mul_three_rotate hcomm01 hcomm02 hcomm12 hβc hβa hβb).symm.trans hβz
      obtain ⟨_, hβa_eq, hβb_eq⟩ :=
        three_factor_unique hcomm01 hcomm02 hcomm12 hA_bot hB_bot
          hβc ha hβa hb hβb hc hrot
      have hββa : β (β a) = c := (congrArg β hβa_eq).trans hβb_eq
      refine ⟨⟨a, ha⟩, ?_⟩
      apply Subtype.ext
      change a * β a * β (β a) = (z : K)
      rw [hz, hββa, hβa_eq]
    have hφ_iso : S i₀ ≃* ↥(O ⊔ J) := MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hsimpleF : IsSimpleGroup ↥(O ⊔ J) :=
      (MulEquiv.isSimpleGroup_congr hφ_iso).mp (hS i₀)
    have hO_cent : O ≤ Subgroup.centralizer (J : Set K) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcom x hx y hy).symm
    have hF_le_normJ : O ⊔ J ≤ Subgroup.normalizer J :=
      sup_le (le_trans hO_cent (Subgroup.centralizer_le_normalizer (J : Set K)))
        Subgroup.le_normalizer
    have hJnormF : (J.subgroupOf (O ⊔ J)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hF_le_normJ
    have hFJ : O ⊔ J = J := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥(O ⊔ J) _ hsimpleF
          (J.subgroupOf (O ⊔ J)) hJnormF with hbot | htop
      · exfalso
        obtain ⟨x, hxJ, y, hyJ, hxy⟩ := hJn
        have hxOJ : x ∈ O ⊔ J := by simpa using Subgroup.mul_mem_sup (O.one_mem) hxJ
        have hyOJ : y ∈ O ⊔ J := by simpa using Subgroup.mul_mem_sup (O.one_mem) hyJ
        have hxsub : (⟨x, hxOJ⟩ : (O ⊔ J : Subgroup K)) ∈ J.subgroupOf (O ⊔ J) :=
          Subgroup.mem_comap.mpr hxJ
        have hysub : (⟨y, hyOJ⟩ : (O ⊔ J : Subgroup K)) ∈ J.subgroupOf (O ⊔ J) :=
          Subgroup.mem_comap.mpr hyJ
        rw [hbot, Subgroup.mem_bot] at hxsub hysub
        have hx1 : x = 1 := by
          have h := congrArg (fun z : (O ⊔ J : Subgroup K) => (z : K)) hxsub
          simpa using h
        have hy1 : y = 1 := by
          have h := congrArg (fun z : (O ⊔ J : Subgroup K) => (z : K)) hysub
          simpa using h
        exact hxy (by rw [hx1, hy1])
      · apply le_antisymm _ le_sup_right
        intro y hy
        have hmem : (⟨y, hy⟩ : (O ⊔ J : Subgroup K)) ∈ J.subgroupOf (O ⊔ J) := by
          rw [htop]; trivial
        exact Subgroup.mem_comap.mp hmem
    have hS0J : S i₀ ≃* ↥J := hφ_iso.trans (MulEquiv.subgroupCongr hFJ)
    have hS1J : S (π i₀) ≃* ↥J :=
      ((MulEquiv.subgroupMap β (S i₀)).trans (MulEquiv.subgroupCongr (hπ i₀))).symm.trans hS0J
    have hS2J : S (π (π i₀)) ≃* ↥J :=
      ((MulEquiv.subgroupMap β (S (π (π i₀)))).trans (MulEquiv.subgroupCongr hCA)).trans hS0J
    exact ⟨S i₀, S (π i₀), S (π (π i₀)), ⟨hS0J⟩, ⟨hS1J⟩, ⟨hS2J⟩,
      hcomm01, hcomm02, hcomm12, h01_bot, h012_bot, hABC_top⟩

end CFSG.SimpleProductFixedPoints

end
