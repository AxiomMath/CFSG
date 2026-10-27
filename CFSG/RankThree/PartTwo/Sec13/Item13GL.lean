module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_of_mem_zpowers_of_pow_three {H : Type*} [Group H] {u x : H} (hu : u ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u ∨ x = u ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, show u ^ (3 : ℤ) = 1 by exact_mod_cast hu, one_zpow, mul_one]
  rw [hk]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero u)
  · exact Or.inr (Or.inl (zpow_one u))
  · exact Or.inr (Or.inr (by norm_cast))

section E9

variable {G : Type*} [Group G] {B : Subgroup G}

@[expose] def fixSub (T : Set (MulAut B)) : Subgroup B where
  carrier := {b | ∀ σ ∈ T, σ b = b}
  mul_mem' {x y} hx hy σ hσ := by rw [map_mul, hx σ hσ, hy σ hσ]
  one_mem' σ _ := map_one σ
  inv_mem' {x} hx σ hσ := by rw [map_inv, hx σ hσ]

theorem mem_fixSub {T : Set (MulAut B)} {b : B} : b ∈ fixSub T ↔ ∀ σ ∈ T, σ b = b :=
  Iff.rfl

@[expose] def invSub (hB : IsMulCommutative B) (σ : MulAut B) : Subgroup B where
  carrier := {b | σ b = b⁻¹}
  mul_mem' {x y} hx hy := by
    show σ (x * y) = (x * y)⁻¹
    rw [map_mul, hx, hy, mul_inv_rev, hB.is_comm.comm y⁻¹ x⁻¹]
  one_mem' := by
    show σ 1 = 1⁻¹
    rw [map_one, inv_one]
  inv_mem' {x} hx := by
    show σ x⁻¹ = x⁻¹⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) hx

theorem mem_invSub {hB : IsMulCommutative B} {σ : MulAut B} {b : B} :
    b ∈ invSub hB σ ↔ σ b = b⁻¹ :=
  Iff.rfl

variable (hB : CFSG.Assembly.IsElemAbelian 3 B)
include hB

theorem pow_three_eq_one (b : B) : b ^ 3 = 1 :=
  Subtype.ext (by simpa using hB.2 b b.2)

theorem mul_comm' (x y : B) : x * y = y * x :=
  hB.1.is_comm.comm x y

omit hB in
theorem exists_fixed_of_isPGroup [Finite B] (h9 : Nat.card B = 9) {P : Subgroup (MulAut B)}
    (hP : IsPGroup 3 P) : ∃ b : B, b ≠ 1 ∧ ∀ σ ∈ P, σ b = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hP.card_modEq_card_fixedPoints B
  rw [h9] at hmod
  have h1 : (1 : B) ∈ MulAction.fixedPoints P B := fun σ => smul_one σ
  have hpos : 0 < Nat.card (MulAction.fixedPoints P B) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
  have h3 : 1 < Nat.card (MulAction.fixedPoints P B) := by
    unfold Nat.ModEq at hmod
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp h3
  obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints P B)
  exact ⟨b, fun h => hb1 (Subtype.ext h), fun σ hσ => hb ⟨σ, hσ⟩⟩

theorem exists_line_of_sq_eq_one [Finite B] (h9 : Nat.card B = 9) {σ : MulAut B}
    (hσ : σ * σ = 1) : ∃ v : B, v ≠ 1 ∧ (σ v = v ∨ σ v = v⁻¹) := by
  by_cases hinv : ∀ b : B, σ b = b⁻¹
  · have : Nontrivial B := by
      rw [← Finite.one_lt_card_iff_nontrivial, h9]
      norm_num
    obtain ⟨v, hv⟩ := exists_ne (1 : B)
    exact ⟨v, hv, Or.inr (hinv v)⟩
  · simp only [not_forall] at hinv
    obtain ⟨b, hb⟩ := hinv
    refine ⟨b * σ b, fun h => hb ?_, Or.inl ?_⟩
    · exact (eq_inv_of_mul_eq_one_right h)
    · have h2 : σ (σ b) = b := by
        rw [← MulAut.mul_apply, hσ, MulAut.one_apply]
      rw [map_mul, h2, mul_comm' hB]

omit hB in
theorem card_eq_three_of_ne [Finite B] (h9 : Nat.card B = 9) {V : Subgroup B} (hV1 : V ≠ ⊥)
    (hVt : V ≠ ⊤) : Nat.card V = 3 := by
  have hdvd : Nat.card V ∣ 9 := h9 ▸ Subgroup.card_subgroup_dvd_card V
  have h1 : Nat.card V ≠ 1 := fun h => hV1 (Subgroup.card_eq_one.mp h)
  have h9' : Nat.card V ≠ 9 := fun h => hVt (Subgroup.card_eq_iff_eq_top V |>.mp (h.trans h9.symm))
  have hle : Nat.card V ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card V <;> first | rfl | (exfalso; omega)

theorem eq_zpowers_of_card_three [Finite B] {V : Subgroup B} (hV : Nat.card V = 3) {u : B}
    (huV : u ∈ V) (hu1 : u ≠ 1) : V = Subgroup.zpowers u := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huV)
  rw [hV, Nat.card_zpowers]
  have := orderOf_dvd_of_pow_eq_one (pow_three_eq_one hB u)
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ this with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hu1
  · rw [h]

theorem sq_apply_eq_inv [Finite B] (h9 : Nat.card B = 9) {σ : MulAut B}
    (h4 : σ * σ * (σ * σ) = 1) (h2 : σ * σ ≠ 1) (b : B) : (σ * σ) b = b⁻¹ := by
  set τ := σ * σ with hτ
  by_contra hb
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    rw [← MulAut.mul_apply, h4, MulAut.one_apply]
  obtain ⟨w, hw⟩ : ∃ w, τ w ≠ w := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact h2 (MulEquiv.ext h)
  set u := w * (τ w)⁻¹ with hudef
  have hu : u ∈ invSub hB.1 τ := by
    show τ u = u⁻¹
    rw [hudef, map_mul, map_inv, hττ, mul_inv_rev, inv_inv]
  have hu1 : u ≠ 1 := fun h => hw (mul_inv_eq_one.mp h).symm
  have hI1 : invSub hB.1 τ ≠ ⊥ := fun h => hu1 (by rw [h] at hu; exact hu)
  have hIt : invSub hB.1 τ ≠ ⊤ := fun h => hb (by
    have : b ∈ invSub hB.1 τ := h ▸ Subgroup.mem_top b
    exact this)
  have hIeq := eq_zpowers_of_card_three hB (card_eq_three_of_ne h9 hI1 hIt) hu hu1
  have hσu : σ u ∈ invSub hB.1 τ := by
    show τ (σ u) = (σ u)⁻¹
    have e1 : τ (σ u) = σ (τ u) := by
      simp only [hτ, MulAut.mul_apply]
    rw [e1, show τ u = u⁻¹ from hu, map_inv]
  rw [hIeq] at hσu
  have hτu : τ u = u := by
    rcases eq_of_mem_zpowers_of_pow_three (pow_three_eq_one hB u) hσu with h | h | h
    · exact absurd ((MulEquiv.map_eq_one_iff σ).mp h) hu1
    · rw [hτ, MulAut.mul_apply, h, h]
    · rw [hτ, MulAut.mul_apply, h, map_pow, h, ← pow_mul,
        show u ^ (2 * 2) = u ^ 3 * u by group, pow_three_eq_one hB, one_mul]
  have h1 : u = u⁻¹ := hτu.symm.trans hu
  apply hu1
  have h2' : u ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h1]; exact mul_inv_cancel u
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [pow_three_eq_one hB, h2', inv_one, one_mul]

omit hB in
theorem eq_of_agree {u v : B} (huv : Subgroup.zpowers u ⊔ Subgroup.zpowers v = ⊤)
    {φ ψ : MulAut B} (hu : φ u = ψ u) (hv : φ v = ψ v) : φ = ψ := by
  have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ (φ.toMonoidHom).eqLocus ψ.toMonoidHom :=
    sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr hv)
  rw [huv] at hle
  exact MulEquiv.ext fun b => hle (Subgroup.mem_top b)

theorem apply_eq_inv_of_agree {u v : B} (huv : Subgroup.zpowers u ⊔ Subgroup.zpowers v = ⊤)
    {φ : MulAut B} (hu : φ u = u⁻¹) (hv : φ v = v⁻¹) (b : B) : φ b = b⁻¹ := by
  have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ invSub hB.1 φ :=
    sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr hv)
  rw [huv] at hle
  exact hle (Subgroup.mem_top b)

theorem exists_inv_of_sq_eq_one [Finite B] (h9 : Nat.card B = 9) {Q : Subgroup (MulAut B)}
    (hQ : Nat.card Q = 4) (hsq : ∀ σ ∈ Q, σ * σ = 1) : ∃ ι ∈ Q, ∀ b, ι b = b⁻¹ := by
  by_contra hno
  simp only [not_exists, not_and, not_forall] at hno
  have hsub : ∀ s : MulAut B, ∃ t ∈ Q, t ≠ 1 ∧ t ≠ s := by
    intro s
    by_contra h
    simp only [not_exists, not_and, ne_eq, not_not] at h
    have hle : (Q : Set (MulAut B)) ⊆ {1, s} := fun t ht => by
      by_cases ht1 : t = 1
      · exact Or.inl ht1
      · exact Or.inr (h t ht ht1)
    have h1 := Set.ncard_le_ncard hle (Set.toFinite _)
    have h2 : ({1, s} : Set (MulAut B)).ncard ≤ 2 :=
      (Set.ncard_insert_le 1 {s}).trans (by rw [Set.ncard_singleton])
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hQ] at h1
    omega
  obtain ⟨s, hsQ, hs1, -⟩ := hsub 1
  obtain ⟨t, htQ, ht1, hts⟩ := hsub s
  have hss : ∀ x, s (s x) = x := fun x => by rw [← MulAut.mul_apply, hsq s hsQ, MulAut.one_apply]
  have hst : s * t = t * s := by
    have h1 := hsq (s * t) (Q.mul_mem hsQ htQ)
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hsq s hsQ)
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hsq t htQ)
    calc s * t = (s * t)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = t * s := by rw [mul_inv_rev, hs', ht']
  have hcomm : ∀ x, s (t x) = t (s x) := fun x => by
    rw [← MulAut.mul_apply, hst, MulAut.mul_apply]
  obtain ⟨b₀, hb₀⟩ := hno s hsQ
  set v := b₀ * s b₀ with hvdef
  have hv : s v = v := by rw [hvdef, map_mul, hss, mul_comm' hB]
  have hv1 : v ≠ 1 := fun h => hb₀ (eq_inv_of_mul_eq_one_right h)
  obtain ⟨w, hw⟩ : ∃ w, s w ≠ w := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hs1 (MulEquiv.ext h)
  set u := w * (s w)⁻¹ with hudef
  have hu : s u = u⁻¹ := by rw [hudef, map_mul, map_inv, hss, mul_inv_rev, inv_inv]
  have hu1 : u ≠ 1 := fun h => hw (mul_inv_eq_one.mp h).symm
  have hvF : v ∈ fixSub ({s} : Set (MulAut B)) := fun σ hσ => by
    rw [Set.mem_singleton_iff.mp hσ]
    exact hv
  have hFcard : Nat.card (fixSub ({s} : Set (MulAut B))) = 3 := by
    refine card_eq_three_of_ne h9 ?_ ?_
    · intro h
      rw [h] at hvF
      exact hv1 hvF
    · intro h
      have : w ∈ fixSub ({s} : Set (MulAut B)) := h ▸ Subgroup.mem_top w
      exact hw (this s rfl)
  have hF : fixSub ({s} : Set (MulAut B)) = Subgroup.zpowers v :=
    eq_zpowers_of_card_three hB hFcard hvF hv1
  have huI : u ∈ invSub hB.1 s := hu
  have hIcard : Nat.card (invSub hB.1 s) = 3 := by
    refine card_eq_three_of_ne h9 ?_ ?_
    · intro h
      rw [h] at huI
      exact hu1 huI
    · intro h
      have : b₀ ∈ invSub hB.1 s := h ▸ Subgroup.mem_top b₀
      exact hb₀ this
  have hI : invSub hB.1 s = Subgroup.zpowers u := eq_zpowers_of_card_three hB hIcard huI hu1
  have huv : Subgroup.zpowers u ⊔ Subgroup.zpowers v = ⊤ := by
    have hvu : v ∉ Subgroup.zpowers u := by
      intro h
      rw [← hI] at h
      have h' : s v = v⁻¹ := h
      rw [hv] at h'
      apply hv1
      have h2 : v ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h']; exact mul_inv_cancel v
      calc v = v ^ 3 * (v ^ 2)⁻¹ := by group
        _ = 1 := by rw [pow_three_eq_one hB, h2, inv_one, one_mul]
    have h3 : Nat.card (Subgroup.zpowers u) = 3 := by rw [← hI]; exact hIcard
    have hdvd : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup B) ∣ 9 :=
      h9 ▸ Subgroup.card_subgroup_dvd_card _
    have hge : 3 ∣ Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup B) := by
      rw [← h3]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hne3 : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup B) ≠ 3 := by
      intro h
      apply hvu
      have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left :
        Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v) (by rw [h, h3])
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    have h9' : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup B) = 9 := by
      have hle : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup B) ≤ 9 :=
        Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup B) <;>
        omega
    exact (Subgroup.card_eq_iff_eq_top _).mp (h9'.trans h9.symm)
  have htv : t v ∈ Subgroup.zpowers v := by
    rw [← hF]
    intro σ hσ
    rw [Set.mem_singleton_iff.mp hσ, hcomm, hv]
  have htu : t u ∈ Subgroup.zpowers u := by
    rw [← hI]
    show s (t u) = (t u)⁻¹
    rw [hcomm, hu, map_inv]
  have hv2 : v ^ 2 = v⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, pow_three_eq_one hB]
  have hu2 : u ^ 2 = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, pow_three_eq_one hB]
  rcases eq_of_mem_zpowers_of_pow_three (pow_three_eq_one hB v) htv with h1 | h1 | h1
  · exact hv1 ((MulEquiv.map_eq_one_iff t).mp h1)
  · rcases eq_of_mem_zpowers_of_pow_three (pow_three_eq_one hB u) htu with h2 | h2 | h2
    · exact hu1 ((MulEquiv.map_eq_one_iff t).mp h2)
    · exact ht1 (eq_of_agree huv (by rw [h2, MulAut.one_apply]) (by rw [h1, MulAut.one_apply]))
    · exact hts (eq_of_agree huv (by rw [h2, hu, hu2]) (by rw [h1, hv]))
  · rcases eq_of_mem_zpowers_of_pow_three (pow_three_eq_one hB u) htu with h2 | h2 | h2
    · exact hu1 ((MulEquiv.map_eq_one_iff t).mp h2)
    · obtain ⟨b, hb⟩ := hno (s * t) (Q.mul_mem hsQ htQ)
      exact hb (apply_eq_inv_of_agree hB huv (by rw [MulAut.mul_apply, h2, hu])
        (by rw [MulAut.mul_apply, h1, hv2, map_inv, hv]) b)
    · obtain ⟨b, hb⟩ := hno t htQ
      exact hb (apply_eq_inv_of_agree hB huv (by rw [h2, hu2]) (by rw [h1, hv2]) b)

omit hB in
theorem finite_mulAut [Finite B] : Finite (MulAut B) :=
  Finite.of_injective (fun σ : MulAut B => (σ : B → B)) DFunLike.coe_injective

theorem exists_inv_mem_of_four_dvd [Finite B] (h9 : Nat.card B = 9) {S : Subgroup (MulAut B)}
    (hS4 : 4 ∣ Nat.card S) : ∃ ι ∈ S, ∀ b, ι b = b⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut B) := finite_mulAut
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 2 (n := 2)
    (by norm_num; exact hS4)
  set Q' := Q.map S.subtype with hQ'def
  have hQ' : Nat.card Q' = 4 := by
    rw [hQ'def, Subgroup.card_map_of_injective S.subtype_injective, hQ]
    norm_num
  have hQS : Q' ≤ S := Subgroup.map_subtype_le Q
  by_cases h : ∀ σ ∈ Q', σ * σ = 1
  · obtain ⟨ι, hιQ, hι⟩ := exists_inv_of_sq_eq_one hB h9 hQ' h
    exact ⟨ι, hQS hιQ, hι⟩
  · simp only [not_forall] at h
    obtain ⟨σ, hσQ, hσ⟩ := h
    have h4 : σ * σ * (σ * σ) = 1 := by
      have h1 := pow_card_eq_one' (G := Q') (x := ⟨σ, hσQ⟩)
      rw [hQ'] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      rw [← h2]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    exact ⟨σ * σ, S.mul_mem (hQS hσQ) (hQS hσQ), sq_apply_eq_inv hB h9 h4 hσ⟩

end E9

end CFSG.RankThree.PartTwo.Sec13
