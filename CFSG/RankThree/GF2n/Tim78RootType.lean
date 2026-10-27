module

public import CFSG.RankThree.GF2n.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {X : Type*} [Group X]

@[expose] def IsRootTypeTI (V : Subgroup X) : Prop :=
  IsTI V ∧ ∀ g : X, V ⊓ Subgroup.normalizer (conjSubgroup g V : Set X) ≠ ⊥ →
    ∀ a ∈ V, ∀ b ∈ conjSubgroup g V, a * b = b * a

theorem mem_closure_pair_involutions {u w : X} (hu : u * u = 1) (hw : w * w = 1) {x : X}
    (hx : x ∈ Subgroup.closure ({u, w} : Set X)) :
    ∃ k : ℤ, x = (u * w) ^ k ∨ x = (u * w) ^ k * u := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  have hconj : ∀ b : ℤ, u * (u * w) ^ b = (u * w) ^ (-b) * u := by
    intro b
    have h1 : u * (u * w) * u⁻¹ = (u * w)⁻¹ := by
      rw [huinv, mul_inv_rev, huinv, hwinv, ← mul_assoc, hu, one_mul]
    have h2 : u * (u * w) ^ b * u⁻¹ = (u * w) ^ (-b) := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow']
    calc u * (u * w) ^ b = u * (u * w) ^ b * u⁻¹ * u := by group
      _ = (u * w) ^ (-b) * u := by rw [h2]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, mul_inv_rev, huinv, hwinv, mul_assoc, hu, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha | ha⟩ := hy <;> obtain ⟨b, hb | hb⟩ := hz <;> subst ha <;> subst hb
    · exact ⟨a + b, Or.inl (zpow_add _ _ _).symm⟩
    · exact ⟨a + b, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨a - b, Or.inr ?_⟩
      rw [mul_assoc, hconj, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨a - b, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc u, hconj, mul_assoc, hu, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv y _ hy =>
    obtain ⟨a, ha | ha⟩ := hy <;> subst ha
    · exact ⟨-a, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨a, Or.inr ?_⟩
      rw [mul_inv_rev, huinv, ← zpow_neg, hconj, neg_neg]

theorem isPGroup_closure_pair_involutions {u w : X} (hu : u * u = 1) (hw : w * w = 1) {n : ℕ}
    (huw : (u * w) ^ 2 ^ n = 1) : IsPGroup 2 (Subgroup.closure ({u, w} : Set X)) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  intro x
  refine ⟨n + 1, Subtype.ext ?_⟩
  obtain ⟨k, hk | hk⟩ := mem_closure_pair_involutions hu hw x.2
  · simp only [Subgroup.coe_pow, hk, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_succ, pow_mul, huw,
      one_pow, one_zpow]
  · simp only [Subgroup.coe_pow, hk, Subgroup.coe_one]
    have h2 : ((u * w) ^ k * u) ^ 2 = 1 := by
      have h1 : u * (u * w) * u⁻¹ = (u * w)⁻¹ := by
        rw [huinv, mul_inv_rev, huinv, hwinv, ← mul_assoc, hu, one_mul]
      have h3 : u * (u * w) ^ k * u⁻¹ = (u * w) ^ (-k) := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow']
      calc ((u * w) ^ k * u) ^ 2 = (u * w) ^ k * (u * (u * w) ^ k * u⁻¹) := by
            rw [sq, huinv]; group
        _ = 1 := by rw [h3, ← zpow_add, add_neg_cancel, zpow_zero]
    rw [pow_succ', pow_mul, h2, one_pow]

theorem orderOf_eq_of_orderOf_sq {z : X} {k : ℕ} (hk : 1 ≤ k) (h : orderOf (z ^ 2) = 2 ^ k) :
    orderOf z = 2 ^ (k + 1) := by
  have hpos : 0 < orderOf z := by
    rcases Nat.eq_zero_or_pos (orderOf z) with h0 | h0
    · rw [orderOf_eq_zero_iff'] at h0
      have : orderOf (z ^ 2) = 0 := by
        rw [orderOf_eq_zero_iff']
        intro n hn hzn
        exact h0 (2 * n) (by omega) (by rw [pow_mul]; exact hzn)
      rw [this] at h
      exact absurd h (by positivity)
    · exact h0
  rw [orderOf_pow' z (by norm_num)] at h
  rcases Nat.even_or_odd (orderOf z) with he | ho
  · have hg : (orderOf z).gcd 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp he)
    rw [hg] at h
    have := Nat.div_mul_cancel (even_iff_two_dvd.mp he)
    rw [h] at this
    rw [← this, pow_succ]
  · have hg : (orderOf z).gcd 2 = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_two_left.mpr ho)
    rw [hg, Nat.div_one] at h
    rw [h] at ho
    exact absurd ho (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩))

theorem conjSubgroup_eq_of_inf_ne_bot [Finite X] {V : Subgroup X} (hV : IsTI V) {g h : X}
    (hne : conjSubgroup g V ⊓ conjSubgroup h V ≠ ⊥) : conjSubgroup g V = conjSubgroup h V := by
  have e : conjSubgroup h V = conjSubgroup (h * g⁻¹) (conjSubgroup g V) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  rw [e] at hne ⊢
  exact (conjSubgroup_eq_of_isTI (isTI_conjSubgroup hV g) hne).symm

theorem commute_of_isRootTypeTI {V : Subgroup X} (hV : IsRootTypeTI V) {g h : X}
    (hne : conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set X) ≠ ⊥) :
    ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨hxA, hxN⟩ := Subgroup.mem_inf.mp hx
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx'V : g⁻¹ * x * g ∈ V := mem_conjSubgroup.mp hxA
  have hx'N : g⁻¹ * x * g ∈ Subgroup.normalizer (conjSubgroup (g⁻¹ * h) V : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [mem_conjSubgroup]
    have hy := (Subgroup.mem_normalizer_iff.mp hxN) (g * y * g⁻¹)
    simp only [mem_conjSubgroup] at hy
    rw [show (g⁻¹ * h)⁻¹ * y * (g⁻¹ * h) = h⁻¹ * (g * y * g⁻¹) * h by group,
      show (g⁻¹ * h)⁻¹ * (g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹) * (g⁻¹ * h) =
        h⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * h by group]
    exact hy
  have hcomm := hV.2 (g⁻¹ * h) (by
    intro hbot
    have : g⁻¹ * x * g ∈ V ⊓ Subgroup.normalizer (conjSubgroup (g⁻¹ * h) V : Set X) :=
      ⟨hx'V, hx'N⟩
    rw [hbot, Subgroup.mem_bot] at this
    apply hx1'
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group)
  intro a ha b hb
  have ha' : g⁻¹ * a * g ∈ V := mem_conjSubgroup.mp ha
  have hb' : g⁻¹ * b * g ∈ conjSubgroup (g⁻¹ * h) V := by
    rw [mem_conjSubgroup, show (g⁻¹ * h)⁻¹ * (g⁻¹ * b * g) * (g⁻¹ * h) = h⁻¹ * b * h by group]
    exact mem_conjSubgroup.mp hb
  have := hcomm _ ha' _ hb'
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
    _ = b * a := by group


theorem orderOf_sq_of_orderOf_eq {z : X} {m : ℕ} (hm : 1 ≤ m) (h : orderOf z = 2 ^ m) :
    orderOf (z ^ 2) = 2 ^ (m - 1) := by
  rw [orderOf_pow' z (by norm_num), h]
  have hg : (2 ^ m).gcd 2 = 2 := Nat.gcd_eq_right (dvd_pow_self 2 (by omega))
  rw [hg]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]

theorem orderOf_mul_comm' (x y : X) : orderOf (x * y) = orderOf (y * x) := by
  have : x * y = x * (y * x) * x⁻¹ := by group
  rw [this, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

variable [Finite X]

theorem tim78_2_13 {V : Subgroup X} (hV : Assembly.IsElemAbelian 2 V) (hroot : IsRootTypeTI V) :
    V ⊓ pCore 2 X = ⊥ ∨ V ≤ pCore 2 X := by
  by_cases hVQ : V ⊓ pCore 2 X = ⊥
  · exact Or.inl hVQ
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCore 2 X with hQdef
  have hQn : Q.Normal := pCore_normal
  have hQ2 : IsPGroup 2 Q := pCore_isPGroup
  have hTI := hroot.1
  have hsq : ∀ (g : X), ∀ a ∈ conjSubgroup g V, a * a = 1 := by
    intro g a ha
    have h := hV.2 _ (mem_conjSubgroup.mp ha)
    have e : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by rw [sq, sq]; group
    have : a ^ 2 = 1 := by
      calc a ^ 2 = g * (g⁻¹ * a ^ 2 * g) * g⁻¹ := by group
        _ = 1 := by rw [← e, h]; group
    rw [← sq]
    exact this
  have hinv : ∀ (g : X), ∀ a ∈ conjSubgroup g V, a⁻¹ = a := fun g a ha =>
    inv_eq_of_mul_eq_one_left (hsq g a ha)
  have hinf : ∀ g h : X, conjSubgroup g V ≠ conjSubgroup h V →
      conjSubgroup g V ⊓ conjSubgroup h V = ⊥ := fun g h hne => by
    by_contra h'
    exact hne (conjSubgroup_eq_of_inf_ne_bot hTI h')
  have hnorm : ∀ g h : X, ∀ x ∈ conjSubgroup g V, x ≠ 1 →
      conjSubgroup x (conjSubgroup h V) = conjSubgroup h V →
      ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
    intro g h x hx hx1 heq
    refine commute_of_isRootTypeTI hroot fun hbot => ?_
    have : x ∈ conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set X) :=
      ⟨hx, conjSubgroup_eq_self_iff.mp heq⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx1 this
  have hcomm_of : ∀ g h : X, ∀ x ∈ conjSubgroup g V, x ≠ 1 → ∀ y ∈ conjSubgroup h V, y ≠ 1 →
      x * y = y * x → ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
    intro g h x hx hx1 y hy hy1 hxy
    refine hnorm g h x hx hx1 ?_
    rw [← conjSubgroup_mul]
    refine conjSubgroup_eq_of_inf_ne_bot hTI fun hbot => hy1 ?_
    have hmem : y ∈ conjSubgroup (x * h) V ⊓ conjSubgroup h V := by
      refine Subgroup.mem_inf.mpr ⟨?_, hy⟩
      rw [conjSubgroup_mul, mem_conjSubgroup]
      have : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [hxy]
          _ = y := by group
      rw [this]
      exact hy
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hQconj : ∀ g : X, conjSubgroup g V ⊓ Q ≠ ⊥ := by
    intro g hbot
    apply hVQ
    have e : conjSubgroup g (V ⊓ Q) = conjSubgroup g V ⊓ Q := by
      rw [conjSubgroup_inf]
      congr 1
      refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_iff.mpr fun y => ?_)
      exact ⟨fun hy => hQn.conj_mem y hy g, fun hy => by
        have := hQn.conj_mem _ hy g⁻¹
        simpa [mul_assoc] using this⟩
    rw [hbot] at e
    exact Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective |>.mp e
  have hconjQ : ∀ g q : X, q ∈ Q → g * q * g⁻¹ ∈ Q := fun g q hq => hQn.conj_mem q hq g
  have hstar : ∀ m : ℕ, ∀ g h : X, conjSubgroup g V ≠ conjSubgroup h V →
      (∃ α ∈ conjSubgroup g V ⊓ Q, α ≠ 1 ∧ ∃ β ∈ conjSubgroup h V ⊓ Q, β ≠ 1 ∧
        orderOf (α * β) = 2 ^ m) →
      ∀ a ∈ conjSubgroup g V, a ≠ 1 → ∀ b ∈ conjSubgroup h V, b ≠ 1 →
        orderOf (a * b) = 2 ^ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro g h hne ⟨α, hα, hα1, β, hβ, hβ1, hαβ⟩
    have hαβ1 : α * β ≠ 1 := by
      intro h1
      have : α = β := by
        calc α = α * β * β⁻¹ := by group
          _ = β := by rw [h1, one_mul, hinv h β hβ.1]
      have hmem : α ∈ conjSubgroup g V ⊓ conjSubgroup h V := ⟨hα.1, this ▸ hβ.1⟩
      rw [hinf g h hne, Subgroup.mem_bot] at hmem
      exact hα1 hmem
    by_cases hAB : ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a
    ·
      have hord2 : ∀ a ∈ conjSubgroup g V, a ≠ 1 → ∀ b ∈ conjSubgroup h V, b ≠ 1 →
          orderOf (a * b) = 2 := by
        intro a ha ha1 b hb hb1
        refine orderOf_eq_prime ?_ ?_
        · rw [sq, mul_assoc, ← mul_assoc b, ← hAB a ha b hb, mul_assoc, hsq h b hb, mul_one,
            hsq g a ha]
        · intro h1
          have : a = b := by
            calc a = a * b * b⁻¹ := by group
              _ = b := by rw [h1, one_mul, hinv h b hb]
          have hmem : a ∈ conjSubgroup g V ⊓ conjSubgroup h V := ⟨ha, this ▸ hb⟩
          rw [hinf g h hne, Subgroup.mem_bot] at hmem
          exact ha1 hmem
      have hm : 2 ^ m = 2 := by rw [← hαβ, hord2 α hα.1 hα1 β hβ.1 hβ1]
      intro a ha ha1 b hb hb1
      rw [hord2 a ha ha1 b hb hb1, hm]
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hαβ
      exact hαβ1 hαβ
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hAB
      refine hcomm_of g h α hα.1 hα1 β hβ.1 hβ1 ?_
      have h2 : (α * β) ^ 2 = 1 := by rw [← pow_one 2, ← hαβ]; exact pow_orderOf_eq_one _
      have : α * β * (α * β) = 1 := by rw [← sq]; exact h2
      calc α * β = α * β * (α * β) * (β⁻¹ * α⁻¹) := by group
        _ = β * α := by rw [this, one_mul, hinv h β hβ.1, hinv g α hα.1]
    have hm2 : 2 ≤ m := by omega
    have hAβ : conjSubgroup (β * g) V ≠ conjSubgroup g V := by
      intro heq
      apply hAB
      intro a ha b hb
      refine (hnorm h g β hβ.1 hβ1 ?_ b hb a ha).symm
      rw [← conjSubgroup_mul]
      exact heq
    have hxβ : ∀ x ∈ conjSubgroup g V, x ≠ 1 → orderOf (x * β) = 2 ^ m := by
      have hα' : β * α * β⁻¹ ∈ conjSubgroup (β * g) V ⊓ Q := by
        refine Subgroup.mem_inf.mpr ⟨?_, hconjQ β α hα.2⟩
        rw [conjSubgroup_mul, mem_conjSubgroup]
        group
        exact hα.1
      have hα'1 : β * α * β⁻¹ ≠ 1 := by
        intro h1
        apply hα1
        calc α = β⁻¹ * (β * α * β⁻¹) * β := by group
          _ = 1 := by rw [h1]; group
      have hαα' : orderOf (α * (β * α * β⁻¹)) = 2 ^ (m - 1) := by
        rw [hinv h β hβ.1, show α * (β * α * β) = (α * β) ^ 2 by rw [sq]; group]
        exact orderOf_sq_of_orderOf_eq (by omega) hαβ
      have hIH := ih (m - 1) (by omega) g (β * g) hAβ.symm
        ⟨α, hα, hα1, β * α * β⁻¹, hα', hα'1, hαα'⟩
      intro x hx hx1
      have hx' : β * x * β⁻¹ ∈ conjSubgroup (β * g) V := by
        rw [conjSubgroup_mul, mem_conjSubgroup]
        group
        exact hx
      have hx'1 : β * x * β⁻¹ ≠ 1 := by
        intro h1
        apply hx1
        calc x = β⁻¹ * (β * x * β⁻¹) * β := by group
          _ = 1 := by rw [h1]; group
      have h1 := hIH x hx hx1 _ hx' hx'1
      rw [hinv h β hβ.1, show x * (β * x * β) = (x * β) ^ 2 by rw [sq]; group] at h1
      have := orderOf_eq_of_orderOf_sq (by omega) h1
      rwa [Nat.sub_add_cancel (by omega)] at this
    intro x hx hx1 y hy hy1
    have hBx : conjSubgroup (x * h) V ≠ conjSubgroup h V := by
      intro heq
      apply hAB
      refine hnorm g h x hx hx1 ?_
      rw [← conjSubgroup_mul]
      exact heq
    have hβ' : x * β * x⁻¹ ∈ conjSubgroup (x * h) V ⊓ Q := by
      refine Subgroup.mem_inf.mpr ⟨?_, hconjQ x β hβ.2⟩
      rw [conjSubgroup_mul, mem_conjSubgroup]
      group
      exact hβ.1
    have hβ'1 : x * β * x⁻¹ ≠ 1 := by
      intro h1
      apply hβ1
      calc β = x⁻¹ * (x * β * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    have hββ' : orderOf (β * (x * β * x⁻¹)) = 2 ^ (m - 1) := by
      rw [hinv g x hx, show β * (x * β * x) = (β * x) ^ 2 by rw [sq]; group]
      refine orderOf_sq_of_orderOf_eq (by omega) ?_
      rw [orderOf_mul_comm']
      exact hxβ x hx hx1
    have hIH := ih (m - 1) (by omega) h (x * h) hBx.symm
      ⟨β, hβ, hβ1, x * β * x⁻¹, hβ', hβ'1, hββ'⟩
    have hy' : x * y * x⁻¹ ∈ conjSubgroup (x * h) V := by
      rw [conjSubgroup_mul, mem_conjSubgroup]
      group
      exact hy
    have hy'1 : x * y * x⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    have h1 := hIH y hy hy1 _ hy' hy'1
    rw [hinv g x hx, show y * (x * y * x) = (y * x) ^ 2 by rw [sq]; group] at h1
    have := orderOf_eq_of_orderOf_sq (by omega) h1
    rw [Nat.sub_add_cancel (by omega)] at this
    rw [orderOf_mul_comm']
    exact this
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact Q.one_mem
  have hvsq : v * v = 1 := hsq 1 v (by rw [conjSubgroup_one]; exact hv)
  refine BaerSuzuki.baer_suzuki (p := 2) v ?_ ?_
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact hvsq) hv1
  · intro g
    have hw : g * v * g⁻¹ ∈ conjSubgroup g V := by
      rw [mem_conjSubgroup]
      group
      exact hv
    by_cases hgV : conjSubgroup g V = conjSubgroup 1 V
    ·
      rw [conjSubgroup_one] at hgV
      rw [hgV] at hw
      have hle : Subgroup.closure ({v, g * v * g⁻¹} : Set X) ≤ V := by
        rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact hv
        · exact hw
      have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
      exact hV2.to_le hle
    · obtain ⟨⟨α, hα⟩, hα1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hQconj 1)
      obtain ⟨⟨β, hβ⟩, hβ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hQconj g)
      have hαβQ : α * β ∈ Q := Q.mul_mem (Subgroup.mem_inf.mp hα).2 (Subgroup.mem_inf.mp hβ).2
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨α * β, hαβQ⟩
      rw [Subgroup.orderOf_mk] at hm
      have hgV' : conjSubgroup 1 V ≠ conjSubgroup g V := fun h => hgV h.symm
      have hord := hstar m 1 g hgV' ⟨α, hα, fun h => hα1 (Subtype.ext h), β, hβ,
        fun h => hβ1 (Subtype.ext h), hm⟩ v (by rw [conjSubgroup_one]; exact hv) hv1
        (g * v * g⁻¹) hw (by
          intro h1
          apply hv1
          calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group)
      have hpow : (v * (g * v * g⁻¹)) ^ 2 ^ m = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one _
      exact isPGroup_closure_pair_involutions hvsq (hsq g _ hw) hpow

end CFSG.RankThree.GF2n.Tim78
