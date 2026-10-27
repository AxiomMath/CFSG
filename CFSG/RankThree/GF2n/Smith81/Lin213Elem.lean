module

public import CFSG.RankThree.GF2n.Smith81.Lin28CondMain

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem lin213_of_pow_four {Z : Subgroup G} {w : G} (hw4 : w ^ 4 = 1)
    (hcl : w ^ 2 ≠ 1 → InZClass Z (w ^ 2)) :
    (orderOf w = 2 ∨ orderOf w = 4 ∨ Odd (orderOf w)) ∧
      (orderOf w = 4 → InZClass Z (w ^ 2)) := by
  have hdvd : orderOf w ∣ 2 ^ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hw4)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨?_, fun ho => hcl fun h1 => ?_⟩
  · interval_cases k
    · right; right; rw [hk']; exact odd_one
    · left; rw [hk']; norm_num
    · right; left; rw [hk']; norm_num
  · have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at h2
    norm_num at h2

theorem lin213_conj {Z : Subgroup G} {w : G} (a : G)
    (h : (orderOf w = 2 ∨ orderOf w = 4 ∨ Odd (orderOf w)) ∧
      (orderOf w = 4 → InZClass Z (w ^ 2))) :
    (orderOf (a * w * a⁻¹) = 2 ∨ orderOf (a * w * a⁻¹) = 4 ∨ Odd (orderOf (a * w * a⁻¹))) ∧
      (orderOf (a * w * a⁻¹) = 4 → InZClass Z ((a * w * a⁻¹) ^ 2)) := by
  have ho : orderOf w = orderOf (a * w * a⁻¹) :=
    SemiconjBy.orderOf_eq a (show a * w = a * w * a⁻¹ * a by group)
  rw [← ho]
  refine ⟨h.1, fun h4 => ?_⟩
  obtain ⟨g, z, hz, hz1, e⟩ := h.2 h4
  refine ⟨a * g, z, hz, hz1, ?_⟩
  rw [conj_pow, e]
  group

variable [Finite G]

theorem lin213_of_mem_Q {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {w : G} (hw : w ∈ Q) :
    (orderOf w = 2 ∨ orderOf w = 4 ∨ Odd (orderOf w)) ∧
      (orderOf w = 4 → InZClass Z (w ^ 2)) :=
  lin213_of_pow_four
    (by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; exact Z_sq H (sq_mem_Z H hw))
    (fun hne => ⟨1, w ^ 2, sq_mem_Z H hw, hne, by group⟩)

theorem InZClass.ne_one {Z : Subgroup G} {v : G} (h : InZClass Z v) : v ≠ 1 := by
  obtain ⟨g, z, -, hz1, rfl⟩ := h
  intro e
  apply hz1
  have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  rw [this, e]
  group

theorem InZClass.mul_self {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {v : G}
    (h : InZClass Z v) : v * v = 1 := by
  obtain ⟨g, z, hz, -, rfl⟩ := h
  have hz2 : z * z = 1 := by rw [← pow_two]; exact Z_sq H hz
  calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [hz2]; group

theorem lin213_of_mem_Q_left {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (H : StrothHyp M Q Z) (hS : LinSetup M Q Z B n V₁ V₂)
    (h31 : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {x y : G} (hxQ : x ∈ Q)
    (hx : InZClass Z x) (hy : InZClass Z y) (hyL : y ∈ Lgen M (LB M Q B)) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  obtain ⟨-, hV₁Q, -, hV₂Q, -, -, hN₁, hN₂, -, -⟩ := hS.basic
  have hyinv : y⁻¹ = y := (eq_inv_of_mul_eq_one_left (hy.mul_self H)).symm
  have hsq : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [hyinv, pow_two]; group
  have hmem : (x * y) ^ 2 ∈ V₁ ∨ (x * y) ^ 2 ∈ V₂ := by
    rw [hsq]
    rcases (h31 x hxQ hx.ne_one).1 hx with h | h
    · exact Or.inl (V₁.mul_mem h ((Subgroup.mem_normalizer_iff.mp (hN₁ hyL) x).mp h))
    · exact Or.inr (V₂.mul_mem h ((Subgroup.mem_normalizer_iff.mp (hN₂ hyL) x).mp h))
  have h31' : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₂ ∨ v ∈ V₁) :=
    fun v hv hv1 => (h31 v hv hv1).trans or_comm
  have hsq1 : (x * y) ^ 2 * (x * y) ^ 2 = 1 := by
    rcases hmem with h | h
    · exact Lin31Prop.sq_eq_one H hV₁Q h31 _ h
    · exact Lin31Prop.sq_eq_one H hV₂Q h31' _ h
  refine lin213_of_pow_four ?_ fun hne => ?_
  · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    exact hsq1
  · have hQ : (x * y) ^ 2 ∈ Q := hmem.elim (fun h => hV₁Q h) (fun h => hV₂Q h)
    exact (h31 _ hQ hne).2 hmem

theorem mem_Lgen_of_inZClass (h212two : Lin212TwoStatement) {M Q Z B : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 2 ≤ n) {y : G} (hyM : y ∈ M) (hy : InZClass Z y)
    (hyQ : y ∉ Q) : y ∈ Lgen M (LB M Q B) := by
  obtain ⟨g, z, hz, hz1, rfl⟩ := hy
  have hs : Sit M Q Z (conjSubgroup g Z) (g * z * g⁻¹) := Sit.of_conj hc.hyp hz hz1 hyM hyQ
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    subst hn2
    exact (h212two G M Q Z B V₁ V₂ hb hc hS _ _ hs).1
  · have h31 := lin31Statement_holds
    have hcond := lin212Cond_of lin28CondStatement_holds linModuleStatement_holds
      (lin212C7_of lin28CondStatement_holds) h31
    have h28a := lin28aBelow_of_parity (lin28aEven_of h31 hcond) (lin28aOdd_of h31 hcond)
    have hne := h28a G M Q Z B _ _ n V₁ V₂ hb hc hS h hs
    exact (hcond G M Q Z B n V₁ V₂ hb hc hS h _ _ hs hne).1

end CFSG.RankThree.GF2n.Smith81

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def Lin213OutsideStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n →
    ∀ x y : G, x ∈ M → y ∈ M → InZClass Z x → InZClass Z y → x ∉ Q → y ∉ Q → x * y ∉ Q →
      (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
        (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2))

theorem lin213Statement_of_outside (h212two : Lin212TwoStatement)
    (hOut : Lin213OutsideStatement) : Lin213Statement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn x y hxM hyM hx hy
  have H := hc.hyp
  by_cases hxy : x * y ∈ Q
  · exact lin213_of_mem_Q H hxy
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS hn
  by_cases hxQ : x ∈ Q
  · have hyQ : y ∉ Q := fun hyQ => hxy (Q.mul_mem hxQ hyQ)
    exact lin213_of_mem_Q_left H hS' h31' hxQ hx hy
      (mem_Lgen_of_inZClass h212two hb hc hS hn hyM hy hyQ)
  by_cases hyQ : y ∈ Q
  · have hxL := mem_Lgen_of_inZClass h212two hb hc hS hn hxM hx hxQ
    have h := lin213_conj x (lin213_of_mem_Q_left H hS' h31' hyQ hy hx hxL)
    rwa [show x * (y * x) * x⁻¹ = x * y by group] at h
  exact hOut G M Q Z B n V₁ V₂ hb hc hS hn x y hxM hyM hx hy hxQ hyQ hxy

end CFSG.RankThree.GF2n.Smith81
