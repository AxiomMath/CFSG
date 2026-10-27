module

public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.Quasithin.SmithCurtis

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

@[expose] def sumT (X : Subgroup G) [Fintype X] (n : G) : V →ₗ[k] V :=
  ∑ x : X, ρ ((x : G) * n)

theorem sumT_apply (X : Subgroup G) [Fintype X] (n : G) (v : V) :
    sumT ρ X n v = ∑ x : X, ρ ((x : G) * n) v := by
  rw [sumT, LinearMap.sum_apply]

theorem sumT_mem_fixSub {U X Us : Subgroup G} {n : G} {_ : Fintype X}
    (hU : ∀ u ∈ U, ∃ x ∈ X, ∃ v ∈ Us, u = x * v)
    (hXUs : ∀ x ∈ X, ∀ v ∈ Us, x⁻¹ * v * x ∈ Us) (hnUs : ∀ v ∈ Us, n⁻¹ * v * n ∈ U)
    {m : V} (hm : m ∈ fixSub ρ U) : sumT ρ X n m ∈ fixSub ρ U := by
  intro u hu
  obtain ⟨x', hx', v, hv, rfl⟩ := hU u hu
  rw [sumT_apply, map_sum]
  have hterm : ∀ x : X, ρ (x' * v) (ρ ((x : G) * n) m) = ρ (x' * (x * n)) m := by
    intro x
    rw [act_mul]
    refine act_eq_of_mem ρ ?_ hm
    have e : (x' * (x * n))⁻¹ * (x' * v * (x * n)) = n⁻¹ * ((x : G)⁻¹ * v * x) * n := by group
    rw [e]
    exact hnUs _ (hXUs x x.2 v hv)
  simp only [hterm]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨x', hx'⟩) _ _ fun x => by
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_assoc]

theorem act_mem_augSub_of_fixed {L X Y Q H : Subgroup G} {n : G} [Finite Y]
    (hL : L ≤ Y ⊔ Q) (hQL : Q ≤ L)
    (hXQ : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hYQ : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hHQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hnQ : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q)
    (hHX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hnY : ∀ y ∈ Y, n * y * n⁻¹ ∈ X)
    (hnX : ∀ x ∈ X, n * x * n⁻¹ ∈ L)
    (hbru : ∀ y ∈ Y, y ≠ 1 → ∃ a ∈ X, ∃ h ∈ H, ∃ c ∈ X, y = a * (h * n) * c)
    {z : V} (hz : z ∈ augSub ρ L) (hfix : ∀ x ∈ X, ρ x z = z) :
    ρ n z ∈ augSub ρ L := by
  classical
  have := Fintype.ofFinite Y
  have hzYQ : z ∈ augSub ρ Y ⊔ augSub ρ Q := augSub_sup_le ρ Y Q (augSub_mono ρ hL hz)
  have hsum : ∑ y : Y, ρ y z ∈ augSub ρ Q := by
    obtain ⟨zY, hzY, zQ, hzQ, rfl⟩ := Submodule.mem_sup.mp hzYQ
    simp only [map_add, Finset.sum_add_distrib, sum_act_eq_zero ρ hzY, zero_add]
    exact Submodule.sum_mem _ fun y _ => act_mem_augSub ρ (hYQ y y.2) hzQ
  have hterm : ∀ y : Y, y ≠ 1 → ρ y z ∈ augSub ρ X ⊔ augSub ρ Q := by
    intro y hy
    obtain ⟨a, ha, h, hh, c, hc, e⟩ := hbru y y.2 fun h1 => hy (OneMemClass.coe_eq_one.mp h1)
    have e2 : ρ y z = ρ a (ρ (h * n) z) := by
      rw [e, ← act_mul, ← act_mul, hfix c hc]
    rw [e2]
    obtain ⟨zY, hzY, zQ, hzQ, rfl⟩ := Submodule.mem_sup.mp hzYQ
    have h1 : ρ (h * n) zY ∈ augSub ρ X := by
      refine act_mem_augSub ρ (fun y' hy' => ?_) hzY
      have e3 : h * n * y' * (h * n)⁻¹ = h * (n * y' * n⁻¹) * h⁻¹ := by group
      rw [e3]
      exact hHX h hh _ (hnY y' hy')
    have h2 : ρ (h * n) zQ ∈ augSub ρ Q := by
      refine act_mem_augSub ρ (fun q hq => ?_) hzQ
      have e3 : h * n * q * (h * n)⁻¹ = h * (n * q * n⁻¹) * h⁻¹ := by group
      rw [e3]
      exact hHQ h hh _ (hnQ q hq)
    rw [map_add, map_add]
    exact add_mem (Submodule.mem_sup_left (act_mem_augSub_self ρ ha h1))
      (Submodule.mem_sup_right (act_mem_augSub ρ (hXQ a ha) h2))
  have hz2 : z ∈ augSub ρ X ⊔ augSub ρ Q := by
    have e : z = ∑ y : Y, ρ y z - ∑ y ∈ (Finset.univ : Finset Y).erase 1, ρ y z := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), OneMemClass.coe_one, map_one,
        Module.End.one_apply, add_sub_cancel_right]
    rw [e]
    exact sub_mem (Submodule.mem_sup_right hsum)
      (Submodule.sum_mem _ fun y hy => hterm y (Finset.ne_of_mem_erase hy))
  obtain ⟨zX, hzX, zQ, hzQ, rfl⟩ := Submodule.mem_sup.mp hz2
  rw [map_add]
  exact add_mem (act_mem_augSub ρ hnX hzX) (act_mem_augSub ρ (fun q hq => hQL (hnQ q hq)) hzQ)

theorem act_sub_sumT_mem_augSub {L U X : Subgroup G} {n : G} {_ : Fintype X}
    {_ : DecidableEq X} (φ : G → G)
    (hφ : ∀ x ∈ X, x ≠ 1 → ∃ l ∈ L, ∃ u ∈ U, x * n = l * φ x * u)
    {m : V} (hm : m ∈ fixSub ρ U) :
    ρ n m - (sumT ρ X n m - ∑ x ∈ (Finset.univ : Finset X).erase 1, ρ (φ x) m) ∈
      augSub ρ L := by
  have hsplit : sumT ρ X n m = ρ n m + ∑ x ∈ (Finset.univ : Finset X).erase 1, ρ (x * n) m := by
    rw [sumT_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), OneMemClass.coe_one,
      one_mul]
  have hterm : ∀ x ∈ (Finset.univ : Finset X).erase 1,
      ρ ((x : G) * n) m - ρ (φ x) m ∈ augSub ρ L := by
    intro x hx
    obtain ⟨l, hl, u, hu, e⟩ :=
      hφ x x.2 fun h => Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp h)
    rw [e, ← act_mul, hm u hu, ← act_mul]
    exact sub_mem_augSub ρ hl _
  have e : ρ n m - (sumT ρ X n m - ∑ x ∈ (Finset.univ : Finset X).erase 1, ρ (φ x) m) =
      -∑ x ∈ (Finset.univ : Finset X).erase 1, (ρ ((x : G) * n) m - ρ (φ x) m) := by
    rw [hsplit, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact neg_mem (Submodule.sum_mem _ hterm)

theorem sumT_sumT {p : ℕ} [CharP k p] {U X : Subgroup G} {n : G} {_ : Fintype X}
    {_ : DecidableEq X} (hpX : p ∣ Nat.card X) (ψ : G → G)
    (hψ : ∀ x ∈ X, x ≠ 1 → ∃ a ∈ X, ∃ u ∈ U, n * x * n = a * n * ψ x * u)
    (hn2 : ∀ x ∈ X, (n * n)⁻¹ * x * (n * n) ∈ U)
    {m : V} (hm : m ∈ fixSub ρ U) :
    sumT ρ X n (sumT ρ X n m) =
      sumT ρ X n (∑ x ∈ (Finset.univ : Finset X).erase 1, ρ (ψ x) m) := by
  have hsplit : sumT ρ X n m = ρ n m + ∑ x ∈ (Finset.univ : Finset X).erase 1, ρ (x * n) m := by
    rw [sumT_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), OneMemClass.coe_one,
      one_mul]
  have h1 : sumT ρ X n (ρ n m) = 0 := by
    rw [sumT_apply]
    have hx : ∀ x : X, ρ ((x : G) * n) (ρ n m) = ρ (n * n) m := by
      intro x
      rw [act_mul]
      refine act_eq_of_mem ρ ?_ hm
      have e : (n * n)⁻¹ * (x * n * n) = (n * n)⁻¹ * x * (n * n) := by group
      rw [e]
      exact hn2 x x.2
    simp only [hx, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨c, hc⟩ := hpX
    rw [hc, mul_nsmul', nsmul_char_eq_zero (k := k) p]
  have h2 : ∀ x ∈ (Finset.univ : Finset X).erase 1,
      sumT ρ X n (ρ ((x : G) * n) m) = sumT ρ X n (ρ (ψ x) m) := by
    intro x hx
    obtain ⟨a, ha, u, hu, e⟩ :=
      hψ x x.2 fun h => Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp h)
    rw [sumT_apply, sumT_apply]
    have hterm : ∀ y : X, ρ ((y : G) * n) (ρ ((x : G) * n) m) = ρ ((y * ⟨a, ha⟩ : X) * n)
        (ρ (ψ x) m) := by
      intro y
      rw [act_mul, act_mul, Subgroup.coe_mul]
      have e2 : (y : G) * n * (x * n) = y * a * n * ψ x * u := by
        rw [mul_assoc (y : G) n, ← mul_assoc n, e]
        group
      rw [e2, ← act_mul _ _ u, hm u hu]
    simp only [hterm]
    exact Fintype.sum_equiv (Equiv.mulRight ⟨a, ha⟩) _ _ fun y => rfl
  rw [hsplit, map_add, h1, zero_add, map_sum, map_sum]
  exact Finset.sum_congr rfl h2

end CFSG.Quasithin.SmithCurtis
