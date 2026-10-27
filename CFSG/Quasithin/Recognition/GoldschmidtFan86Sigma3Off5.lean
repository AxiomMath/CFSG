module

public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin

variable {H : Type*} [Group H] [Finite H]

theorem offender_bound {N A Q S : Subgroup H} (hN : IsElemAbelian 2 N) (hNS : N ≤ S)
    (hA : IsMaxElemAbelian S A) (hQN : ∀ q ∈ Q, ∀ n ∈ N, q * n = n * q)
    (hQS : Q.relIndex S = 2) :
    Nat.card N ≤ 2 * Nat.card ↥(N ⊓ Subgroup.centralizer (A : Set H)) := by
  have h1 := card_le_relIndex_mul_card hN hNS hA
  have hle : A ⊓ Q ≤ A ⊓ Subgroup.centralizer (N : Set H) :=
    inf_le_inf_left A fun q hq => Subgroup.mem_centralizer_iff.2 fun n hn => (hQN q hq n hn).symm
  have h2 : (A ⊓ Subgroup.centralizer (N : Set H)).relIndex A ≤ 2 := by
    calc (A ⊓ Subgroup.centralizer (N : Set H)).relIndex A ≤ (A ⊓ Q).relIndex A :=
          Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
      _ = Q.relIndex A := by rw [inf_comm, Subgroup.inf_relIndex_right]
      _ ≤ Q.relIndex S := Subgroup.relIndex_le_of_le_right hA.1 (by omega)
      _ = 2 := hQS
  exact h1.trans (Nat.mul_le_mul_right _ h2)

omit [Finite H] in
theorem fixed_free {N : Subgroup H} {x a q c : H} (hx3 : x * x * x = 1)
    (hxinv : ∀ n ∈ N, x⁻¹ * n * x ∈ N) (hfix : ∀ n ∈ N, x * n * x⁻¹ = n → n = 1)
    (hqN : ∀ n ∈ N, q * n = n * q) (haxq : a * x * a⁻¹ = q * x⁻¹) (hc : c ∈ N)
    (hac : a * c * a⁻¹ = c) (haw : a * (x * c * x⁻¹) * a⁻¹ = x * c * x⁻¹) :
    x * c * x⁻¹ = 1 := by
  have hq := hqN _ (hxinv c hc)
  have h1 : a * (x * c * x⁻¹) * a⁻¹ = x⁻¹ * c * x := by
    calc a * (x * c * x⁻¹) * a⁻¹ = (a * x * a⁻¹) * (a * c * a⁻¹) * (a * x * a⁻¹)⁻¹ := by group
      _ = (q * x⁻¹) * c * (q * x⁻¹)⁻¹ := by rw [haxq, hac]
      _ = q * (x⁻¹ * c * x) * q⁻¹ := by group
      _ = (x⁻¹ * c * x) * q * q⁻¹ := by rw [hq]
      _ = x⁻¹ * c * x := by group
  have h2 : x * c * x⁻¹ = x⁻¹ * c * x := by rw [← h1, haw]
  have h3 : c = x * c * x⁻¹ := by
    calc c = (x * x * x) * c * (x * x * x)⁻¹ := by rw [hx3]; group
      _ = x * (x * (x * c * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = x * (x * (x⁻¹ * c * x) * x⁻¹) * x⁻¹ := by rw [h2]
      _ = x * c * x⁻¹ := by group
  rw [hfix c hc h3.symm]
  group

omit [Finite H] in
theorem conj_eq_of_mem_centralizer {a g : H} (h : g ∈ Subgroup.centralizer {a}) :
    a * g * a⁻¹ = g := by
  have := Subgroup.mem_centralizer_singleton_iff.1 h
  rw [← this]
  group

theorem card_sq_le {N : Subgroup H} {x a q : H} (hx3 : x * x * x = 1)
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxinv : ∀ n ∈ N, x⁻¹ * n * x ∈ N)
    (hfix : ∀ n ∈ N, x * n * x⁻¹ = n → n = 1) (hqN : ∀ n ∈ N, q * n = n * q)
    (haxq : a * x * a⁻¹ = q * x⁻¹) :
    Nat.card ↥(N ⊓ Subgroup.centralizer {a}) ^ 2 ≤ Nat.card N := by
  set C := N ⊓ Subgroup.centralizer {a} with hC
  let Φ : C × C → N := fun p =>
    ⟨(p.1 : H) * (x * (p.2 : H) * x⁻¹), N.mul_mem p.1.2.1 (hxN _ p.2.2.1)⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ hΦ
    have hΦ' : (u : H) * (x * (v : H) * x⁻¹) = (u' : H) * (x * (v' : H) * x⁻¹) :=
      congrArg Subtype.val hΦ
    set c : H := (v' : H) * (v : H)⁻¹ with hcdef
    have hcC : c ∈ C := C.mul_mem v'.2 (C.inv_mem v.2)
    have hw : x * c * x⁻¹ = (u' : H)⁻¹ * (u : H) := by
      calc x * c * x⁻¹ = (x * (v' : H) * x⁻¹) * (x * (v : H) * x⁻¹)⁻¹ := by rw [hcdef]; group
        _ = (u' : H)⁻¹ * ((u' : H) * (x * (v' : H) * x⁻¹)) * (x * (v : H) * x⁻¹)⁻¹ := by group
        _ = (u' : H)⁻¹ * ((u : H) * (x * (v : H) * x⁻¹)) * (x * (v : H) * x⁻¹)⁻¹ := by rw [hΦ']
        _ = (u' : H)⁻¹ * (u : H) := by group
    have hw1 : x * c * x⁻¹ = 1 := by
      refine fixed_free hx3 hxinv hfix hqN haxq hcC.1 (conj_eq_of_mem_centralizer hcC.2) ?_
      rw [hw]
      exact conj_eq_of_mem_centralizer (C.mul_mem (C.inv_mem u'.2) u.2).2
    have hc1 : c = 1 := by
      calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
        _ = 1 := by rw [hw1]; group
    have hvv : (v' : H) = (v : H) := by
      have := hc1
      rw [hcdef, mul_inv_eq_one] at this
      exact this
    have huu : (u : H) = (u' : H) := by
      rw [hw1] at hw
      have := hw.symm
      rw [inv_mul_eq_one] at this
      exact this.symm
    exact Prod.ext (Subtype.ext huu) (Subtype.ext hvv.symm)
  have := Nat.card_le_card_of_injective Φ hinj
  rwa [Nat.card_prod, ← pow_two] at this

end CFSG.Quasithin.Fan86.Sigma3
