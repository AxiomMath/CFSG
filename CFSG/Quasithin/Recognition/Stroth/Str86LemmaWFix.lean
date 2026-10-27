module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Stroth

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commute_of_commute_of_fixedPointFree {H V L N : Subgroup G} {w y v : G}
    (hV : IsPGroup 2 V) (hLN : L ≤ N) (hNV : N ≤ V)
    (hL : ⁅L, oTwoUpper H⁆ = ⊥) (hN : ⁅V, oTwoUpper H⁆ ≤ N)
    (hfpf : ∀ x ∈ N, w * x * w⁻¹ * x⁻¹ ∈ L → x ∈ L)
    (hyH : y ∈ H) (hy : Odd (orderOf y)) (hyw : Commute y w)
    (hv : v ∈ V) (hvw : Commute v w) : Commute y v := by
  have hyO : y ∈ oTwoUpper H := mem_oTwoUpper_of_odd hyH hy
  set c : G := ⁅v, y⁆ with hc
  have hc_eq : c = v * y * v⁻¹ * y⁻¹ := by rw [hc, commutatorElement_def]
  have hcN : c ∈ N := by
    rw [hc]
    exact hN (Subgroup.commutator_mem_commutator hv hyO)
  have hconj : w * c * w⁻¹ = c := by
    rw [hc, conjugate_commutatorElement, (Commute.symm hvw).mul_inv_cancel,
      (Commute.symm hyw).mul_inv_cancel]
  have hmem : w * c * w⁻¹ * c⁻¹ ∈ L := by
    rw [hconj, mul_inv_cancel]
    exact L.one_mem
  have hcL : c ∈ L := hfpf c hcN hmem
  have hcV : c ∈ V := hNV (hLN hcL)
  have hcent : c ∈ Subgroup.centralizer (oTwoUpper H : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL) hcL
  have hyc : Commute y c := (Subgroup.mem_centralizer_iff.mp hcent) y hyO
  have hci : Commute y c⁻¹ := hyc.inv_right
  have hc_inv : c⁻¹ = y * v * y⁻¹ * v⁻¹ := by
    rw [hc_eq]
    group
  have hstep : y * v * y⁻¹ = c⁻¹ * v := by
    rw [hc_inv]
    group
  have hpow : ∀ j : ℕ, y ^ j * v * (y ^ j)⁻¹ = (c⁻¹) ^ j * v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hj : y ^ j * c⁻¹ = c⁻¹ * y ^ j := (hci.pow_left j).eq
      calc
        y ^ (j + 1) * v * (y ^ (j + 1))⁻¹
            = y ^ j * (y * v * y⁻¹) * (y ^ j)⁻¹ := by group
        _ = y ^ j * (c⁻¹ * v) * (y ^ j)⁻¹ := by rw [hstep]
        _ = (y ^ j * c⁻¹) * (v * (y ^ j)⁻¹) := by group
        _ = (c⁻¹ * y ^ j) * (v * (y ^ j)⁻¹) := by rw [hj]
        _ = c⁻¹ * (y ^ j * v * (y ^ j)⁻¹) := by group
        _ = c⁻¹ * ((c⁻¹) ^ j * v) := by rw [ih]
        _ = (c⁻¹) ^ (j + 1) * v := by rw [pow_succ']; group
  have hcn : c ^ orderOf y = 1 := by
    have h := hpow (orderOf y)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    have h2 : (c⁻¹) ^ orderOf y = 1 := by
      have h3 := congrArg (· * v⁻¹) h
      simpa [mul_assoc] using h3.symm
    simpa [inv_pow] using h2
  have hdvd : orderOf c ∣ orderOf y := orderOf_dvd_of_pow_eq_one hcn
  obtain ⟨j, hj⟩ := hV ⟨c, hcV⟩
  have hcj : c ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hdvd2 : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hcj
  have hcop : Nat.Coprime (orderOf y) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hy)
  have hord : orderOf c = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd hcop) hdvd2
  have hone : c = 1 := orderOf_eq_one_iff.mp hord
  have hv' : y * v * y⁻¹ = v := by
    rw [hstep, hone, inv_one, one_mul]
  have hyv : y * v = v * y := by
    have h := congrArg (· * y) hv'
    simpa [mul_assoc] using h
  exact hyv

end CFSG.Quasithin.Stroth

end
