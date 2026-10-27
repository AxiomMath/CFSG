module

public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ1
public import CFSG.Quasithin.Vol2.Ch3E213MP6CA
public import CFSG.Quasithin.SteinbergBSSymplecticRoots

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp uElt uElt_mul antiSp_ext uMat_zero antiUnipotent antiUnipotentCenter_comm)
open CFSG.Quasithin.SteinbergBS (upper_of_mem_normalizer)

theorem exists_pow_conj_eq {G : Type*} [Group G] [Finite G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (h : ∀ t : G, t * x = x * t → t * y = y * t → t = 1) :
    ∃ n : ℕ, (x * y) ^ n * x * ((x * y) ^ n)⁻¹ = y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hinv : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hxi, hyi]
  have hx' : ∀ n : ℕ, x * (x * y) ^ n * x⁻¹ = ((x * y) ^ n)⁻¹ := by
    intro n
    rw [← conj_pow, ← inv_pow, hinv, hxi]
    congr 1
    calc x * (x * y) * x = x * x * (y * x) := by group
      _ = y * x := by rw [hx, one_mul]
  have hy' : ∀ n : ℕ, y * (x * y) ^ n * y⁻¹ = ((x * y) ^ n)⁻¹ := by
    intro n
    rw [← conj_pow, ← inv_pow, hinv]
    congr 1
    group
  set r := x * y with hr
  rcases Nat.even_or_odd (orderOf r) with ⟨j, hj⟩ | ⟨j, hj⟩
  · exfalso
    have hpos := orderOf_pos r
    have ht1 : r ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have ht2 : (r ^ j)⁻¹ = r ^ j := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, ← hj, pow_orderOf_eq_one]
    refine ht1 (h _ ?_ ?_)
    · have e := hx' j
      rw [ht2] at e
      calc r ^ j * x = x * r ^ j * x⁻¹ * x := by rw [e]
        _ = x * r ^ j := by group
    · have e := hy' j
      rw [ht2] at e
      calc r ^ j * y = y * r ^ j * y⁻¹ * y := by rw [e]
        _ = y * r ^ j := by group
  · refine ⟨j, ?_⟩
    have key : x * (r ^ j)⁻¹ = r ^ j * x := by
      rw [← hx' j, hxi]
      calc x * (x * r ^ j * x) = x * x * (r ^ j * x) := by group
        _ = r ^ j * x := by rw [hx, one_mul]
    have hr2 : r ^ (j + j) = r⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ, show j + j + 1 = orderOf r by omega, pow_orderOf_eq_one]
    calc r ^ j * x * (r ^ j)⁻¹ = r ^ j * (x * (r ^ j)⁻¹) := by group
      _ = r ^ (j + j) * x := by rw [key, pow_add]; group
      _ = y := by rw [hr2, hr, mul_inv_rev, hyi]; group

variable {k : Type} [Field k] [CharP k 2]

theorem center_mul_self (β γ : k) : uElt 0 β γ 0 * uElt 0 β γ 0 = (1 : antiSp k) := by
  have e : uElt (0 + 0 : k) (β + β + 0 * 0) (γ + γ + 0 * β + 0 * 0 * 0 + β * 0) (0 + 0) =
      uElt 0 0 0 0 := by
    congr 1 <;> simp [CharTwo.add_self_eq_zero]
  rw [uElt_mul, e]
  exact antiSp_ext uMat_zero

theorem center_mul (b c b' c' : k) :
    uElt 0 b c 0 * uElt 0 b' c' 0 = (uElt 0 (b + b') (c + c') 0 : antiSp k) := by
  rw [uElt_mul]
  congr 1 <;> ring

theorem eq_one_of_comm_comm {g : antiSp k} (hg : IsOppStd g) {b c b' c' : k} (hb : b ≠ 0)
    (hc : c ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0) {t : antiSp k}
    (h1 : t * uElt 0 b c 0 = uElt 0 b c 0 * t)
    (h2 : t * (g * uElt 0 b' c' 0 * g⁻¹) = g * uElt 0 b' c' 0 * g⁻¹ * t) : t = 1 := by
  have htU := mem_antiUnipotent_of_comm hb hc h1
  have hvU : g⁻¹ * t * g ∈ antiUnipotent k := by
    refine mem_antiUnipotent_of_comm hb' hc' ?_
    calc g⁻¹ * t * g * uElt 0 b' c' 0 = g⁻¹ * (t * (g * uElt 0 b' c' 0 * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * uElt 0 b' c' 0 * g⁻¹ * t) * g := by rw [h2]
      _ = uElt 0 b' c' 0 * (g⁻¹ * t * g) := by group
  exact eq_one_of_mul_eq_mul hg htU hvU (by group)

theorem isUpper_of_conj_eq {n : antiSp k} {b c b' c' : k} (hb : b ≠ 0) (hc : c ≠ 0)
    (hb' : b' ≠ 0) (hc' : c' ≠ 0) (h : n * uElt 0 b c 0 * n⁻¹ = uElt 0 b' c' 0) : IsUpper n := by
  refine upper_of_mem_normalizer (Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => ?_,
    fun hu => ?_⟩)
  · have hxu := antiUnipotentCenter_comm ⟨b, c, rfl⟩ hu
    refine mem_antiUnipotent_of_comm hb' hc' ?_
    rw [← h]
    calc n * u * n⁻¹ * (n * uElt 0 b c 0 * n⁻¹) = n * (u * uElt 0 b c 0) * n⁻¹ := by group
      _ = n * (uElt 0 b c 0 * u) * n⁻¹ := by rw [hxu]
      _ = n * uElt 0 b c 0 * n⁻¹ * (n * u * n⁻¹) := by group
  · have hxu := antiUnipotentCenter_comm ⟨b', c', rfl⟩ hu
    refine mem_antiUnipotent_of_comm hb hc ?_
    have hx : uElt 0 b c 0 = n⁻¹ * uElt 0 b' c' 0 * n := by rw [← h]; group
    rw [hx]
    calc u * (n⁻¹ * uElt 0 b' c' 0 * n) = n⁻¹ * ((n * u * n⁻¹) * uElt 0 b' c' 0) * n := by group
      _ = n⁻¹ * (uElt 0 b' c' 0 * (n * u * n⁻¹)) * n := by rw [hxu]
      _ = n⁻¹ * uElt 0 b' c' 0 * n * u := by group

end CFSG.Quasithin.Ch3E213M.G41.CTwo
