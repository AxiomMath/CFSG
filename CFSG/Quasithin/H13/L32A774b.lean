module

public import CFSG.Quasithin.H13.L32A774a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_three_of_comm {z a b c : G} (ha : a * z = z * a) (hb : b * z = z * b)
    (hz2 : z * z = 1) : (z * a) * (z * b) * (z * c) = z * (a * b * c) := by
  calc (z * a) * (z * b) * (z * c) = z * (a * z) * b * (z * c) := by group
    _ = z * (z * a) * b * (z * c) := by rw [ha]
    _ = (z * z) * a * (b * z) * c := by group
    _ = (z * z) * a * (z * b) * c := by rw [hb]
    _ = (z * z) * (a * z) * b * c := by group
    _ = (z * z) * (z * a) * b * c := by rw [ha]
    _ = z * (z * z) * (a * b * c) := by group
    _ = z * (a * b * c) := by rw [hz2, mul_one]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem comm_eq_one_of_comm_mem {q : G} (hqV : q ∈ Subgroup.centralizer (V : Set G))
    (hqU : ∀ u ∈ fsuU T V, q * u * q⁻¹ * u⁻¹ ∈ V)
    (hqL : ∀ l ∈ L, l * q * l⁻¹ * q⁻¹ ∈ V) {u : G} (hu : u ∈ fsuU T V) : q * u = u * q := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe ha hb
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  have hz2 : z * z = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (v_le_fsuU hzV)
  have hfU : ∀ {w : G}, w ∈ fsuU T V → q * w * q⁻¹ * w⁻¹ ∈ fsuU T V := fun hw =>
    v_le_fsuU (hqU _ hw)
  have hfmul : ∀ {a b : G}, a ∈ fsuU T V → b ∈ fsuU T V →
      q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by
    intro a b ha hb
    have h1 := hUc a ha _ (hfU hb)
    calc q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹ * b⁻¹) * a⁻¹ := by group
      _ = (q * a * q⁻¹) * a⁻¹ * (a * (q * b * q⁻¹ * b⁻¹)) * a⁻¹ := by group
      _ = (q * a * q⁻¹) * a⁻¹ * ((q * b * q⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [h1]
      _ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by group
  have hfV : ∀ {v : G}, v ∈ V → q * v * q⁻¹ * v⁻¹ = 1 := fun hv => by
    rw [← Subgroup.mem_centralizer_iff.mp hqV _ hv, mul_inv_cancel_right, mul_inv_cancel]
  have hfL : ∀ {l : G}, l ∈ L → ∀ {a : G}, a ∈ fsuU T V →
      q * (l * a * l⁻¹) * q⁻¹ * (l * a * l⁻¹)⁻¹ = l * (q * a * q⁻¹ * a⁻¹) * l⁻¹ := by
    intro l hl a ha
    have hv' : l⁻¹ * q * l * q⁻¹ ∈ V := by
      have := hqL l⁻¹ (inv_mem hl)
      rwa [inv_inv] at this
    have hqa : q * a * q⁻¹ ∈ fsuU T V := by
      have := mul_mem (hfU ha) ha
      rwa [show q * a * q⁻¹ * a⁻¹ * a = q * a * q⁻¹ by group] at this
    have h1 := hUc _ (v_le_fsuU hv') _ hqa
    calc q * (l * a * l⁻¹) * q⁻¹ * (l * a * l⁻¹)⁻¹
        = l * ((l⁻¹ * q * l * q⁻¹) * (q * a * q⁻¹)) * (l⁻¹ * q * l * q⁻¹)⁻¹ * a⁻¹ * l⁻¹ := by
          group
      _ = l * ((q * a * q⁻¹) * (l⁻¹ * q * l * q⁻¹)) * (l⁻¹ * q * l * q⁻¹)⁻¹ * a⁻¹ * l⁻¹ := by
          rw [h1]
      _ = l * (q * a * q⁻¹ * a⁻¹) * l⁻¹ := by group
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have hxN := C.l1_le_normalizer hxL1
  have hxz : x * z * x⁻¹ = z :=
    (mem_normalizer_iff_of_gen hzV1 hz1 hgen).mp
      (Subgroup.mem_inf.mp (L32NSet14.Setting.L1_le hxL1)).2
  have hxU : ∀ {w : G}, w ∈ fsuU T V → x * w * x⁻¹ ∈ fsuU T V := fun hw =>
    (Subgroup.mem_normalizer_iff.mp hxN _).mp hw
  have hrel : ∀ {w : G}, w ∈ fsuU T V →
      (q * w * q⁻¹ * w⁻¹) * (x * (q * w * q⁻¹ * w⁻¹) * x⁻¹) *
        (x * x * (q * w * q⁻¹ * w⁻¹) * (x * x)⁻¹) = 1 := by
    intro w hw
    have hw1 := hxU hw
    have hw2 := hxU hw1
    set y := w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) with hy
    have hyU : y ∈ fsuU T V := mul_mem (mul_mem hw hw1) hw2
    have hyV : y ∈ V := by
      by_contra hyV
      apply C.comm_not_mem C.u0_eq hxL1 hx3 hx1 hyU hyV
      have hx3' : x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = w := by
        calc x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * w * (x ^ 3)⁻¹ := by
              simp only [pow_succ, pow_zero, one_mul]; group
          _ = w := by rw [hx3]; group
      have e : x * y * x⁻¹ = y := by
        rw [hy]
        calc x * (w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) * x⁻¹
            = (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) *
                (x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹) := by group
          _ = (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) * w := by rw [hx3']
          _ = w * ((x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) := by
              rw [hUc _ (mul_mem hw1 hw2) w hw]
          _ = w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) := by group
      rw [e, mul_inv_cancel]
      exact one_mem _
    have h1 := hfV hyV
    rw [hy, hfmul (mul_mem hw hw1) hw2, hfmul hw hw1, hfL hxL hw,
      show x * (x * w * x⁻¹) * x⁻¹ = (x * x) * w * (x * x)⁻¹ by group,
      hfL (mul_mem hxL hxL) hw] at h1
    exact h1
  by_contra hne
  set a := q * u * q⁻¹ * u⁻¹ with ha
  have haV : a ∈ V := hqU u hu
  have ha1 : a ≠ 1 := fun h => hne (by
    rw [ha] at h
    calc q * u = (q * u * q⁻¹ * u⁻¹) * u * q := by group
      _ = u * q := by rw [h, one_mul])
  have hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    hUc v (v_le_fsuU hv) w (v_le_fsuU hw)
  have haz : a ≠ z := by
    intro h
    have h1 := hrel hu
    rw [← ha, h, hxz, show x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ by group, hxz, hxz,
      hz2, one_mul] at h1
    exact hz1 h1
  have hza1 : z * a ≠ 1 := fun h => haz (by
    calc a = z * (z * a) := by rw [← mul_assoc, hz2, one_mul]
      _ = z := by rw [h, mul_one])
  obtain ⟨l, hl, hlz, hla⟩ := exists_conj_eq_pair (C.hyp.hyp1281One C.h13322 C.hMod)
    hzV haV hzV (mul_mem hzV haV) hz1 ha1 hz1 hza1 (Ne.symm haz)
    (fun h => ha1 (by
      calc a = z * (z * a) := by rw [← mul_assoc, hz2, one_mul]
        _ = z * z := by rw [← h]
        _ = 1 := hz2))
  have hlN : l ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    le_normalizer_conjClosure V _ ((mem_normalizer_iff_of_gen hzV1 hz1 hgen).mpr hlz)
  have hu' : l * u * l⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp hlN u).mp hu
  have h1 := hrel hu'
  rw [hfL hl hu, ← ha, hla] at h1
  have hxa : x * a * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hxL) a).mp haV
  have hxxa : x * x * a * (x * x)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hLV (mul_mem hxL hxL)) a).mp haV
  have h2 := hrel hu
  rw [← ha] at h2
  have e1 : x * (z * a) * x⁻¹ = z * (x * a * x⁻¹) := by
    rw [show x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) by group, hxz]
  have e2 : x * x * (z * a) * (x * x)⁻¹ = z * (x * x * a * (x * x)⁻¹) := by
    rw [show x * x * (z * a) * (x * x)⁻¹ = (x * (x * z * x⁻¹) * x⁻¹) * (x * x * a * (x * x)⁻¹)
      by group, hxz, hxz]
  rw [e1, e2, mul_three_of_comm (hVc z hzV a haV).symm (hVc z hzV _ hxa).symm hz2, h2,
    mul_one] at h1
  exact hz1 h1

theorem comm_sL_eq_one {p : G} (hp : p ∈ pCoreOf 2 L) (hpL : ∀ l ∈ L, l * p * l⁻¹ * p⁻¹ ∈ V)
    {s : G} (hs : s ∈ sL T L V) : p * s = s * p := by
  have hLV := C.L_le_normalizer_V
  have hPL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hPn : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have key : ∀ l ∈ L, ∀ u ∈ fsuU T V, p * (l * u * l⁻¹) = (l * u * l⁻¹) * p := by
    intro l hl u hu
    set q := l⁻¹ * p * l with hq
    have hqP : q ∈ pCoreOf 2 L := by
      have := (Subgroup.mem_normalizer_iff.mp (hPn (inv_mem hl)) p).mp hp
      rwa [inv_inv] at this
    have hqV : q ∈ Subgroup.centralizer (V : Set G) := by
      rw [C.pCoreOf_eq] at hqP
      exact (Subgroup.mem_inf.mp hqP).2
    have hqL : ∀ l' ∈ L, l' * q * l'⁻¹ * q⁻¹ ∈ V := by
      intro l' hl'
      have h1 := hpL (l * l' * l⁻¹) (mul_mem (mul_mem hl hl') (inv_mem hl))
      have h2 := (Subgroup.mem_normalizer_iff.mp (hLV (inv_mem hl)) _).mp h1
      rwa [show l⁻¹ * (l * l' * l⁻¹ * p * (l * l' * l⁻¹)⁻¹ * p⁻¹) * l⁻¹⁻¹ =
        l' * q * l'⁻¹ * q⁻¹ by rw [hq]; group] at h2
    have h := C.comm_eq_one_of_comm_mem hqV (fun u hu => C.comm_mem_v_sL hqP
      (le_conjClosure _ _ hu)) hqL hu
    calc p * (l * u * l⁻¹) = l * (q * u) * l⁻¹ := by rw [hq]; group
      _ = l * (u * q) * l⁻¹ := by rw [h]
      _ = (l * u * l⁻¹) * p := by rw [hq]; group
  have hs' : s ∈ Subgroup.closure {y | ∃ l ∈ L, ∃ u ∈ fsuU T V, l * u * l⁻¹ = y} := hs
  clear hs
  induction hs' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, u, hu, rfl⟩ := hy
    exact key l hl u hu
  | one => simp
  | mul a b _ _ iha ihb =>
    calc p * (a * b) = (p * a) * b := by group
      _ = a * (p * b) := by rw [iha]; group
      _ = a * b * p := by rw [ihb]; group
  | inv a _ iha =>
    calc p * a⁻¹ = a⁻¹ * (a * p) * a⁻¹ := by group
      _ = a⁻¹ * (p * a) * a⁻¹ := by rw [iha]
      _ = a⁻¹ * p := by group

end Ctx73

end CFSG.Quasithin.H13.L32A
