module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

section Heis

variable {G : Type*} [Group G] {x y : G}

theorem heis_yinv_x_y (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    y⁻¹ * x * y = x * ⁅x, y⁆ := by
  have h1 : ⁅x, y⁆ * y * x = x * y := by
    rw [commutatorElement_def]
    group
  have h2 : y * ⁅x, y⁆ = ⁅x, y⁆ * y := hzy.symm.eq
  calc y⁻¹ * x * y = y⁻¹ * (⁅x, y⁆ * y * x) := by rw [h1]; group
    _ = y⁻¹ * (y * ⁅x, y⁆ * x) := by rw [h2]
    _ = ⁅x, y⁆ * x := by group
    _ = x * ⁅x, y⁆ := hzx.eq

theorem heis_xinv_y_x (hzx : Commute ⁅x, y⁆ x) : x⁻¹ * y * x = ⁅x, y⁆⁻¹ * y := by
  have h : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  have hc : x⁻¹ * ⁅x, y⁆⁻¹ * x = ⁅x, y⁆⁻¹ := by
    rw [mul_assoc, (hzx.inv_left).eq]; group
  calc x⁻¹ * y * x = x⁻¹ * (⁅x, y⁆⁻¹ * (⁅x, y⁆ * y)) * x := by group
    _ = x⁻¹ * (⁅x, y⁆⁻¹ * (x * y * x⁻¹)) * x := by rw [h]
    _ = (x⁻¹ * ⁅x, y⁆⁻¹ * x) * y := by group
    _ = ⁅x, y⁆⁻¹ * y := by rw [hc]

theorem heis_yinv_xpow_y (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (a : ℕ) :
    y⁻¹ * x ^ a * y = x ^ a * ⁅x, y⁆ ^ a := by
  have h := heis_yinv_x_y hzx hzy
  have hconj : y⁻¹ * x ^ a * y = (y⁻¹ * x * y) ^ a := by
    rw [show y⁻¹ * x ^ a * y = y⁻¹ * x ^ a * y⁻¹⁻¹ by rw [inv_inv], ← conj_pow, inv_inv]
  rw [hconj, h, (hzx.symm).mul_pow]

theorem heis_xinv_ypow_x (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (b : ℕ) :
    x⁻¹ * y ^ b * x = (⁅x, y⁆⁻¹) ^ b * y ^ b := by
  have hconj : x⁻¹ * y ^ b * x = (x⁻¹ * y * x) ^ b := by
    rw [show x⁻¹ * y ^ b * x = x⁻¹ * y ^ b * x⁻¹⁻¹ by rw [inv_inv], ← conj_pow, inv_inv]
  rw [hconj, heis_xinv_y_x hzx, (hzy.inv_left).mul_pow]

theorem heis_ypow_x (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (b : ℕ) :
    y ^ b * x = x * y ^ b * (⁅x, y⁆⁻¹) ^ b := by
  have h := heis_xinv_ypow_x hzx hzy b
  have hc : Commute ((⁅x, y⁆⁻¹) ^ b) (y ^ b) := ((hzy.inv_left).pow_left b).pow_right b
  calc y ^ b * x = x * (x⁻¹ * y ^ b * x) := by group
    _ = x * ((⁅x, y⁆⁻¹) ^ b * y ^ b) := by rw [h]
    _ = x * (y ^ b * (⁅x, y⁆⁻¹) ^ b) := by rw [hc.eq]
    _ = x * y ^ b * (⁅x, y⁆⁻¹) ^ b := by group

theorem heis_ypow_xpow (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (b i : ℕ) :
    y ^ b * x ^ i = x ^ i * y ^ b * (⁅x, y⁆⁻¹) ^ (b * i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hcx : Commute ((⁅x, y⁆⁻¹) ^ (b * i)) x := (hzx.inv_left).pow_left _
    calc y ^ b * x ^ (i + 1) = (y ^ b * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = x ^ i * y ^ b * (⁅x, y⁆⁻¹) ^ (b * i) * x := by rw [ih]
      _ = x ^ i * (y ^ b * x) * (⁅x, y⁆⁻¹) ^ (b * i) := by
          rw [mul_assoc (x ^ i * y ^ b), hcx.eq]; group
      _ = x ^ i * (x * y ^ b * (⁅x, y⁆⁻¹) ^ b) * (⁅x, y⁆⁻¹) ^ (b * i) := by
          rw [heis_ypow_x hzx hzy b]
      _ = x ^ (i + 1) * y ^ b * (⁅x, y⁆⁻¹) ^ (b * (i + 1)) := by
          rw [pow_succ, mul_add, mul_one, pow_add]
          group

@[expose] def heisSet (x y : G) : Set G := {g | ∃ a b c : ℕ, g = x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c}

theorem heisSet_mul (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) {g h : G}
    (hg : g ∈ heisSet x y) (hh : h ∈ heisSet x y) : g * h ∈ heisSet x y := by
  obtain ⟨a, b, c, rfl⟩ := hg
  obtain ⟨i, j, k, rfl⟩ := hh
  refine ⟨a + i, b + j, c + k + b * i, ?_⟩
  have hwx : ∀ n : ℕ, Commute ((⁅x, y⁆⁻¹) ^ n) x := fun n => (hzx.inv_left).pow_left n
  have hwy : ∀ n : ℕ, Commute ((⁅x, y⁆⁻¹) ^ n) y := fun n => (hzy.inv_left).pow_left n
  have h1 : (⁅x, y⁆⁻¹) ^ c * (x ^ i * y ^ j * (⁅x, y⁆⁻¹) ^ k) =
      x ^ i * y ^ j * (⁅x, y⁆⁻¹) ^ (c + k) := by
    rw [pow_add]
    calc (⁅x, y⁆⁻¹) ^ c * (x ^ i * y ^ j * (⁅x, y⁆⁻¹) ^ k)
        = ((⁅x, y⁆⁻¹) ^ c * x ^ i) * y ^ j * (⁅x, y⁆⁻¹) ^ k := by group
      _ = (x ^ i * (⁅x, y⁆⁻¹) ^ c) * y ^ j * (⁅x, y⁆⁻¹) ^ k := by
          rw [((hwx c).pow_right i).eq]
      _ = x ^ i * ((⁅x, y⁆⁻¹) ^ c * y ^ j) * (⁅x, y⁆⁻¹) ^ k := by group
      _ = x ^ i * (y ^ j * (⁅x, y⁆⁻¹) ^ c) * (⁅x, y⁆⁻¹) ^ k := by
          rw [((hwy c).pow_right j).eq]
      _ = x ^ i * y ^ j * ((⁅x, y⁆⁻¹) ^ c * (⁅x, y⁆⁻¹) ^ k) := by group
  calc x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c * (x ^ i * y ^ j * (⁅x, y⁆⁻¹) ^ k)
      = x ^ a * y ^ b * (x ^ i * y ^ j * (⁅x, y⁆⁻¹) ^ (c + k)) := by rw [mul_assoc, h1]
    _ = x ^ a * (y ^ b * x ^ i) * y ^ j * (⁅x, y⁆⁻¹) ^ (c + k) := by group
    _ = x ^ a * (x ^ i * y ^ b * (⁅x, y⁆⁻¹) ^ (b * i)) * y ^ j * (⁅x, y⁆⁻¹) ^ (c + k) := by
        rw [heis_ypow_xpow hzx hzy]
    _ = x ^ (a + i) * y ^ b * ((⁅x, y⁆⁻¹) ^ (b * i) * y ^ j) * (⁅x, y⁆⁻¹) ^ (c + k) := by
        rw [pow_add]; group
    _ = x ^ (a + i) * y ^ b * (y ^ j * (⁅x, y⁆⁻¹) ^ (b * i)) * (⁅x, y⁆⁻¹) ^ (c + k) := by
        rw [((hwy (b * i)).pow_right j).eq]
    _ = x ^ (a + i) * y ^ (b + j) * (⁅x, y⁆⁻¹) ^ (c + k + b * i) := by
        rw [pow_add y, pow_add (⁅x, y⁆⁻¹) (c + k)]
        rw [show (⁅x, y⁆⁻¹) ^ (c + k) * (⁅x, y⁆⁻¹) ^ (b * i) =
          (⁅x, y⁆⁻¹) ^ (b * i) * (⁅x, y⁆⁻¹) ^ (c + k) from (Commute.pow_pow_self _ _ _)]
        group

theorem heis_mem_normal_form [Finite G] (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g ∈ heisSet x y := by
  have hone : (1 : G) ∈ heisSet x y := ⟨0, 0, 0, by simp⟩
  have hpow : ∀ {h : G}, h ∈ heisSet x y → ∀ n : ℕ, h ^ n ∈ heisSet x y := by
    intro h hh n
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact heisSet_mul hzx hzy ih hh
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
  | one => exact hone
  | mul g h _ _ ihg ihh => exact heisSet_mul hzx hzy ihg ihh
  | inv g _ ihg =>
    have := hpow ihg (orderOf g - 1)
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    rw [hinv]
    exact this

theorem heis_comm_pow (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) {p : ℕ}
    (hx : x ^ p = 1) : ⁅x, y⁆ ^ p = 1 := by
  have h := heis_yinv_xpow_y hzx hzy p
  rw [hx, mul_one, inv_mul_cancel, one_mul] at h
  exact h.symm

@[expose] def heisMap (x y : G) (p : ℕ) : Fin p × Fin p × Fin p → G :=
  fun t => x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * (⁅x, y⁆⁻¹) ^ (t.2.2 : ℕ)

theorem heis_conj_y_normal (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (a b c : ℕ) :
    y⁻¹ * (x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c) * y =
      x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c * ⁅x, y⁆ ^ a := by
  have hwy : Commute ((⁅x, y⁆⁻¹) ^ c) y := (hzy.inv_left).pow_left c
  calc y⁻¹ * (x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c) * y
      = (y⁻¹ * x ^ a * y) * y ^ b * (y⁻¹ * (⁅x, y⁆⁻¹) ^ c * y) := by group
    _ = (x ^ a * ⁅x, y⁆ ^ a) * y ^ b * (⁅x, y⁆⁻¹) ^ c := by
        rw [heis_yinv_xpow_y hzx hzy, mul_assoc y⁻¹, hwy.eq]; group
    _ = x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c * ⁅x, y⁆ ^ a := by
        have h1 : ⁅x, y⁆ ^ a * y ^ b = y ^ b * ⁅x, y⁆ ^ a := ((hzy.pow_left a).pow_right b).eq
        have h2 : ⁅x, y⁆ ^ a * (⁅x, y⁆⁻¹) ^ c = (⁅x, y⁆⁻¹) ^ c * ⁅x, y⁆ ^ a :=
          (Commute.pow_pow ((Commute.refl ⁅x, y⁆).inv_right) a c).eq
        calc x ^ a * ⁅x, y⁆ ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c
            = x ^ a * (⁅x, y⁆ ^ a * y ^ b) * (⁅x, y⁆⁻¹) ^ c := by group
          _ = x ^ a * (y ^ b * ⁅x, y⁆ ^ a) * (⁅x, y⁆⁻¹) ^ c := by rw [h1]
          _ = x ^ a * y ^ b * (⁅x, y⁆ ^ a * (⁅x, y⁆⁻¹) ^ c) := by group
          _ = x ^ a * y ^ b * ((⁅x, y⁆⁻¹) ^ c * ⁅x, y⁆ ^ a) := by rw [h2]
          _ = x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c * ⁅x, y⁆ ^ a := by group

theorem heis_conj_x_normal (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (a b c : ℕ) :
    x⁻¹ * (x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c) * x =
      x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c * (⁅x, y⁆⁻¹) ^ b := by
  have hwx : Commute ((⁅x, y⁆⁻¹) ^ c) x := (hzx.inv_left).pow_left c
  have h1 : (⁅x, y⁆⁻¹) ^ b * y ^ b = y ^ b * (⁅x, y⁆⁻¹) ^ b :=
    (((hzy.inv_left).pow_left b).pow_right b).eq
  have h2 : (⁅x, y⁆⁻¹) ^ b * (⁅x, y⁆⁻¹) ^ c = (⁅x, y⁆⁻¹) ^ c * (⁅x, y⁆⁻¹) ^ b :=
    Commute.pow_pow_self _ _ _
  have hxa : x⁻¹ * x ^ a = x ^ a * x⁻¹ := (Commute.self_pow x a).inv_left.eq
  calc x⁻¹ * (x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c) * x
      = (x⁻¹ * x ^ a) * y ^ b * (⁅x, y⁆⁻¹) ^ c * x := by simp only [mul_assoc]
    _ = (x ^ a * x⁻¹) * y ^ b * (⁅x, y⁆⁻¹) ^ c * x := by rw [hxa]
    _ = x ^ a * (x⁻¹ * y ^ b * x) * (x⁻¹ * (⁅x, y⁆⁻¹) ^ c * x) := by group
    _ = x ^ a * ((⁅x, y⁆⁻¹) ^ b * y ^ b) * (⁅x, y⁆⁻¹) ^ c := by
        rw [heis_xinv_ypow_x hzx hzy, mul_assoc x⁻¹, hwx.eq]; group
    _ = x ^ a * (y ^ b * (⁅x, y⁆⁻¹) ^ b) * (⁅x, y⁆⁻¹) ^ c := by rw [h1]
    _ = x ^ a * y ^ b * ((⁅x, y⁆⁻¹) ^ b * (⁅x, y⁆⁻¹) ^ c) := by group
    _ = x ^ a * y ^ b * ((⁅x, y⁆⁻¹) ^ c * (⁅x, y⁆⁻¹) ^ b) := by rw [h2]
    _ = x ^ a * y ^ b * (⁅x, y⁆⁻¹) ^ c * (⁅x, y⁆⁻¹) ^ b := by group

theorem heisMap_injective (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) {p : ℕ}
    (hzp : orderOf ⁅x, y⁆ = p) : Function.Injective (heisMap x y p) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [heisMap] at h
  have hwp : orderOf (⁅x, y⁆⁻¹) = p := by rw [orderOf_inv, hzp]
  have ha : a = a' := by
    have h1 := heis_conj_y_normal hzx hzy a b c
    have h2 := heis_conj_y_normal hzx hzy a' b' c'
    rw [h] at h1
    rw [h1] at h2
    have h3 : ⁅x, y⁆ ^ (a : ℕ) = ⁅x, y⁆ ^ (a' : ℕ) := mul_left_cancel h2
    have := pow_injOn_Iio_orderOf (x := ⁅x, y⁆) (by rw [hzp]; exact a.2)
      (by rw [hzp]; exact a'.2) h3
    exact Fin.ext this
  have hb : b = b' := by
    have h1 := heis_conj_x_normal hzx hzy a b c
    have h2 := heis_conj_x_normal hzx hzy a' b' c'
    rw [h] at h1
    rw [h1] at h2
    have h3 : (⁅x, y⁆⁻¹) ^ (b : ℕ) = (⁅x, y⁆⁻¹) ^ (b' : ℕ) := mul_left_cancel h2
    have := pow_injOn_Iio_orderOf (x := ⁅x, y⁆⁻¹) (by rw [hwp]; exact b.2)
      (by rw [hwp]; exact b'.2) h3
    exact Fin.ext this
  subst ha
  subst hb
  have h3 : (⁅x, y⁆⁻¹) ^ (c : ℕ) = (⁅x, y⁆⁻¹) ^ (c' : ℕ) := mul_left_cancel h
  have hc := pow_injOn_Iio_orderOf (x := ⁅x, y⁆⁻¹) (by rw [hwp]; exact c.2)
    (by rw [hwp]; exact c'.2) h3
  rw [Fin.ext hc]

theorem card_heis [Finite G] (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) {p : ℕ}
    [hp : Fact p.Prime] (hx : x ^ p = 1) (hy : y ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3 := by
  have hzp : orderOf ⁅x, y⁆ = p := orderOf_eq_prime (heis_comm_pow hzx hzy hx) hz1
  have hrange : (Subgroup.closure ({x, y} : Set G) : Set G) = Set.range (heisMap x y p) := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, b, c, rfl⟩ := heis_mem_normal_form hzx hzy hg
      have hp0 : 0 < p := hp.out.pos
      refine ⟨(⟨a % p, Nat.mod_lt _ hp0⟩, ⟨b % p, Nat.mod_lt _ hp0⟩, ⟨c % p, Nat.mod_lt _ hp0⟩),
        ?_⟩
      have hw : (⁅x, y⁆⁻¹) ^ p = 1 := by rw [inv_pow, heis_comm_pow hzx hzy hx, inv_one]
      simp only [heisMap]
      rw [← pow_eq_pow_mod a hx, ← pow_eq_pow_mod b hy, ← pow_eq_pow_mod c hw]
    · rintro ⟨t, rfl⟩
      have hxm : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (Or.inl rfl)
      have hym : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (Or.inr rfl)
      have hzm : ⁅x, y⁆ ∈ Subgroup.closure ({x, y} : Set G) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxm hym)
          (Subgroup.inv_mem _ hxm)) (Subgroup.inv_mem _ hym)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hxm _)
        (Subgroup.pow_mem _ hym _)) (Subgroup.pow_mem _ (Subgroup.inv_mem _ hzm) _)
  rw [← SetLike.coe_sort_coe, hrange, Nat.card_range_of_injective (heisMap_injective hzx hzy hzp)]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
  ring

end Heis


section ExtraIndex

variable {W : Type} [CommGroup W] [Finite W] {p : ℕ} {x y z : MulAut W}

omit [Finite W] in
theorem range_prodE_le_imgT : (prodE x z p).range ≤ imgT z := by
  rintro _ ⟨e, rfl⟩
  rw [prodE_apply]
  exact Subgroup.prod_mem _ fun j _ => (mem_eigE.1 (e j).2).1

omit [Finite W] in
theorem range_prodE_inf_fixV_le :
    (prodE x z p).range ⊓ fixV (Subgroup.zpowers x) ≤ eigE x z 0 := by
  intro v hv
  rw [Subgroup.mem_inf] at hv
  refine mem_eigE.2 ⟨range_prodE_le_imgT hv.1, ?_⟩
  rw [pow_zero, mul_one]
  exact mem_fixV_zpowers.1 hv.2

theorem card_range_prodE_of_cfg [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) :
    Nat.card (prodE x z p).range = Nat.card (eigE x z 0) ^ p := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (prodE_injective h hW hodd)).toEquiv, Nat.card_pi,
    Finset.prod_congr rfl (fun j _ => h.card_eigE_eq (le_of_lt j.2))]
  simp

theorem card_pow_le_index_of_cfg [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) :
    Nat.card (eigE x z 0) ^ (p - 1) ≤ (fixV (Subgroup.zpowers x)).index := by
  set P := (prodE x z p).range with hP
  set C := fixV (Subgroup.zpowers x) with hC
  have h1 : C.relIndex P * Nat.card (C ⊓ P : Subgroup W) = Nat.card P := C.relIndex_mul_card P
  have h2 : C.relIndex P ≤ C.index := by
    have h0 : C.relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite
    have := Subgroup.relIndex_le_of_le_right (le_top : P ≤ ⊤) h0
    rwa [Subgroup.relIndex_top_right] at this
  have h3 : Nat.card (C ⊓ P : Subgroup W) ≤ Nat.card (eigE x z 0) := by
    apply Subgroup.card_le_of_le
    rw [inf_comm]
    exact range_prodE_inf_fixV_le
  have h4 := card_range_prodE_of_cfg h hW hodd
  have hpos : 0 < Nat.card (eigE x z 0) := Nat.card_pos
  have h5 : Nat.card (eigE x z 0) ^ (p - 1) * Nat.card (eigE x z 0) ≤
      C.index * Nat.card (eigE x z 0) := by
    rw [← pow_succ, Nat.sub_add_cancel hodd.pos, ← h4, ← h1]
    exact Nat.mul_le_mul h2 h3
  exact Nat.le_of_mul_le_mul_right h5 hpos

theorem two_pow_le_index_of_cfg [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) :
    2 ^ ((p - 1) * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers x)).index := by
  calc 2 ^ ((p - 1) * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ (p - 1) := by
        rw [mul_comm, pow_mul]
    _ ≤ Nat.card (eigE x z 0) ^ (p - 1) :=
        Nat.pow_le_pow_left (h.two_pow_le_card_eigE hW hodd) _
    _ ≤ _ := card_pow_le_index_of_cfg h hW hodd

omit [Finite W] in
theorem ker_cHom (z : MulAut W) : (cHom z).ker = fixV (Subgroup.zpowers z) := by
  ext v
  rw [MonoidHom.mem_ker, mem_fixV_zpowers]
  exact mul_inv_eq_one

theorem two_pow_le_index_center_of_cfg [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) :
    2 ^ (p * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers z)).index := by
  rw [← ker_cHom, Subgroup.index_ker]
  calc 2 ^ (p * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ p := by
        rw [mul_comm, pow_mul]
    _ ≤ Nat.card (eigE x z 0) ^ p := Nat.pow_le_pow_left (h.two_pow_le_card_eigE hW hodd) _
    _ = Nat.card (prodE x z p).range := (card_range_prodE_of_cfg h hW hodd).symm
    _ ≤ Nat.card (cHom z).range := Subgroup.card_le_of_le range_prodE_le_imgT

end ExtraIndex

section Sylow

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_card {p : ℕ} [hp : Fact p.Prime] {Q : Subgroup G} {k : ℕ}
    (hQ : Nat.card Q = p ^ k) (hk : ¬ p ^ (k + 1) ∣ Nat.card G) {g : G} (hg : g ^ p = 1) :
    ∃ c : G, c * g * c⁻¹ ∈ Q := by
  have hfac : (Nat.card G).factorization p = k := by
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have h1 : p ^ k ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    rw [hp.out.pow_dvd_iff_le_factorization hG0] at h1 hk
    omega
  let P : Sylow p G := Sylow.ofCard Q (by rw [hQ, hfac])
  have hpg : IsPGroup p (Subgroup.zpowers g) := by
    rintro ⟨_, m, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show ((fun n : ℤ => g ^ n) m) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  obtain ⟨R, hR⟩ := hpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G R P
  have hgR : g ∈ (R : Subgroup G) := hR (Subgroup.mem_zpowers g)
  have hmem : MulAut.conj c • g ∈ MulAut.conj c • (R : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul g (MulAut.conj c) (R : Subgroup G) hgR
  rw [← Sylow.coe_subgroup_smul, hc, Sylow.coe_ofCard] at hmem
  exact ⟨c, by simpa [MulAut.smul_def, MulAut.conj_apply] using hmem⟩

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite G] [Finite W] in
theorem extraCfg_map {p : ℕ} (σ : G →* MulAut W) (hσ : Function.Injective σ) {x y z : G}
    (hx : x ^ p = 1) (hz : z ^ p = 1) (hzx : x * z = z * x) (hzy : y * z = z * y)
    (hyx : y⁻¹ * x * y = x * z) (hz1 : z ≠ 1) : ExtraCfg p (σ x) (σ y) (σ z) where
  xp := by rw [← map_pow, hx, map_one]
  zp := by rw [← map_pow, hz, map_one]
  zx := by rw [← map_mul, hzx, map_mul]
  zy := by rw [← map_mul, hzy, map_mul]
  yx := by rw [← map_inv, ← map_mul, ← map_mul, hyx, map_mul]
  z1 := fun h => hz1 (hσ (h.trans (map_one σ).symm))

theorem two_pow_le_index_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hG : ¬ p ^ 4 ∣ Nat.card G) (hW : ∀ w : W, w * w = 1)
    (σ : G →* MulAut W) (hσ : Function.Injective σ) {g : G} (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    2 ^ ((p - 1) * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers (σ g))).index := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨c, hc⟩ := exists_conj_mem_of_card (card_heis hzx hzy hx hy hz1) hG hg
  set q := c * g * c⁻¹ with hq
  have hq1 : q ≠ 1 := by
    intro h
    apply hg1
    have : g = c⁻¹ * q * c := by rw [hq]; group
    rw [this, h]
    group
  have hqp : q ^ p = 1 := by
    rw [hq, conj_pow, hg]
    group
  have hidx : (fixV (Subgroup.zpowers (σ g))).index =
      (fixV (Subgroup.zpowers (σ q))).index := by
    rw [hq, map_mul, map_mul, map_inv, index_fixV_conj]
  rw [hidx]
  obtain ⟨a, b, e, hqe⟩ := heis_mem_normal_form hzx hzy hc
  set z := ⁅x, y⁆ with hz
  have hzp1 : z ^ p = 1 := heis_comm_pow hzx hzy hx
  have hzp : orderOf z = p := orderOf_eq_prime hzp1 hz1
  have hwp : orderOf z⁻¹ = p := by rw [orderOf_inv, hzp]
  have hzq : Commute z q := by
    rw [hqe]
    exact ((hzx.pow_right a).mul_right (hzy.pow_right b)).mul_right
      ((Commute.refl z).inv_right.pow_right e)
  by_cases ha : p ∣ a
  · by_cases hb : p ∣ b
    ·
      have hxa : x ^ a = 1 := by
        obtain ⟨k, rfl⟩ := ha
        rw [pow_mul, hx, one_pow]
      have hyb : y ^ b = 1 := by
        obtain ⟨k, rfl⟩ := hb
        rw [pow_mul, hy, one_pow]
      have hqw : q = z⁻¹ ^ e := by rw [hqe, hxa, hyb, one_mul, one_mul]
      have he : ¬ p ∣ e := by
        rintro ⟨k, rfl⟩
        apply hq1
        rw [hqw, pow_mul, ← hwp, pow_orderOf_eq_one, one_pow]
      have hwp1 : z⁻¹ ^ p = 1 := by rw [inv_pow, hzp1, inv_one]
      obtain ⟨n, hn⟩ := exists_pow_pow_eq_self_W hwp1 he
      have hle : fixV (Subgroup.zpowers (σ q)) ≤ fixV (Subgroup.zpowers (σ z)) := by
        apply fixV_anti
        rw [Subgroup.zpowers_le]
        have h1 : σ z = ((σ q) ^ n)⁻¹ := by
          rw [← map_pow, ← map_inv, hqw, hn, inv_inv]
        rw [h1]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n)
      have hcfg := extraCfg_map σ hσ hx hzp1 hzx.eq.symm hzy.eq.symm (heis_yinv_x_y hzx hzy) hz1
      calc 2 ^ ((p - 1) * orderOf (2 : ZMod p)) ≤ 2 ^ (p * orderOf (2 : ZMod p)) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (Nat.sub_le p 1))
        _ ≤ (fixV (Subgroup.zpowers (σ z))).index := two_pow_le_index_center_of_cfg hcfg hW hodd
        _ ≤ (fixV (Subgroup.zpowers (σ q))).index := Subgroup.index_antitone hle
    ·
      have hcfg := extraCfg_map σ hσ (y := x) (z := z⁻¹ ^ b) hqp
        (by rw [← pow_mul, mul_comm, pow_mul, inv_pow, hzp1, inv_one, one_pow])
        ((hzq.inv_left.pow_left b).eq.symm) ((hzx.inv_left.pow_left b).eq.symm)
        (by rw [hqe]; exact heis_conj_x_normal hzx hzy a b e)
        (fun h => hb (hwp ▸ orderOf_dvd_of_pow_eq_one h))
      exact two_pow_le_index_of_cfg hcfg hW hodd
  ·
    have hcfg := extraCfg_map σ hσ (y := y) (z := z ^ a) hqp
      (by rw [← pow_mul, mul_comm, pow_mul, hzp1, one_pow])
      ((hzq.pow_left a).eq.symm) ((hzy.pow_left a).eq.symm)
      (by rw [hqe]; exact heis_conj_y_normal hzx hzy a b e)
      (fun h => ha (hzp ▸ orderOf_dvd_of_pow_eq_one h))
    exact two_pow_le_index_of_cfg hcfg hW hodd

end Sylow

end CFSG.Quasithin.B45Exc
