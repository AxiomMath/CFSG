module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

private theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

private theorem conjugate_conjugate' (H : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate H a) b = CFSG.conjugate H (a * b) := by
  ext x
  rw [mem_conjugate_iff', mem_conjugate_iff', mem_conjugate_iff',
    show a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ by group]

theorem commute_of_conjugates_meet {V : Subgroup G}
    (hV : ∀ x : G, V ⊓ CFSG.conjugate V x ≠ ⊥ → ⁅V, CFSG.conjugate V x⁆ = ⊥) {a b z : G}
    (hz1 : z ≠ 1) (hza : z ∈ CFSG.conjugate V a) (hzb : z ∈ CFSG.conjugate V b) {y y' : G}
    (hy : y ∈ CFSG.conjugate V a) (hy' : y' ∈ CFSG.conjugate V b) : y * y' = y' * y := by
  rw [mem_conjugate_iff'] at hza hzb hy hy'
  have hx : ∀ t, b * t * b⁻¹ ∈ V → a * t * a⁻¹ ∈ CFSG.conjugate V (b * a⁻¹) := fun t ht => by
    rw [mem_conjugate_iff', show b * a⁻¹ * (a * t * a⁻¹) * (b * a⁻¹)⁻¹ = b * t * b⁻¹ by group]
    exact ht
  have hne : V ⊓ CFSG.conjugate V (b * a⁻¹) ≠ ⊥ := by
    refine (ne_bot_iff_exists_ne_one.mpr ⟨⟨a * z * a⁻¹, hza, hx z hzb⟩, fun h => hz1 ?_⟩)
    have h' : a * z * a⁻¹ = 1 := congrArg Subtype.val h
    calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
      _ = 1 := by rw [h']; group
  have hc := hV _ hne
  rw [commutator_eq_bot_iff_le_centralizer] at hc
  have h := mem_centralizer_iff.mp (hc hy) _ (hx y' hy')
  calc y * y' = a⁻¹ * ((a * y * a⁻¹) * (a * y' * a⁻¹)) * a := by group
    _ = a⁻¹ * ((a * y' * a⁻¹) * (a * y * a⁻¹)) * a := by rw [← h]
    _ = y' * y := by group

theorem commutator_le_of_forall_mem_mul {K N H : Subgroup G} (hKN : K ≤ normalizer (N : Set G))
    (hHN : H ≤ normalizer (N : Set G)) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hK : ∀ k ∈ K, ∃ n ∈ N, ∃ h ∈ H, n * h = k) : ⁅K, K⁆ ≤ N := by
  rw [commutator_le]
  intro i hi j hj
  obtain ⟨n, hn, h, hh, rfl⟩ := hK i hi
  obtain ⟨n', hn', h', hh', rfl⟩ := hK j hj
  have e : ⁅n * h, n' * h'⁆ = n * (h * n' * h⁻¹) * (h * h' * h⁻¹ * h'⁻¹) * n'⁻¹ *
      ((n' * h') * n⁻¹ * (n' * h')⁻¹) := by
    rw [commutatorElement_def]
    group
  have h1 : h * h' * h⁻¹ * h'⁻¹ = 1 := by
    rw [hH h hh h' hh']
    group
  rw [e, h1, mul_one]
  refine N.mul_mem (N.mul_mem (N.mul_mem hn ((mem_normalizer_iff.mp (hHN hh) n').mp hn'))
    (N.inv_mem hn')) ((mem_normalizer_iff.mp (hKN hj) _).mp (N.inv_mem hn))

theorem intersecting_conjugates_two_hulls_class_two {V : Subgroup G}
    (hV : ∀ x : G, V ⊓ CFSG.conjugate V x ≠ ⊥ → ⁅V, CFSG.conjugate V x⁆ = ⊥) (g : G)
    (hVW : V ⊓ centralizer (CFSG.conjugate V g : Set G) ≠ ⊥)
    (hWV : CFSG.conjugate V g ⊓ centralizer (V : Set G) ≠ ⊥) :
    let W := CFSG.conjugate V g
    let I := V ⊔ W
    let X := ⨆ w : W, CFSG.conjugate V w
    let Y := ⨆ v : V, CFSG.conjugate W v
    IsMulCommutative X ∧ IsMulCommutative Y ∧ X ≤ I ∧ Y ≤ I ∧
      (X.subgroupOf I).Normal ∧ (Y.subgroupOf I).Normal ∧
      (I : Set G) = (X : Set G) * (Y : Set G) ∧
      ⁅I, I⁆ ≤ X ⊓ Y ∧ X ⊓ Y ≤ (center I).map I.subtype := by
  intro W I X Y
  have hconj1 : ∀ H : Subgroup G, CFSG.conjugate H 1 = H := fun H => by
    ext x
    rw [mem_conjugate_iff', one_mul, inv_one, mul_one]
  have hcomm : ∀ {H : Subgroup G}, IsMulCommutative H → ∀ a ∈ H, ∀ b ∈ H, a * b = b * a :=
    fun hH a ha b hb => congrArg Subtype.val (hH.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWconj : ∀ v : G, CFSG.conjugate W v = CFSG.conjugate V (g * v) :=
    fun v => conjugate_conjugate' V g v
  obtain ⟨⟨a₀, ha₀V, ha₀C⟩, ha₀1'⟩ := ne_bot_iff_exists_ne_one.mp hVW
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀1' (Subtype.ext h)
  obtain ⟨⟨c₀, hc₀W, hc₀C⟩, hc₀1'⟩ := ne_bot_iff_exists_ne_one.mp hWV
  have hc₀1 : c₀ ≠ 1 := fun h => hc₀1' (Subtype.ext h)
  have ha₀ : ∀ w ∈ W, a₀ ∈ CFSG.conjugate V w := fun w hw => by
    rw [mem_conjugate_iff', mem_centralizer_iff.mp ha₀C w hw, mul_inv_cancel_right]
    exact ha₀V
  have hc₀ : ∀ v ∈ V, c₀ ∈ CFSG.conjugate W v := fun v hv => by
    rw [mem_conjugate_iff', mem_centralizer_iff.mp hc₀C v hv, mul_inv_cancel_right]
    exact hc₀W
  have hXcl : X = closure (⋃ w : W, (CFSG.conjugate V w : Set G)) := iSup_eq_closure _
  have hYcl : Y = closure (⋃ v : V, (CFSG.conjugate W v : Set G)) := iSup_eq_closure _
  have hXab : IsMulCommutative X := by
    rw [hXcl]
    refine isMulCommutative_closure fun s hs t ht _ => ?_
    obtain ⟨_, ⟨w, rfl⟩, hsw⟩ := hs
    obtain ⟨_, ⟨w', rfl⟩, htw⟩ := ht
    exact commute_of_conjugates_meet hV ha₀1 (ha₀ w w.2) (ha₀ w' w'.2) hsw htw
  have hYab : IsMulCommutative Y := by
    rw [hYcl]
    refine isMulCommutative_closure fun s hs t ht _ => ?_
    obtain ⟨_, ⟨v, rfl⟩, hsv⟩ := hs
    obtain ⟨_, ⟨v', rfl⟩, htv⟩ := ht
    have h1 := hc₀ v v.2
    have h2 := hc₀ v' v'.2
    rw [SetLike.mem_coe] at hsv htv
    rw [hWconj] at h1 h2 hsv htv
    exact commute_of_conjugates_meet hV hc₀1 h1 h2 hsv htv
  have hVI : V ≤ I := le_sup_left
  have hWI : W ≤ I := le_sup_right
  have hVX : V ≤ X := by
    rw [← hconj1 V]
    exact le_iSup (fun w : W => CFSG.conjugate V w) ⟨1, W.one_mem⟩
  have hWY : W ≤ Y := by
    rw [← hconj1 W]
    exact le_iSup (fun v : V => CFSG.conjugate W v) ⟨1, V.one_mem⟩
  have hconjI : ∀ {H : Subgroup G}, H ≤ I → ∀ t ∈ I, CFSG.conjugate H t ≤ I := by
    intro H hH t ht x hx
    rw [mem_conjugate_iff'] at hx
    have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [this]
    exact I.mul_mem (I.mul_mem (I.inv_mem ht) (hH hx)) ht
  have hXI : X ≤ I := iSup_le fun w => hconjI hVI w (hWI w.2)
  have hYI : Y ≤ I := iSup_le fun v => hconjI hWI v (hVI v.2)
  have hWNX : W ≤ normalizer (X : Set G) := by
    rw [hXcl, le_normalizer_closure_iff]
    rintro h hh s ⟨_, ⟨w, rfl⟩, hsw⟩
    refine subset_closure (Set.mem_iUnion.mpr ⟨⟨w * h⁻¹, W.mul_mem w.2 (W.inv_mem hh)⟩, ?_⟩)
    rw [SetLike.mem_coe, mem_conjugate_iff'] at hsw ⊢
    rw [show w * h⁻¹ * (h * s * h⁻¹) * (w * h⁻¹)⁻¹ = w * s * (w : G)⁻¹ by group]
    exact hsw
  have hVNY : V ≤ normalizer (Y : Set G) := by
    rw [hYcl, le_normalizer_closure_iff]
    rintro h hh s ⟨_, ⟨v, rfl⟩, hsv⟩
    refine subset_closure (Set.mem_iUnion.mpr ⟨⟨v * h⁻¹, V.mul_mem v.2 (V.inv_mem hh)⟩, ?_⟩)
    rw [SetLike.mem_coe, mem_conjugate_iff'] at hsv ⊢
    rw [show v * h⁻¹ * (h * s * h⁻¹) * (v * h⁻¹)⁻¹ = v * s * (v : G)⁻¹ by group]
    exact hsv
  have hINX : I ≤ normalizer (X : Set G) := sup_le (hVX.trans le_normalizer) hWNX
  have hINY : I ≤ normalizer (Y : Set G) := sup_le hVNY (hWY.trans le_normalizer)
  have hXY : X ⊔ Y = I :=
    le_antisymm (sup_le hXI hYI) (sup_le (hVX.trans le_sup_left) (hWY.trans le_sup_right))
  have hIXY : (I : Set G) = (X : Set G) * (Y : Set G) := by
    rw [← hXY]
    exact coe_mul_of_right_le_normalizer_left X Y (hYI.trans hINX)
  have hIYX : (I : Set G) = (Y : Set G) * (X : Set G) := by
    rw [← hXY, sup_comm]
    exact coe_mul_of_right_le_normalizer_left Y X (hXI.trans hINY)
  have hdecXY : ∀ k ∈ I, ∃ x ∈ X, ∃ y ∈ Y, x * y = k := fun k hk => by
    have hk' : k ∈ (I : Set G) := hk
    rw [hIXY] at hk'
    obtain ⟨x, hx, y, hy, rfl⟩ := hk'
    exact ⟨x, hx, y, hy, rfl⟩
  have hdecYX : ∀ k ∈ I, ∃ y ∈ Y, ∃ x ∈ X, y * x = k := fun k hk => by
    have hk' : k ∈ (I : Set G) := hk
    rw [hIYX] at hk'
    obtain ⟨y, hy, x, hx, rfl⟩ := hk'
    exact ⟨y, hy, x, hx, rfl⟩
  refine ⟨hXab, hYab, hXI, hYI, (normal_subgroupOf_iff_le_normalizer hXI).mpr hINX,
    (normal_subgroupOf_iff_le_normalizer hYI).mpr hINY, hIXY,
    le_inf (commutator_le_of_forall_mem_mul hINX (hYI.trans hINX) (hcomm hYab) hdecXY)
      (commutator_le_of_forall_mem_mul hINY (hXI.trans hINY) (hcomm hXab) hdecYX), ?_⟩
  intro z ⟨hzX, hzY⟩
  refine mem_map.mpr ⟨⟨z, hXI hzX⟩, ?_, rfl⟩
  rw [mem_center_iff]
  rintro ⟨k, hk⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hdecXY k hk
  apply Subtype.ext
  change x * y * z = z * (x * y)
  rw [mul_assoc, ← hcomm hYab z hzY y hy, ← mul_assoc, ← hcomm hXab z hzX x hx, mul_assoc]

end CFSG.Quasithin.SteinbergBM
