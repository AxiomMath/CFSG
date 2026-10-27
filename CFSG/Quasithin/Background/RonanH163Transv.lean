module

public import CFSG.Quasithin.Background.RonanH163Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem fullTr_T1 : ∀ u < 32, ∀ x ∈ b9, actC10 (nq2Arr u) x ^^^ x ∈ combos b4 := by
  decide +kernel

theorem fullTr_T2 : ∀ u < 32, actC10 (nq2Arr u) 128 ^^^ 128 ∈ combos b9 := by
  decide +kernel

theorem fullTr_T3 : ∀ m < 2 ^ 10, m ∉ combos b9 → 128 ^^^ m ∈ combos b9 := by
  decide +kernel

theorem fullTr_T4 :
    ∀ m ∈ combos b9, ∃ u < 32, (actC10 (nq2Arr u) 128 ^^^ 128) ^^^ m ∈ combos b4 := by
  decide +kernel

theorem fullTr_T5 : ∀ u < 32, u ≠ 0 → ∃ m < 2 ^ 10, actC10 (nq2Arr u) m ^^^ m ∉ combos b4 := by
  decide +kernel

theorem fullTr_b9 : ∀ a ∈ b9, a < 2 ^ 10 := by decide +kernel

theorem fullTr_b4 : ∀ a ∈ b4, a < 2 ^ 10 := by decide +kernel

theorem toW10_inv (k : ℕ) : (toW 10 k)⁻¹ = toW 10 k := by
  have h : toW 10 k * toW 10 k = 1 :=
    (toW_xor 10 k k).symm.trans (by rw [Nat.xor_self]; exact toW_zero 10)
  exact inv_eq_of_mul_eq_one_right h

theorem mem_U4_of_mask {k : ℕ} (hk : k ∈ combos b4) : toW 10 k ∈ U4 :=
  (toW_mem_U4_iff (combos_lt fullTr_b4 k hk)).2 hk

theorem mem_U9_of_mask {k : ℕ} (hk : k ∈ combos b9) : toW 10 k ∈ U9 :=
  (toW_mem_U9_iff (combos_lt fullTr_b9 k hk)).2 hk

theorem R_mul_inv (u : Fin 32) (k : ℕ) :
    R (nq2Elt u) (toW 10 k) * (toW 10 k)⁻¹ = toW 10 (actC10 (nq2Arr u) k ^^^ k) := by
  rw [R_nq2, toW10_inv, toW_xor]

theorem R_mul_inv_mul_inv (u : Fin 32) (k m : ℕ) :
    R (nq2Elt u) (toW 10 k) * (toW 10 k)⁻¹ * (toW 10 m)⁻¹ =
      toW 10 ((actC10 (nq2Arr u) k ^^^ k) ^^^ m) := by
  rw [R_mul_inv, toW10_inv, ← toW_xor]

theorem fullTr_diff (u : Fin 32) {m : ℕ} (hm : m ∈ combos b9) :
    actC10 (nq2Arr u) m ^^^ m ∈ combos b4 := by
  refine mem_of_combos (fun x => actC10 (nq2Arr u) x ^^^ x ∈ combos b4) ?_ ?_ b9 ?_ m hm
  · show actC10 (nq2Arr u) 0 ^^^ 0 ∈ combos b4
    rw [(xorLin_actC10 (nq2Arr u)).map_zero, Nat.xor_zero]
    exact zero_mem_combos b4
  · intro a b ha hb
    show actC10 (nq2Arr u) (a ^^^ b) ^^^ (a ^^^ b) ∈ combos b4
    have e : actC10 (nq2Arr u) (a ^^^ b) ^^^ (a ^^^ b) =
        (actC10 (nq2Arr u) a ^^^ a) ^^^ (actC10 (nq2Arr u) b ^^^ b) := by
      rw [xorLin_actC10 (nq2Arr u) a b]
      ac_rfl
    rw [e]
    exact xor_mem_combos b4 ha hb
  · intro x hx
    exact fullTr_T1 u u.2 x hx

theorem fullTr_mem_U4 (u : Fin 32) {x : Wn 10} (hx : x ∈ U9) :
    R (nq2Elt u) x * x⁻¹ ∈ U4 := by
  obtain ⟨k, hk, rfl⟩ := toW_surj 10 x
  rw [R_mul_inv]
  exact mem_U4_of_mask (fullTr_diff u ((toW_mem_U9_iff hk).1 hx))

theorem fullTr_second (u : Fin 32) {m : ℕ}
    (hm : (actC10 (nq2Arr u) 128 ^^^ 128) ^^^ m ∈ combos b4)
    {x : Wn 10} (hx : x ∉ U9) :
    R (nq2Elt u) x * x⁻¹ * (toW 10 m)⁻¹ ∈ U4 := by
  obtain ⟨k, hk, rfl⟩ := toW_surj 10 x
  have hkn : k ∉ combos b9 := fun h => hx ((toW_mem_U9_iff hk).2 h)
  obtain ⟨v, hv, rfl⟩ : ∃ v, v ∈ combos b9 ∧ k = 128 ^^^ v :=
    ⟨128 ^^^ k, fullTr_T3 k hk hkn, by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]⟩
  rw [R_mul_inv_mul_inv]
  have e : (actC10 (nq2Arr u) (128 ^^^ v) ^^^ (128 ^^^ v)) ^^^ m =
      ((actC10 (nq2Arr u) 128 ^^^ 128) ^^^ m) ^^^ (actC10 (nq2Arr u) v ^^^ v) := by
    rw [xorLin_actC10 (nq2Arr u) 128 v]
    ac_rfl
  rw [e]
  exact mem_U4_of_mask (xor_mem_combos b4 hm (fullTr_diff u hv))

theorem fullTr_transv (u : Fin 32) {m : ℕ}
    (hm : (actC10 (nq2Arr u) 128 ^^^ 128) ^^^ m ∈ combos b4) :
    IsTranspAxis (R (nq2Elt u)) U4 U9 (toW 10 m) :=
  ⟨fun _ hx => fullTr_mem_U4 u hx, fun _ hx => fullTr_second u hm hx⟩

theorem mem_rImg_NQ2 {g : MulAut (Wn 10)} : g ∈ rImg R NQ2 ↔ ∃ u : Fin 32, R (nq2Elt u) = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨u, hu⟩ := mem_NQ2_iff.1 (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨u, congrArg (⇑R) (Subtype.ext hu).symm⟩
  · rintro ⟨u, rfl⟩
    exact Subgroup.mem_map.2 ⟨nq2Elt u, Subgroup.mem_subgroupOf.2 (mem_NQ2_iff.2 ⟨u, rfl⟩), rfl⟩

theorem fullTr_conj {V : Type*} [CommGroup V] {g h : MulAut V} {U W : Subgroup V} {c : V}
    (hU : ∀ u ∈ U, h u ∈ U) (hW : ∀ w ∈ W, h w ∈ W) (hW' : ∀ w ∈ W, h⁻¹ w ∈ W)
    (hg : IsTranspAxis g U W c) : IsTranspAxis (h * g * h⁻¹) U W (h c) := by
  obtain ⟨h1, h2⟩ := hg
  have e1 : ∀ y : V, (h * g * h⁻¹) (h y) = h (g y) := fun y => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, x = h y := ⟨h⁻¹ x, by rw [MulAut.apply_inv_self]⟩
    have hy : y ∈ W := by
      have := hW' _ hx
      rwa [MulAut.inv_apply_self] at this
    have e : (h * g * h⁻¹) (h y) * (h y)⁻¹ = h (g y * y⁻¹) := by
      rw [e1, map_mul, map_inv]
    rw [e]
    exact hU _ (h1 y hy)
  · obtain ⟨y, rfl⟩ : ∃ y, x = h y := ⟨h⁻¹ x, by rw [MulAut.apply_inv_self]⟩
    have hy : y ∉ W := fun hy => hx (hW _ hy)
    have e : (h * g * h⁻¹) (h y) * (h y)⁻¹ * (h c)⁻¹ = h (g y * y⁻¹ * c⁻¹) := by
      rw [e1, map_mul, map_mul, map_inv, map_inv]
    rw [e]
    exact hU _ (h2 y hy)

theorem fullTransp_std :
    FullTranspAxis (rImg R (MY mog22plus Qstd)) (rImg R (KY mog22plus Qstd))
      (fixV (rImg R (KY mog22plus Qstd))) U9 := by
  rw [KY_Q_L2, fixV_NQ2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨u, rfl⟩ := mem_rImg_NQ2.1 hg
    have hc : actC10 (nq2Arr u) 128 ^^^ 128 ∈ combos b9 := fullTr_T2 u u.2
    have hc0 : (actC10 (nq2Arr u) 128 ^^^ 128) ^^^ (actC10 (nq2Arr u) 128 ^^^ 128) ∈
        combos b4 := by
      rw [Nat.xor_self]
      exact zero_mem_combos b4
    exact ⟨toW 10 (actC10 (nq2Arr u) 128 ^^^ 128), mem_U9_of_mask hc, fullTr_transv u hc0⟩
  · intro c hc
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 c
    obtain ⟨u, hu, hcu⟩ := fullTr_T4 m ((toW_mem_U9_iff hm).1 hc)
    exact ⟨R (nq2Elt ⟨u, hu⟩), mem_rImg_NQ2.2 ⟨⟨u, hu⟩, rfl⟩, fullTr_transv ⟨u, hu⟩ hcu⟩
  · intro g hg hall
    obtain ⟨u, rfl⟩ := mem_rImg_NQ2.1 hg
    by_cases hu : (u : ℕ) = 0
    · have hu0 : u = 0 := Fin.ext hu
      subst hu0
      have h1 : nq2Elt 0 = 1 := Subtype.ext nq2Perm_zero
      rw [h1]
      exact map_one R
    · exfalso
      obtain ⟨m, hm, hmn⟩ := fullTr_T5 (u : ℕ) u.2 hu
      apply hmn
      have h' : toW 10 (actC10 (nq2Arr u) m ^^^ m) ∈ U4 := by
        rw [← R_mul_inv u m]
        exact hall (toW 10 m)
      exact (toW_mem_U4_iff (Nat.xor_lt_two_pow (actC10_lt (nq2Arr u) m) hm)).1 h'
  · intro h hh g _ c hc
    exact fullTr_conj (fun x hx => inv_U4 h hh x hx)
      (fun x hx => inv_U9 h hh x hx) (fun x hx => inv_U9 h⁻¹ (Subgroup.inv_mem _ hh) x hx) hc

end CFSG.Quasithin.RonanH163
