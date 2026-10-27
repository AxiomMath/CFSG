module

public import CFSG.Quasithin.Background.RonanH164Gen
public import CFSG.Quasithin.Background.RonanH164Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem ftcw_c5_lt : ∀ a ∈ c5, a < 2 ^ 10 := by decide +kernel

theorem ftcw_basis_mem : ∀ a ∈ c5, a ∈ combos c5 := by decide +kernel

theorem ftcw_c1 : ∀ m ∈ combos c1, m = 0 ∨ m = 1 := by decide +kernel

theorem ftcw_F1 : ∀ t : Fin 16, ∀ x ∈ c5, actC10 (koArr t) x ^^^ x ∈ combos c1 := by
  decide +kernel

theorem ftcw_fix_one : ∀ t : Fin 16, actC10 (koArr t) 1 = 1 := by decide +kernel

theorem ftcw_faithful : ∀ t : Fin 16, (∀ m ∈ combos c5, actC10 (koArr t) m = m) → t = 0 := by
  decide +kernel

theorem ftcw_pattern : ∀ e0 : Fin 2, ∀ e1 : Fin 2, ∀ e2 : Fin 2, ∀ e3 : Fin 2,
    ∃ t : Fin 16, actC10 (koArr t) 512 = 512 ^^^ (e0 : ℕ) ∧
      actC10 (koArr t) 256 = 256 ^^^ (e1 : ℕ) ∧
      actC10 (koArr t) 10 = 10 ^^^ (e2 : ℕ) ∧ actC10 (koArr t) 6 = 6 ^^^ (e3 : ℕ) := by
  decide +kernel

theorem ftcw_koPerm_zero : koPerm 0 = 1 := by
  have h : ∀ i : Fin 24, koPerm 0 i = i := by decide +kernel
  exact Equiv.ext fun i => h i

theorem ftcw_koElt_zero : koElt 0 = 1 := by
  apply Subtype.ext
  exact ftcw_koPerm_zero

theorem ftcw_xor4 (A B x y : ℕ) : (A ^^^ B) ^^^ (x ^^^ y) = (A ^^^ x) ^^^ (B ^^^ y) := by
  rw [Nat.xor_assoc A B (x ^^^ y), ← Nat.xor_assoc B x y, Nat.xor_comm B x,
    Nat.xor_assoc x B y, ← Nat.xor_assoc A x (B ^^^ y)]

theorem ftcw_xorLin_sub (a : Array ℕ) (x y : ℕ) :
    actC10 a (x ^^^ y) ^^^ (x ^^^ y) = (actC10 a x ^^^ x) ^^^ (actC10 a y ^^^ y) := by
  rw [xorLin_actC10 a x y]
  exact ftcw_xor4 _ _ _ _

theorem ftcw_F1_all (a : Array ℕ) (ha : ∀ x ∈ c5, actC10 a x ^^^ x ∈ combos c1) :
    ∀ m ∈ combos c5, actC10 a m ^^^ m ∈ combos c1 := by
  refine mem_of_combos (fun m => actC10 a m ^^^ m ∈ combos c1) ?_ ?_ c5 ha
  · show actC10 a 0 ^^^ 0 ∈ combos c1
    rw [XorLin.map_zero (xorLin_actC10 a), Nat.xor_self]
    exact zero_mem_combos c1
  · intro x y hx hy
    show actC10 a (x ^^^ y) ^^^ (x ^^^ y) ∈ combos c1
    rw [ftcw_xorLin_sub a x y]
    exact xor_mem_combos c1 hx hy

theorem ftcw_inv_self (m : ℕ) : (toW 10 m)⁻¹ = toW 10 m :=
  inv_eq_of_mul_eq_one_right ((toW_xor 10 m m).symm.trans (by rw [Nat.xor_self]; exact toW_zero 10))

theorem ftcw_mem_X {g : MulAut W10} (hg : g ∈ rImg R fixO) : ∃ t : Fin 16, g = R (koElt t) := by
  obtain ⟨k, hk, rfl⟩ :=
    Subgroup.mem_map.1 (show g ∈ Subgroup.map R (fixO.subgroupOf mog22plus) from hg)
  obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hk)
  exact ⟨t, congrArg R (Subtype.ext ht)⟩

theorem ftcw_R_mem_X (t : Fin 16) : R (koElt t) ∈ rImg R fixO :=
  Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 ((mem_fixO_iff _).2 ⟨t, rfl⟩))

theorem ftcw_clause1 : ∀ g : MulAut W10, g ∈ rImg R fixO → ∀ x : W10, x ∈ V5 →
    g x * x⁻¹ ∈ V1 := by
  intro g hg x hx
  obtain ⟨t, rfl⟩ := ftcw_mem_X hg
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show x ∈ maskSub 10 c5 from hx)
  have hF : toW 10 (actC10 (koArr t) m ^^^ m) ∈ maskSub 10 c1 :=
    toW_mem_maskSub (n := 10) (l := c1) (ftcw_F1_all (koArr t) (ftcw_F1 t) m hm)
  have e2 : R (koElt t) (toW 10 m) * (toW 10 m)⁻¹ = toW 10 (actC10 (koArr t) m ^^^ m) := by
    rw [R_ko, ftcw_inv_self]
    exact (toW_xor 10 (actC10 (koArr t) m) m).symm
  exact (congrArg (fun y : W10 => y ∈ maskSub 10 c1) e2).mpr hF

theorem ftcw_clause3 : ∀ g : MulAut W10, g ∈ rImg R fixO →
    (∀ x : W10, x ∈ V5 → g x = x) → g = 1 := by
  intro g hg hfix
  obtain ⟨t, rfl⟩ := ftcw_mem_X hg
  have hm : ∀ m ∈ combos c5, actC10 (koArr t) m = m := by
    intro m hm
    have h : R (koElt t) (toW 10 m) = toW 10 m :=
      hfix (toW 10 m) (toW_mem_maskSub (n := 10) (l := c5) hm)
    exact toW_inj (actC10_lt _ m) (combos_lt (n := 10) ftcw_c5_lt m hm)
      ((R_ko t m).symm.trans h)
  have ht : t = 0 := ftcw_faithful t hm
  subst ht
  exact (congrArg R ftcw_koElt_zero).trans (map_one R)

theorem ftcw_clause4 :
    ∀ h : MulAut W10, h ∈ rImg R (MY mog22plus Hstd) →
      ∀ g : MulAut W10, g ∈ rImg R fixO → h * g * h⁻¹ ∈ rImg R fixO := by
  intro h hh g hg
  obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.1
    (show h ∈ Subgroup.map R ((MY mog22plus Hstd).subgroupOf mog22plus) from hh)
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1
    (show g ∈ Subgroup.map R (fixO.subgroupOf mog22plus) from hg)
  have hN : (fixO.subgroupOf (MY mog22plus Hstd)).Normal := by
    rw [← ker_piH2]
    infer_instance
  have hkM : (⟨(k : P24), fixO_le_MY_H_plus (Subgroup.mem_subgroupOf.1 hk)⟩ :
      ↥(MY mog22plus Hstd)) ∈ fixO.subgroupOf (MY mog22plus Hstd) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hk)
  have hy := hN.conj_mem _ hkM ⟨(h₀ : P24), Subgroup.mem_subgroupOf.1 hh₀⟩
  have hmem : h₀ * k * h₀⁻¹ ∈ fixO.subgroupOf mog22plus :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hy)
  have e : R h₀ * R k * (R h₀)⁻¹ = R (h₀ * k * h₀⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  exact (congrArg (fun y : MulAut W10 => y ∈ rImg R fixO) e).mpr
    (Subgroup.mem_map_of_mem R hmem)

theorem ftcw_form (τ : MulAut ↥V5)
    (hτ : ∀ x : ↥V5, ((τ x : ↥V5) : W10) * ((x : ↥V5) : W10)⁻¹ ∈ V1) (x : ↥V5) :
    ((τ x : ↥V5) : W10) = (x : W10) ∨ ((τ x : ↥V5) : W10) = toW 10 1 * (x : W10) := by
  obtain ⟨m, hm, hmx⟩ := mem_maskSub.1
    (show ((τ x : ↥V5) : W10) * ((x : ↥V5) : W10)⁻¹ ∈ maskSub 10 c1 from hτ x)
  rcases ftcw_c1 m hm with rfl | rfl
  · rw [toW_zero] at hmx
    exact Or.inl (mul_inv_eq_one.1 hmx.symm)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.1 hmx.symm)

theorem ftcw_bform (τ : MulAut ↥V5)
    (hτ : ∀ x : ↥V5, ((τ x : ↥V5) : W10) * ((x : ↥V5) : W10)⁻¹ ∈ V1) {b : ℕ}
    (hb : b ∈ combos c5) : ∃ e < 2, ∀ h : toW 10 b ∈ V5,
      ((τ ⟨toW 10 b, h⟩ : ↥V5) : W10) = toW 10 (b ^^^ e) := by
  rcases ftcw_form τ hτ ⟨toW 10 b, toW_mem_maskSub (n := 10) (l := c5) hb⟩ with hc | hc
  · refine ⟨0, by norm_num, fun h => ?_⟩
    rw [Nat.xor_zero]
    exact hc
  · refine ⟨1, by norm_num, fun h => ?_⟩
    have hc' : ((τ ⟨toW 10 b, h⟩ : ↥V5) : W10) = toW 10 1 * toW 10 b := hc
    rw [hc', ← toW_xor, Nat.xor_comm]

theorem ftcw_fixc (τ : MulAut ↥V5)
    (hτ : ∀ x : ↥V5, ((τ x : ↥V5) : W10) * ((x : ↥V5) : W10)⁻¹ ∈ V1)
    (h : toW 10 1 ∈ V5) : ((τ ⟨toW 10 1, h⟩ : ↥V5) : W10) = toW 10 1 := by
  rcases ftcw_form τ hτ ⟨toW 10 1, h⟩ with hc | hc
  · exact hc
  · exfalso
    have hsq : toW 10 1 * toW 10 1 = 1 := by
      rw [← toW_xor, Nat.xor_self, toW_zero]
    have h1 : ((τ ⟨toW 10 1, h⟩ : ↥V5) : W10) = 1 := hc.trans hsq
    have h2 : τ ⟨toW 10 1, h⟩ = τ 1 := by
      rw [map_one]
      exact Subtype.ext h1
    have h3 : (⟨toW 10 1, h⟩ : ↥V5) = 1 := τ.injective h2
    have h4 : toW 10 1 = toW 10 0 := by
      rw [toW_zero]
      exact congrArg Subtype.val h3
    exact one_ne_zero (toW_inj (n := 10) (by norm_num) (by norm_num) h4)

theorem ftcw_gen (τ : MulAut ↥V5) (g : MulAut W10)
    (hbasis : ∀ a ∈ c5, a ∈ combos c5 ∧ ∀ h : toW 10 a ∈ V5,
      g (toW 10 a) = ((τ ⟨toW 10 a, h⟩ : ↥V5) : W10)) :
    ∀ m ∈ combos c5, m ∈ combos c5 ∧ ∀ h : toW 10 m ∈ V5,
      g (toW 10 m) = ((τ ⟨toW 10 m, h⟩ : ↥V5) : W10) := by
  refine mem_of_combos (fun m => m ∈ combos c5 ∧ ∀ h : toW 10 m ∈ V5,
    g (toW 10 m) = ((τ ⟨toW 10 m, h⟩ : ↥V5) : W10)) ?_ ?_ c5 hbasis
  · refine ⟨zero_mem_combos c5, fun h => ?_⟩
    have e : (⟨toW 10 0, h⟩ : ↥V5) = 1 := Subtype.ext (toW_zero 10)
    rw [e, map_one, toW_zero, map_one] <;> rfl
  · intro a b ha hb
    refine ⟨xor_mem_combos c5 ha.1 hb.1, fun h => ?_⟩
    have ha' : toW 10 a ∈ V5 := toW_mem_maskSub (n := 10) (l := c5) ha.1
    have hb' : toW 10 b ∈ V5 := toW_mem_maskSub (n := 10) (l := c5) hb.1
    have e : (⟨toW 10 (a ^^^ b), h⟩ : ↥V5) = ⟨toW 10 a, ha'⟩ * ⟨toW 10 b, hb'⟩ :=
      Subtype.ext (toW_xor 10 a b)
    rw [e, map_mul, Subgroup.coe_mul, ← ha.2 ha', ← hb.2 hb', toW_xor, map_mul]

theorem ftcw_clause2 :
    ∀ τ : MulAut ↥V5, (∀ x : ↥V5, ((τ x : ↥V5) : W10) * ((x : ↥V5) : W10)⁻¹ ∈ V1) →
      ∃ g ∈ rImg R fixO, ∀ x : ↥V5, g (x : W10) = ((τ x : ↥V5) : W10) := by
  intro τ hτ
  obtain ⟨e0, he0, h0⟩ := ftcw_bform τ hτ (ftcw_basis_mem 512 (by decide))
  obtain ⟨e1, he1, h1⟩ := ftcw_bform τ hτ (ftcw_basis_mem 256 (by decide))
  obtain ⟨e2, he2, h2⟩ := ftcw_bform τ hτ (ftcw_basis_mem 10 (by decide))
  obtain ⟨e3, he3, h3⟩ := ftcw_bform τ hτ (ftcw_basis_mem 6 (by decide))
  obtain ⟨t, t0, t1, t2, t3⟩ := ftcw_pattern ⟨e0, he0⟩ ⟨e1, he1⟩ ⟨e2, he2⟩ ⟨e3, he3⟩
  have hR : ∀ m : ℕ, R (koElt t) (toW 10 m) = toW 10 (actC10 (koArr t) m) :=
    fun m => R_ko t m
  have hbasis : ∀ a ∈ c5, a ∈ combos c5 ∧ ∀ h : toW 10 a ∈ V5,
      R (koElt t) (toW 10 a) = ((τ ⟨toW 10 a, h⟩ : ↥V5) : W10) := by
    intro a ha
    refine ⟨ftcw_basis_mem a ha, fun h => ?_⟩
    have ha5 : a = 512 ∨ a = 256 ∨ a = 10 ∨ a = 6 ∨ a = 1 := by
      simpa [c5, c1] using ha
    rcases ha5 with rfl | rfl | rfl | rfl | rfl
    · exact (hR 512).trans ((congrArg (toW 10) t0).trans (h0 h).symm)
    · exact (hR 256).trans ((congrArg (toW 10) t1).trans (h1 h).symm)
    · exact (hR 10).trans ((congrArg (toW 10) t2).trans (h2 h).symm)
    · exact (hR 6).trans ((congrArg (toW 10) t3).trans (h3 h).symm)
    · exact (hR 1).trans ((congrArg (toW 10) (ftcw_fix_one t)).trans
        (ftcw_fixc τ hτ h).symm)
  refine ⟨R (koElt t), ftcw_R_mem_X t, fun x => ?_⟩
  obtain ⟨m, hm, hmx⟩ := mem_maskSub.1 (show (x : W10) ∈ maskSub 10 c5 from x.2)
  have hmem : toW 10 m ∈ V5 := toW_mem_maskSub (n := 10) (l := c5) hm
  have e : (⟨toW 10 m, hmem⟩ : ↥V5) = x := Subtype.ext hmx
  have key := (ftcw_gen τ (R (koElt t)) hbasis m hm).2 hmem
  rw [e, hmx] at key
  exact key

theorem ftc_std :
    FullTranspCenter (rImg R (MY mog22plus Hstd)) (rImg R (KY mog22plus Hstd)) V5
      (fixV (rImg R (KY mog22plus Hstd))) := by
  rw [KY_H_L2, fixV_fixO]
  unfold FullTranspCenter
  exact ⟨ftcw_clause1, ftcw_clause2, ftcw_clause3, ftcw_clause4⟩

end CFSG.Quasithin.RonanH163
