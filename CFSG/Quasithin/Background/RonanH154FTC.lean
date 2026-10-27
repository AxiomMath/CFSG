module

public import CFSG.Quasithin.Background.RonanH154Gen
public import CFSG.Quasithin.Background.RonanH164Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem ftc_basis_mem : ∀ a ∈ w6, a ∈ combos w6 := by decide +kernel

theorem ftc_c1 : ∀ m ∈ combos w1, m = 0 ∨ m = 128 := by decide +kernel

theorem ftc_F1 : ∀ u < 32, ∀ x ∈ w6, act10 (nq2Arr u) x ^^^ x ∈ combos w1 := by
  decide +kernel

theorem ftc_fix_c : ∀ u < 32, act10 (nq2Arr u) 128 = 128 := by decide +kernel

theorem ftc_faithful : ∀ u < 32, (∀ m ∈ combos w6, act10 (nq2Arr u) m = m) → u = 0 := by
  decide +kernel

theorem ftc_pattern : ∀ e0 : Fin 2, ∀ e1 : Fin 2, ∀ e2 : Fin 2, ∀ e3 : Fin 2, ∀ e4 : Fin 2,
    ∃ u < 32, act10 (nq2Arr u) 30 = 30 ^^^ 128 * (e0 : ℕ) ∧
      act10 (nq2Arr u) 32 = 32 ^^^ 128 * (e1 : ℕ) ∧
      act10 (nq2Arr u) 262 = 262 ^^^ 128 * (e2 : ℕ) ∧
      act10 (nq2Arr u) 512 = 512 ^^^ 128 * (e3 : ℕ) ∧
      act10 (nq2Arr u) 78 = 78 ^^^ 128 * (e4 : ℕ) := by
  decide +kernel

theorem ftc_nq2Perm_zero_elt : nq2Elt 0 = 1 := by
  apply Subtype.ext
  exact nq2Perm_zero

theorem ftc_xor4 (A B x y : ℕ) : (A ^^^ B) ^^^ (x ^^^ y) = (A ^^^ x) ^^^ (B ^^^ y) := by
  rw [Nat.xor_assoc A B (x ^^^ y), ← Nat.xor_assoc B x y, Nat.xor_comm B x,
    Nat.xor_assoc x B y, ← Nat.xor_assoc A x (B ^^^ y)]

theorem ftc_xorLin_sub (a : Array ℕ) (x y : ℕ) :
    act10 a (x ^^^ y) ^^^ (x ^^^ y) = (act10 a x ^^^ x) ^^^ (act10 a y ^^^ y) := by
  rw [xorLin_act10 a x y]
  exact ftc_xor4 _ _ _ _

theorem ftc_F1_all (a : Array ℕ) (ha : ∀ x ∈ w6, act10 a x ^^^ x ∈ combos w1) :
    ∀ m ∈ combos w6, act10 a m ^^^ m ∈ combos w1 := by
  refine mem_of_combos (fun m => act10 a m ^^^ m ∈ combos w1) ?_ ?_ w6 ha
  · show act10 a 0 ^^^ 0 ∈ combos w1
    rw [XorLin.map_zero (xorLin_act10 a), Nat.xor_self]
    exact zero_mem_combos w1
  · intro x y hx hy
    show act10 a (x ^^^ y) ^^^ (x ^^^ y) ∈ combos w1
    rw [ftc_xorLin_sub a x y]
    exact xor_mem_combos w1 hx hy

theorem ftc_inv_self (m : ℕ) : (toW 10 m)⁻¹ = toW 10 m :=
  inv_eq_of_mul_eq_one_right ((toW_xor 10 m m).symm.trans (by rw [Nat.xor_self]; exact toW_zero 10))

theorem ftc_mem_X {g : MulAut W10} (hg : g ∈ rImg Rc NQ2) : ∃ u : Fin 32, g = Rc (nq2Elt u) := by
  obtain ⟨k, hk, rfl⟩ :=
    Subgroup.mem_map.1 (show g ∈ Subgroup.map Rc (NQ2.subgroupOf mog22plus) from hg)
  obtain ⟨u, hu⟩ := mem_NQ2_iff.1 (Subgroup.mem_subgroupOf.1 hk)
  exact ⟨u, congrArg Rc (Subtype.ext hu)⟩

theorem ftc_Rc_mem_X (u : Fin 32) : Rc (nq2Elt u) ∈ rImg Rc NQ2 :=
  Subgroup.mem_map_of_mem Rc (Subgroup.mem_subgroupOf.2 (mem_NQ2_iff.2 ⟨u, rfl⟩))

theorem ftc_clause1 : ∀ g : MulAut W10, g ∈ rImg Rc NQ2 → ∀ x : W10, x ∈ X6 →
    g x * x⁻¹ ∈ X1 := by
  intro g hg x hx
  obtain ⟨u, rfl⟩ := ftc_mem_X hg
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 (show x ∈ maskSub 10 w6 from hx)
  have hF : toW 10 (act10 (nq2Arr u) m ^^^ m) ∈ maskSub 10 w1 :=
    toW_mem_maskSub (n := 10) (l := w1) (ftc_F1_all (nq2Arr u) (ftc_F1 u u.2) m hm)
  have e2 : Rc (nq2Elt u) (toW 10 m) * (toW 10 m)⁻¹ = toW 10 (act10 (nq2Arr u) m ^^^ m) := by
    rw [Rc_nq2, ftc_inv_self]
    exact (toW_xor 10 (act10 (nq2Arr u) m) m).symm
  exact (congrArg (fun y : W10 => y ∈ maskSub 10 w1) e2).mpr hF

theorem ftc_clause3 : ∀ g : MulAut W10, g ∈ rImg Rc NQ2 →
    (∀ x : W10, x ∈ X6 → g x = x) → g = 1 := by
  intro g hg hfix
  obtain ⟨u, rfl⟩ := ftc_mem_X hg
  have hm : ∀ m ∈ combos w6, act10 (nq2Arr u) m = m := by
    intro m hm
    have h : Rc (nq2Elt u) (toW 10 m) = toW 10 m :=
      hfix (toW 10 m) (toW_mem_maskSub (n := 10) (l := w6) hm)
    exact toW_inj (act10_lt _ m) (combos_lt (n := 10) mask_lt_w6 m hm)
      ((Rc_nq2 u m).symm.trans h)
  have hu : (u : ℕ) = 0 := ftc_faithful u u.2 hm
  have hu0 : u = 0 := Fin.ext hu
  subst hu0
  exact (congrArg Rc ftc_nq2Perm_zero_elt).trans (map_one Rc)

theorem ftc_clause4 :
    ∀ h : MulAut W10, h ∈ rImg Rc (MY mog22plus Qstd) →
      ∀ g : MulAut W10, g ∈ rImg Rc NQ2 → h * g * h⁻¹ ∈ rImg Rc NQ2 := by
  intro h hh g hg
  obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.1
    (show h ∈ Subgroup.map Rc ((MY mog22plus Qstd).subgroupOf mog22plus) from hh)
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1
    (show g ∈ Subgroup.map Rc (NQ2.subgroupOf mog22plus) from hg)
  have hN : (NQ2.subgroupOf (MY mog22plus Qstd)).Normal := by
    rw [← ker_piQ_L2]
    infer_instance
  have hkM : (⟨(k : P24), NQ2_le_MY_Q (Subgroup.mem_subgroupOf.1 hk)⟩ :
      ↥(MY mog22plus Qstd)) ∈ NQ2.subgroupOf (MY mog22plus Qstd) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hk)
  have hy := hN.conj_mem _ hkM ⟨(h₀ : P24), Subgroup.mem_subgroupOf.1 hh₀⟩
  have hmem : h₀ * k * h₀⁻¹ ∈ NQ2.subgroupOf mog22plus :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hy)
  have e : Rc h₀ * Rc k * (Rc h₀)⁻¹ = Rc (h₀ * k * h₀⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  exact (congrArg (fun y : MulAut W10 => y ∈ rImg Rc NQ2) e).mpr
    (Subgroup.mem_map_of_mem Rc hmem)

theorem ftc_form (τ : MulAut ↥X6)
    (hτ : ∀ x : ↥X6, ((τ x : ↥X6) : W10) * ((x : ↥X6) : W10)⁻¹ ∈ X1) (x : ↥X6) :
    ((τ x : ↥X6) : W10) = (x : W10) ∨ ((τ x : ↥X6) : W10) = toW 10 128 * (x : W10) := by
  obtain ⟨m, hm, hmx⟩ := mem_maskSub.1
    (show ((τ x : ↥X6) : W10) * ((x : ↥X6) : W10)⁻¹ ∈ maskSub 10 w1 from hτ x)
  rcases ftc_c1 m hm with rfl | rfl
  · rw [toW_zero] at hmx
    exact Or.inl (mul_inv_eq_one.1 hmx.symm)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.1 hmx.symm)

theorem ftc_bform (τ : MulAut ↥X6)
    (hτ : ∀ x : ↥X6, ((τ x : ↥X6) : W10) * ((x : ↥X6) : W10)⁻¹ ∈ X1) {b : ℕ}
    (hb : b ∈ combos w6) : ∃ e < 2, ∀ h : toW 10 b ∈ X6,
      ((τ ⟨toW 10 b, h⟩ : ↥X6) : W10) = toW 10 (b ^^^ 128 * e) := by
  rcases ftc_form τ hτ ⟨toW 10 b, toW_mem_maskSub (n := 10) (l := w6) hb⟩ with hc | hc
  · refine ⟨0, by norm_num, fun h => ?_⟩
    rw [Nat.mul_zero, Nat.xor_zero]
    exact hc
  · refine ⟨1, by norm_num, fun h => ?_⟩
    have hc' : ((τ ⟨toW 10 b, h⟩ : ↥X6) : W10) = toW 10 128 * toW 10 b := hc
    rw [hc', ← toW_xor, Nat.xor_comm, Nat.mul_one]

theorem ftc_fixc (τ : MulAut ↥X6)
    (hτ : ∀ x : ↥X6, ((τ x : ↥X6) : W10) * ((x : ↥X6) : W10)⁻¹ ∈ X1)
    (h : toW 10 128 ∈ X6) : ((τ ⟨toW 10 128, h⟩ : ↥X6) : W10) = toW 10 128 := by
  rcases ftc_form τ hτ ⟨toW 10 128, h⟩ with hc | hc
  · exact hc
  · exfalso
    have hsq : toW 10 128 * toW 10 128 = 1 := by
      rw [← toW_xor, Nat.xor_self, toW_zero]
    have h1 : ((τ ⟨toW 10 128, h⟩ : ↥X6) : W10) = 1 := hc.trans hsq
    have h2 : τ ⟨toW 10 128, h⟩ = τ 1 := by
      rw [map_one]
      exact Subtype.ext h1
    have h3 : (⟨toW 10 128, h⟩ : ↥X6) = 1 := τ.injective h2
    have h4 : toW 10 128 = toW 10 0 := by
      rw [toW_zero]
      exact congrArg Subtype.val h3
    exact absurd (toW_inj (n := 10) (by norm_num) (by norm_num) h4) (by norm_num)

theorem ftc_gen (τ : MulAut ↥X6) (g : MulAut W10)
    (hbasis : ∀ a ∈ w6, a ∈ combos w6 ∧ ∀ h : toW 10 a ∈ X6,
      g (toW 10 a) = ((τ ⟨toW 10 a, h⟩ : ↥X6) : W10)) :
    ∀ m ∈ combos w6, m ∈ combos w6 ∧ ∀ h : toW 10 m ∈ X6,
      g (toW 10 m) = ((τ ⟨toW 10 m, h⟩ : ↥X6) : W10) := by
  refine mem_of_combos (fun m => m ∈ combos w6 ∧ ∀ h : toW 10 m ∈ X6,
    g (toW 10 m) = ((τ ⟨toW 10 m, h⟩ : ↥X6) : W10)) ?_ ?_ w6 hbasis
  · refine ⟨zero_mem_combos w6, fun h => ?_⟩
    have e : (⟨toW 10 0, h⟩ : ↥X6) = 1 := Subtype.ext (toW_zero 10)
    rw [e, map_one, toW_zero, map_one] <;> rfl
  · intro a b ha hb
    refine ⟨xor_mem_combos w6 ha.1 hb.1, fun h => ?_⟩
    have ha' : toW 10 a ∈ X6 := toW_mem_maskSub (n := 10) (l := w6) ha.1
    have hb' : toW 10 b ∈ X6 := toW_mem_maskSub (n := 10) (l := w6) hb.1
    have e : (⟨toW 10 (a ^^^ b), h⟩ : ↥X6) = ⟨toW 10 a, ha'⟩ * ⟨toW 10 b, hb'⟩ :=
      Subtype.ext (toW_xor 10 a b)
    rw [e, map_mul, Subgroup.coe_mul, ← ha.2 ha', ← hb.2 hb', toW_xor, map_mul]

theorem ftc_clause2 :
    ∀ τ : MulAut ↥X6, (∀ x : ↥X6, ((τ x : ↥X6) : W10) * ((x : ↥X6) : W10)⁻¹ ∈ X1) →
      ∃ g ∈ rImg Rc NQ2, ∀ x : ↥X6, g (x : W10) = ((τ x : ↥X6) : W10) := by
  intro τ hτ
  obtain ⟨e0, he0, h0⟩ := ftc_bform τ hτ (ftc_basis_mem 30 (by decide))
  obtain ⟨e1, he1, h1⟩ := ftc_bform τ hτ (ftc_basis_mem 32 (by decide))
  obtain ⟨e2, he2, h2⟩ := ftc_bform τ hτ (ftc_basis_mem 262 (by decide))
  obtain ⟨e3, he3, h3⟩ := ftc_bform τ hτ (ftc_basis_mem 512 (by decide))
  obtain ⟨e4, he4, h4⟩ := ftc_bform τ hτ (ftc_basis_mem 78 (by decide))
  obtain ⟨u, hu, t0, t1, t2, t3, t4⟩ := ftc_pattern ⟨e0, he0⟩ ⟨e1, he1⟩ ⟨e2, he2⟩ ⟨e3, he3⟩
    ⟨e4, he4⟩
  have hR : ∀ m : ℕ, Rc (nq2Elt ⟨u, hu⟩) (toW 10 m) = toW 10 (act10 (nq2Arr u) m) :=
    fun m => Rc_nq2 ⟨u, hu⟩ m
  have hbasis : ∀ a ∈ w6, a ∈ combos w6 ∧ ∀ h : toW 10 a ∈ X6,
      Rc (nq2Elt ⟨u, hu⟩) (toW 10 a) = ((τ ⟨toW 10 a, h⟩ : ↥X6) : W10) := by
    intro a ha
    refine ⟨ftc_basis_mem a ha, fun h => ?_⟩
    have ha6 : a = 30 ∨ a = 32 ∨ a = 262 ∨ a = 512 ∨ a = 78 ∨ a = 128 := by
      simpa [w6, w2, w1] using ha
    rcases ha6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hR 30).trans ((congrArg (toW 10) t0).trans (h0 h).symm)
    · exact (hR 32).trans ((congrArg (toW 10) t1).trans (h1 h).symm)
    · exact (hR 262).trans ((congrArg (toW 10) t2).trans (h2 h).symm)
    · exact (hR 512).trans ((congrArg (toW 10) t3).trans (h3 h).symm)
    · exact (hR 78).trans ((congrArg (toW 10) t4).trans (h4 h).symm)
    · exact (hR 128).trans ((congrArg (toW 10) (ftc_fix_c u hu)).trans
        (ftc_fixc τ hτ h).symm)
  refine ⟨Rc (nq2Elt ⟨u, hu⟩), ftc_Rc_mem_X ⟨u, hu⟩, fun x => ?_⟩
  obtain ⟨m, hm, hmx⟩ := mem_maskSub.1 (show (x : W10) ∈ maskSub 10 w6 from x.2)
  have hmem : toW 10 m ∈ X6 := toW_mem_maskSub (n := 10) (l := w6) hm
  have e : (⟨toW 10 m, hmem⟩ : ↥X6) = x := Subtype.ext hmx
  have key := (ftc_gen τ (Rc (nq2Elt ⟨u, hu⟩)) hbasis m hm).2 hmem
  rw [e, hmx] at key
  exact key

theorem ftc_std :
    FullTranspCenter (rImg Rc (MY mog22plus Qstd)) (rImg Rc (KY mog22plus Qstd)) X6
      (fixV (rImg Rc (KY mog22plus Qstd))) := by
  rw [KY_Q_L2, fixV_NQ2_X1]
  unfold FullTranspCenter
  exact ⟨ftc_clause1, ftc_clause2, ftc_clause3, ftc_clause4⟩

end CFSG.Quasithin.RonanH154
