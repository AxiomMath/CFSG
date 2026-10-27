module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H24

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem smul_single_of_topH {g : ↥(stabStd m k)} {i j : Fin m} (h : i ≠ j)
    (hg : topH m k g = trvE i j h) :
    g.1 • Pi.single (Fin.castAdd k j) (1 : ZMod 2) =
      (Pi.single (Fin.castAdd k j) 1 + Pi.single (Fin.castAdd k i) 1 : Fin (m + k) → ZMod 2) := by
  have hg' : topB ((g.1 : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) =
      ((trvE i j h : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) := by
    rw [← coe_topH, hg]
  have hne : ∀ (a : Fin k) (b : Fin m), Fin.natAdd m a ≠ Fin.castAdd k b := fun a b hab => by
    have := congrArg Fin.val hab
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  funext l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) l
  · rw [top_smul_of_mem (castAdd_mem_stdE j), hg']
    have hf : (fun l : Fin m => (Pi.single (Fin.castAdd k j) (1 : ZMod 2) :
        Fin (m + k) → ZMod 2) (Fin.castAdd k l)) = Pi.single j 1 := by
      funext l
      simp [Pi.single_apply, Fin.castAdd_inj]
    rw [hf, ← smul_eq_mulVec', trvE_mulVec, Pi.single_eq_same, one_smul]
    simp [Pi.single_apply, Fin.castAdd_inj]
  · rw [bot_smul g.2]
    have hf : (fun l : Fin k => (Pi.single (Fin.castAdd k j) (1 : ZMod 2) :
        Fin (m + k) → ZMod 2) (Fin.natAdd m l)) = 0 := by
      funext l
      simp [hne l j]
    rw [hf, mulVec_zero]
    simp [hne b j, hne b i]

theorem concl_of_E3 {X : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 2)) (ZMod 2))}
    (hX : X ≤ stabStd 3 2) (hperf : ⁅X, X⁆ = X) (hcard : Nat.card X = Nat.card (o2G X) * 168)
    {y : Matrix.SpecialLinearGroup (Fin (3 + 2)) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin (3 + 2)) (ZMod 2))))
    (hy3 : orderOf y = 3) (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X) :
    ∃ r ∈ uniSL (3 + 2), ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1 := by
  have hbot := botH_eq_one_of_perfect hX hperf
  have himg := map_eq_top_of_sq hX (topH 3 2) (fun x hx ht =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val ht) (congrArg Subtype.val (hbot x hx))) hcard
  have hyS : y ∈ stabStd 3 2 := by
    refine presStd_of_smul_mem fun j => ?_
    obtain ⟨j', hj'⟩ : ∃ j' : Fin 3, j ≠ j' := ⟨j + 1, by fin_cases j <;> decide⟩
    have hg : trvE j j' hj' ∈ (X.subgroupOf (stabStd 3 2)).map (topH 3 2) := by
      rw [himg]; trivial
    obtain ⟨x, hx, hxt⟩ := hg
    have hxX : x.1 ∈ X := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨w, hw⟩ : ∃ w : Fin (3 + 2) → ZMod 2, w = Pi.single (Fin.castAdd 2 j') 1 :=
      ⟨_, rfl⟩
    have hej : Pi.single (Fin.castAdd 2 j) (1 : ZMod 2) = x.1 • w + w := by
      rw [hw, smul_single_of_topH hj' hxt, add_add_cancel_vec]
    have hz : y * x.1 * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hyN _).mp hxX
    rw [hej, smul_add, show y • x.1 • w = (y * x.1 * y⁻¹) • y • w by
      rw [smul_smul, smul_smul, inv_mul_cancel_right]]
    obtain ⟨z, hzd⟩ : ∃ z : ↥(stabStd 3 2), z.1 = y * x.1 * y⁻¹ := ⟨⟨_, hX hz⟩, rfl⟩
    have hb1 := congrArg Subtype.val (hbot z (hzd ▸ hz))
    rw [coe_botH, hzd] at hb1
    exact smul_add_mem_of_botB_one (hX hz) hb1 _
  obtain ⟨ys, hys⟩ : ∃ ys : ↥(stabStd 3 2), ys = ⟨y, hyS⟩ := ⟨_, rfl⟩
  have hys1 : ys.1 = y := by rw [hys]
  have htop : topH 3 2 ys = 1 :=
    eq_one_of_center_section hX (topH 3 2) himg (y := ys) (hys1 ▸ hyc)
  obtain ⟨c, hc⟩ : ∃ c, c = botH 3 2 ys := ⟨_, rfl⟩
  have hc3 : c ^ 3 = 1 := by rw [hc, ← map_pow, hys, pow_three_stab hy3 hyS, map_one]
  have hc1 : c ≠ 1 := fun h => blocks_ne_of_orderOf_three (hys1 ▸ hy3) htop (hc ▸ h)
  obtain ⟨rs, hrs⟩ : ∃ rs : ↥(stabStd 3 2), rs.1 = trvE 3 4 (by decide) :=
    ⟨⟨trvE 3 4 (by decide), by rw [mem_stabStd]; unfold PresStd; decide⟩, rfl⟩
  have htr : topH 3 2 rs = 1 := Subtype.ext (by rw [coe_topH, hrs]; decide)
  have hbr : botH 3 2 rs = tSL2 := Subtype.ext (by rw [coe_botH, hrs]; decide)
  refine ⟨rs.1, hrs ▸ trvE_mem_uniSL 3 4 (by decide), 1, ?_⟩
  rw [← hys1]
  refine sq_conj_of_blocks ?_ ?_
  · rw [map_mul, map_mul, map_mul, map_inv, htr, htop]
    group
  · rw [map_mul, map_mul, map_mul, map_inv, hbr, ← hc, conj_tSL2 c hc3 hc1, inv_mul_cancel]

theorem concl_of_inv23 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h23 : InvStd X 2 ∨ InvStd X 3) (hperf : ⁅X, X⁆ = X)
    (hcard : Nat.card X = Nat.card (o2G X) * 168) {y : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hy3 : orderOf y = 3) (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X) :
    ∃ r ∈ uniSL 5, ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1 := by
  rcases h23 with h2 | h3
  · exact concl_of_E2 (le_stabStd_of_invStd (m := 2) (k := 3) h2) hperf hcard hyN hy3 hyc
  · exact concl_of_E3 (le_stabStd_of_invStd (m := 3) (k := 2) h3) hperf hcard hyN hy3 hyc

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
