module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H23
public import CFSG.Quasithin.Vol2.Ch10SecQ9H22

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n m k : ℕ}

@[expose] def InvStd (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) (M : ℕ) : Prop :=
  ∀ x ∈ X, ∀ v ∈ stdE n M, x • v ∈ stdE n M

theorem le_stabStd_of_invStd {X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2))}
    (h : InvStd X m) : X ≤ stabStd m k := fun x hx =>
  presStd_of_smul_mem fun j => h x hx _ (castAdd_mem_stdE j)

theorem pow_three_stab {K : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}
    {y : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hy3 : orderOf y = 3) (hy : y ∈ K) :
    (⟨y, hy⟩ : ↥K) ^ 3 = 1 :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hy3 ▸ pow_orderOf_eq_one y)

theorem map_eq_top_of_sq {X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2))}
    (hX : X ≤ stabStd m k) (f : ↥(stabStd m k) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hf : ∀ x : ↥(stabStd m k), x.1 ∈ X → f x = 1 → x.1 * x.1 = 1)
    (hcard : Nat.card X = Nat.card (o2G X) * 168) : (X.subgroupOf (stabStd m k)).map f = ⊤ :=
  Subgroup.eq_top_of_le_card _ (by rw [card_SL_three_two]; exact card_map_ge hX f hf hcard)

theorem concl_of_E2 {X : Subgroup (Matrix.SpecialLinearGroup (Fin (2 + 3)) (ZMod 2))}
    (hX : X ≤ stabStd 2 3) (hperf : ⁅X, X⁆ = X) (hcard : Nat.card X = Nat.card (o2G X) * 168)
    {y : Matrix.SpecialLinearGroup (Fin (2 + 3)) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin (2 + 3)) (ZMod 2))))
    (hy3 : orderOf y = 3) (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X) :
    ∃ r ∈ uniSL (2 + 3), ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1 := by
  have htop := topH_eq_one_of_perfect hX hperf
  have himg := map_eq_top_of_sq hX (botH 2 3) (fun x hx hb =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val (htop x hx)) (congrArg Subtype.val hb)) hcard
  have hfix : ∀ v, v ∈ fixN X → v ∈ stdE (2 + 3) 2 := by
    intro v hv
    have hw : (fun j : Fin 3 => v (Fin.natAdd 2 j)) = 0 := by
      refine eq_zero_of_fixed (by norm_num) fun g => ?_
      have hg : g ∈ (X.subgroupOf (stabStd 2 3)).map (botH 2 3) := by rw [himg]; trivial
      obtain ⟨x, hx, rfl⟩ := hg
      funext j
      rw [smul_eq_mulVec', coe_botH, ← bot_smul x.2, hv x.1 (Subgroup.mem_subgroupOf.mp hx)]
    intro i hi
    have := congrFun hw ⟨(i : ℕ) - 2, by omega⟩
    rwa [show Fin.natAdd 2 (⟨(i : ℕ) - 2, by omega⟩ : Fin 3) = i from
      Fin.ext (by simp; omega)] at this
  have hfix' : ∀ v ∈ stdE (2 + 3) 2, v ∈ fixN X := fun v hv x hx =>
    smul_eq_of_topB_one (hX hx) (congrArg Subtype.val (htop ⟨x, hX hx⟩ hx)) hv
  have hyS : y ∈ stabStd 2 3 := presStd_of_smul_mem fun j =>
    hfix _ (smul_mem_fixN hyN (hfix' _ (castAdd_mem_stdE j)))
  obtain ⟨ys, hys⟩ : ∃ ys : ↥(stabStd 2 3), ys = ⟨y, hyS⟩ := ⟨_, rfl⟩
  have hys1 : ys.1 = y := by rw [hys]
  have hbot : botH 2 3 ys = 1 :=
    eq_one_of_center_section hX (botH 2 3) himg (y := ys) (hys1 ▸ hyc)
  obtain ⟨c, hc⟩ : ∃ c, c = topH 2 3 ys := ⟨_, rfl⟩
  have hc3 : c ^ 3 = 1 := by rw [hc, ← map_pow, hys, pow_three_stab hy3 hyS, map_one]
  have hc1 : c ≠ 1 := fun h => blocks_ne_of_orderOf_three (hys1 ▸ hy3) (hc ▸ h) hbot
  obtain ⟨rs, hrs⟩ : ∃ rs : ↥(stabStd 2 3), rs.1 = trvE 0 1 (by decide) :=
    ⟨⟨trvE 0 1 (by decide), by rw [mem_stabStd]; unfold PresStd; decide⟩, rfl⟩
  have htr : topH 2 3 rs = tSL2 := Subtype.ext (by rw [coe_topH, hrs]; decide)
  have hbr : botH 2 3 rs = 1 := Subtype.ext (by rw [coe_botH, hrs]; decide)
  refine ⟨rs.1, hrs ▸ trvE_mem_uniSL 0 1 (by decide), 1, ?_⟩
  rw [← hys1]
  refine sq_conj_of_blocks ?_ ?_
  · rw [map_mul, map_mul, map_mul, map_inv, htr, ← hc, conj_tSL2 c hc3 hc1, inv_mul_cancel]
  · rw [map_mul, map_mul, map_mul, map_inv, hbr, hbot]
    group

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
