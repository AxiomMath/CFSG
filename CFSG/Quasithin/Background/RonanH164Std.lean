module

public import CFSG.Quasithin.Background.RonanH164Chain
public import CFSG.Quasithin.Background.RonanH164FTC
public import CFSG.Quasithin.Background.RonanH164Dual
public import CFSG.Quasithin.Background.RonanH164Beta
public import CFSG.Quasithin.Background.RonanH164Uniq

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem mem_rImg_fixO {g : MulAut W10} (hg : g ∈ rImg R fixO) : ∃ t : Fin 16, g = R (koElt t) := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hk)
  exact ⟨t, congrArg R (Subtype.ext ht)⟩

theorem toW_inv_self (m : ℕ) : (toW 10 m)⁻¹ = toW 10 m := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact (toW_xor 10 m m).symm.trans (by rw [Nat.xor_self, toW_zero]; rfl)

theorem V5_char :
    ∀ x : W10, x ∈ V5 ↔
      ∀ g ∈ rImg R (KY mog22plus Hstd), g x * x⁻¹ ∈ fixV (rImg R (KY mog22plus Hstd)) := by
  intro x
  have hK : KY mog22plus Hstd = fixO := KY_H_L2
  have hF : ∀ y : W10, y ∈ fixV (rImg R (KY mog22plus Hstd)) ↔ y ∈ V1 := by
    intro y
    rw [hK, fixV_fixO]
    exact Iff.rfl
  obtain ⟨⟨m, hm⟩, rfl⟩ := (toWFin_bijective 10).2 x
  have hx : toWFin 10 ⟨m, hm⟩ = toW 10 m := rfl
  rw [hx]
  have F5a : ∀ m ∈ combos c5, ∀ t : Fin 16, (actC10 (koArr t) m ^^^ m) ∈ combos c1 := by
    decide +kernel
  have F5b : ∀ m < 2 ^ 10, (∀ t : Fin 16, (actC10 (koArr t) m ^^^ m) ∈ combos c1) →
      m ∈ combos c5 := by
    decide +kernel
  have hlt : ∀ t : Fin 16, actC10 (koArr t) m < 2 ^ 10 := fun t => actC10_lt _ _
  have hkey : ∀ t : Fin 16,
      R (koElt t) (toW 10 m) * (toW 10 m)⁻¹ = toW 10 (actC10 (koArr t) m ^^^ m) := by
    intro t
    rw [R_ko, toW_inv_self, toW_xor]
  constructor
  · intro hx5 g hg
    rw [hK] at hg
    obtain ⟨t, rfl⟩ := mem_rImg_fixO hg
    refine (hF _).2 ?_
    have hm5 : m ∈ combos c5 := (toW_mem_V5_iff hm).1 hx5
    have h2 : toW 10 (actC10 (koArr t) m ^^^ m) ∈ V1 :=
      (toW_mem_V1_iff (Nat.xor_lt_two_pow (hlt t) hm)).2 (F5a m hm5 t)
    convert h2 using 1
    exact hkey t
  · intro h
    refine (toW_mem_V5_iff hm).2 (F5b m hm fun t => ?_)
    have h2 := (hF _).1 (h (R (koElt t)) (by
      rw [hK]
      exact ⟨koElt t, Subgroup.mem_subgroupOf.2 ((mem_fixO_iff _).2 ⟨t, rfl⟩), rfl⟩))
    have h3 : toW 10 (actC10 (koArr t) m ^^^ m) ∈ V1 := by
      convert h2 using 1
      exact (hkey t).symm
    exact (toW_mem_V1_iff (Nat.xor_lt_two_pow (hlt t) hm)).1 h3

theorem std164 :
    Concl164 R Hstd Qstd :=
  ⟨V5, V6, chain164_std, ⟨ftc_std, dual_std⟩,
    ⟨⟨piH2, MonoidHom.range_eq_top.1 piH2_range_top, by rw [KY_H_L2]; exact ker_piH2⟩,
      induces6_std⟩,
    part4_std, V5_char⟩

end CFSG.Quasithin.RonanH163
