module

public import CFSG.Sporadic.Fi24.ExtCentralizer

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Sporadic.Th

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fix_M_iff
    (k : Fin 306936) : (∀ h ∈ M, h • k = k) ↔ k = root := by
  constructor
  · intro hk
    by_contra hne
    have hcard : 1 < (Finset.univ.filter fun p : Fin 306936 => subLab p = subLab k).card := by
      rcases subLab_cases k with h | h | h
      · exact absurd (subLab_eq_zero.1 h) hne
      · rw [h, card_subLab_one]; norm_num
      · rw [h, card_subLab_two]; norm_num
    obtain ⟨k', hk', hne'⟩ := Finset.exists_mem_ne hcard k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    obtain ⟨h, hh, hhk⟩ := subLab_orb k k' hk'.symm
    exact hne' (by rw [← hhk]; exact hk h (mem_stabilizer_of_lvl hh))
  · rintro rfl h hh
    exact hh

theorem eq_one_of_commute_M
    {j : J} (hj : ∀ g ∈ M, g * j = j * g) : j = 1 := by
  have hroot : j • root = root := (fix_M_iff (j • root)).1 fun g hg => by
    rw [smul_smul, hj g hg, mul_smul, show g • root = root from hg]
  have hc : (⟨j, hroot⟩ : M) ∈ Subgroup.center M :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hj g g.2)
  rw [center_M, Subgroup.mem_bot] at hc
  have := congrArg Subtype.val hc
  exact this

instance : JR.Normal := normal_JR

@[expose] noncomputable def conjJ :
    R →* MulAut J :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe J_le_R)).toMonoidHom.comp MulAut.conjNormal

theorem coe_conjJ (r : R) (g : J) :
    ((conjJ r g : J) : GL (Fin 781) (ZMod 3)) = (r : GL (Fin 781) (ZMod 3)) * g * (r⁻¹ : R) :=
  rfl

theorem jR_conjJ
    (r : R) (g : J) : jR (conjJ r g) = r * jR g * r⁻¹ := Subtype.ext (coe_conjJ r g)

theorem conjJ_jR
    (g : J) : conjJ (jR g) = MulAut.conj g := by
  refine MulEquiv.ext fun x => jR_injective ?_
  rw [jR_conjJ, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem conjJ_injective :
    Function.Injective conjJ := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hc : ∀ g : J, jR g * r = r * jR g := fun g => by
    have h := jR_conjJ r g
    rw [hr, MulAut.one_apply] at h
    calc jR g * r = r * jR g * r⁻¹ * r := by rw [← h]
      _ = r * jR g := by rw [inv_mul_cancel_right]
  obtain ⟨j, rfl | rfl⟩ := eq_jR_or r
  · have hj : j ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g =>
      jR_injective (by rw [map_mul, map_mul]; exact hc g)
    rw [center_J, Subgroup.mem_bot] at hj
    rw [hj, map_one]
  · exfalso
    have hj : j = 1 := eq_one_of_commute_M fun g hg => by
      apply jR_injective
      have h := hc g
      have ht := (commute_tR_iff g).2 hg
      rw [map_mul, map_mul]
      calc jR g * jR j = jR g * (jR j * tR) * tR := by
            rw [← mul_assoc (jR g), mul_assoc _ tR tR, tR_mul_tR, mul_one]
        _ = jR j * tR * jR g * tR := by rw [h]
        _ = jR j * jR g := by
            rw [mul_assoc (jR j) tR (jR g), ← ht]; simp only [mul_assoc, tR_mul_tR, mul_one]
    subst hj
    have h := hc a
    rw [map_one, one_mul] at h
    have haM : a ∈ M := (commute_tR_iff a).1 h
    exact p1_ne_root haM

theorem conjJ_tR_ne
    (g : J) : conjJ tR ≠ MulAut.conj g := by
  intro h
  rw [← conjJ_jR] at h
  apply tR_not_mem_JR
  rw [conjJ_injective h]
  exact jR_mem_JR g

theorem conjJ_tR_mul_self :
    conjJ tR * conjJ tR = 1 := by
  rw [← map_mul, tR_mul_tR, map_one]

end CFSG.Sporadic.Fi24
