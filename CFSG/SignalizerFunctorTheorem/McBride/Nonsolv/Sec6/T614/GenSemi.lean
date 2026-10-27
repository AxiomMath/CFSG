module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Khat
public import CFSG.Assembly.LowTwoRankDefs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T614

variable {Γ : Type*} [Group Γ] [Finite Γ] {H B : Subgroup Γ}

omit [Finite Γ] in
private theorem exists_mul_of_mem_sup (hBH : B ≤ Subgroup.normalizer (H : Set Γ)) {x : Γ}
    (hx : x ∈ H ⊔ B) : ∃ h ∈ H, ∃ b ∈ B, x = h * b := by
  have hx' : x ∈ ((H ⊔ B : Subgroup Γ) : Set Γ) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H B hBH] at hx'
  obtain ⟨h, hh, b, hb, rfl⟩ := hx'
  exact ⟨h, hh, b, hb, rfl⟩

omit [Finite Γ] in
private theorem mem_normalizer_of_forall_commute {g : Γ} {J : Subgroup Γ}
    (hg : ∀ c ∈ J, c * g = g * c) : g ∈ Subgroup.normalizer (J : Set Γ) :=
  Subgroup.centralizer_le_normalizer (J : Set Γ) (Subgroup.mem_centralizer_iff.mpr hg)

omit [Finite Γ] in
private theorem eq_one_of_mul_mem_normalizer
    (hfree : ∀ b ∈ B, b ≠ 1 → ∀ J ∈ lcal H, J.map (MulAut.conj b).toMonoidHom ≠ J)
    {h b : Γ} {J : Subgroup Γ} (hb : b ∈ B) (hJ : J ∈ lcal H)
    (hh : h ∈ Subgroup.normalizer (J : Set Γ)) (hhb : h * b ∈ Subgroup.normalizer (J : Set Γ)) :
    b = 1 := by
  by_contra hb1
  refine hfree b hb hb1 J hJ (Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_)
  simpa using mul_mem (inv_mem hh) hhb

omit [Finite Γ] in
theorem lcal_sup_eq (hB : IsMulCommutative B) (hBH : B ≤ Subgroup.normalizer (H : Set Γ)) :
    lcal (H ⊔ B) = lcal H := by
  ext J
  refine ⟨fun hJ => L69.mem_lcal_of_mem_lcal_sup hB hBH hJ, fun hJ => ?_⟩
  have hXn : H ⊔ B ≤ Subgroup.normalizer (H : Set Γ) := sup_le Subgroup.le_normalizer hBH
  exact T515ab.mem_lcal_of_isSubnormal hJ le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXn).isSubnormal

theorem sol_sup_eq_bot (hBH : B ≤ Subgroup.normalizer (H : Set Γ)) (hsol : sol H = ⊥)
    (hH : ∀ x ∈ H, ∀ J ∈ lcal H, x ∈ Subgroup.normalizer (J : Set Γ))
    (hfree : ∀ b ∈ B, b ≠ 1 → ∀ J ∈ lcal H, J.map (MulAut.conj b).toMonoidHom ≠ J)
    (hne : (lcal H).Nonempty) : sol (H ⊔ B) = ⊥ := by
  obtain ⟨J, hJ⟩ := hne
  refine eq_bot_iff.mpr fun s hs => ?_
  obtain ⟨h, hh, b, hb, rfl⟩ := exists_mul_of_mem_sup hBH (sol_le _ hs)
  have hb1 : b = 1 := eq_one_of_mul_mem_normalizer hfree hb hJ (hH h hh J hJ)
    (mem_normalizer_of_forall_commute fun c hc =>
      (L69.commute_of_mem_sol_sup hBH hsol hs (lcal_le hJ hc)).eq.symm)
  subst hb1
  rw [mul_one] at hs ⊢
  have h1 : H ⊓ sol (H ⊔ B) ≤ sol H :=
    SolQuot.inf_le_sol (isSolvable_sol _) (le_sup_left.trans (SolQuot.le_nrm_sol _))
  rw [hsol, le_bot_iff] at h1
  exact h1 ▸ Subgroup.mem_inf.mpr ⟨hh, hs⟩

theorem kOf_sup_eq (hB : IsMulCommutative B) (hBH : B ≤ Subgroup.normalizer (H : Set Γ))
    (hsol : sol H = ⊥) (hsol' : sol (H ⊔ B) = ⊥) : kOf (H ⊔ B) = kOf H := by
  rw [← (isDirectProduct_lcal_kOf hsol').sSup_eq, ← (isDirectProduct_lcal_kOf hsol).sSup_eq,
    lcal_sup_eq hB hBH]

theorem jTilde_sup_eq (hBH : B ≤ Subgroup.normalizer (H : Set Γ)) (hsol : sol H = ⊥)
    (hH : ∀ x ∈ H, ∀ J ∈ lcal H, x ∈ Subgroup.normalizer (J : Set Γ))
    (hfree : ∀ b ∈ B, b ≠ 1 → ∀ J ∈ lcal H, J.map (MulAut.conj b).toMonoidHom ≠ J)
    (hsol' : sol (H ⊔ B) = ⊥) (hB : IsMulCommutative B) {J : Subgroup Γ} (hJ : J ∈ lcal H)
    (hJ' : ∃ J' ∈ lcal H, J' ≠ J) : jTilde (H ⊔ B) J = jTilde H J := by
  have hJX : J ∈ lcal (H ⊔ B) := (lcal_sup_eq hB hBH).symm ▸ hJ
  unfold jTilde
  rw [kOf_inf_centralizer_eq_sSup_diff hsol' hJX, kOf_inf_centralizer_eq_sSup_diff hsol hJ,
    lcal_sup_eq hB hBH]
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ le_sup_left)
  obtain ⟨hxX, hxc⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, b, hb, rfl⟩ := exists_mul_of_mem_sup hBH hxX
  obtain ⟨J', hJ'L, hJ'ne⟩ := hJ'
  have hJ'le : J' ≤ sSup (lcal H \ {J}) := le_sSup ⟨hJ'L, hJ'ne⟩
  have hb1 : b = 1 := eq_one_of_mul_mem_normalizer hfree hb hJ'L (hH h hh J' hJ'L)
    (mem_normalizer_of_forall_commute fun c hc =>
      Subgroup.mem_centralizer_iff.mp hxc c (hJ'le hc))
  subst hb1
  rw [mul_one] at hxc ⊢
  exact Subgroup.mem_inf.mpr ⟨hh, hxc⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T614
