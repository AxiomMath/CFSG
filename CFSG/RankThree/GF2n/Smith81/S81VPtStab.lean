module

public import CFSG.RankThree.GF2n.Smith81.S81VOrth
public import CFSG.RankThree.GF2n.Smith81.S81UElem

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.Open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem vec_add_self_eq_zero_aux [CharP F 2] (v : Fin 6 → F) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

theorem ptStab_smul_sub_mem (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) {g : SUid σ 6} (hg : g ∈ PtStab σ W)
    (v : Fin 6 → F) : g • v - v ∈ W := by
  refine mem_of_orth hσ hti h3 fun w hw => ?_
  have h1 : herm σ (g • w) (g • v) = herm σ w v := herm_smul_smul (σ := σ) g w v
  rw [(mem_ptStab (σ := σ)).mp hg w hw] at h1
  rw [herm_sub_right, h1, sub_self]

private theorem ptStab_smul_smul_apply_aux (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) {g g' : SUid σ 6} (hg : g ∈ PtStab σ W)
    (hg' : g' ∈ PtStab σ W) (v : Fin 6 → F) : g • (g' • v) = g • v + (g' • v - v) := by
  have hu : g • (g' • v - v) = g' • v - v :=
    (mem_ptStab (σ := σ)).mp hg _ (ptStab_smul_sub_mem hσ hti h3 hg' v)
  calc g • (g' • v) = g • ((g' • v - v) + v) := by rw [sub_add_cancel]
    _ = g • (g' • v - v) + g • v := smul_add _ _ _
    _ = g • v + (g' • v - v) := by rw [hu]; abel

private theorem ptStab_smul_comm_aux (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) {g g' : SUid σ 6} (hg : g ∈ PtStab σ W)
    (hg' : g' ∈ PtStab σ W) (v : Fin 6 → F) : g • (g' • v) = g' • (g • v) := by
  rw [ptStab_smul_smul_apply_aux hσ hti h3 hg hg' v,
    ptStab_smul_smul_apply_aux hσ hti h3 hg' hg v]
  abel

private theorem ptStab_mul_comm_aux (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) {g g' : SUid σ 6} (hg : g ∈ PtStab σ W)
    (hg' : g' ∈ PtStab σ W) : g * g' = g' * g := by
  refine ext_smul (σ := σ) fun v => ?_
  rw [mul_smul, mul_smul]
  exact ptStab_smul_comm_aux hσ hti h3 hg hg' v

private theorem ptStab_mul_self_aux [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {W : Submodule F (Fin 6 → F)} (hti : IsTotIso σ W) (h3 : finrank F W = 3)
    {g : SUid σ 6} (hg : g ∈ PtStab σ W) : g * g = 1 := by
  refine ext_smul (σ := σ) fun v => ?_
  rw [mul_smul, one_smul, ptStab_smul_smul_apply_aux hσ hti h3 hg hg v]
  calc g • v + (g • v - v) = (g • v + g • v) - v := by abel
    _ = v := by
      rw [vec_add_self_eq_zero_aux, zero_sub,
        neg_eq_of_add_eq_zero_left (vec_add_self_eq_zero_aux v)]

theorem ptStab_isElemAbelian [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) :
    IsElemAbelian 2 ((PtStab σ W).map (SUid σ 6).subtype) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨g', hg', hgb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hga, ← hgb]
    show ((g * g' : SUid σ 6) : GL (Fin 6) F) = ((g' * g : SUid σ 6) : GL (Fin 6) F)
    rw [ptStab_mul_comm_aux hσ hti h3 hg hg']
  · obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hx
    rw [← hgx, pow_two]
    show (g : GL (Fin 6) F) * (g : GL (Fin 6) F) = 1
    rw [← Subgroup.coe_mul, ptStab_mul_self_aux hσ hti h3 hg, Subgroup.coe_one]

theorem card_ptStab_le [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {W : Submodule F (Fin 6 → F)} (hti : IsTotIso σ W) (h3 : finrank F W = 3) :
    Nat.card (PtStab σ W) ≤ Nat.card (Fσ σ) ^ 9 := by
  have hE : IsElemAbelian 2 ((PtStab σ W).map (SUid σ 6).subtype) :=
    ptStab_isElemAbelian hσ.invol hti h3
  have hle : (PtStab σ W).map (SUid σ 6).subtype ≤ SUid σ 6 := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have h := card_sq_le_pow_of_isElemAbelian_SUid hσ.exists_ne hE hle
  rw [Subgroup.card_map_of_injective (SUid σ 6).subtype_injective] at h
  rw [← card_Fσ_sq hσ] at h
  have h9 : (Nat.card (Fσ σ) ^ 2) ^ (6 * 6 / 4) = (Nat.card (Fσ σ) ^ 9) ^ 2 := by
    rw [show 6 * 6 / 4 = 9 by norm_num]
    ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp (h.trans_eq h9)

end CFSG.RankThree.GF2n.Smith81.S81V
