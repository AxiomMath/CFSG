module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD8b

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_sum_proj9 (V : Fin 9 → ZMod 3) :
    ∑ j : Fin 8, hdRo7SmAAux_proj9 V j = ∑ k : Fin 9, V k := by
  have hcast : ∑ j : Fin 8, V (Fin.castSucc j) = (∑ k : Fin 9, V k) - V (Fin.last 8) := by
    rw [Fin.sum_univ_castSucc (n := 8) (f := V)]
    abel
  calc ∑ j : Fin 8, hdRo7SmAAux_proj9 V j
      = ∑ j : Fin 8, (V (Fin.castSucc j) - V (Fin.last 8)) := by
        apply Finset.sum_congr rfl; intro j _
        rw [hdRo7SmAAux_proj9_apply]
    _ = (∑ j : Fin 8, V (Fin.castSucc j)) - ∑ j : Fin 8, V (Fin.last 8) :=
        Finset.sum_sub_distrib (fun j => V (Fin.castSucc j)) (fun _ => V (Fin.last 8))
    _ = ((∑ k : Fin 9, V k) - V (Fin.last 8)) - ∑ j : Fin 8, V (Fin.last 8) := by
        rw [hcast]
    _ = (∑ k : Fin 9, V k) - V (Fin.last 8) - (8 : ZMod 3) * V (Fin.last 8) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = ∑ k : Fin 9, V k := by
        ring_nf
        conv_lhs => rw [show (9 : ZMod 3) = 0 by decide]
        simp

theorem hdRo7SmAAux_q9_sum_zero (σ : Equiv.Perm (Fin 9)) (W : SMV 8)
    (hW : ∑ j, W j = 0) : ∑ j, hdRo7SmAAux_q9 σ W j = 0 := by
  have h1 : hdRo7SmAAux_q9 σ W =
      hdRo7SmAAux_proj9 (coordPerm 3 8 σ (hdRo7SmAAux_ext9 W)) := rfl
  rw [h1]
  rw [hdRo7SmAAux_sum_proj9]
  simp only [coordPerm_apply]
  rw [Equiv.sum_comp σ.symm (hdRo7SmAAux_ext9 W)]
  rw [Fin.sum_univ_castSucc]
  have hsum : ∑ i : Fin 8, hdRo7SmAAux_ext9 W i.castSucc = ∑ i : Fin 8, W i := by
    apply Finset.sum_congr rfl; intro i _
    simp [hdRo7SmAAux_ext9_apply, i.isLt]
  rw [hsum, hW]
  simp

@[expose] noncomputable def hdRo7SmAAux_d9 (σ : Equiv.Perm (Fin 9)) : SMGL 7 where
  toFun v := hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ (hdRo7SmAAux_delEmbed v))
  invFun v := hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ⁻¹ (hdRo7SmAAux_delEmbed v))
  map_add' := by intro a b; simp only [map_add]
  map_smul' := by intro c v; simp only [map_smul, RingHom.id_apply]
  left_inv := by
    intro v
    calc hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ⁻¹
            (hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
              (hdRo7SmAAux_q9 σ (hdRo7SmAAux_delEmbed v)))))
        = hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ⁻¹
            (hdRo7SmAAux_q9 σ (hdRo7SmAAux_delEmbed v))) := by
          rw [hdRo7SmAAux_delEmbed_proj _
            (hdRo7SmAAux_q9_sum_zero σ _ (hdRo7SmAAux_delEmbed_sum_zero v))]
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_q9 (σ⁻¹ * σ) (hdRo7SmAAux_delEmbed v)) := by
          show hdRo7SmAAux_delProj ((hdRo7SmAAux_q9Hom σ⁻¹)
            ((hdRo7SmAAux_q9Hom σ) (hdRo7SmAAux_delEmbed v))) =
            hdRo7SmAAux_delProj (hdRo7SmAAux_q9Hom (σ⁻¹ * σ) (hdRo7SmAAux_delEmbed v))
          rw [map_mul]
          rfl
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v) := by
          show hdRo7SmAAux_delProj ((hdRo7SmAAux_q9Hom (σ⁻¹ * σ)) (hdRo7SmAAux_delEmbed v)) =
            hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v)
          rw [inv_mul_cancel, map_one]
          rfl
      _ = v := hdRo7SmAAux_delProj_embed v
  right_inv := by
    intro v
    calc hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ
            (hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
              (hdRo7SmAAux_q9 σ⁻¹ (hdRo7SmAAux_delEmbed v)))))
        = hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ
            (hdRo7SmAAux_q9 σ⁻¹ (hdRo7SmAAux_delEmbed v))) := by
          rw [hdRo7SmAAux_delEmbed_proj _
            (hdRo7SmAAux_q9_sum_zero σ⁻¹ _ (hdRo7SmAAux_delEmbed_sum_zero v))]
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_q9 (σ * σ⁻¹) (hdRo7SmAAux_delEmbed v)) := by
          show hdRo7SmAAux_delProj ((hdRo7SmAAux_q9Hom σ)
            ((hdRo7SmAAux_q9Hom σ⁻¹) (hdRo7SmAAux_delEmbed v))) =
            hdRo7SmAAux_delProj (hdRo7SmAAux_q9Hom (σ * σ⁻¹) (hdRo7SmAAux_delEmbed v))
          rw [map_mul]
          rfl
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v) := by
          show hdRo7SmAAux_delProj ((hdRo7SmAAux_q9Hom (σ * σ⁻¹)) (hdRo7SmAAux_delEmbed v)) =
            hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v)
          rw [mul_inv_cancel, map_one]
          rfl
      _ = v := hdRo7SmAAux_delProj_embed v

@[expose] noncomputable def hdRo7SmAAux_d9Hom : Equiv.Perm (Fin 9) →* SMGL 7 where
  toFun := hdRo7SmAAux_d9
  map_one' := by
    ext v i
    show hdRo7SmAAux_delProj ((hdRo7SmAAux_q9Hom 1) (hdRo7SmAAux_delEmbed v)) i = v i
    rw [map_one]
    simp
  map_mul' σ τ := by
    apply LinearEquiv.ext; intro v
    change hdRo7SmAAux_delProj (hdRo7SmAAux_q9 (σ * τ) (hdRo7SmAAux_delEmbed v)) =
      hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ
        (hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
          (hdRo7SmAAux_q9 τ (hdRo7SmAAux_delEmbed v)))))
    rw [hdRo7SmAAux_delEmbed_proj _
      (hdRo7SmAAux_q9_sum_zero τ _ (hdRo7SmAAux_delEmbed_sum_zero v))]
    show hdRo7SmAAux_delProj (hdRo7SmAAux_q9Hom (σ * τ) (hdRo7SmAAux_delEmbed v)) =
      hdRo7SmAAux_delProj ((hdRo7SmAAux_q9Hom σ) ((hdRo7SmAAux_q9Hom τ)
        (hdRo7SmAAux_delEmbed v)))
    rw [map_mul]
    rfl

theorem hdRo7SmAAux_d9Hom_swap_inner (k : Fin 6) :
    hdRo7SmAAux_d9Hom
        (Equiv.swap (Fin.castSucc (Fin.castSucc (Fin.castSucc k)))
          (Fin.succ (Fin.castSucc (Fin.castSucc k)))) =
      hdRo7SmAAux_permLin 7 (Equiv.swap (Fin.castSucc k) (Fin.succ k)) := by
  apply LinearEquiv.ext; intro v; ext i
  fin_cases k <;> fin_cases i <;>
    simp [hdRo7SmAAux_d9Hom, hdRo7SmAAux_d9, hdRo7SmAAux_delProj, hdRo7SmAAux_delEmbed,
      hdRo7SmAAux_permLin_apply, LinearMap.pi_apply, Equiv.swap_apply_def, hdRo7SmAAux_q9]

end CFSG.StandardType.HdRo7SU.Small
