module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsADel

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_delEmbed_single (i : Fin 7) (c : ZMod 3) :
    hdRo7SmAAux_delEmbed (Pi.single i c : SMV 7) =
      Pi.single (Fin.castSucc i) c - Pi.single (Fin.last 7) c := by
  ext j
  fin_cases i <;> fin_cases j <;>
    (simp [hdRo7SmAAux_delEmbed, hdRo7SmAAux_delEmbed_last, hdRo7SmAAux_delEmbed_castSucc,
      Pi.single_apply, Finset.sum_eq_single] <;> ring)

theorem hdRo7SmAAux_permLin_single (σ : Equiv.Perm (Fin 8)) (a : Fin 8) (c : ZMod 3) :
    hdRo7SmAAux_permLin 8 σ (Pi.single a c) = Pi.single (σ a) c := by
  ext j
  simp only [hdRo7SmAAux_permLin_apply, Pi.single_apply]
  by_cases h : j = σ a
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hh
    exact h (by rw [← hh, Equiv.apply_symm_apply])

@[expose] noncomputable def hdRo7SmAAux_d8 (σ : Equiv.Perm (Fin 8)) : SMGL 7 where
  toFun v := hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v))
  invFun v := hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ⁻¹ (hdRo7SmAAux_delEmbed v))
  map_add' := by intro a b; simp only [map_add]
  map_smul' := by intro c v; simp only [map_smul, RingHom.id_apply]
  left_inv := by
    intro v
    calc hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ⁻¹
            (hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
              (hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v)))))
        = hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ⁻¹
            (hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v))) := by
          rw [hdRo7SmAAux_delEmbed_proj _
            (hdRo7SmAAux_permLin_sum_zero σ _ (hdRo7SmAAux_delEmbed_sum_zero v))]
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 (σ⁻¹ * σ) (hdRo7SmAAux_delEmbed v)) := by
          simp [map_mul]
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v) := by simp
      _ = v := hdRo7SmAAux_delProj_embed v
  right_inv := by
    intro v
    calc hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ
            (hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
              (hdRo7SmAAux_permLin 8 σ⁻¹ (hdRo7SmAAux_delEmbed v)))))
        = hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ
            (hdRo7SmAAux_permLin 8 σ⁻¹ (hdRo7SmAAux_delEmbed v))) := by
          rw [hdRo7SmAAux_delEmbed_proj _
            (hdRo7SmAAux_permLin_sum_zero σ⁻¹ _ (hdRo7SmAAux_delEmbed_sum_zero v))]
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 (σ * σ⁻¹) (hdRo7SmAAux_delEmbed v)) := by
          simp [map_mul]
      _ = hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v) := by simp
      _ = v := hdRo7SmAAux_delProj_embed v

@[expose] noncomputable def hdRo7SmAAux_d8Hom : Equiv.Perm (Fin 8) →* SMGL 7 where
  toFun := hdRo7SmAAux_d8
  map_one' := by
    ext v i; simp [hdRo7SmAAux_d8]
  map_mul' σ τ := by
    apply LinearEquiv.ext; intro v
    change hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 (σ * τ) (hdRo7SmAAux_delEmbed v)) =
      hdRo7SmAAux_delProj (hdRo7SmAAux_permLin 8 σ
        (hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
          (hdRo7SmAAux_permLin 8 τ (hdRo7SmAAux_delEmbed v)))))
    rw [hdRo7SmAAux_delEmbed_proj _
      (hdRo7SmAAux_permLin_sum_zero τ _ (hdRo7SmAAux_delEmbed_sum_zero v))]
    rw [map_mul]
    rfl

theorem hdRo7SmAAux_d8Hom_injective : Function.Injective hdRo7SmAAux_d8Hom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ v : SMV 7,
      hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v) = hdRo7SmAAux_delEmbed v := by
    intro v
    have h1 : hdRo7SmAAux_delProj
        (hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v)) = v := by
      have h2 := congrArg (fun f : SMGL 7 => f v) hσ
      simpa [hdRo7SmAAux_d8Hom, hdRo7SmAAux_d8] using h2
    have h3 : hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v)
        = hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj
          (hdRo7SmAAux_permLin 8 σ (hdRo7SmAAux_delEmbed v))) :=
      (hdRo7SmAAux_delEmbed_proj _
        (hdRo7SmAAux_permLin_sum_zero σ _ (hdRo7SmAAux_delEmbed_sum_zero v))).symm
    rw [h3, h1]
  have hfix_cast : ∀ i : Fin 7, σ (Fin.castSucc i) = Fin.castSucc i := by
    intro i
    have h3 := congrFun (hfix (Pi.single i (1 : ZMod 3))) (Fin.castSucc i)
    rw [hdRo7SmAAux_delEmbed_single, map_sub, hdRo7SmAAux_permLin_single,
      hdRo7SmAAux_permLin_single] at h3
    simp only [Pi.sub_apply, Pi.single_apply] at h3
    by_cases h : σ (Fin.castSucc i) = Fin.castSucc i
    · exact h
    · exfalso
      rw [if_neg (fun hh => h hh.symm)] at h3
      by_cases h5 : (Fin.castSucc i : Fin 8) = σ (Fin.last 7)
      · rw [if_pos h5, if_neg (Fin.castSucc_ne_last i)] at h3
        exact absurd h3 (show ¬ ((0 : ZMod 3) - 1 = 1) by decide)
      · rw [if_neg h5, if_neg (Fin.castSucc_ne_last i)] at h3
        exact absurd h3 (show ¬ ((0 : ZMod 3) - 0 = 1) by decide)
  apply Equiv.ext
  intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · exact hfix_cast i
  · rcases Fin.eq_castSucc_or_eq_last (σ (Fin.last 7)) with ⟨m, hm⟩ | hlast
    · exfalso
      have h1 : σ (Fin.castSucc m) = σ (Fin.last 7) := by rw [hfix_cast m, hm]
      exact (Fin.castSucc_ne_last m) (σ.injective h1)
    · exact hlast

theorem hdRo7SmAAux_d8Hom_swap_inner (k : Fin 6) :
    hdRo7SmAAux_d8Hom
        (Equiv.swap (Fin.castSucc (Fin.castSucc k)) (Fin.succ (Fin.castSucc k))) =
      hdRo7SmAAux_permLin 7 (Equiv.swap (Fin.castSucc k) (Fin.succ k)) := by
  apply LinearEquiv.ext; intro v; ext i
  fin_cases k <;> fin_cases i <;>
    simp [hdRo7SmAAux_d8Hom, hdRo7SmAAux_d8, hdRo7SmAAux_delProj, hdRo7SmAAux_delEmbed,
      hdRo7SmAAux_permLin_apply, LinearMap.pi_apply, Equiv.swap_apply_def]

end CFSG.StandardType.HdRo7SU.Small
