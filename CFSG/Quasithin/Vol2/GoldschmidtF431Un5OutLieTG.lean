module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTF
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieV
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique CFSG.LocalAnalysis.EvenBN.U5 CFSG.RankThree.PartOne.U5K
  CFSG.Quasithin.H13.F431.Un

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5tg_fieldP_innM (σ : K ≃+* K) (g : hypSU hK 2 1) :
    fieldP hK σ * innM hK g * (fieldP hK σ)⁻¹ = innM hK (fieldAut hK σ g) := by
  have h := aut5_mul_cj5_mul_inv hK (fieldP hK σ) (hypProj hK 2 1 g)
  rw [fieldP_apply] at h
  exact h

theorem un5tg_comm_z (σ : K ≃+* K) :
    fieldP hK σ * innM hK (z₁SU hK) = innM hK (z₁SU hK) * fieldP hK σ := by
  have h := un5tg_fieldP_innM hK σ (z₁SU hK)
  rw [fieldAut_z₁SU] at h
  calc fieldP hK σ * innM hK (z₁SU hK) =
      fieldP hK σ * innM hK (z₁SU hK) * (fieldP hK σ)⁻¹ * fieldP hK σ := by group
    _ = innM hK (z₁SU hK) * fieldP hK σ := by rw [h]

theorem un5tg_comm_t (σ : K ≃+* K) :
    fieldP hK σ * innM hK (z₂SU hK) = innM hK (z₂SU hK) * fieldP hK σ := by
  have h := un5tg_fieldP_innM hK σ (z₂SU hK)
  rw [fieldAut_z₂SU] at h
  calc fieldP hK σ * innM hK (z₂SU hK) =
      fieldP hK σ * innM hK (z₂SU hK) * (fieldP hK σ)⁻¹ * fieldP hK σ := by group
    _ = innM hK (z₂SU hK) * fieldP hK σ := by rw [h]

theorem un5tg_inf_z {T : Subgroup (MulAut (hypPSU hK 2 1))}
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    T ⊓ Subgroup.centralizer ({innM hK (z₁SU hK)} : Set (MulAut (hypPSU hK 2 1))) = T := by
  refine inf_eq_left.2 fun τ hτ => ?_
  obtain ⟨u, ⟨g, hg, rfl⟩, σ, rfl⟩ := hT τ hτ
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have hgz : innM hK g * innM hK (z₁SU hK) = innM hK (z₁SU hK) * innM hK g := by
    rw [← map_mul, ← map_mul, (ZPsub_commute z₁SU_mem_ZPsub hg).symm]
  calc innM hK g * fieldP hK σ * innM hK (z₁SU hK) =
      innM hK g * (fieldP hK σ * innM hK (z₁SU hK)) := mul_assoc _ _ _
    _ = innM hK g * (innM hK (z₁SU hK) * fieldP hK σ) := by rw [un5tg_comm_z hK σ]
    _ = (innM hK g * innM hK (z₁SU hK)) * fieldP hK σ := (mul_assoc _ _ _).symm
    _ = (innM hK (z₁SU hK) * innM hK g) * fieldP hK σ := by rw [hgz]
    _ = innM hK (z₁SU hK) * (innM hK g * fieldP hK σ) := mul_assoc _ _ _

theorem un5tg_card_Sh : Nat.card (Sh hK) = (2 ^ f) ^ 8 := by
  unfold Sh
  rw [card_map_innM (u5_center_eq_bot hK) Ssub_le_Usub, card_Ssub]

theorem un5tg_lt_card_Uh : (2 ^ f) ^ 4 < Nat.card (Uh hK) := by
  have h1 : 1 < 2 ^ f := hK.one_lt_pow
  have h2 : (2 ^ f) ^ 4 < (2 ^ f) ^ 8 := Nat.pow_lt_pow_right h1 (by norm_num)
  have := CFSG.RankThree.PartOne.U5K.Hyp.finite_mulAut_hyp hK
  have h3 : Nat.card (Sh hK) ≤ Nat.card (Uh hK) := Subgroup.card_le_of_le Sh_le_Uh
  rw [un5tg_card_Sh] at h3
  omega

theorem un5tg_card_Tt {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (_hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    Nat.card (Sh hK) * Nat.card (un5tfFp hK T) ≤
      Nat.card ↥(T ⊓ Subgroup.centralizer
        ({innM hK (z₂SU hK)} : Set (MulAut (hypPSU hK 2 1)))) := by
  have := CFSG.RankThree.PartOne.U5K.Hyp.finite_mulAut_hyp hK
  have hZ := u5_center_eq_bot hK
  have hts : ∀ s ∈ Sh hK, s * innM hK (z₂SU hK) = innM hK (z₂SU hK) * s := fun s hs => by
    have ht : innM hK (z₂SU hK) ∈ zOf (Sh hK) := by
      rw [zOf_Sh hZ]
      exact (un5_V_zt hK).2
    exact (mem_zOf_iff.1 ht).2 s hs
  have hmem : ∀ p : Sh hK × un5tfFp hK T,
      (p.1 : MulAut (hypPSU hK 2 1)) * fieldP hK p.2 ∈ T ⊓ Subgroup.centralizer
        ({innM hK (z₂SU hK)} : Set (MulAut (hypPSU hK 2 1))) := fun p =>
    Subgroup.mem_inf.2 ⟨T.mul_mem (hU (Sh_le_Uh p.1.2)) p.2.2,
      Subgroup.mem_centralizer_singleton_iff.2
        (Commute.mul_left (hts p.1 p.1.2 : Commute _ _)
          (un5tg_comm_t hK p.2 : Commute _ _)).eq⟩
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : Sh hK × un5tfFp hK T => (⟨(p.1 : MulAut (hypPSU hK 2 1)) * fieldP hK p.2, hmem p⟩ :
      ↥(T ⊓ Subgroup.centralizer ({innM hK (z₂SU hK)} : Set (MulAut (hypPSU hK 2 1)))))) ?_
  rintro ⟨s, σ⟩ ⟨s', σ'⟩ e
  obtain ⟨h1, h2⟩ := un5t_decomp_unique hK (Sh_le_Uh s.2) (Sh_le_Uh s'.2) (congrArg Subtype.val e)
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

theorem un5_Tf_lt_z (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (hb : fieldP hK (bar5 hK) ∈ T) :
    Nat.card (spTf T (fieldP hK (bar5 hK))) <
      Nat.card ↥(T ⊓ Subgroup.centralizer ({innM hK (z₁SU hK)} :
        Set (MulAut (hypPSU hK 2 1)))) := by
  have _hf := hf
  have _hb := hb
  have := fld5_finite hK
  rw [un5tg_inf_z hK hT, un5tf_card_Tf hK hU hT, un5tf_card_T hK hU hT]
  exact Nat.mul_lt_mul_of_pos_right (un5tg_lt_card_Uh hK) Nat.card_pos

theorem un5_Tf_lt_t (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (hb : fieldP hK (bar5 hK) ∈ T) :
    Nat.card (spTf T (fieldP hK (bar5 hK))) <
      Nat.card ↥(T ⊓ Subgroup.centralizer ({innM hK (z₂SU hK)} :
        Set (MulAut (hypPSU hK 2 1)))) := by
  have _hf := hf
  have _hb := hb
  have := fld5_finite hK
  have h1 : 1 < 2 ^ f := hK.one_lt_pow
  have h2 := un5tg_card_Tt hK hU hT
  rw [un5tg_card_Sh] at h2
  rw [un5tf_card_Tf hK hU hT]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right h1 (by norm_num))
    Nat.card_pos) h2

end CFSG.Quasithin.H13.F431.Un.OL5
