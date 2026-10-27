module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin11

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2a

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

@[expose] def suborbit (D E : Subgroup (Perm (Fin 5))) : Set (Subgroup (Perm (Fin 5))) :=
  {F | ∃ d ∈ D, F = cj d E}

@[expose] noncomputable def suborbitSize (D E : Subgroup (Perm (Fin 5))) : ℕ :=
  (suborbit D E).ncard

theorem suborbit_cj (g : Perm (Fin 5)) (D E : Subgroup (Perm (Fin 5))) :
    suborbit (cj g D) (cj g E) = cj g '' suborbit D E := by
  ext F
  constructor
  · rintro ⟨d', hd', rfl⟩
    refine ⟨cj (g⁻¹ * d' * g) E, ⟨_, mem_cj.mp hd', rfl⟩, ?_⟩
    rw [← cj_mul, ← cj_mul]; congr 1; group
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨g * d * g⁻¹, mem_cj_conj.mpr hd, ?_⟩
    rw [← cj_mul, ← cj_mul]; congr 1; group

theorem suborbitSize_cj (g : Perm (Fin 5)) (D E : Subgroup (Perm (Fin 5))) :
    suborbitSize (cj g D) (cj g E) = suborbitSize D E := by
  unfold suborbitSize
  rw [suborbit_cj, Set.ncard_image_of_injective _ (cj_injective g)]

theorem eq_of_zc_eq {D E : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hE : Nat.card E = 8)
    (h : zc D = zc E) : D = E := by
  ext x
  rw [mem_sylow_iff_comm hD (isCentInv_zc hD) x, mem_sylow_iff_comm hE (isCentInv_zc hE) x, h]

theorem suborbitSize_std (r : Perm (Fin 5)) :
    suborbitSize S5Syl (cj r S5Syl) =
      (S5SylF.image fun d => d * (r * zStd * r⁻¹) * d⁻¹).card := by
  have hE : Nat.card (cj r S5Syl) = 8 := card_cj_S5Syl r
  have hz : zc (cj r S5Syl) = r * zStd * r⁻¹ := by rw [zc_cj card_S5Syl, zc_std]
  have hinj : Set.InjOn zc (suborbit S5Syl (cj r S5Syl)) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩ h
    exact eq_of_zc_eq (by rw [card_cj]; exact hE) (by rw [card_cj]; exact hE) h
  have himg : zc '' suborbit S5Syl (cj r S5Syl) =
      ((S5SylF.image fun d => d * (r * zStd * r⁻¹) * d⁻¹ : Finset (Perm (Fin 5))) :
        Set (Perm (Fin 5))) := by
    ext y
    simp only [Set.mem_image, Finset.coe_image, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨d, (mem_S5Syl_iff d).mp hd, by rw [zc_cj hE, hz]⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨_, ⟨d, (mem_S5Syl_iff d).mpr hd, rfl⟩, by rw [zc_cj hE, hz]⟩
  unfold suborbitSize
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset]

private theorem orbit_card_1 :
    (S5SylF.image fun d =>
      d * ((1 : Perm (Fin 5)) * zStd * (1 : Perm (Fin 5))⁻¹) * d⁻¹).card = 1 := by
  unfold zStd; decide +kernel

private theorem orbit_card_r2 :
    (S5SylF.image fun d => d * (r2 * zStd * r2⁻¹) * d⁻¹).card = 2 := by
  unfold zStd r2; decide +kernel

private theorem orbit_card_r4 :
    (S5SylF.image fun d => d * (r4 * zStd * r4⁻¹) * d⁻¹).card = 4 := by
  unfold zStd r4; decide +kernel

private theorem orbit_card_r8 :
    (S5SylF.image fun d => d * (r8 * zStd * r8⁻¹) * d⁻¹).card = 8 := by
  unfold zStd r8; decide +kernel

theorem suborbitSize_std_self : suborbitSize S5Syl S5Syl = 1 := by
  have := suborbitSize_std 1
  rw [cj_one] at this
  rw [this]; exact orbit_card_1

theorem suborbitSize_std_r2 : suborbitSize S5Syl (cj r2 S5Syl) = 2 := by
  rw [suborbitSize_std]; exact orbit_card_r2

theorem suborbitSize_std_r4 : suborbitSize S5Syl (cj r4 S5Syl) = 4 := by
  rw [suborbitSize_std]; exact orbit_card_r4

theorem suborbitSize_std_r8 : suborbitSize S5Syl (cj r8 S5Syl) = 8 := by
  rw [suborbitSize_std]; exact orbit_card_r8

end CFSG.Quasithin.F53.Stellmacher.S35.F2a
