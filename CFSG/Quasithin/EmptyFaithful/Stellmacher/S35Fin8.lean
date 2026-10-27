module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin7

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem inf_cenW_commW_std {d : Perm (Fin 5)} (hd : d ∈ S5T) (h1 : d ≠ 1) (hz : d ≠ zStd) :
    S5Syl ⊓ cenW (commW orth (Subgroup.zpowers d) ⊤) = Subgroup.zpowers d := by
  have hdd : ∀ d ∈ S5TF, d * d = 1 := by decide +kernel
  have h : ∀ d ∈ S5TF, d ≠ 1 → d ≠ zStd → ∀ x : Perm (Fin 5),
      (x ∈ S5SylF ∧ ∀ w ∈ commF d, orth.act x w = w) ↔ (x = 1 ∨ x = d) := by
    unfold commF zStd; decide +kernel
  have hdT : d ∈ S5TF := (mem_S5T_iff d).mp hd
  ext x
  rw [Subgroup.mem_inf, mem_cenW, mem_zpowers_iff_of_mul_self (hdd d hdT), ← h d hdT h1 hz x,
    mem_S5Syl_iff]
  simp only [mem_commW_zpowers_iff]

theorem inf_cenW_commW_zpowers {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {d : Perm (Fin 5)} (hd : d ∈ Tsub D) (h1 : d ≠ 1)
    (hdz : d ≠ z) : D ⊓ cenW (commW orth (Subgroup.zpowers d) ⊤) = Subgroup.zpowers d := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hz' := isCentInv_cj_std_iff.mp hz
  obtain ⟨d0, rfl⟩ : ∃ d0, d = g * d0 * g⁻¹ := ⟨g⁻¹ * d * g, by group⟩
  have hd0 : d0 ∈ S5T := by
    rw [← cj_Tsub, Tsub_std] at hd
    exact mem_cj_conj.mp hd
  have h1' : d0 ≠ 1 := by
    intro h; apply h1; rw [h]; group
  have hz0 : d0 ≠ zStd := by
    intro h; apply hdz; rw [h, hz']
  rw [commW_zpowers_cj, cenW_mp, ← cj_inf, inf_cenW_commW_std hd0 h1' hz0, cj_zpowers]

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
