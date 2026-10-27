module

public import CFSG.Quasithin.Vol2.Ch10SecABasicL0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem eq_of_le_of_le_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {X : Subgroup G} (hTX : T ≤ X) (hX : X ≤ fsuL0 T L ⊔ T)
    (hL : L ≤ X ∨ CFSG.conjugate L t ≤ X) : X = fsuL0 T L ⊔ T := by
  have htX := hTX ht
  have hL' : L ≤ X := by
    rcases hL with h | h
    · exact h
    · intro l hl
      have h1 : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hl
      have := X.mul_mem (X.mul_mem htX (h h1)) (X.inv_mem htX)
      simpa [mul_assoc] using this
  refine le_antisymm hX (sup_le ?_ hTX)
  rw [fsuL0_eq_sup h37 h38 hyp ht htn]
  refine sup_le hL' fun y hy => ?_
  rw [mem_conjugate_iff] at hy
  have := X.mul_mem (X.mul_mem (X.inv_mem htX) (hL' hy)) htX
  simpa [mul_assoc] using this

theorem normal_comap_inl {A B : Type*} [Group A] [Group B] {Y : Subgroup (A × B)}
    (hY : Y.map (MonoidHom.fst A B) = ⊤) : (Y.comap (MonoidHom.inl A B)).Normal := by
  refine ⟨fun a ha b => ?_⟩
  obtain ⟨y, hy, hyb⟩ := (Subgroup.mem_map).mp (hY ▸ Subgroup.mem_top b)
  rw [Subgroup.mem_comap] at ha ⊢
  have h := Y.mul_mem (Y.mul_mem hy ha) (Y.inv_mem hy)
  convert h using 1
  ext
  · simp [← hyb]
  · simp

theorem normal_comap_inr {A B : Type*} [Group A] [Group B] {Y : Subgroup (A × B)}
    (hY : Y.map (MonoidHom.snd A B) = ⊤) : (Y.comap (MonoidHom.inr A B)).Normal := by
  refine ⟨fun a ha b => ?_⟩
  obtain ⟨y, hy, hyb⟩ := (Subgroup.mem_map).mp (hY ▸ Subgroup.mem_top b)
  rw [Subgroup.mem_comap] at ha ⊢
  have h := Y.mul_mem (Y.mul_mem hy ha) (Y.inv_mem hy)
  convert h using 1
  ext
  · simp
  · simp [← hyb]

theorem mem_normalizer_prod {A B : Type*} [Group A] [Group B] {S₁ : Subgroup A}
    {S₂ : Subgroup B} {y : A × B} (h₁ : y.1 ∈ Subgroup.normalizer (S₁ : Set A))
    (h₂ : y.2 ∈ Subgroup.normalizer (S₂ : Set B)) :
    y ∈ Subgroup.normalizer ((S₁.prod S₂ : Subgroup (A × B)) : Set (A × B)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro p
  simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  exact and_congr ((Subgroup.mem_normalizer_iff.mp h₁) p.1)
    ((Subgroup.mem_normalizer_iff.mp h₂) p.2)

end CFSG.Quasithin.Vol2.Ch10.SecA
