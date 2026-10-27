module

public import CFSG.Quasithin.Background.F918V3SZC1
public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin

open scoped Pointwise commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem sz_L_triv (hV : ∀ w : W, w ^ 2 = 1) {Y T L : Subgroup (MulAut W)} {I : Subgroup W}
    (hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)))
    (hLY : ∀ l ∈ L, ∀ y ∈ Y, l * y = y * l)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hperf : ⁅L, L⁆ = L)
    (hI : I ∈ IrrPlusOn Y (orbSup T I) T)
    (hUL : ∀ l ∈ L, ∀ u ∈ orbSup T I, l u ∈ orbSup T I) :
    ∀ l ∈ L, ∀ u ∈ orbSup T I, l u * u⁻¹ ∈ fixV Y := by
  have hIU : I ≤ orbSup T I := le_orbSup T I
  have hLs : L ≤ stabSub (orbSup T I) := fun l hl u =>
    ⟨fun h => by simpa using hUL l⁻¹ (L.inv_mem hl) _ h, fun h => hUL l hl u h⟩
  have hT's : L ⊔ T ≤ stabSub (orbSup T I) := sup_le hLs (le_stabSub_orbSup T I)
  have hW : ∀ t ∈ L ⊔ T, ∀ w ∈ orbSup T I, t • w ∈ orbSup T I := fun t ht w hw =>
    ((hT's ht) w).2 hw
  have hLcent : L ≤ Subgroup.centralizer (Y : Set (MulAut W)) := fun l hl =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hLY l hl y hy).symm
  have hnorm : L ⊔ T ≤ Subgroup.normalizer (Y : Set (MulAut W)) :=
    sup_le (hLcent.trans (Subgroup.centralizer_le_normalizer _)) hTY
  have hsup : (⨆ y ∈ L ⊔ T, y • I) = orbSup T I := by
    refine le_antisymm (iSup₂_le fun y hy => ?_) ?_
    · rintro _ hx
      obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact hW y hy s (hIU hs)
    · rw [orbSup_eq_biSup_smul]
      exact iSup₂_le fun y hy => le_iSup₂_of_le y (Subgroup.mem_sup_right hy) le_rfl
  have hI' : I ∈ IrrPlusOn Y (orbSup T I) (L ⊔ T) := by
    refine ⟨hI.1, ?_⟩
    rw [hsup]
    have h := hI.2
    rwa [← orbSup_eq_biSup_smul] at h
  have hlI : ∀ l ∈ L, l • I = I := fun l hl =>
    (forall_smul_eq_iff_mem_irrPlusOn hnorm hW hI.1).mpr hI' l
      ⟨Subgroup.mem_sup_left hl, iso_tilde_smul_of_commute hnorm hW (Subgroup.mem_sup_left hl)
        (hLY l hl) I⟩
  have hLI : ∀ l ∈ L, ∀ x ∈ I, l x ∈ I := fun l hl x hx => by
    have h2 : l • x ∈ l • I := Subgroup.smul_mem_pointwise_smul x l I hx
    rw [hlI l hl] at h2
    exact h2
  have hI1 : ∀ l ∈ L, ∀ x ∈ I, l x * x⁻¹ ∈ fixV Y :=
    sz_trivial_mod_fix hV hI.1.2 hperf (fun d hd l hl => (hLY l hl d hd).symm) hLI
  intro l hl
  let f : W →* W := MonoidHom.mk' (fun u => l u * u⁻¹) fun a b => by
    simp only [map_mul, mul_inv_rev]
    ac_rfl
  have hf : orbSup T I ≤ (fixV Y).comap f := by
    refine orbSup_le fun t ht => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hl' : t⁻¹ * l * t⁻¹⁻¹ ∈ L := hTL t⁻¹ (T.inv_mem ht) l hl
    have h5 := hI1 _ hl' y hy
    have hfixt : ∀ v ∈ fixV Y, t v ∈ fixV Y := by
      intro v hv y' hy'
      have h6 := hv _ (inv_conj_mem_of_mem_normalizer (hTY ht) hy')
      calc y' (t v) = t ((t⁻¹ * y' * t) v) := by simp [MulAut.mul_apply]
        _ = t v := by rw [h6]
    have e : l (t y) * (t y)⁻¹ = t ((t⁻¹ * l * t⁻¹⁻¹) y * y⁻¹) := by
      simp [MulAut.mul_apply]
    rw [Subgroup.mem_comap]
    show l (t y) * (t y)⁻¹ ∈ fixV Y
    rw [e]
    exact hfixt _ h5
  intro u hu
  exact hf hu

end CFSG.Quasithin
