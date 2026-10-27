module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixNormA
public import CFSG.LargeExtraspecial.S12TriG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13.U3.S6Out CFSG.LargeExtraspecial.S12Tri Equiv

private def s1611e3_conjHom :
    Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6)) :=
  MulAut.conjNormal (H := alternatingGroup (Fin 6))

private def s1611e3_inn : Subgroup (MulAut ↥(alternatingGroup (Fin 6))) :=
  s1611e3_conjHom.range

private theorem s1611e3_conjHom_apply (s : Perm (Fin 6))
    (a : ↥(alternatingGroup (Fin 6))) :
    ((s1611e3_conjHom s a : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
      s * (a : Perm (Fin 6)) * s⁻¹ :=
  MulAut.conjNormal_apply s a

private theorem s1611e3_sixAlphaA_coe (a : ↥(alternatingGroup (Fin 6))) :
    ((sixAlphaA a : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
      sixAlpha (a : Perm (Fin 6)) := rfl

private def s1611e3_alphaAut : MulAut ↥(alternatingGroup (Fin 6)) where
  toFun := sixAlphaA
  invFun := sixAlphaA
  left_inv := fun a => by
    apply Subtype.ext
    rw [s1611e3_sixAlphaA_coe, s1611e3_sixAlphaA_coe, sixAlpha_sixAlpha]
  right_inv := fun a => by
    apply Subtype.ext
    rw [s1611e3_sixAlphaA_coe, s1611e3_sixAlphaA_coe, sixAlpha_sixAlpha]
  map_mul' := sixAlphaA.map_mul

private theorem s1611e3_alphaAut_coe (a : ↥(alternatingGroup (Fin 6))) :
    ((s1611e3_alphaAut a : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
      sixAlpha (a : Perm (Fin 6)) :=
  s1611e3_sixAlphaA_coe a

private theorem s1611e3_alphaAut_mul_self :
    s1611e3_alphaAut * s1611e3_alphaAut = 1 := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change ((s1611e3_alphaAut (s1611e3_alphaAut a) : ↥(alternatingGroup (Fin 6))) :
      Perm (Fin 6)) = (a : Perm (Fin 6))
  rw [s1611e3_alphaAut_coe, s1611e3_alphaAut_coe, sixAlpha_sixAlpha]

private def s1611e3_threeCycle : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem s1611e3_threeCycle_support :
    (s1611e3_threeCycle : Perm (Fin 6)).support.card = 3 := by
  decide +kernel

private theorem s1611e3_alphaAut_threeCycle_support :
    ((s1611e3_alphaAut s1611e3_threeCycle : ↥(alternatingGroup (Fin 6))) :
      Perm (Fin 6)).support.card = 6 := by
  rw [s1611e3_alphaAut_coe]
  decide +kernel

private theorem s1611e3_centralizer_a6ab :
    ∀ s : Perm (Fin 6), s * a6a * s⁻¹ = a6a →
      s * a6b * s⁻¹ = a6b → s = 1 := by
  decide +kernel

private theorem s1611e3_conjNormal_eq_one
    (s : Perm (Fin 6)) (h : s1611e3_conjHom s = 1) : s = 1 := by
  have hgen : Subgroup.closure ({a6a, a6b} : Set (Perm (Fin 6))) =
      alternatingGroup (Fin 6) := closure_a6
  have hAmem : a6a ∈ alternatingGroup (Fin 6) := by
    rw [← hgen]; exact Subgroup.subset_closure (by simp)
  have hBmem : a6b ∈ alternatingGroup (Fin 6) := by
    rw [← hgen]; exact Subgroup.subset_closure (by simp)
  have ha : s * a6a * s⁻¹ = a6a := by
    have h1 := congrArg (fun f : MulAut ↥(alternatingGroup (Fin 6)) =>
      f ⟨a6a, hAmem⟩) h
    have h2 := congrArg (fun b : ↥(alternatingGroup (Fin 6)) =>
      (b : Perm (Fin 6))) h1
    simpa [s1611e3_conjHom_apply] using h2
  have hb : s * a6b * s⁻¹ = a6b := by
    have h1 := congrArg (fun f : MulAut ↥(alternatingGroup (Fin 6)) =>
      f ⟨a6b, hBmem⟩) h
    have h2 := congrArg (fun b : ↥(alternatingGroup (Fin 6)) =>
      (b : Perm (Fin 6))) h1
    simpa [s1611e3_conjHom_apply] using h2
  exact s1611e3_centralizer_a6ab s ha hb

private theorem s1611e3_conjNormal_injective :
    Function.Injective s1611e3_conjHom := by
  intro s t h
  have h1 : s1611e3_conjHom (s * t⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : s * t⁻¹ = 1 := s1611e3_conjNormal_eq_one (s * t⁻¹) h1
  calc s = s * t⁻¹ * t := by group
    _ = t := by rw [h2, one_mul]

private theorem s1611e3_inn_card :
    Nat.card s1611e3_inn = 720 := by
  have hPerm : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hsurj : Function.Surjective (fun s : Perm (Fin 6) =>
      (⟨s1611e3_conjHom s, ⟨s, rfl⟩⟩ : s1611e3_inn)) := by
    rintro ⟨y, hy⟩
    rw [s1611e3_inn, MonoidHom.mem_range] at hy
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s, Subtype.ext rfl⟩
  have hinj : Function.Injective (fun s : Perm (Fin 6) =>
      (⟨s1611e3_conjHom s, ⟨s, rfl⟩⟩ : s1611e3_inn)) := by
    intro s t h
    exact s1611e3_conjNormal_injective (Subtype.ext_iff.mp h)
  have hle : Nat.card s1611e3_inn ≤ Nat.card (Perm (Fin 6)) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hge : Nat.card (Perm (Fin 6)) ≤ Nat.card s1611e3_inn :=
    Nat.card_le_card_of_injective _ hinj
  omega

private theorem s1611e3_alphaAut_notin : s1611e3_alphaAut ∉ s1611e3_inn := by
  intro h
  rw [s1611e3_inn, MonoidHom.mem_range] at h
  obtain ⟨s, hs⟩ := h
  have hc := congrArg (fun f : MulAut ↥(alternatingGroup (Fin 6)) =>
    ((f s1611e3_threeCycle : ↥(alternatingGroup (Fin 6))) :
      Perm (Fin 6)).support.card) hs
  rw [s1611e3_alphaAut_threeCycle_support] at hc
  rw [s1611e3_conjHom_apply, Equiv.Perm.card_support_conj,
    s1611e3_threeCycle_support] at hc
  exact absurd hc (by norm_num)

theorem s1611e3_six_aut_cosets
    (ε : MulAut ↥(alternatingGroup (Fin 6))) :
    (∃ s : Perm (Fin 6), ∀ a : ↥(alternatingGroup (Fin 6)),
      ((ε a : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = s * (a : Perm (Fin 6)) * s⁻¹) ∨
    (∃ s : Perm (Fin 6), ∀ a : ↥(alternatingGroup (Fin 6)),
      ((ε a : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
        s * ((sixAlphaA a : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) * s⁻¹) := by
  have hcard : Nat.card s1611e3_inn = 720 := s1611e3_inn_card
  have hαself : s1611e3_alphaAut * s1611e3_alphaAut = 1 := s1611e3_alphaAut_mul_self
  have hαnotin : s1611e3_alphaAut ∉ s1611e3_inn := s1611e3_alphaAut_notin
  have hne_top : s1611e3_inn ≠ ⊤ := by
    intro htop
    exact hαnotin (htop ▸ Subgroup.mem_top s1611e3_alphaAut)
  have hle : s1611e3_inn.index ≤ 2 := by
    have hcm := Subgroup.card_mul_index (H := s1611e3_inn)
    rw [hcard] at hcm
    have hcardAut : Nat.card (MulAut ↥(alternatingGroup (Fin 6))) ≤ 1440 :=
      card_mulAut_alternatingGroup_six_le
    omega
  have hpos : 0 < s1611e3_inn.index := by
    have hcm := Subgroup.card_mul_index (H := s1611e3_inn)
    rw [hcard] at hcm
    have hposAut : 0 < Nat.card (MulAut ↥(alternatingGroup (Fin 6))) := Nat.card_pos
    omega
  have hne1 : s1611e3_inn.index ≠ 1 := fun h1 =>
    hne_top (Subgroup.index_eq_one.mp h1)
  have hidx : s1611e3_inn.index = 2 := by omega
  by_cases hε : ε ∈ s1611e3_inn
  · left
    rw [s1611e3_inn, MonoidHom.mem_range] at hε
    obtain ⟨s, hs⟩ := hε
    refine ⟨s, fun a => ?_⟩
    rw [← hs, s1611e3_conjHom_apply]
  · right
    have hmem : ε * s1611e3_alphaAut ∈ s1611e3_inn := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact ⟨fun h => absurd h hε, fun h => absurd h hαnotin⟩
    rw [s1611e3_inn, MonoidHom.mem_range] at hmem
    obtain ⟨s, hs⟩ := hmem
    refine ⟨s, fun a => ?_⟩
    have heps : ε = s1611e3_conjHom s * s1611e3_alphaAut := by
      calc ε = (ε * s1611e3_alphaAut) * s1611e3_alphaAut := by
            rw [mul_assoc, hαself, mul_one]
        _ = s1611e3_conjHom s * s1611e3_alphaAut := by rw [← hs]
    rw [heps, MulAut.mul_apply, s1611e3_conjHom_apply]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
