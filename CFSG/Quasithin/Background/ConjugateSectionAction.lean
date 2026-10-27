module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.Quasithin.Background.MovingSectionRank

public section

namespace CFSG.Quasithin.ConjugateSection

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type*} [CommGroup W]

theorem map_mem_irrSet_map_conj {H : Subgroup (MulAut W)} {φ : MulAut W} {I : Subgroup W}
    (hI : I ∈ irrSet H) :
    I.map φ.toMonoidHom ∈ irrSet (H.map (MulAut.conj φ).toMonoidHom) := by
  obtain ⟨hcomm, hlt, hstabI, hstabN, hmax⟩ := hI
  have hfix : fixV (H.map (MulAut.conj φ).toMonoidHom) = (fixV H).map φ.toMonoidHom :=
    fixV_map_conj_eq H φ
  have hinf : I.map φ.toMonoidHom ⊓ fixV (H.map (MulAut.conj φ).toMonoidHom) =
      (I ⊓ fixV H).map φ.toMonoidHom := by
    rw [hfix, Subgroup.map_inf_eq _ _ _ φ.injective]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [s15_Core_commSub_map_conj, hcomm]
  · rw [hinf]
    exact (Subgroup.map_lt_map_iff_of_injective φ.injective).mpr hlt
  · intro x hx u hu
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr
      ⟨h i, hstabI h hh i hi, by simp [MulAut.conj_apply, MulAut.mul_apply]⟩
  · rw [hinf]
    intro x hx u hu
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr
      ⟨h i, hstabN h hh i hi, by simp [MulAut.conj_apply, MulAut.mul_apply]⟩
  · intro J hJstab hNJ hJI
    have hJ'stab : StableUnder H (J.map (φ⁻¹).toMonoidHom) := by
      intro h hh j hj
      obtain ⟨j0, hj0, rfl⟩ := Subgroup.mem_map.mp hj
      refine Subgroup.mem_map.mpr ⟨(MulAut.conj φ h) j0, ?_, ?_⟩
      · exact hJstab _ (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩) j0 hj0
      · simp [MulAut.conj_apply, MulAut.mul_apply]
    have hcomp_id : (φ.toMonoidHom).comp (φ⁻¹).toMonoidHom = MonoidHom.id W := by
      ext x
      simp
    have hmap_id : ∀ K : Subgroup W, (K.map (φ⁻¹).toMonoidHom).map φ.toMonoidHom = K := by
      intro K
      rw [Subgroup.map_map, hcomp_id, Subgroup.map_id]
    have hNJ' : I ⊓ fixV H ≤ J.map (φ⁻¹).toMonoidHom := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨φ x, hNJ ?_, by simp⟩
      exact ⟨Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩,
        by rw [hfix]; exact Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩⟩
    have hJ'I : J.map (φ⁻¹).toMonoidHom ≤ I := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨i, hi, hji⟩ := Subgroup.mem_map.mp (hJI hj)
      rw [← hji]
      simpa using hi
    rcases hmax (J.map (φ⁻¹).toMonoidHom) hJ'stab hNJ' hJ'I with h | h
    · left
      have hmap : J = (I ⊓ fixV H).map φ.toMonoidHom := by
        calc J = (J.map (φ⁻¹).toMonoidHom).map φ.toMonoidHom := (hmap_id J).symm
          _ = (I ⊓ fixV H).map φ.toMonoidHom := by rw [h]
      rw [hmap, hinf]
    · right
      have hmap : J = I.map φ.toMonoidHom := by
        calc J = (J.map (φ⁻¹).toMonoidHom).map φ.toMonoidHom := (hmap_id J).symm
          _ = I.map φ.toMonoidHom := by rw [h]
      exact hmap

theorem mQuot_map_conj (U Z : Subgroup W) (φ : MulAut W) :
    E3.mQuot (U.map φ.toMonoidHom) (Z.map φ.toMonoidHom) = E3.mQuot U Z := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_map_map_of_injective Z U φ.injective]

theorem mQuot_commSub_top_inf_fixV_map_conj (H : Subgroup (MulAut W)) (φ : MulAut W) :
    E3.mQuot (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom))
      (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
        fixV (H.map (MulAut.conj φ).toMonoidHom)) =
    E3.mQuot (commSub (⊤ : Subgroup W) H) (commSub (⊤ : Subgroup W) H ⊓ fixV H) := by
  rw [s15_Infra_commSub_top_map_conj, fixV_map_conj_eq,
    ← Subgroup.map_inf_eq _ _ _ φ.injective, mQuot_map_conj]

theorem commSub_commSub_map_conj_eq_bot_of_ne {A H : Subgroup (MulAut W)}
    (hcross : ∀ g ∈ A, g ∉ Subgroup.normalizer (H : Set (MulAut W)) →
      commSub (commSub (⊤ : Subgroup W) H) (H.map (MulAut.conj g).toMonoidHom) = ⊥)
    {a b : MulAut W} (ha : a ∈ A) (hb : b ∈ A)
    (hne : H.map (MulAut.conj a).toMonoidHom ≠ H.map (MulAut.conj b).toMonoidHom) :
    commSub (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom))
      (H.map (MulAut.conj b).toMonoidHom) = ⊥ := by
  set g : MulAut W := a⁻¹ * b with hg
  have hgA : g ∈ A := A.mul_mem (A.inv_mem ha) hb
  have hcompeq : (MulAut.conj a).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (a * g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hgnot : g ∉ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro hgn
    have hgmap : H.map (MulAut.conj g).toMonoidHom = H :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgn
    have hab : a * g = b := by rw [hg]; group
    have hHb : H.map (MulAut.conj b).toMonoidHom =
        (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      rw [← hab, ← hcompeq, Subgroup.map_map]
    exact hne (by rw [hHb, hgmap])
  have hbot := hcross g hgA hgnot
  have hmap := s15_Core_commSub_map_conj (commSub (⊤ : Subgroup W) H)
    (H.map (MulAut.conj g).toMonoidHom) a
  rw [hbot, Subgroup.map_bot, ← s15_Infra_commSub_top_map_conj] at hmap
  have hab : a * g = b := by rw [hg]; group
  have hHb : H.map (MulAut.conj b).toMonoidHom =
      (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [← hab, ← hcompeq, Subgroup.map_map]
  rwa [← hHb] at hmap

theorem commSub_le_fixV_of_conj_ne {A H : Subgroup (MulAut W)}
    (hcross : ∀ g ∈ A, g ∉ Subgroup.normalizer (H : Set (MulAut W)) →
      commSub (commSub (⊤ : Subgroup W) H) (H.map (MulAut.conj g).toMonoidHom) = ⊥)
    {a b : MulAut W} (ha : a ∈ A) (hb : b ∈ A)
    (hne : H.map (MulAut.conj a).toMonoidHom ≠ H.map (MulAut.conj b).toMonoidHom) :
    commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom) ≤
      fixV (H.map (MulAut.conj b).toMonoidHom) ∧
    commSub (⊤ : Subgroup W) (H.map (MulAut.conj b).toMonoidHom) ≤
      fixV (H.map (MulAut.conj a).toMonoidHom) :=
  ⟨commSub_eq_bot_iff.mp (commSub_commSub_map_conj_eq_bot_of_ne hcross ha hb hne),
    commSub_eq_bot_iff.mp (commSub_commSub_map_conj_eq_bot_of_ne hcross hb ha hne.symm)⟩

section Finite

variable [Finite W]

theorem mQuot_le_rk_of_not_mem_normalizer {A H : Subgroup (MulAut W)}
    (hcross : ∀ g ∈ A, g ∉ Subgroup.normalizer (H : Set (MulAut W)) →
      commSub (commSub (⊤ : Subgroup W) H) (H.map (MulAut.conj g).toMonoidHom) = ⊥)
    {a t : MulAut W} (ha : a ∈ A) (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (hnot : t ∉ Subgroup.normalizer
      (H.map (MulAut.conj a).toMonoidHom : Set (MulAut W))) :
    E3.mQuot (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom))
      (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom) ⊓
        fixV (H.map (MulAut.conj a).toMonoidHom)) ≤
    rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  have hta : t * a ∈ A := A.mul_mem htA ha
  have hcompeq : (MulAut.conj t).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (t * a)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hne : H.map (MulAut.conj a).toMonoidHom ≠
      H.map (MulAut.conj (t * a)).toMonoidHom := by
    intro h
    apply hnot
    have h' : (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        H.map (MulAut.conj (t * a)).toMonoidHom := by
      rw [← hcompeq, Subgroup.map_map]
    have h'' : (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        H.map (MulAut.conj a).toMonoidHom := by
      rw [h']
      exact h.symm
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr h''
  have hbot := commSub_commSub_map_conj_eq_bot_of_ne hcross ha hta hne
  have hgt : H.map (MulAut.conj (t * a)).toMonoidHom =
      (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [← hcompeq, Subgroup.map_map]
  rw [hgt] at hbot
  have hle : commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom) ≤
      (fixV (H.map (MulAut.conj a).toMonoidHom)).map t.toMonoidHom := by
    rw [← fixV_map_conj_eq]
    exact commSub_eq_bot_iff.mp hbot
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have htt : ∀ w : W, (MulEquiv.toMonoidHom t) ((MulEquiv.toMonoidHom t) w) = w := by
    intro w
    have h2 : (t * t) w = w := by
      rw [ht2']
      rfl
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply] using h2
  have hmap_le : (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom)).map
      t.toMonoidHom ≤ fixV (H.map (MulAut.conj a).toMonoidHom) := by
    rintro v ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (hle hu)
    rw [htt w]
    exact hw
  exact mQuot_le_rk_commSub_of_inf_map_le t inf_le_left
    (inf_le_inf_left _ hmap_le)

end Finite

theorem exists_not_fixed_of_iSup_eq_top {ι : Type*} {U : ι → Subgroup W} {t : MulAut W}
    (hspan : (⨆ i, U i) = ⊤) (ht1 : t ≠ 1) :
    ∃ i, ∃ u ∈ U i, t u ≠ u := by
  by_contra h
  push Not at h
  have htop : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers t) := by
    rw [← hspan]
    refine iSup_le fun i => ?_
    intro u hu
    rw [mem_fixV_zpowers_iff_apply]
    exact h i u hu
  have hfix : ∀ w : W, t w = w := fun w =>
    mem_fixV_zpowers_iff_apply.mp (htop (Subgroup.mem_top w))
  exact ht1 (MulEquiv.ext hfix)

end CFSG.Quasithin.ConjugateSection
