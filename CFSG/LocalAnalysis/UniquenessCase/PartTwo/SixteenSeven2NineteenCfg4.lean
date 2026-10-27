module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Unif

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_cfg4_map_eq_of_le_fixV {Y : Subgroup W} {t : MulAut W}
    (h : Y ≤ fixV (Subgroup.zpowers t)) : Y.map t.toMonoidHom = Y := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    show t v ∈ Y
    rw [(mem_fixV_zpowers_iff_apply).mp (h hv)]
    exact hv
  · intro hy
    exact ⟨y, hy, (mem_fixV_zpowers_iff_apply).mp (h hy)⟩

private theorem s16c167_cfg4_cent_of_fix {X : Subgroup (MulAut W)} {Z : Subgroup W}
    {Y₁ Y₂ Y₃ Y₄ : Subgroup W} (hT : conjSubs X Z \ {Y₁, Y₂} = {Y₃, Y₄}) {t : MulAut W}
    (h₁ : Y₁ ≤ fixV (Subgroup.zpowers t)) (h₂ : Y₂ ≤ fixV (Subgroup.zpowers t))
    (h₃ : Y₃ ≤ fixV (Subgroup.zpowers t)) (h₄ : Y₄ ≤ fixV (Subgroup.zpowers t)) :
    ∀ Y ∈ conjSubs X Z, t ∈ centSub Y := by
  intro Y hY
  rw [mem_centSub]
  intro u hu
  by_cases hY₁ : Y = Y₁
  · rw [hY₁] at hu
    exact (mem_fixV_zpowers_iff_apply).mp (h₁ hu)
  by_cases hY₂ : Y = Y₂
  · rw [hY₂] at hu
    exact (mem_fixV_zpowers_iff_apply).mp (h₂ hu)
  · have hYT : Y ∈ conjSubs X Z \ {Y₁, Y₂} := by
      refine ⟨hY, ?_⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hY₁ h
      · exact hY₂ h
    rw [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hYT
    rcases hYT with rfl | rfl
    · exact (mem_fixV_zpowers_iff_apply).mp (h₃ hu)
    · exact (mem_fixV_zpowers_iff_apply).mp (h₄ hu)

private theorem s16c167_cfg4_swap {X L : Subgroup (MulAut W)} {Z : Subgroup W}
    (F : Cfg4Setting X L Z) {Y₁ Y₂ Y₃ Y₄ : Subgroup W}
    (hY₁ : Y₁ ∈ conjSubs X Z) (hY₂ : Y₂ ∈ conjSubs X Z)
    (hY₃ : Y₃ ∈ conjSubs X Z) (hY₄ : Y₄ ∈ conjSubs X Z)
    (hne : Y₁ ≠ Y₂) (hT : conjSubs X Z \ {Y₁, Y₂} = {Y₃, Y₄}) (h34 : Y₃ ≠ Y₄)
    {t : MulAut W} (htX : t ∈ X) (ht : t * t = 1) (htne : t ≠ 1)
    (h₁ : Y₁ ≤ fixV (Subgroup.zpowers t)) (h₂ : Y₂ ≤ fixV (Subgroup.zpowers t)) :
    Y₃.map t.toMonoidHom = Y₄ ∧ Y₄.map t.toMonoidHom = Y₃ := by
  have hm₁ : Y₁.map t.toMonoidHom = Y₁ := s16c167_cfg4_map_eq_of_le_fixV h₁
  have hm₂ : Y₂.map t.toMonoidHom = Y₂ := s16c167_cfg4_map_eq_of_le_fixV h₂
  have hY₃T : Y₃ ∈ conjSubs X Z \ {Y₁, Y₂} := by rw [hT]; simp
  have hY₄T : Y₄ ∈ conjSubs X Z \ {Y₁, Y₂} := by rw [hT]; simp
  have hY₃₁ : Y₃ ≠ Y₁ := fun h => hY₃T.2 (by rw [h]; simp)
  have hY₄₁ : Y₄ ≠ Y₁ := fun h => hY₄T.2 (by rw [h]; simp)
  have hnotin : ∀ Y ∈ conjSubs X Z \ {Y₁, Y₂},
      Y.map t.toMonoidHom ∈ ({Y₃, Y₄} : Set (Subgroup W)) := by
    intro Y hY
    have hmap : Y.map t.toMonoidHom ∈ conjSubs X Z := s16c167_cfg4_map_mem htX hY.1
    have hnot : Y.map t.toMonoidHom ∉ ({Y₁, Y₂} : Set (Subgroup W)) := by
      intro hmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · have hYeq : Y = Y₁ := Subgroup.map_injective t.injective (by rw [h, hm₁])
        exact hY.2 (by rw [hYeq]; simp)
      · have hYeq : Y = Y₂ := Subgroup.map_injective t.injective (by rw [h, hm₂])
        exact hY.2 (by rw [hYeq]; simp)
    have hmemT : Y.map t.toMonoidHom ∈ conjSubs X Z \ {Y₁, Y₂} := ⟨hmap, hnot⟩
    rwa [hT] at hmemT
  have hmY₃ : Y₃.map t.toMonoidHom ∈ ({Y₃, Y₄} : Set (Subgroup W)) := hnotin Y₃ hY₃T
  have hkey : Y₃.map t.toMonoidHom = Y₃ → False := by
    intro hfix
    have hmY₄ : Y₄.map t.toMonoidHom = Y₄ := by
      have hmem := hnotin Y₄ hY₄T
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact absurd (Subgroup.map_injective t.injective (by rw [h, hfix])) h34
      · exact h
    have hcent : ∀ Y ∈ conjSubs X Z, t ∈ centSub Y :=
      s16c167_cfg4_cent_of_fix hT h₁ h₂
        ((s16c167_cfg4_unif F htX ht hY₁ hY₃ hY₃₁.symm hm₁ hfix).mp h₁)
        ((s16c167_cfg4_unif F htX ht hY₁ hY₄ hY₄₁.symm hm₁ hmY₄).mp h₁)
    exact htne (s16c167_cfg4_faithful F hcent)
  have h3 : Y₃.map t.toMonoidHom = Y₄ := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmY₃
    rcases hmY₃ with h | h
    · exact absurd h hkey
    · exact h
  have h4 : Y₄.map t.toMonoidHom = Y₃ := by
    have hmem := hnotin Y₄ hY₄T
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact h
    · exfalso
      have hmaps : (Y₃.map t.toMonoidHom).map t.toMonoidHom = Y₃.map t.toMonoidHom := by
        rw [h3, h]
      exact hkey (Subgroup.map_injective t.injective hmaps)
  exact ⟨h3, h4⟩

theorem s16c167_cfg4_uniq19 {X L : Subgroup (MulAut W)} {Z : Subgroup W} (F : Cfg4Setting X L Z) :
    Uniq19 X {I | ∃ Y₁ ∈ conjSubs X Z, ∃ Y₂ ∈ conjSubs X Z, Y₁ ≠ Y₂ ∧ I = Y₁ ⊔ Y₂} := by
  intro t₁ htX₁ t₂ htX₂ ht₁ ht₂ hcomm htne₁ htne₂ I hI hf₁ hf₂
  obtain ⟨Y₁, hY₁, Y₂, hY₂, hne, hIeq⟩ := hI
  have hle₁₁ : Y₁ ≤ fixV (Subgroup.zpowers t₁) := le_sup_left.trans (hIeq ▸ hf₁)
  have hle₂₁ : Y₂ ≤ fixV (Subgroup.zpowers t₁) := le_sup_right.trans (hIeq ▸ hf₁)
  have hle₁₂ : Y₁ ≤ fixV (Subgroup.zpowers t₂) := le_sup_left.trans (hIeq ▸ hf₂)
  have hle₂₂ : Y₂ ≤ fixV (Subgroup.zpowers t₂) := le_sup_right.trans (hIeq ▸ hf₂)
  have hpair : ({Y₁, Y₂} : Set (Subgroup W)) ⊆ conjSubs X Z := by
    intro Y hY
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    rcases hY with rfl | rfl
    · exact hY₁
    · exact hY₂
  have hTcard : (conjSubs X Z \ {Y₁, Y₂}).ncard = 2 := by
    rw [Set.ncard_sdiff hpair, F.ncard_eq, Set.ncard_pair hne]
  obtain ⟨Y₃, Y₄, h34, hT⟩ := Set.ncard_eq_two.mp hTcard
  have hY₃T : Y₃ ∈ conjSubs X Z \ {Y₁, Y₂} := by rw [hT]; simp
  have hY₄T : Y₄ ∈ conjSubs X Z \ {Y₁, Y₂} := by rw [hT]; simp
  have hY₃ : Y₃ ∈ conjSubs X Z := hY₃T.1
  have hY₄ : Y₄ ∈ conjSubs X Z := hY₄T.1
  have hY₃₁ : Y₃ ≠ Y₁ := fun h => hY₃T.2 (by rw [h]; simp)
  have hY₄₁ : Y₄ ≠ Y₁ := fun h => hY₄T.2 (by rw [h]; simp)
  have swap₁ := s16c167_cfg4_swap F hY₁ hY₂ hY₃ hY₄ hne hT h34 htX₁ ht₁ htne₁ hle₁₁ hle₂₁
  have swap₂ := s16c167_cfg4_swap F hY₁ hY₂ hY₃ hY₄ hne hT h34 htX₂ ht₂ htne₂ hle₁₂ hle₂₂
  let s : MulAut W := t₁ * t₂
  have hsX : s ∈ X := X.mul_mem htX₁ htX₂
  have hs2 : s * s = 1 := by
    show (t₁ * t₂) * (t₁ * t₂) = 1
    calc (t₁ * t₂) * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by group
      _ = t₁ * (t₁ * t₂) * t₂ := by rw [hcomm]
      _ = (t₁ * t₁) * (t₂ * t₂) := by group
      _ = 1 := by rw [ht₁, ht₂, one_mul]
  have hY1s : Y₁ ≤ fixV (Subgroup.zpowers s) := by
    intro y hy
    rw [mem_fixV_zpowers_iff_apply]
    show (t₁ * t₂) y = y
    rw [MulAut.mul_apply, (mem_fixV_zpowers_iff_apply).mp (hle₁₂ hy),
      (mem_fixV_zpowers_iff_apply).mp (hle₁₁ hy)]
  have hY2s : Y₂ ≤ fixV (Subgroup.zpowers s) := by
    intro y hy
    rw [mem_fixV_zpowers_iff_apply]
    show (t₁ * t₂) y = y
    rw [MulAut.mul_apply, (mem_fixV_zpowers_iff_apply).mp (hle₂₂ hy),
      (mem_fixV_zpowers_iff_apply).mp (hle₂₁ hy)]
  have hm₁s : Y₁.map s.toMonoidHom = Y₁ := s16c167_cfg4_map_eq_of_le_fixV hY1s
  have hY3s : Y₃.map s.toMonoidHom = Y₃ := by
    have hmul : (Y₃.map t₂.toMonoidHom).map t₁.toMonoidHom =
        Y₃.map (t₁ * t₂).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [swap₂.1, swap₁.2] at hmul
    change Y₃.map (t₁ * t₂).toMonoidHom = Y₃
    exact hmul.symm
  have hY4s : Y₄.map s.toMonoidHom = Y₄ := by
    have hmul : (Y₄.map t₂.toMonoidHom).map t₁.toMonoidHom =
        Y₄.map (t₁ * t₂).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [swap₂.2, swap₁.1] at hmul
    change Y₄.map (t₁ * t₂).toMonoidHom = Y₄
    exact hmul.symm
  have hY₃fs : Y₃ ≤ fixV (Subgroup.zpowers s) :=
    (s16c167_cfg4_unif F hsX hs2 hY₁ hY₃ hY₃₁.symm hm₁s hY3s).mp hY1s
  have hY₄fs : Y₄ ≤ fixV (Subgroup.zpowers s) :=
    (s16c167_cfg4_unif F hsX hs2 hY₁ hY₄ hY₄₁.symm hm₁s hY4s).mp hY1s
  have hcent : ∀ Y ∈ conjSubs X Z, s ∈ centSub Y :=
    s16c167_cfg4_cent_of_fix hT hY1s hY2s hY₃fs hY₄fs
  have hs1 : s = 1 := s16c167_cfg4_faithful F hcent
  have hmul : t₁ * t₂ = 1 := by simpa [s] using hs1
  calc t₁ = t₁ * 1 := by rw [mul_one]
    _ = t₁ * (t₂ * t₂) := by rw [ht₂]
    _ = (t₁ * t₂) * t₂ := by rw [mul_assoc]
    _ = 1 * t₂ := by rw [hmul]
    _ = t₂ := by rw [one_mul]

theorem s16c167_cfg4_two19 {X L : Subgroup (MulAut W)} {Z : Subgroup W} (F : Cfg4Setting X L Z) :
    Two19 X := by
  intro E hEX hE2 hEc hrk
  exact s16c167_two_bad_four (𝒴 := conjSubs X Z)
    ⟨F.sq, hE2, hEc, F.ncard_eq, fun Y hY => by rw [s16c167_cfg4_rk_mem hY, F.rk_eq],
      F.indep, F.sup_eq, fun e he Y hY => s16c167_cfg4_map_mem (hEX he) hY⟩ hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
