module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot

open AChief

variable {Γ : Type u} [Group Γ] {R Y : Subgroup Γ}

theorem inf_le_sol (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) : Y ⊓ R ≤ sol Y := by
  have hn : (qres R Y hY).ker.Normal := inferInstance
  have hs := isSolvable_ker_qres hR hY
  have h := Nonsolvable.le_solvableRadical hn hs
  have h2 := Subgroup.map_mono (f := Y.subtype) h
  rw [ker_qres, Subgroup.subgroupOf_map_subtype] at h2
  rwa [inf_comm]

theorem le_sol (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) (hRY : R ≤ Y) : R ≤ sol Y :=
  (le_inf hRY le_rfl).trans (inf_le_sol hR hY)

theorem normalizer_le_nrm_sol (G : Subgroup Γ) :
    Subgroup.normalizer (G : Set Γ) ≤ nrm (sol G) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.normalizer (G : Set Γ) → ∀ {x : Γ}, x ∈ sol G →
      g * x * g⁻¹ ∈ sol G := by
    intro g hg x hx
    let φ : MulAut ↥G := G.normalizerMonoidHom ⟨g, hg⟩
    have hφ : ∀ t : G, ((φ t : G) : Γ) = g * t * g⁻¹ := fun t =>
      Subgroup.normalizerMonoidHom_apply_apply_coe G ⟨g, hg⟩ t
    have hchar : (CFSG.solvableRadical ↥G).map φ.toMonoidHom = CFSG.solvableRadical ↥G :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance φ
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨φ t, ?_, (hφ t).symm ▸ rfl⟩
    rw [← hchar]
    exact ⟨t, ht, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hg hx, fun hx => ?_⟩
  have := key (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem le_nrm_sol (G : Subgroup Γ) : G ≤ nrm (sol G) :=
  Subgroup.le_normalizer.trans (normalizer_le_nrm_sol G)

variable [Finite Γ]

theorem sol_qimg (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    sol (qimg R Y) = qimg R (sol Y) := by
  unfold sol
  rw [qimg_map_subtype hY, ← map_solvableRadical (qres_surjective hY) (isSolvable_ker_qres hR hY)]

theorem kOf_qimg (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    kOf (qimg R Y) = qimg R (kOf Y) := by
  unfold kOf
  rw [qimg_map_subtype hY, ← map_oStar (qres_surjective hY) (isSolvable_ker_qres hR hY)]

theorem qimg_mem_mcal_iff (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) {M : Subgroup Γ}
    (hMY : M ≤ Y) (hM : sol Y ≤ M) : qimg R M ∈ mcal (qimg R Y) ↔ M ∈ mcal Y := by
  have hρ := qres_surjective hY
  have hk := isSolvable_ker_qres hR hY
  constructor
  · rintro ⟨-, -, h3⟩
    refine ⟨hMY, hM, ?_⟩
    rw [subgroupOf_qimg hY hMY] at h3
    exact (map_mk'_mem_lcalOf_iff hρ hk _).mp h3
  · rintro ⟨-, -, h3⟩
    refine ⟨qimg_mono hMY, ?_, ?_⟩
    · rw [sol_qimg hR hY]
      exact qimg_mono hM
    · rw [subgroupOf_qimg hY hMY]
      exact (map_mk'_mem_lcalOf_iff hρ hk _).mpr h3

theorem exists_mem_mcal_qimg_eq (hR : Group.IsSolvable R) (hY : Y ≤ nrm R)
    {M' : Subgroup (QG R)} (hM' : M' ∈ mcal (qimg R Y)) :
    ∃ M ∈ mcal Y, qimg R M = M' := by
  have hM'Y := hM'.1
  have hsolM' := hM'.2.1
  have hMY : Y ⊓ qpre R M' ≤ Y := inf_le_left
  have hMN : Y ⊓ qpre R M' ≤ nrm R := hMY.trans hY
  have himg : qimg R (Y ⊓ qpre R M') = M' := by
    refine le_antisymm ((qimg_le_iff hMN).mpr inf_le_right) fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R Y z).mp (hM'Y hz)
    exact (mem_qimg_iff R _ _).mpr ⟨y, ⟨hy, mem_qpre_iff.mpr ⟨y.2, hz⟩⟩, rfl⟩
  have hsol : sol Y ≤ Y ⊓ qpre R M' := by
    refine le_inf (sol_le Y) ((qimg_le_iff ((sol_le Y).trans hY)).mp ?_)
    rw [← sol_qimg hR hY]
    exact hsolM'
  refine ⟨Y ⊓ qpre R M', ?_, himg⟩
  rw [← qimg_mem_mcal_iff hR hY hMY hsol, himg]
  exact hM'

omit [Finite Γ] in
theorem injOn_mcal (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) : Set.InjOn (qimg R) (mcal Y) := by
  have key : ∀ {M₁ M₂ : Subgroup Γ}, M₁ ∈ mcal Y → M₂ ∈ mcal Y → qimg R M₁ ≤ qimg R M₂ →
      M₁ ≤ M₂ := by
    intro M₁ M₂ h₁ h₂ h x hx
    have hxY : x ∈ Y := h₁.1 hx
    refine mem_of_qmap_mem_qimg h₂.1 ((inf_le_sol hR hY).trans h₂.2.1) (z := ⟨x, hY hxY⟩) hxY ?_
    exact h ((mem_qimg_iff R M₁ _).mpr ⟨⟨x, hY hxY⟩, hx, rfl⟩)
  intro M₁ hM₁ M₂ hM₂ h
  exact le_antisymm (key hM₁ hM₂ h.le) (key hM₂ hM₁ h.ge)

theorem bijOn_mcal (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    Set.BijOn (qimg R) (mcal Y) (mcal (qimg R Y)) :=
  ⟨fun _ hM => (qimg_mem_mcal_iff hR hY hM.1 hM.2.1).mpr hM, injOn_mcal hR hY,
    fun _ hM' => by
      obtain ⟨M, hM, rfl⟩ := exists_mem_mcal_qimg_eq hR hY hM'
      exact ⟨M, hM, rfl⟩⟩

theorem bijOn_ltilde (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    Set.BijOn (qimg R) (ltilde Y) (ltilde (qimg R Y)) := by
  by_cases hs : Group.IsSolvable Y
  · have hs' : Group.IsSolvable (qimg R Y) := (isSolvable_qimg_iff hR hY).mpr hs
    have h1 : ltilde Y = {Y} := by
      ext M
      simp [ltilde, hs]
    have h2 : ltilde (qimg R Y) = {qimg R Y} := by
      ext M
      simp [ltilde, hs']
    rw [h1, h2]
    exact Set.bijOn_singleton.mpr rfl
  · have hs' : ¬ Group.IsSolvable (qimg R Y) := fun h => hs ((isSolvable_qimg_iff hR hY).mp h)
    have h1 : ltilde Y = mcal Y := by
      ext M
      simp [ltilde, hs]
    have h2 : ltilde (qimg R Y) = mcal (qimg R Y) := by
      ext M
      simp [ltilde, hs']
    rw [h1, h2]
    exact bijOn_mcal hR hY

omit [Finite Γ] in
private theorem mem_khat_iff {X : Subgroup Γ} {x : Γ} :
    x ∈ khat X ↔ x ∈ X ∧ ∀ M ∈ ltilde X, x ∈ Subgroup.normalizer (M : Set Γ) := by
  simp [khat, Subgroup.mem_inf, Subgroup.mem_iInf]

omit [Finite Γ] in
theorem le_of_mem_ltilde (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) {M : Subgroup Γ}
    (hM : M ∈ ltilde Y) : M ≤ Y ∧ Y ⊓ R ≤ M := by
  rcases hM with ⟨-, rfl⟩ | ⟨-, hM⟩
  · exact ⟨le_rfl, inf_le_left⟩
  · exact ⟨hM.1, (inf_le_sol hR hY).trans hM.2.1⟩

theorem mem_khat_iff_qmap_mem (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) {y : Γ} (hy : y ∈ Y) :
    qmap R ⟨y, hY hy⟩ ∈ khat (qimg R Y) ↔ y ∈ khat Y := by
  rw [mem_khat_iff, mem_khat_iff]
  have hyY : qmap R ⟨y, hY hy⟩ ∈ qimg R Y := (mem_qimg_iff R Y _).mpr ⟨⟨y, hY hy⟩, hy, rfl⟩
  refine ⟨fun ⟨_, h⟩ => ⟨hy, fun M hM => ?_⟩, fun ⟨_, h⟩ => ⟨hyY, fun M' hM' => ?_⟩⟩
  · obtain ⟨hMY, hRM⟩ := le_of_mem_ltilde hR hY hM
    exact (mem_normalizer_qimg_iff hMY hRM hY hy).mp
      (h _ ((bijOn_ltilde hR hY).mapsTo hM))
  · obtain ⟨M, hM, rfl⟩ := (bijOn_ltilde hR hY).surjOn hM'
    obtain ⟨hMY, hRM⟩ := le_of_mem_ltilde hR hY hM
    exact (mem_normalizer_qimg_iff hMY hRM hY hy).mpr (h M hM)

theorem khat_qimg (hR : Group.IsSolvable R) (hY : Y ≤ nrm R) :
    khat (qimg R Y) = qimg R (khat Y) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R Y z).mp (khat_le _ hz)
    exact (mem_qimg_iff R _ _).mpr ⟨y, (mem_khat_iff_qmap_mem hR hY hy).mp hz, rfl⟩
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R _ z).mp hz
    exact (mem_khat_iff_qmap_mem hR hY (khat_le Y hy)).mpr hy

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
