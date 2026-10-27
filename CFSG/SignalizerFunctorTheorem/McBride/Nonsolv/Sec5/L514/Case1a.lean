module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.FixedPoint
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514Aux

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isSolvable_projX
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) : Group.IsSolvable (projX G A J X) := by
  have hAG := h.normalizes
  have hle : projX G A J X ≤ G :=
    (projX_le_orbitClosure G A J X).trans ((orbitClosure_le_kOf hAG hsol hJ.1).trans (kOf_le G))
  refine isSolvable_of_inf_centralizer_eq_bot h.prime h.elemAbelian
    (fun a ha => mem_normalizer_projX_of_mem hAG hsol hJ.1 hAX ha) (hypB_of_le h.hypB hle) ?_
  rw [← hbot]
  ext y
  simp only [Subgroup.mem_inf, smear]
  exact ⟨fun ⟨hy1, hy2⟩ => ⟨hy1, projX_le_orbitClosure G A J X hy1, hy2⟩,
    fun ⟨hy1, _, hy2⟩ => ⟨hy1, hy2⟩⟩

theorem projIn_projX_eq_bot
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) :
    projIn (conjOrbit A J) J (projX G A J X) = ⊥ := by
  have hAG := h.normalizes
  have hL := isDirectProduct_conjOrbit hAG hJ.1
  have hJΩ := self_mem_conjOrbit A J
  have hdp := hL.isDirectPair hJΩ
  refine eq_bot_of_isSolvable_of_normalized h hJ (projIn_le J _)
    (isSolvable_proj hdp (projX_le_orbitClosure G A J X) (isSolvable_projX h hAX hsol hJ hbot)) ?_
  intro z hz
  rw [← projIn_centralizer_eq hL (fun a ha K hK => map_conj_mem_conjOrbit hK ha) hJΩ] at hz
  obtain ⟨hzJ, l, hl, hzl⟩ := (mem_proj_iff hdp.commute).mp hz
  exact mem_normalizer_proj hdp hzJ hl
    (mem_normalizer_projX_of_mem_smear hAG hsol hJ.1 hDX hzl)

theorem projX_eq_bot
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) : projX G A J X = ⊥ := by
  have hAG := h.normalizes
  have hL := isDirectProduct_conjOrbit hAG hJ.1
  have hJΩ := self_mem_conjOrbit A J
  have hper : ∀ a ∈ A, ∀ K ∈ conjOrbit A J, K.map (MulAut.conj a).toMonoidHom ∈ conjOrbit A J :=
    fun a ha K hK => map_conj_mem_conjOrbit hK ha
  have h1 := projIn_projX_eq_bot h hDX hAX hsol hJ hbot
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ orbitClosure J A := projX_le_orbitClosure G A J X hx
  have key : (⟨x, hxL⟩ : orbitClosure J A) = 1 := by
    apply hL.ext_coord
    intro J' hJ'
    rw [map_one]
    obtain ⟨a, ha, rfl⟩ := hJ'
    have hy : a⁻¹ * x * a ∈ projX G A J X := by
      have := (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_projX_of_mem hAG hsol hJ.1 hAX (inv_mem ha)) x).mp hx
      simpa using this
    have hyL : a⁻¹ * x * a ∈ orbitClosure J A := projX_le_orbitClosure G A J X hy
    have hco : ((hL.coord hJΩ ⟨a⁻¹ * x * a, hyL⟩ : J) : Γ) ∈
        projIn (conjOrbit A J) J (projX G A J X) :=
      (hL.mem_projIn_iff hJΩ).mpr ⟨⟨a⁻¹ * x * a, hyL⟩, hy, rfl⟩
    rw [h1, Subgroup.mem_bot] at hco
    have h2 := hL.coord_conj (hper a ha) hJΩ hyL
    have hx' : (⟨a * (a⁻¹ * x * a) * a⁻¹, hL.conj_mem (hper a ha) hyL⟩ : orbitClosure J A) =
        ⟨x, hxL⟩ := Subtype.ext (by group)
    rw [hx', hco] at h2
    apply Subtype.ext
    simpa using h2
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val key)

theorem inf_kOf_le_outsideOrbit
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) : X ⊓ kOf G ≤ outsideOrbit G A J := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit h.normalizes hsol hJ.1
  have hproj := projX_eq_bot h hDX hAX hsol hJ hbot
  intro x hx
  obtain ⟨l, hl, m, hm, hlm⟩ := exists_mul_of_isDirectPair hdp (Subgroup.mem_inf.mp hx).2
  have hl' : l ∈ projX G A J X := (mem_proj_iff hdp.commute).mpr ⟨hl, m, hm, hlm ▸ hx⟩
  rw [hproj, Subgroup.mem_bot] at hl'
  subst hl'
  simpa [← hlm] using hm

theorem commutator_mem_outsideOrbit
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hXG : X ≤ G) (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) {c x : Γ} (hc : c ∈ smear J A) (hx : x ∈ X) :
    ⁅c, x⁆ ∈ outsideOrbit G A J := by
  have hAG := h.normalizes
  refine inf_kOf_le_outsideOrbit h hDX hAX hsol hJ hbot (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have hcX := mem_normalizer_of_mem_smear hAG hsol hJ.1 hDX hc
    have := (Subgroup.mem_normalizer_iff.mp hcX x).mp hx
    exact mul_mem this (inv_mem hx)
  · have hcK : c ∈ kOf G := orbitClosure_le_kOf hAG hsol hJ.1 (smear_le_orbitClosure J A hc)
    have hxK := (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_kOf hsol (Subgroup.le_normalizer (hXG hx))) c⁻¹).mp (inv_mem hcK)
    have : ⁅c, x⁆ = c * (x * c⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hcK hxK

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
