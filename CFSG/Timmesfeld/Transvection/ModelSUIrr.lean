module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.Timmesfeld.Transvection.ModelSUTorus
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem exists_addSubgroup_radVec_eq {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (hΘ : SUThetaFacts σ a d T) {R : Subgroup (SU σ m)} (hRU : R ≤ uRad σ a) :
    ∃ S : AddSubgroup (Fin m → F), ∀ w, w ∈ S ↔ ∃ r ∈ R, radVec σ a d r = w :=
  ⟨{ carrier := {w | ∃ r ∈ R, radVec σ a d r = w}
     add_mem' := by
       rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
       exact ⟨r * s, R.mul_mem hr hs, hΘ.mul (hRU hr) (hRU hs)⟩
     zero_mem' := ⟨1, R.one_mem, hΘ.one⟩
     neg_mem' := by
       rintro _ ⟨r, hr, rfl⟩
       exact ⟨r⁻¹, R.inv_mem hr, hΘ.inv (hRU hr)⟩ }, fun _ => Iff.rfl⟩

theorem smul_levAct_mem_of_radVec {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (hΘ : SUThetaFacts σ a d T) {R : Subgroup (SU σ m)} (hRU : R ≤ uRad σ a)
    (hR : ∀ b ∈ uLine σ a, ∀ r ∈ R, b * r * b⁻¹ ∈ R) {S : AddSubgroup (Fin m → F)}
    (hS : ∀ w, w ∈ S ↔ ∃ r ∈ R, radVec σ a d r = w) {g : SU σ m} {μ : F} (hμ : μ ≠ 0)
    (hg : suMat σ m g *ᵥ a = μ • a) {w : Fin m → F} (hw : w ∈ S) :
    σ μ • levAct σ a d g w ∈ S := by
  obtain ⟨r, hr, rfl⟩ := (hS w).1 hw
  exact (hS _).2 ⟨g * r * g⁻¹, hR g ⟨μ, hμ, hg⟩ r hr, hΘ.conj hg (hRU hr)⟩

theorem eq_or_eq_uRad_of_normalized [CharP F 2] [Finite F] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} {T : Subgroup (SU σ m)} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (hΘ : SUThetaFacts σ a d T) (hG : SUGeomFacts σ a d)
    (hTor : SUTorusStmt σ m) {R : Subgroup (SU σ m)} (hTR : T ≤ R) (hRU : R ≤ uRad σ a)
    (hR : ∀ b ∈ uLine σ a, ∀ r ∈ R, b * r * b⁻¹ ∈ R) : R = T ∨ R = uRad σ a := by
  obtain ⟨S, hS⟩ := exists_addSubgroup_radVec_eq hΘ hRU
  have hSP : ∀ x ∈ S, x ∈ perpPair σ a d := fun x hx => by
    obtain ⟨r, -, rfl⟩ := (hS x).1 hx
    exact hΘ.mem_perp r
  have hkey : ∀ v ∈ perpPair σ a d, uForm σ v v = 0 → ∀ x ∈ S, uForm σ v x ≠ 0 →
      ∀ c : F, c • v ∈ S := by
    intro v hv hvv x hx hvx c
    have h1 : uForm σ v x • v ∈ S := by
      obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hvv
        (show (1 : F) + σ 1 = 0 by rw [map_one, CharTwo.add_self_eq_zero])
      have h2 := smul_levAct_mem_of_radVec hΘ hRU hR hS (g := t) (μ := 1) one_ne_zero
        (by rw [hΘ.transv_a hv ht, one_smul]) hx
      rw [map_one, one_smul, hΘ.levAct_transv hv hvv ht (hSP x hx), one_mul] at h2
      simpa using S.sub_mem h2 hx
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hvx (by simp [uForm_eq])
    obtain ⟨v', hv', hv'v', hvv'⟩ := hG.partner hv hv0 hvv
    have h3 : ∀ μ : F, μ ≠ 0 → (σ μ * uForm σ v x * σ μ) • v ∈ S := by
      intro μ hμ
      obtain ⟨g, hga, -, hgv, -⟩ :=
        hTor haa hdd had hvv hv'v' hvv' hv.1 hv'.1 hv.2 hv'.2 hμ
      have h4 := smul_levAct_mem_of_radVec hΘ hRU hR hS hμ hga h1
      rwa [hΘ.levAct_smul, levAct, hgv, projPair_of_mem (Submodule.smul_mem _ _ hv),
        smul_smul, smul_smul] at h4
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact S.zero_mem
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (c / uForm σ v x)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hr
      exact hr.elim hc hvx
    have h5 := h3 (σ r) ((map_ne_zero σ).2 hr0)
    rw [div_eq_iff hvx] at hr
    rwa [hσ, show r * uForm σ v x * r = c by linear_combination -hr] at h5
  rcases hG.kl S hSP hkey with hbot | htop
  · refine Or.inl (le_antisymm (fun r hr => ?_) hTR)
    have h := (hS _).2 ⟨r, hr, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at h
    exact (hΘ.eq_zero_iff (hRU hr)).1 h
  · refine Or.inr (le_antisymm hRU fun x hx => ?_)
    obtain ⟨r, hr, hrx⟩ := (hS _).1 (htop _ (hΘ.mem_perp x))
    have hr' := (uRad σ a).inv_mem (hRU hr)
    have hxr : x * r⁻¹ ∈ T := (hΘ.eq_zero_iff ((uRad σ a).mul_mem hx hr')).1 (by
      rw [hΘ.mul hx hr', hΘ.inv (hRU hr), hrx, add_neg_cancel])
    simpa using R.mul_mem (hTR hxr) hr

end ModelRank

end CFSG.Timmesfeld.Transvection
