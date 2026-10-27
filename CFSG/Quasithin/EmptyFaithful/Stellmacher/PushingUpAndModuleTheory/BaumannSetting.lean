module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

public section

namespace CFSG.Quasithin.F53Push

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

variable {H : Type*} [Group H] {F : Type*} [Field F] [CharP F 2]

theorem exists_natQuotSetting_of_sl2' [Finite H] [Finite F] {R M V : Subgroup H}
    (hsyl : IsSylowTwoOf R (⊤ : Subgroup H)) (hnn : ¬ R.Normal) (hRM : R ≤ M) (hMt : M < ⊤)
    (hMu : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M)
    (hVe : IsElemAbelian 2 V) (hVn : V.Normal)
    (α : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = Subgroup.centralizer (V : Set H))
    (β : V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (h : H) (v v' : V), (v' : H) = h * v * h⁻¹ →
      Multiplicative.toAdd (β v') =
        (α h : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)).subgroupOf V) :
    ∃ ρ : H →* Gamma F, (∀ h, ((ρ h : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (α h)) ∧
      IsNatQuotSetting R M V ρ β := by
  classical
  let ρ : H →* Gamma F := (slGamma F).subtype.comp ((slGammaEquiv F).toMonoidHom.comp α)
  have hρ : ∀ h, ((ρ h : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (α h) :=
    fun h => slGammaEquiv_apply (α h)
  have hρmem : ∀ h, ρ h ∈ slGamma F := fun h => ((slGammaEquiv F) (α h)).2
  have hρker : ∀ h, ρ h = 1 ↔ α h = 1 := by
    intro h
    constructor
    · intro hh
      have h1 : (slGammaEquiv F) (α h) = 1 := Subtype.ext hh
      exact (slGammaEquiv F).injective (by rw [h1, map_one])
    · intro hh
      simp [ρ, hh]
  have hρsurj : ∀ g : Gamma F, g ∈ slGamma F → ∃ h, ρ h = g := by
    intro g hg
    obtain ⟨A, hA⟩ := mem_slGamma_iff.mp hg
    obtain ⟨h, hh⟩ := hα A
    exact ⟨h, Subtype.ext (by rw [hρ h, hh, ← hA])⟩
  refine ⟨ρ, hρ, ?_⟩
  refine
    { sylow := hsyl, nonnormal := hnn, le_M := hRM, M_lt := hMt, M_max := hMu, reduced := ?_,
      sl_le := ?_, two_quot := ?_, φ_surj := hβ, φ_equiv := ?_, φ_ker := ?_ }
  · refine ⟨le_top, top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hVn), hVe, ?_⟩
    intro D _ hDn hDpow
    have hDnorm : ∀ h : H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := fun h d hd =>
      (Subgroup.mem_normalizer_iff.mp (hDn (Subgroup.mem_top h)) d).mp hd
    have hA : D.map ρ = ⊥ := by
      apply eq_bot_of_normal_isPGroup
      · intro a
        obtain ⟨d, hd, hda⟩ := a.2
        obtain ⟨k, hk⟩ := hDpow d hd
        refine ⟨k, Subtype.ext ?_⟩
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        have hk' : d ^ 2 ^ k ∈ α.ker := by rw [hαk]; exact hk
        rw [← hda, ← map_pow]
        exact (hρker _).mpr (MonoidHom.mem_ker.mp hk')
      · intro g hg a ha
        obtain ⟨h, rfl⟩ := hρsurj g hg
        obtain ⟨d, hd, rfl⟩ := ha
        exact ⟨h * d * h⁻¹, hDnorm h d hd, by simp⟩
    intro d hd
    have h1 : ρ d ∈ D.map ρ := ⟨d, hd, rfl⟩
    rw [hA, Subgroup.mem_bot] at h1
    rw [← hαk]
    exact (hρker d).mp h1
  · intro A
    obtain ⟨h, rfl⟩ := hα A
    exact ⟨h, hρ h⟩
  · intro h
    exact ⟨0, by simpa using hρmem h⟩
  · intro h v v' hv'
    rw [hρ h, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    exact hβe h v v' hv'
  · exact hβk

end CFSG.Quasithin.F53Push
