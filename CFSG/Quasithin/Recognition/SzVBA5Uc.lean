module

public import CFSG.Quasithin.Recognition.SzVBA5Loc

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

@[expose] noncomputable def Uc (V : Subgroup G) (y β : CosetGeom G₀ G₁ G₂) : Subgroup G :=
  secCentr (pCoreOf 2 (stab y)) (Vv V y) ⊓ Vv V β

omit [Finite G] in
theorem mem_Uc {V : Subgroup G} {y β : CosetGeom G₀ G₁ G₂} {w : G} :
    w ∈ Uc V y β ↔ (w ∈ Subgroup.normalizer (Vv V y : Set G) ∧
      ∀ q ∈ pCoreOf 2 (stab y), q * w * q⁻¹ * w⁻¹ ∈ Vv V y) ∧ w ∈ Vv V β := Iff.rfl

omit [Finite G] in
theorem le_normalizer_secCentr {H Q V : Subgroup G} (hQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hV : H ≤ Subgroup.normalizer (V : Set G)) :
    H ≤ Subgroup.normalizer (secCentr Q V : Set G) := by
  have key : ∀ h ∈ H, ∀ w ∈ secCentr Q V, h * w * h⁻¹ ∈ secCentr Q V := by
    intro h hh w hw
    obtain ⟨hwN, hw'⟩ := mem_secCentr.mp hw
    refine mem_secCentr.mpr ⟨?_, fun q hq => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hV hh) hwN) (Subgroup.inv_mem _ (hV hh))
    · have hq' : h⁻¹ * q * h ∈ Q := by
        have := (Subgroup.mem_normalizer_iff''.mp (hQ hh) q).mp hq
        exact this
      have h1 := hw' _ hq'
      have h2 := (Subgroup.mem_normalizer_iff.mp (hV hh) _).mp h1
      have e : h * (h⁻¹ * q * h * w * (h⁻¹ * q * h)⁻¹ * w⁻¹) * h⁻¹ =
          q * (h * w * h⁻¹) * q⁻¹ * (h * w * h⁻¹)⁻¹ := by group
      rwa [e] at h2
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => key h hh w hw, fun hw => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hw
  simpa [mul_assoc] using this

omit [Finite G] in
theorem Uc_smul (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (g : ↥G₀)
    (y β : CosetGeom G₀ G₁ G₂) : Uc V (g • y) (g • β) = conjSub (g : G) (Uc V y β) := by
  unfold Uc
  rw [conjSub_inf, conjSub_secCentr, stab_smul, pCoreOf_conjSub, Vv_smul hN, Vv_smul hN]

omit [Finite G] in
theorem stab_inf_le_normalizer_Uc (hN : G₁ ≤ Subgroup.normalizer (V : Set G))
    (y β : CosetGeom G₀ G₁ G₂) :
    stab y ⊓ stab β ≤ Subgroup.normalizer (Uc V y β : Set G) := by
  unfold Uc
  refine F7.le_normalizer_inf ?_ ?_
  · refine le_normalizer_secCentr ?_ ?_
    · exact inf_le_left.trans (le_normalizer_pCoreOf 2 _)
    · exact inf_le_left.trans (stab_le_normalizer_Vv hN y)
  · exact inf_le_right.trans (stab_le_normalizer_Vv hN β)

end CFSG.Quasithin.SzVB
