module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Coordinates
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Orbit

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}

namespace Setting

variable (S : Setting p H B θ)

include S

theorem exists_conj_of_mem_apply {b : Γ} (hb : b ∈ B) (hb1 : b ≠ 1) {x : Γ} (hx : x ∈ θ b)
    {J : Subgroup Γ} (hJ : J ∈ lcal H) :
    ∃ w ∈ thetaOf θ B, ∀ j ∈ J, x * j * x⁻¹ = w * j * w⁻¹ := by
  classical
  obtain ⟨e⟩ := S.iso b hb hb1
  have hEB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hW₀V : thetaOf θ B ≤ θ b := thetaOf_le_apply hb hb1
  let ν : (Fin p → ↥(thetaOf θ B)) →* Γ := (θ b).subtype.comp e.toMonoidHom
  have hν : Function.Injective ν := (θ b).subtype_injective.comp e.injective
  have hνV : ∀ y, ν y ∈ θ b := fun y => (e y).2
  have hνsurj : ∀ g ∈ θ b, ∃ y, ν y = g := fun g hg => ⟨e.symm ⟨g, hg⟩, by simp [ν]⟩
  have hMV : smear J (Subgroup.zpowers b) ≤ θ b := S.smear_le_apply hb hb1 hJ
  obtain ⟨hMs, hMnc⟩ := S.isSimpleGroup_smear hEB hJ
  have hVn : ∀ v ∈ θ b, ∀ K ∈ orbitOf (Subgroup.zpowers b) J,
      v ∈ Subgroup.normalizer (K : Set Γ) := fun v hv K hK =>
    S.apply_normalizes hb hb1 v hv K (S.orbitOf_subset hEB hJ hK)
  have hVc : ∀ v ∈ θ b, ∀ a ∈ Subgroup.zpowers b, v * a = a * v := by
    intro v hv a ha
    have hvb : Commute v b := Subgroup.mem_centralizer_singleton_iff.mp
      (S.functor.le_centralizer b hb hb1 hv)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hvb.zpow_right n).eq
  have hVM : ∀ v ∈ θ b, v ∈ Subgroup.normalizer ((smear J (Subgroup.zpowers b) : Subgroup Γ) :
      Set Γ) := fun v hv => mem_normalizer_smear (hVn v hv) (hVc v hv)
  let M' : Subgroup (Fin p → ↥(thetaOf θ B)) := (smear J (Subgroup.zpowers b)).comap ν
  have : M'.Normal := ⟨fun y hy g => by
    show ν (g * y * g⁻¹) ∈ smear J (Subgroup.zpowers b)
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hVM (ν g) (hνV g)) (ν y)).mp hy⟩
  have hMinj : Function.Injective (ν.subgroupComap (smear J (Subgroup.zpowers b))) :=
    fun a c h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (hν h')
  have hMsurj : Function.Surjective (ν.subgroupComap (smear J (Subgroup.zpowers b))) := by
    rintro ⟨m, hm⟩
    obtain ⟨y, hy⟩ := hνsurj m (hMV hm)
    exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hm⟩, Subtype.ext hy⟩
  let eM : ↥M' ≃* ↥(smear J (Subgroup.zpowers b)) :=
    MulEquiv.ofBijective (ν.subgroupComap (smear J (Subgroup.zpowers b))) ⟨hMinj, hMsurj⟩
  have : IsSimpleGroup ↥M' := eM.isSimpleGroup
  obtain ⟨k, hk⟩ := exists_le_coordSub S.center_thetaOf (M := M')
  have hU : ∀ y : Fin p → ↥(thetaOf θ B), y k = 1 → ∀ j ∈ J, ν y * j = j * ν y := by
    intro y hyk
    have hcM : ∀ m ∈ smear J (Subgroup.zpowers b), ν y * m = m * ν y := by
      intro m hm
      obtain ⟨y', hy'⟩ := hνsurj m (hMV hm)
      have hy'M : y' ∈ M' := by
        show ν y' ∈ smear J (Subgroup.zpowers b)
        rw [hy']
        exact hm
      have hc : y * y' = y' * y := by
        funext k'
        by_cases hkk : k' = k
        · subst hkk
          simp [hyk]
        · simp [hk hy'M k' hkk]
      rw [← hy', ← map_mul, ← map_mul, hc]
    exact S.centralizes_orbitOf hEB hJ (hVn (ν y) (hνV y)) hcM J (self_mem_orbitOf _ J)
  let κ : ↥(thetaOf θ B) →* ↥(thetaOf θ B) :=
    (Pi.evalMonoidHom (fun _ : Fin p => ↥(thetaOf θ B)) k).comp
      (e.symm.toMonoidHom.comp (Subgroup.inclusion hW₀V))
  have hŵ : ∀ w : ↥(thetaOf θ B),
      ν (e.symm (Subgroup.inclusion hW₀V w)) = (w : Γ) := fun w => by simp [ν]
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h := hU (e.symm (Subgroup.inclusion hW₀V w)) (by simpa [κ] using hw)
    rw [hŵ] at h
    exact Subtype.ext (S.eq_one_of_centralizes_one (S.thetaOf_le_H w.2)
      (S.thetaOf_le_centralizer w.2) hJ h)
  have hκsurj : Function.Surjective κ := Finite.injective_iff_surjective.mp hκinj
  obtain ⟨y, hy⟩ := hνsurj x hx
  obtain ⟨w, hw⟩ := hκsurj (y k)
  refine ⟨(w : Γ), w.2, fun j hj => ?_⟩
  have hy'k : (y * (e.symm (Subgroup.inclusion hW₀V w))⁻¹) k = 1 := by
    have : (e.symm (Subgroup.inclusion hW₀V w)) k = y k := hw
    simp [this]
  have hc := hU _ hy'k
  have hx' : x = ν (y * (e.symm (Subgroup.inclusion hW₀V w))⁻¹) * w := by
    rw [map_mul, map_inv, hŵ, ← hy]
    group
  have hwj : (w : Γ) * j * (w : Γ)⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (S.thetaOf_normalizes w w.2 J hJ) j).mp hj
  have hcw := hc _ hwj
  rw [hx']
  calc ν (y * (e.symm (Subgroup.inclusion hW₀V w))⁻¹) * w * j *
        (ν (y * (e.symm (Subgroup.inclusion hW₀V w))⁻¹) * w)⁻¹ =
      ν (y * (e.symm (Subgroup.inclusion hW₀V w))⁻¹) * ((w : Γ) * j * (w : Γ)⁻¹) *
        (ν (y * (e.symm (Subgroup.inclusion hW₀V w))⁻¹))⁻¹ := by group
    _ = (w : Γ) * j * (w : Γ)⁻¹ := by rw [hcw]; group

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
