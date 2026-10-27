module

public import CFSG.Sporadic.J4.QTOutComm

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

theorem maps_P0_iff (α : MulAut J) (hαP : ∀ x ∈ P0, α x ∈ P0) (x : J) : α x ∈ P0 ↔ x ∈ P0 := by
  refine ⟨fun hx => ?_, fun hx => hαP x hx⟩
  let φ : P0 → P0 := fun y => ⟨α y, hαP y y.2⟩
  have hinj : Function.Injective φ := fun y z h =>
    Subtype.ext (α.injective (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj ⟨α x, hx⟩
  have hyx : α y = α x := congrArg Subtype.val hy
  rw [← α.injective hyx]
  exact y.2

theorem aut_of_maps_P0 (hF : J4Facts) (α : MulAut J) (hαP : ∀ x ∈ P0, α x ∈ P0) :
    ∃ k : J, ∀ x, α x = k * x * k⁻¹ := by
  have hM := hF.mat
  have hα : ∀ x, α x ∈ P0 ↔ x ∈ P0 := maps_P0_iff α hαP
  have hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11 := eta_char hM hF α hα
  have hH : ∀ x, α x ∈ Hj ↔ x ∈ Hj := Hj_of_Eg hF α hE
  obtain ⟨g, hg, hgη⟩ := exists_inner_twist hF α hE hH
  have hE1 : ∀ x, twistAut g α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11 := fun x => by
    rw [twistAut_apply, twist_mem_Eg hM hg, hE]
  have hH1 : ∀ x, twistAut g α x ∈ Hj ↔ x ∈ Hj := fun x => by
    rw [twistAut_apply, twist_mem_Hj hg, hH]
  have hfix1 : ∀ c < 2 ^ 11, twistAut g α (eta uJ 11 c) = eta uJ 11 c := fun c hc => by
    rw [twistAut_apply]
    exact hgη c hc
  obtain ⟨β, ⟨v, hv, hβ⟩, hEβ, hHβ, hfixβ, hcase⟩ := classify_gens hF (twistAut g α) hE1 hH1 hfix1
  rcases hcase with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  swap
  · exact (no_delta_class hF β hfixβ h0 h1 h2).elim
  have hβHj : ∀ h ∈ Hj, β h = h := by
    have hle : Hj ≤ fixedSub β := by
      refine (Subgroup.closure_le (fixedSub β)).2 ?_
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact mem_fixedSub.2 h0
      · exact mem_fixedSub.2 h1
      · exact mem_fixedSub.2 h2
    exact fun h hh => mem_fixedSub.1 (hle hh)
  have hid : ∀ x, β x = x := eq_id_of_fix_Hj hF β hβHj
  have hvinv : (eta uJ 11 v)⁻¹ = eta uJ 11 v := eta_inv_self hM v
  refine ⟨g * (eta uJ 11 v)⁻¹, fun x => ?_⟩
  have e1 : eta uJ 11 v * (g⁻¹ * α x * g) * (eta uJ 11 v)⁻¹ = x := by
    have := hid x
    rw [hβ, twistAut_apply, ← hvinv] at this
    rw [hvinv]
    rw [hvinv] at this
    exact this
  calc α x = (g * (eta uJ 11 v)⁻¹) * (eta uJ 11 v * (g⁻¹ * α x * g) * (eta uJ 11 v)⁻¹) *
        (g * (eta uJ 11 v)⁻¹)⁻¹ := by group
    _ = (g * (eta uJ 11 v)⁻¹) * x * (g * (eta uJ 11 v)⁻¹)⁻¹ := by rw [e1]

end CFSG.Sporadic.J4.QT
