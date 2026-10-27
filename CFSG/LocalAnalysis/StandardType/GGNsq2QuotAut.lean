module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.CoprimeKernel

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.automizer_le_map (hD : Datum p N f L Bs Z) {X : Subgroup G} (hZX : Z ≤ X) (hXN : X ≤ N) :
    ggAutomizer (img N f X) (img N f Bs) ≤
      (ggAutomizer X Bs).map (MulAut.congr hD.tau).toMonoidHom := by
  unfold ggAutomizer
  rw [Subgroup.closure_le]
  intro φ hφ
  obtain ⟨g, hgX, hgN, hφg⟩ := hφ
  obtain ⟨n, hnX, rfl⟩ := mem_img.1 hgX
  obtain ⟨z, hz, hn', hφψ⟩ := hD.exists_induced_of_normalizes n hgN
  have hzX : ((z : ↥N) : G) ∈ X := hZX ((hD.mem_ker_iff z).1 hz)
  have hmem : (((z⁻¹ * n : ↥N)) : G) ∈ X := by
    have h1 : (((z⁻¹ * n : ↥N)) : G) = ((z : ↥N) : G)⁻¹ * ((n : ↥N) : G) := rfl
    rw [h1]
    exact X.mul_mem (X.inv_mem hzX) hnX
  have hψ : Bs.normalizerMonoidHom ⟨(((z⁻¹ * n : ↥N)) : G), hn'⟩ ∈ ggInduced X Bs :=
    ⟨(((z⁻¹ * n : ↥N)) : G), hmem, hn', fun _ => rfl⟩
  exact ⟨_, Subgroup.subset_closure hψ, hφψ φ hφg⟩

theorem Datum.card_automizer_le [Finite Q] (hD : Datum p N f L Bs Z) {X : Subgroup G} (hZX : Z ≤ X) (hXN : X ≤ N) :
    Nat.card ↥(ggAutomizer (img N f X) (img N f Bs)) ≤ Nat.card ↥(ggAutomizer X Bs) := by
  haveI : Finite (MulAut ↥(img N f Bs)) :=
    Finite.of_injective (fun φ : MulAut ↥(img N f Bs) => (φ : ↥(img N f Bs) → ↥(img N f Bs)))
      DFunLike.coe_injective
  have h1 := Subgroup.card_le_of_le (hD.automizer_le_map hZX hXN)
  rw [Subgroup.card_map_of_injective (MulAut.congr hD.tau).injective] at h1
  exact h1

theorem Datum.exists_lift_reflection (hD : Datum p N f L Bs Z) {X : Subgroup G} (hZX : Z ≤ X)
    (hXN : X ≤ N) {r : MulAut ↥(img N f Bs)} (hr : r ∈ ggAutomizer (img N f X) (img N f Bs))
    (hrefl : GGIsReflection p r) :
    ∃ r₀ ∈ ggAutomizer X Bs, GGIsReflection p r₀ ∧ MulAut.congr hD.tau r₀ = r := by
  obtain ⟨r₀, hr₀, hr₀r⟩ := Subgroup.mem_map.1 (hD.automizer_le_map hZX hXN hr)
  have h : MulAut.congr hD.tau r₀ = r := hr₀r
  refine ⟨r₀, hr₀, ?_, h⟩
  rw [← ggIsReflection_congr_iff hD.tau r₀, h]
  exact hrefl

end NsQuot

end CFSG.StandardType

end
