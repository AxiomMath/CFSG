module

public import CFSG.Quasithin.Background.G119Basic
public import CFSG.Quasithin.Background.G119Schur

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

namespace G119Ctx

variable (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem transvection_Ix (h14 : G1014Concl B Γ v₁ W X L) {x : GLV V} (hx : x ∈ X)
    (hxC : x ∉ centralizerIn X (normalClosure Γ L)) {J : Submodule (ZMod 2) V}
    (hJ : IrrPlus (normalClosure Γ L) J) (hle : J ≤ B.orthogonal I) (hne : J ≠ I)
    (hfix : conjSub x J = J) :
    ∃ c' : V, J ⊓ W = Submodule.span (ZMod 2) {c'} ∧ InducesTransvection x J c' := by
  have hv : v₁ ∉ J := c.v₁_not_mem hJ hne
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxC (g119_mem_centralizerIn_iff.2 ⟨hx, fun h _ => by simp⟩)
  have hnc : ∃ h ∈ normalClosure Γ L, x * h * x⁻¹ * h⁻¹ ∉ centralizerOn (normalClosure Γ L) J := by
    by_contra hcon
    push Not at hcon
    apply hxC
    refine g119_mem_centralizerIn_iff.2 ⟨hx, fun h hh => ?_⟩
    have hker := hcon h hh
    have hone : x * h * x⁻¹ * h⁻¹ = 1 :=
      (faithfulOn_iff.1 (c.faithful_irrPlus hJ)) _ hker.1 hker.2
    have h1 : x * h * x⁻¹ = h := by
      have := congrArg (· * h) hone
      simpa using this
    have h3 : x * h = h * x := by
      have := congrArg (· * x) h1
      simpa [mul_assoc] using this
    exact h3.symm
  have hperp : J ≤ perp B v₁ := fun u hu => by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.1 (hle hu)) v₁ c.v₁_mem
    exact LinearMap.mem_ker.2 this
  rcases h14 J hJ hv x ⟨hx, hfix⟩ hx1 hnc with ⟨-, hc⟩ | ⟨hnot, -⟩ | ⟨hnot, -⟩
  · exact hc
  · exact absurd hperp hnot
  · exact absurd hperp hnot

theorem finrank_commMap_I (h14 : G1014Concl B Γ v₁ W X L) {x : GLV V} (hx : x ∈ X)
    (hxC : x ∉ centralizerIn X (normalClosure Γ L)) {J : Submodule (ZMod 2) V}
    (hJ : IrrPlus (normalClosure Γ L) J) (hle : J ≤ B.orthogonal I) (hne : J ≠ I)
    (hfix : conjSub x J = J) :
    Module.finrank (ZMod 2) (LinearMap.range (commMap x I (c.conjSub_I hx))) = 1 := by
  obtain ⟨c', -, htr⟩ := c.transvection_Ix h14 hx hxC hJ hle hne hfix
  obtain ⟨φ, hφ⟩ := c.hiso hJ
  have hcomm := g119_commute_of_transvection (c.irrPlus_isIrr hJ) c.irrPlus.1 (c.irrPlus_two_lt hJ)
    (fun h hh => c.X_normalizes x hx h hh) (c.conjSub_I hx) hfix (c.X_sq hx) ⟨c', htr⟩ φ hφ
  rw [g119_finrank_commMap_eq_of_commute (c.conjSub_I hx) hfix φ hcomm]
  exact (inducesTransvection_iff_finrank hfix).1 ⟨c', htr⟩

end G119Ctx

end G11

end CFSG.Quasithin
