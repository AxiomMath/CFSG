module

public import CFSG.Quasithin.Background.C124YLInd

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open Matrix
open scoped MatrixGroups

@[expose] def slAct {F : Type*} [Field F] (s : SL(2, F)) (q : Multiplicative (Fin 2 → F)) :
    Multiplicative (Fin 2 → F) :=
  Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd q)

structure L2Ctx {W : Type*} [CommGroup W] [Finite W] (F : Type) [Field F] [Finite F]
    (Xs Ls : Subgroup (MulAut W)) (U Z : Subgroup W) where
  hF4 : Nat.card F = 4
  θ : SL(2, F) →* ↥Ls
  θ_inj : Function.Injective θ
  θ_surj : Function.Surjective θ
  c : ↥U →* Multiplicative (Fin 2 → F)
  coord : IsCoord U Z c
  hLX : Ls ≤ Xs
  hnorm : ∀ x ∈ Xs, x ∈ Subgroup.normalizer (Ls : Set (MulAut W))
  hU : ∀ x ∈ Xs, ∀ u, u ∈ U ↔ x u ∈ U
  hZ : ∀ x ∈ Xs, ∀ z, z ∈ Z ↔ x z ∈ Z
  equiv : ∀ (s : SL(2, F)) (u : ↥U) (hu : ((θ s : ↥Ls) : MulAut W) u ∈ U),
    c ⟨((θ s : ↥Ls) : MulAut W) u, hu⟩ = slAct s (c u)
  hFstar : quasithinGenFitting Xs = Ls

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

@[expose] def thetaX (s : SL(2, F)) : ↥Xs := ⟨((C.θ s : ↥Ls) : MulAut W), C.hLX (C.θ s).2⟩

theorem ind_theta (s : SL(2, F)) (q : Multiplicative (Fin 2 → F)) :
    indHom C.coord Xs C.hU C.hZ (C.thetaX s) q = slAct s q := by
  obtain ⟨u, rfl⟩ := C.coord.surj q
  rw [show (indHom C.coord Xs C.hU C.hZ (C.thetaX s)) (C.c u) =
    C.c (resU Xs C.hU (C.thetaX s) u) from indHom_apply C.coord Xs C.hU C.hZ _ u]
  exact C.equiv s u _

theorem slAct_eq_self {s : SL(2, F)} (h : ∀ q, slAct s q = q) : s = 1 := by
  apply Subtype.ext
  ext i j
  have := congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd (Pi.single j 1)))
  have h2 := congrFun this i
  simp only [slAct, toAdd_ofAdd] at h2
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h2

theorem faithful_theta {s : SL(2, F)} (h : indHom C.coord Xs C.hU C.hZ (C.thetaX s) = 1) :
    s = 1 := by
  apply slAct_eq_self
  intro q
  rw [← C.ind_theta, h]
  rfl

theorem faithful {x : ↥Xs} (hx : indHom C.coord Xs C.hU C.hZ x = 1) : x = 1 := by
  refine faithful_of_fstar C.coord C.hLX C.hnorm C.hFstar C.hU C.hZ ?_ x hx
  intro l hl
  obtain ⟨s, hs⟩ := C.θ_surj l
  have : C.thetaX s = ⟨l, C.hLX l.2⟩ := Subtype.ext (by rw [← hs]; rfl)
  rw [← this] at hl
  have h1 := C.faithful_theta hl
  rw [← hs, h1, map_one]

end L2Ctx

end CFSG.Quasithin.C124.YL
