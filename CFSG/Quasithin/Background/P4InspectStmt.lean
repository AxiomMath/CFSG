module

public import CFSG.Quasithin.Background.G10FifteenInputs
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

@[expose] def InspectSQTData {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (M K : Subgroup (GLV U)) : Prop :=
  IsPermCoreModule K (alternatingGroup (Fin 5)) ∨
  (Module.finrank (ZMod 2) U = 4 ∧ Nonempty (↥M ≃* Equiv.Perm (Fin 5)) ∧ IsL24ModuleFor K) ∨
  IsPermCoreModule K (alternatingGroup (Fin 6)) ∨
  IsPermCoreModule K (alternatingGroup (Fin 8))

@[expose] def InspectSpCase : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → M = spSub f →
      IsSimpleGroup ↥K ∧ (CFSG.IsStronglyQuasithin ↥K → InspectSQTData M K)

@[expose] def InspectOrthCase : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v →
    (∃ q : U → ZMod 2, (∀ x y, q (x + y) = q x + q y + f x y) ∧
      (M = orthSub q ∨ M = omegaSub f q)) →
      IsSimpleGroup ↥K ∧ (CFSG.IsStronglyQuasithin ↥K → InspectSQTData M K)

@[expose] def InspectD4Case : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → Module.finrank (ZMod 2) U = 4 →
    (M = ⁅spSub f, spSub f⁆ ∨
      (Nonempty (↥M ≃* Equiv.Perm (Fin 5)) ∧ ∃ A : Subgroup (GLV U), A ≤ M ∧ IsL24ModuleFor A)) →
      IsSimpleGroup ↥K ∧ (CFSG.IsStronglyQuasithin ↥K → InspectSQTData M K)

@[expose] def InspectSylowEnd : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → CFSG.IsStronglyQuasithin ↥K → InspectSQTData M K →
    ∀ P : Sylow 2 ↥K, (∀ s ∈ P, ((s : ↥K) : GLV U) ∈ Q) →
      Module.finrank (ZMod 2) U = 4 ∧ Nat.card ↥Q = 4 ∧
        ∃ (φ : ↥K ≃* ↥(alternatingGroup (Fin 5))) (ψ : U ≃ₗ[ZMod 2] ↥(permCore 5)),
          ∀ (k : ↥K) (u w : U), w = (k : GLV U) u →
            (ψ w : Fin 5 → ZMod 2) =
              permAct ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ u)

@[expose] def InspectOuterEnd : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → CFSG.IsStronglyQuasithin ↥K → InspectSQTData M K →
    ∀ (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K), (∀ s ∈ P, α s ∈ P) → (∀ s, α (α s) = s) →
      (∀ s ∈ P, ∀ t ∈ P, (s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) →
      ∃ g : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = g * (k : GLV U) * g⁻¹

theorem inspect_cases (hSp : InspectSpCase) (hOrth : InspectOrthCase) (hD4 : InspectD4Case)
    {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    {f : LinearMap.BilinForm (ZMod 2) U} {M K Q : Subgroup (GLV U)} {v : U}
    (h : G121Data f M K Q v) :
    IsSimpleGroup ↥K ∧ (CFSG.IsStronglyQuasithin ↥K → InspectSQTData M K) := by
  rcases h.concl with h1 | ⟨q, hq, hM, -⟩ | ⟨hd, hM⟩
  · exact hSp U f M K Q v h h1
  · exact hOrth U f M K Q v h ⟨q, hq, hM⟩
  · exact hD4 U f M K Q v h hd hM

theorem inspectSimple_of_cases (hSp : InspectSpCase) (hOrth : InspectOrthCase)
    (hD4 : InspectD4Case) : InspectSimple :=
  fun _ _ _ _ _ _ _ _ _ h => (inspect_cases hSp hOrth hD4 h).1

theorem inspectSylow_of_cases (hSp : InspectSpCase) (hOrth : InspectOrthCase)
    (hD4 : InspectD4Case) (hEnd : InspectSylowEnd) : InspectSylow :=
  fun U _ _ _ f M K Q v h hsqt P hP =>
    hEnd U f M K Q v h hsqt ((inspect_cases hSp hOrth hD4 h).2 hsqt) P hP

theorem inspectOuter_of_cases (hSp : InspectSpCase) (hOrth : InspectOrthCase)
    (hD4 : InspectD4Case) (hEnd : InspectOuterEnd) : InspectOuter :=
  fun U _ _ _ f M K Q v h hsqt α P hP hα hcomm =>
    hEnd U f M K Q v h hsqt ((inspect_cases hSp hOrth hD4 h).2 hsqt) α P hP hα hcomm

end G11

end CFSG.Quasithin
