module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

open Classical in
@[expose] noncomputable def twistKindM {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : TwistKind :=
  if twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) then .inner
  else if (compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)])) then .exc
  else if 4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1)
    then .twoD
  else if 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1)
    then .suN
  else .inner

theorem twistKindM_eq_twistKind {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) {L : Type} [Field L]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    twistKindM ρ χ i = twistKind ρ χ i := by
  rfl

theorem twistKindM_eq_of_componentRoots_eq {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M N : Type*} [CommGroup M] [CommGroup N]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* N}
    {i : KernelComponent χ} {j : KernelComponent χ'}
    (h : componentRoots χ i = componentRoots χ' j) :
    twistKindM ρ χ i = twistKindM ρ χ' j := by
  unfold twistKindM
  rw [h]

theorem rationalRootsM_eq_of_componentRoots_eq {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M N : Type*} [CommGroup M] [CommGroup N]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* N}
    {i : KernelComponent χ} {j : KernelComponent χ'}
    (h : componentRoots χ i = componentRoots χ' j) :
    rationalRootsM ρ χ i = rationalRootsM ρ χ' j := by
  unfold rationalRootsM
  rw [h]

theorem rationalComponentM_eq_of_componentRoots_eq
    {τ : Tag} {L : Type} [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    {M N : Type*} [CommGroup M] [CommGroup N]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* N}
    {i : KernelComponent χ} {j : KernelComponent χ'}
    (h : componentRoots χ i = componentRoots χ' j) :
    rationalComponentM ρ Γ χ i = rationalComponentM ρ Γ χ' j := by
  unfold rationalComponentM rationalSpanM
  rw [rationalRootsM_eq_of_componentRoots_eq ρ h]

theorem twistKindM_twoD_unpack {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (h : twistKindM ρ χ i = .twoD) :
    ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) ∧
      4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1) := by
  unfold twistKindM at h
  split_ifs at h with h1 h2 h3
  exact ⟨h1, h3⟩

end CFSG.StandardType.TableCRes
