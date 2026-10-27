module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelOrbit

@[expose] public section

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes CFSG.StandardType.LieCore
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.F4ExplicitPos.OddKernelActual

variable {L : Type} [Field L]

theorem f4_cyclic_componentRoots_image_eq_of_coord
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    {p : ℕ} (hp : Odd p) (hpa : ∀ i, a i ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i :=
  OddKernelOrbit.f4_cyclic_componentRoots_image_eq_of_odd D ρ hρ a ha hp
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 a hpa γ) i

theorem f4_cyclic_componentOrbitLength_eq_one_of_coord
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    {p : ℕ} (hp : Odd p) (hpa : ∀ i, a i ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i ∧
      componentOrbitLength ρ (componentRoots (rootCharHom a) i) = 1 :=
  OddKernelOrbit.f4_cyclic_componentOrbitLength_eq_one_of_odd D ρ hρ a ha hp
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 a hpa γ) i

theorem f4_cyclic_rationalRoots_eq_of_coord
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    {p : ℕ} (hp : Odd p) (hpa : ∀ i, a i ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    rationalRoots ρ (rootCharHom a) i = componentRoots (rootCharHom a) i :=
  CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.f4_cyclic_rationalRoots_eq_of_odd D ρ hρ a ha hp
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 a hpa γ) i

theorem f4_joint_componentRoots_image_eq_of_coord
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a d : Fin Tag.F4.rank → Lˣ)
    (ha : rootDiagUnit Tag.F4 a ∈ D.torus) (hd : rootDiagUnit Tag.F4 d ∈ D.torus)
    {p : ℕ} (hp : Odd p) (hpa : ∀ i, a i ^ p = 1) (hpd : ∀ i, d i ^ p = 1)
    (i : KernelComponent (jointChar a d)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (jointChar a d) i = componentRoots (jointChar a d) i :=
  OddKernelOrbit.f4_joint_componentRoots_image_eq_of_odd D ρ hρ a d ha hd hp
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 a hpa γ)
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 d hpd γ) i

theorem f4_joint_ratOrbit_eq_of_coord
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a d : Fin Tag.F4.rank → Lˣ)
    (ha : rootDiagUnit Tag.F4 a ∈ D.torus) (hd : rootDiagUnit Tag.F4 d ∈ D.torus)
    {p : ℕ} (hp : Odd p) (hpa : ∀ i, a i ^ p = 1) (hpd : ∀ i, d i ^ p = 1)
    (i : KernelComponent (jointChar a d)) :
    ratOrbit (fun u => ρ u) (componentRoots (jointChar a d) i) =
      componentRoots (jointChar a d) i :=
  CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.f4_joint_ratOrbit_eq_of_odd D ρ hρ a d ha hd hp
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 a hpa γ)
    (fun γ _ => CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_eq_one_no117 d hpd γ) i

end CFSG.StandardType.F4ExplicitPos.OddKernelActual

end

end
