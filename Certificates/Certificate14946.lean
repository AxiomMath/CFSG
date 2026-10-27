
module

public import Certificates.Kernel.F4Planes.TwGlue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.AnisoE6

public section

namespace Certificates

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.AnisoE6 in
theorem certificate14946 :     ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (k : Type) [Field k] [Finite k] [Algebra k K]
      (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c),
      Nat.card K = 2 ^ 2 → (∀ c : K, σ c = c ^ 2) → Nat.card k = 2 →
      ∀ E₃ : Subgroup (adjointGroup .F4 k), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure
          ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range :
              Set (twistedE6RootGroup K σ)) ∪
            (Subgroup.centralizer
              ({((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom) e} :
                Set (twistedE6RootGroup K σ)) : Set (twistedE6RootGroup K σ))) = ⊤ :=
  CFSG.KC.F4PlanesTw.twCloseAtTwo_kernel

end Certificates
