module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Act
public import CFSG.Quasithin.H13.NParamRootFourLift
public import CFSG.Quasithin.Background.G6Transvection
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19S
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

@[expose] def Res619S5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) (y z : G)
    (T' D' : Subgroup G), Hyp6116 G T M L V n → Hyp611 G T' M L V n →
    Dat619 T M L V H n y z T' D' →
    ∀ (hW : IsElemAbelian 2 (ch619W T L V z))
      (Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))),
      G6.IsTransvectionDecomposition (L619.img0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks →
      Nonempty (↥(Ks 0) ≃* Equiv.Perm (Fin 5)) →
      IsHStar T' M (conjClosure (conjSub y V) (ch619I T L V ⊔ T') ⊔ T') →
      ∀ (hPN : conjClosure (conjSub y V) (ch619I T L V ⊔ T') ⊔ T' ≤
          L619.normWZX (ch619W T L V z) (ch6ZS T L V)
            (conjClosure (conjSub y V) (ch619I T L V ⊔ T')))
        (ψ : ↥(conjClosure (conjSub y V) (ch619I T L V ⊔ T') ⊔ T') →* Equiv.Perm (Fin 5)),
        Function.Surjective ψ →
        (∀ x, ψ x = 1 ↔ L619.act0 hW (ch6ZS T L V)
          (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) (Subgroup.inclusion hPN x) = 1) →
        E1.LiftS5.RootFourLift (conjClosure (conjSub y V) (ch619I T L V ⊔ T') ⊔ T') T' ψ

@[expose] def Res625Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ) (l : G) (DL K : Subgroup G),
    In625 → Dat625 T M L V n l DL K → IsLieChar2Big (KBar K) →
    ∀ t₀ ∈ T, (∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
        K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom) →
      ∀ H₂ : Subgroup G, IsHStar T M H₂ →
        H₂ ≤ (K ⊔ K.map (MulAut.conj t₀).toMonoidHom) ⊔ T → ¬ Group.IsSolvable ↥H₂ →
          E1.nParam H₂ ≠ 1

end CFSG.Quasithin.H13
