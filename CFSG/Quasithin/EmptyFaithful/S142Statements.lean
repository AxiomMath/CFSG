module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.EmptyFaithful.Skeleton
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def StageTheorem1427 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M →
    (∀ H : Subgroup G, IsHStar T M H → E1.nParam H = 1) ∨
      (Nonempty (G ≃* quasithinTrialityD4Two) ∨ Nonempty (G ≃* quasithinJ2) ∨
        Nonempty (G ≃* quasithinJ3))

@[expose] def StageTheorem14220 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M →
    ∀ H : Subgroup G, IsHStar T M H →
      ((Nonempty (OTwoQuot H ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot H ≃* ↥(Sz 0))) →
          Nonempty (G ≃* quasithinTits)) ∧
        (Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)) →
          Nonempty (G ≃* quasithinM12) ∨ Nonempty (G ≃* PSU3 3 1))

@[expose] def uOfL22 {G : Type*} [Group G] (T M : Subgroup G) : Subgroup G :=
  conjClosure (VZ T M) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))

@[expose] def StageTheorem14316 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    IsMulCommutative ↥(uOfL22 T M)

@[expose] def StageSection146 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    IsMulCommutative ↥(uOfL22 T M) → False

theorem stageTheorem14625_of_parts (h316 : StageTheorem14316) (h146 : StageSection146) :
    StageTheorem14625 := by
  intro G _ _ T M h
  by_contra hn
  exact h146 G T M h hn (h316 G T M h hn)

end CFSG.Quasithin
