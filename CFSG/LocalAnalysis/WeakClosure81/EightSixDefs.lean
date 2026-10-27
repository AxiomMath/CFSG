module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G]

@[expose] def kGenIn (V H : Subgroup G) : Subgroup G :=
  ⨆ k ∈ conjClosure V H, conjSubgroup V k

@[expose] def omegaHIn (V H : Subgroup G) : Set (Subgroup G) :=
  {W | ∃ h ∈ H, W = conjSubgroup V h}

@[expose] def eCentSet (V H T : Subgroup G) : Set G :=
  (Subgroup.centralizer (eSub V H T : Set G) : Set G)

@[expose] def KBarShape (V H T : Subgroup G) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  HasQuotShape (kGenIn V H) (eCentSet V H T) P

@[expose] def KBarCenterShape (V H T : Subgroup G) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  HasQuotShape (kGenIn V H) (centerPre (kGenIn V H) (eCentSet V H T)) P

@[expose] noncomputable def rankBarV (V H T : Subgroup G) : ℕ :=
  E3.mQuot V (V ⊓ Subgroup.centralizer (eSub V H T : Set G))

@[expose] def Hyp85Three (V H T : Subgroup G) : Prop :=
  (∃ m n : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∧ rankBarV V H T = n) ∨
    (∃ m n : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsPSUGp X m n) ∧
      rankBarV V H T = n) ∨
    (∃ m : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsSymGp X m))

@[expose] def Shape86Delta (V H T : Subgroup G) : Prop :=
  ∃ m n : ℕ, 3 < m ∧ 1 < n ∧ rankBarV V H T = 1 ∧
    (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
      KBarCenterShape V H T (fun X _ => IsPSUGp X m n))

end CFSG.LocalAnalysis.WeakClosure81
