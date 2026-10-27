module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Thm93Syl (V T : Subgroup G) : Prop :=
  IsSylowIn 2 T ⊤ → normalizer (T : Set G) ≤ normalizer (V : Set G) → Thm93 V T

theorem Thm93Syl.thm93 {V T : Subgroup G} (h : Thm93Syl V T) (hS : IsSylowIn 2 T ⊤)
    (hN : normalizer (T : Set G) ≤ normalizer (V : Set G)) : Thm93 V T :=
  h hS hN

end CFSG.LocalAnalysis.WeakClosure81
