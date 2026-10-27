module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

@[expose] def KList12631 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K →
        Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5)) ∨
          (conjClosure K T = K ∧ ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 4 ∧
            (Nonempty (↥(star H K) ≃* PSL3Model F') ∨
              Nonempty (↥(star H K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F'))))

end CFSG.Quasithin.H13
