module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Route
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent361
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Lem154

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem res1Lem154_l2 {Q : ∀ (X : Type) [Group X], Prop} :
    Sylow155R1.Res1Lem154 Q Res1OpenL2Type :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ =>
    ⟨⟨fun a b => Subtype.ext (res1L2_r_comm τ a a.2 b b.2)⟩⟩


theorem res1ZExclLeN_l2_of_route150 (h142 : Concl142S14) (hst : StellmacherKP)
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h148 : Item148R)
    {Q : ∀ (X : Type) [Group X], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hQE9 : Sylow155R1.Res1QE9 Q)
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h340 : Sylow155R1.Res1Thm340 Q Res1OpenL2Type)
    (h150 : Sylow155R1.Res1Thm150b Q Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN Q Res1OpenL2Type :=
  res1ZExclLeN_l2_of_route h142 hst hbot h1444 h149 h148 hQ h153 hn h340
    (Sylow155R1.res1Thm361_of h149 hQE9 h150 res1Lem154_l2)

theorem res1ZExclLeN_l2_a7_of_route150 (h142 : Concl142S14) (hst : StellmacherKP)
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
        Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type A c
        L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h340 : Sylow155R1.Res1Thm340 (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
      Res1OpenL2Type)
    (h150 : Sylow155R1.Res1Thm150b (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
      Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
      Res1OpenL2Type :=
  res1ZExclLeN_l2_of_route150 h142 hst hbot h1444 h149 h148 (fun _ _ h => Or.inl h)
    Sylow155R1.res1QE9_a7 h153 hn h340 h150

theorem res1ZExclLeN_l2_m22_of_route150 (h142 : Concl142S14) (hst : StellmacherKP)
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
        Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
        Res1OpenL2Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h340 : Sylow155R1.Res1Thm340 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type)
    (h150 : Sylow155R1.Res1Thm150b (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type :=
  res1ZExclLeN_l2_of_route150 h142 hst hbot h1444 h149 h148 (fun _ _ h => Or.inr h)
    Sylow155R1.res1QE9_m22 h153 hn h340 h150

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
