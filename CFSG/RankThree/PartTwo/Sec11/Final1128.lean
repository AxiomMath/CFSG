module

public import CFSG.RankThree.PartTwo.Sec11.Skeleton
import CFSG.RankThree.PartTwo.Sec11.Item1125Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Final1128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g a' : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} → orderOf x = 9 →
      a' ∈ A → a' ∉ Subgroup.closure {c, d} →
      ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {a', d} → YNotField c L a' → False

namespace Final1128

variable {G : Type} [Group G] [Finite G]

theorem false_of_sec11Final (hfin : Final1128) {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (hf : Sec11Final G A c L a R Y d x s r g) : False := by
  obtain ⟨-, hacd, -⟩ := hf.toSec11Std.not_mem_facts hf.inf_eq hf.closure_eq
  exact hfin G A c L a R Y d x s r g a hf.toSec11Data hf.zpowers_s_eq hf.closure_eq_closure
    hf.orderOf_x hf.a_mem hacd hf.commutator_eq
    ⟨Y, hf.mem_thetaComponentsAt_Y, hf.sec11K_le, hf.not_field⟩

end Final1128

theorem sec11Never_of_final1128 (hex : Sec11DataExists) (h1116 : Item1116) (h1117 : Item1117)
    (h1118 : Item1118) (hfin : Final1128) : Sec11Never := by
  intro G _ _ A c L a R Y hstd
  obtain ⟨a₀, Y₀, d, x, s, r, g, h⟩ := hex G A c L a R Y hstd
  have hx9 := h1118 G A c L a₀ R Y₀ d x s r g h
  have hsr : Subgroup.zpowers s = Subgroup.zpowers c ∧
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a₀, s} := by
    by_contra hne
    have := h1116 G A c L a₀ R Y₀ d x s r g h (by tauto)
    omega
  obtain ⟨⟨a', ha'A, ha'cd, hPP, hnf⟩, -⟩ := h1117 G A c L a₀ R Y₀ d x s r g h hsr.1 hsr.2
  exact hfin G A c L a₀ R Y₀ d x s r g a' h hsr.1 hsr.2 hx9 ha'A ha'cd hPP hnf

theorem sec11Never_of_steps_final1128 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hex : Sec11DataExists) (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118)
    (h1119 : Item1119) (h1123 : Item1123) (hinv : Inverter1118) (hfin : Final1128) :
    Sec11Never :=
  sec11Never_of_final1128 hex h1116 h1117
    (item1118_of h1116 h1117 hset
      (sec11BigNever_of h113 h117 h1117 h1119 h1123 (item1125_of h45 h113) hinv)) hfin

theorem hyp91Never_of_steps_final1128 (h1016 : Sec10.Item1016) (h97 : Sec9.Item97)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113) (h117 : Item117)
    (hex : Sec11DataExists) (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118)
    (h1119 : Item1119) (h1123 : Item1123) (hinv : Inverter1118) (hfin : Final1128) :
    Hyp91Never :=
  hyp91Never_of_item1016 h1016 (setUp11_of h97 h45 h48)
    (sec11Never_of_steps_final1128 h45 h113 h117 hex h1116 h1117 hset h1119 h1123 hinv hfin)

theorem item1134E27_of_steps_final1128 (h1016 : Sec10.Item1016) (h97 : Sec9.Item97)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113) (h117 : Item117)
    (hex : Sec11DataExists) (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118)
    (h1119 : Item1119) (h1123 : Item1123) (hinv : Inverter1118) (hfin : Final1128) :
    Item1134E27 :=
  item1134E27_of
    (hyp91Never_of_steps_final1128 h1016 h97 h45 h48 h113 h117 hex h1116 h1117 hset h1119 h1123
      hinv hfin)

end CFSG.RankThree.PartTwo.Sec11
