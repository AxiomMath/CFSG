module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec93L2
public import CFSG.RankThree.GF2n.Stroth80.Sec312Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Cfg93c (hc : Ctx M Q Z B) (n : ℕ) (t r : G) (Z0 : Subgroup G) (h : G) : Prop where
  hs : Sec9Hyp hc n t
  hr : Sec7A hc t r
  hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q
  hsc : StronglyClosedMod M Z0 (LB M Q B)
  hh : h ∈ M
  hne : LB M Q B ≠ conjSubgroup h (LB M Q B)
  hK : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≠ Q
  hZQ : Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) = Q

end HS9

@[expose] def Step93SLCaseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), x ∉ Q → SLNat hc x →
      QuotSat (LB M Q B ⊔ conjSubgroup h (LB M Q B))
          (inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)))
          (IsSLModel 2 (Nat.card Z)) ∨
        LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x

@[expose] def Step93OmegaCaseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), x ∉ Q →
      LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x → False

@[expose] def Step93L2AltXHStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    QuotSat (LB M Q B ⊔ conjSubgroup h (LB M Q B))
        (inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)))
        (IsSLModel 2 (Nat.card Z)) →
      LB M Q B ⊓ hc.CN t ≤ inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) ∨
        (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B

@[expose] def Step93L2FirstStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    QuotSat (LB M Q B ⊔ conjSubgroup h (LB M Q B))
        (inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)))
        (IsSLModel 2 (Nat.card Z)) →
      LB M Q B ⊓ hc.CN t ≤ inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) →
        Z0 ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B)

@[expose] def Step93L2SecondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    QuotSat (LB M Q B ⊔ conjSubgroup h (LB M Q B))
        (inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)))
        (IsSLModel 2 (Nat.card Z)) →
      (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B → False

structure Step93ThreeXH : Prop where
  sl : Step93SLCaseStatement
  omega : Step93OmegaCaseStatement
  alt : Step93L2AltXHStatement
  first : Step93L2FirstStatement
  second : Step93L2SecondStatement

theorem step93TI_of_threeXH (h312b : Stroth312bStatement) (S : Step93ThreeXH) :
    Step93TIStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc h hh hK hZQ
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.mem hZ0
  by_cases hLB : LB M Q B = conjSubgroup h (LB M Q B)
  · have htK : t ∈ Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) :=
      ⟨htZ, ⟨hs.mem, hLB ▸ hs.mem⟩⟩
    rw [hZQ] at htK
    exact hs.notQ htK
  have cfg : HS9.Cfg93c hc n t r Z0 h := ⟨hs, hr, hZ0, hsc, hh, hLB, hK, hZQ⟩
  have hQK : Q ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
    le_inf le_sup_left (by
      calc Q = conjSubgroup h Q := (hc.conj_Q_eq hh).symm
        _ ≤ conjSubgroup h (LB M Q B) := Subgroup.map_mono le_sup_left)
  have hlt : Q < LB M Q B ⊓ conjSubgroup h (LB M Q B) := lt_of_le_of_ne hQK (Ne.symm hK)
  obtain ⟨x, hxK, hxQ⟩ := Set.exists_of_ssubset hlt
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
  have hxLh : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxK).2
  have hdich : QuotSat (LB M Q B ⊔ conjSubgroup h (LB M Q B))
      (inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)))
      (IsSLModel 2 (Nat.card Z)) ∨
      LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x := by
    by_cases hSL : SLNat hc x
    · exact S.sl G M Q Z B hc n t r Z0 h cfg x hxK hxQ hSL
    · exact h312b G M Q Z B hc n hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
        x hxL hxQ (LB M Q B) (conjSubgroup h (LB M Q B))
        ⟨1, Subgroup.one_mem M, (conjSubgroup_one (LB M Q B)).symm⟩ ⟨h, hh, rfl⟩ hxL hxLh hLB
        hSL
  rcases hdich with hq | hR
  · rcases S.alt G M Q Z B hc n t r Z0 h cfg hq with h1 | h2
    · exact step93L2_false_of_le_H hc hs hZ0 (S.first G M Q Z B hc n t r Z0 h cfg hq h1) hZQ
    · exact S.second G M Q Z B hc n t r Z0 h cfg hq h2
  · exact S.omega G M Q Z B hc n t r Z0 h cfg x hxK hxQ hR

end CFSG.RankThree.GF2n.Stroth80
