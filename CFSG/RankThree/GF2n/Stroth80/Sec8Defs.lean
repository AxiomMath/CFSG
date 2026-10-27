module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec8Hyp (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop where
  toSec5 : Sec5Hyp hc n t
  sp : ∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m

theorem Sec8Hyp.spNat {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec8Hyp hc n t) : SpNat hc t := by
  obtain ⟨m, hm, K, iK, iF, hK, hrep⟩ := h.sp
  exact ⟨K, iK, iF, hK, m, hm, hrep⟩

@[expose] def Sec8V1 (M Q Z B : Subgroup G) (t r : G) : Subgroup G :=
  Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)

@[expose] def Sec8W1 (M Q Z B : Subgroup G) (t r : G) : Subgroup G :=
  Wt Q (Sec8V1 M Q Z B t r)

@[expose] def Conc81a (hc : Ctx M Q Z B) (t : G) : Prop := Conc71a hc t

@[expose] def Conc81b (hc : Ctx M Q Z B) (t r : G) : Prop :=
  SpMNat hc t 2 ∧
  (∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
      ∃ w ∈ Sec8W1 M Q Z B t r, ⁅x, w⁆ ∉ Sec8V1 M Q Z B t r) ∧
  (∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → ∀ v ∈ Sec8V1 M Q Z B t r, ⁅x, v⁆ ∈ Z)

@[expose] def SpNonA2 {m : ℕ} {K : Type} [Field K] (A : GL (Fin m ⊕ Fin m) K) : Prop :=
  ∃ y : Fin m ⊕ Fin m → K,
    spForm m K y ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0

omit [Finite G] in
@[expose] def CommSec (P I : Subgroup G) (z : G) : Subgroup G := ⁅P, Subgroup.zpowers z⁆ ⊔ I

structure Sec8Pts (hc : Ctx M Q Z B) (t r : G) (m : ℕ) (K : Type) [Field K] [Finite K]
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K) : Prop where
  two_le : 2 ≤ m
  card : Nat.card K = Nat.card Z
  range : φ.range = CFSG.Open.StatedSp m K
  ker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)
  act : SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
    (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
  uu' : spForm m K u u' ≠ 0
  hL : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u
  hL' : ((conjSubgroup r (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u'

theorem Sec8Pts.spMNat {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (h : Sec8Pts hc t r m K φ u u') : SpMNat hc t m :=
  ⟨K, inferInstance, inferInstance, h.card, φ, h.range, h.ker, h.act⟩

@[expose] def Close81Hyp (hc : Ctx M Q Z B) (n : ℕ) (t r : G) : Prop :=
  Sec8Hyp hc n t ∧ Sec7A hc t r ∧ ¬ Conc81a hc t ∧
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q →
      ∀ w ∈ Sec8W1 M Q Z B t r, ⁅x, w⁆ ∈ Sec8V1 M Q Z B t r

@[expose] def Close82Hyp (hc : Ctx M Q Z B) (n : ℕ) (t r : G) : Prop :=
  Sec8Hyp hc n t ∧ Sec7A hc t r ∧ ¬ Conc81a hc t ∧ Conc81b hc t r

end CFSG.RankThree.GF2n.Stroth80
