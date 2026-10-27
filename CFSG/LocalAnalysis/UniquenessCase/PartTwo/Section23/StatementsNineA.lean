module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure S23_9_A0Data (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) where
  q : ℕ
  hq : q.Prime
  hq2 : q ≠ 2
  Q : Subgroup G
  hQM : Q ≤ D.M
  hQp : IsPGroup q ↥Q
  hQnc : ¬ IsCyclic ↥Q
  hQexp : ∀ x ∈ Q, x ^ q = 1
  hQclass : ⁅⁅Q, Q⁆, Q⁆ = ⊥
  hQnorm : D.M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 D.M ⊔ Q : Subgroup G) : Set G)
  E : Subgroup (Bar2 D.M)
  hEnorm : E.Normal
  hEp : IsPGroup q ↥E
  hEne : E ≠ ⊥
  hEnc : ¬ IsCyclic ↥E
  hEexp : ∀ x ∈ E, x ^ q = 1
  hEclass : ⁅⁅E, E⁆, E⁆ = ⊥
  hEel : IsElementaryAbelian q (↥E ⧸ frattini ↥E)
  hEQ : barImage D.M Q = E

namespace S23_9_A0Data

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}

@[expose] noncomputable def rep (d : S23_9_A0Data D Ch c) :
    letI : Fact d.q.Prime := ⟨d.hq⟩
    letI : d.E.Normal := d.hEnorm
    letI : IsPGroup d.q ↥d.E := d.hEp
    letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
    letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
    Representation (ZMod d.q) (Bar2 D.M) (Additive (↥d.E ⧸ frattini ↥d.E)) := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  exact CFSG.RankThree.PartOne.FixedRank36.frattiniRep d.q (MulAut.conjNormal (H := d.E))

@[expose] noncomputable def fixV (d : S23_9_A0Data D Ch c) (X : Subgroup (Bar2 D.M)) :
    letI : Fact d.q.Prime := ⟨d.hq⟩
    letI : d.E.Normal := d.hEnorm
    letI : IsPGroup d.q ↥d.E := d.hEp
    letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
    letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
    Submodule (ZMod d.q) (Additive (↥d.E ⧸ frattini ↥d.E)) := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  exact UCK.fixV d.rep X

end S23_9_A0Data

@[expose] def S23_9_A0 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    let K : Subgroup G := Hinf (D.M ⊓ c.L)
    K ≠ ⊥ → ⁅barImage D.M K, CFSG.fittingSubgroup (Bar2 D.M)⁆ ≠ ⊥ →
      ∃ d : S23_9_A0Data D Ch c, ¬ barImage D.M K ≤ d.rep.ker

@[expose] def S23_9_SU44 (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) : Prop :=
  let Lstar : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
  IsSUn ↥Lstar 4 2 ∧ NatSUn Lstar ⊤ ⊥ 4 2 ∧ c.n = 4

structure S23_9_AdjData (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (dA0 : S23_9_A0Data D Ch c)
    (b : G) (hb : b ∈ c.B0) (r : ℕ) where
  m : ℕ
  hm2 : 2 ≤ m
  hrm : r ∣ 2 ^ m - 1
  hparity : (∃ k : ℕ, c.n = 2 ^ k) → ¬ S23_9_SU44 D Ch c hV → 4 ≤ m ∧ Even m
  X : Subgroup G
  hXK : X ≤ Hinf (D.M ⊓ c.L)
  hXperf : ⁅X, X⁆ = X
  hXsl : IsSLn (Bar2 X) 2 m
  hbX : b ∈ Subgroup.normalizer (X : Set G)
  dRoot : G
  hdX : dRoot ∈ X
  hdorder : orderOf dRoot = r
  hdb : dRoot * b = b * dRoot
  hinner : ∀ x ∈ X, b * x * b⁻¹ * (dRoot * x * dRoot⁻¹)⁻¹ ∈ (CFSG.pCore 2 ↥X).map X.subtype
  hnotker : ¬ barImage D.M X ≤ dA0.rep.ker

@[expose] def S23_9_ASem (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ d : S23_9_A0Data D Ch c,
    ∀ b (hb : b ∈ c.B0) (r : ℕ), r.Prime → r ≠ 2 → orderOf b = r →
      b ∉ Subgroup.centralizer (D.Z : Set G) →
        d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥ ∧ r ≠ d.q

@[expose] def S23_9_Adj (D : Data G) (Ch : Choice2011 G) : Prop :=
  KAdj → H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ (hV : IsElemAbelian 2 c.V), ∀ d : S23_9_A0Data D Ch c,
      ¬ barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker →
      ∀ b (hb : b ∈ c.B0) (r : ℕ), r.Prime → r ≠ 2 → orderOf b = r →
        b ∉ Subgroup.centralizer (D.Z : Set G) →
        ((∃ s : ℕ, s ∣ c.n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
          (∃ k : ℕ, c.n = 2 ^ k ∧ r = 3)) →
          Nonempty (S23_9_AdjData D Ch c hV d b hb r)

@[expose] def S23_9_A3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ (hV : IsElemAbelian 2 c.V),
    ∀ d : S23_9_A0Data D Ch c,
    ∀ b (hb : b ∈ c.B0) (r : ℕ), r.Prime → r ≠ 2 → orderOf b = r →
      (∃ s : ℕ, s ∣ c.n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) →
      d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥ → r ≠ d.q →
      ∀ a : S23_9_AdjData D Ch c hV d b hb r,
        ¬ (∃ k : ℕ, c.n = 2 ^ k) → False

@[expose] def S23_9_A4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ (hV : IsElemAbelian 2 c.V), ∀ d : S23_9_A0Data D Ch c,
    ∀ b (hb : b ∈ c.B0) (r : ℕ), r.Prime → r ≠ 2 → orderOf b = r → r = 3 →
      d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥ → r ≠ d.q →
      (∃ k : ℕ, c.n = 2 ^ k) → ¬ S23_9_SU44 D Ch c hV →
      ∀ a : S23_9_AdjData D Ch c hV d b hb r,
        CFSG.LocalAnalysis.UniquenessCase.UCK.K462 → False

@[expose] def S23_9_A5 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ (hV : IsElemAbelian 2 c.V),
    ∀ d : S23_9_A0Data D Ch c,
      S23_9_SU44 D Ch c hV → KSU44 → S23_9_Semireg D Ch →
      d.q ≠ 3 → ¬ barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker → False

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
