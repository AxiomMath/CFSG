module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.Timmesfeld.Defs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Stroth80.Sec311Cover

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld.RootInvolutions
open Subgroup
open scoped commutatorElement

section Bridges

variable {G : Type} [Group G]

theorem wac_eq_weakClosure (A : Subgroup G) :
    WAC A = weakClosure A (centralizer (A : Set G)) := by
  apply le_antisymm
  · refine iSup₂_le fun g hg x hx => ?_
    unfold CFSG.Timmesfeld.RootInvolutions.weakClosure
    exact Subgroup.subset_closure ⟨g, hg, hx⟩
  · unfold CFSG.Timmesfeld.RootInvolutions.weakClosure
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨g, hg, hx⟩
    exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hg hx)

theorem sylow_le_normalizer_iff (A : Subgroup G) [Finite G] :
    (∃ S : Sylow 2 G, (S : Subgroup G) ≤ normalizer (A : Set G)) ↔
      ∃ S : Subgroup G, IsPGroup 2 S ∧ (∀ T : Subgroup G, IsPGroup 2 T → S ≤ T → T = S) ∧
        S ≤ normalizer (A : Set G) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S, S.isPGroup', fun T hT hST => S.is_maximal' hT hST, hS⟩
  · rintro ⟨S, hS, hmax, hle⟩
    exact ⟨⟨S, hS, fun {Q} hQ hle' => hmax Q hQ hle'⟩, hle⟩

@[expose] def Cor2Alt1 (A : Subgroup G) : Prop := WAC A = A ∧ ThmAConclusion A

@[expose] def Cor2Alt2Alpha (A : Subgroup G) : Prop :=
  IsCoveringOf Tim77Cor2AlphaList ↥(Subgroup.normalClosure (A : Set G))

@[expose] def Cor2Alt2Beta (A : Subgroup G) : Prop :=
  ⁅WAC A, WAC A⁆ = ⊥ ∧
    ∃ (r : ℕ) (X : Fin r → Subgroup ↥(Subgroup.normalClosure (A : Set G))),
      (∀ i, (X i).Normal) ∧ (∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) ∧
      ⨆ i, X i = ⊤ ∧
      ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)

@[expose] def Cor2Alt3 (A : Subgroup G) : Prop :=
  ∃ (N : Subgroup ↥(Subgroup.normalClosure (A : Set G))) (_ : N.Normal), IsElemAbelian 2 N ∧
    Nat.card A = 2 * Nat.card ↥(A ⊓ N.map (Subgroup.normalClosure (A : Set G)).subtype) ∧
    ∃ Z : Subgroup (↥(Subgroup.normalClosure (A : Set G)) ⧸ N),
      Z ≤ Subgroup.center (↥(Subgroup.normalClosure (A : Set G)) ⧸ N) ∧
      ∃ _ : Z.Normal, Tim77Cor2BetaList ((↥(Subgroup.normalClosure (A : Set G)) ⧸ N) ⧸ Z)

end Bridges

theorem tim77Cor2_iff : Tim77Cor2Statement ↔
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian 2 A → IsTI A →
      ⁅WAC A, WAC A⁆ ≤ A → (∃ S : Sylow 2 G, (S : Subgroup G) ≤ normalizer (A : Set G)) →
      Cor2Alt1 A ∨ Cor2Alt2Alpha A ∨ Cor2Alt2Beta A ∨ Cor2Alt3 A := Iff.rfl

@[expose] def Tim77Lemma21Statement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (D : Set Y), CFSG.Timmesfeld.IsRootInvolutionSet D →
    (∃ d₀ : Y, D = {g | IsConj d₀ g}) → Subgroup.closure D = ⊤ → Group.IsSolvable Y →
    (∀ d ∈ D, IsMulCommutative (Subgroup.closure {e | e ∈ D ∧ e * d = d * e})) →
    haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
    ZStarCase (Y ⧸ CFSG.pCore 2 Y)

section Ctx

variable {G : Type} [Group G]

structure Sec3Ctx (A Abar S₀ B : Subgroup G) : Prop where
  hyp : ElementaryAbelianTIRootCentralizerHypothesis A
  not_root : ¬ IsRootType 2 A
  not_wc : ¬ ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A
  nota : Section3.Notation A Abar S₀ B

@[expose] def Sec3SChoiceAt (A Abar S₀ B : Subgroup G) (b s : G) : Prop :=
  b ∈ B ∧ b ≠ 1 ∧
    ((∃ x ∈ Section3.Abar0 A Abar, x ≠ 1 ∧ (orderOf (x * b) = 2 ∨ orderOf (x * b) = 4)) ∧ s = b ∨
     ((∀ x ∈ Section3.Abar0 A Abar, x ≠ 1 → orderOf (x * b) ≠ 2 ∧ orderOf (x * b) ≠ 4) ∧
      ∃ x ∈ Section3.Abar0 A Abar, x ≠ 1 ∧
        s ∈ Subgroup.closure {x, b} ∧ s ∈ S₀ ∧ s ∈ centralizer (A : Set G) ∧
        Section3.Abar0 A Abar ≠ conjSubgroup s (Section3.Abar0 A Abar) ∧
        (∀ a ∈ Section3.Abar0 A Abar, ∀ c ∈ conjSubgroup s (Section3.Abar0 A Abar), a * c = c * a) ∧
        orderOf s = 4))

theorem isSChoice_iff {A Abar S₀ B : Subgroup G} {s : G} :
    Section3.IsSChoice A Abar S₀ B s ↔ ∃ b, Sec3SChoiceAt A Abar S₀ B b s := Iff.rfl

@[expose] def Sec4A0LeCenterH (A Abar : Subgroup G) : Prop :=
  Section3.A0 A Abar ≤ (Subgroup.center (Section5.H A Abar)).map (Section5.H A Abar).subtype

@[expose] def Sec45Z (A Abar B : Subgroup G) : Subgroup G := A ⊔ ⨆ b ∈ B, conjSubgroup b Abar

@[expose] def Sec45Q (A Abar B : Subgroup G) : Subgroup G :=
  Section3.A0 A Abar ⊔ ⨆ b ∈ B, conjSubgroup b (Section3.Abar0 A Abar)

end Ctx

@[expose] def IsPSL2Model (R : Type) [Group R] (f : ℕ) : Prop :=
  Nonempty (R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))

@[expose] def IsSzModel (R : Type) [Group R] (a : ℕ) : Prop := Nonempty (R ≃* Sz a)

@[expose] def Tim77Sec31Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    ∀ x ∈ Section3.Abar0 A Abar, x ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      orderOf (x * b) ≠ 2 → orderOf (x * b) ≠ 4 →
      ∃ s ∈ Subgroup.closure ({x, b} : Set G), s ∈ S₀ ∧ s ∈ centralizer (A : Set G) ∧
        Section3.Abar0 A Abar ≠ conjSubgroup s (Section3.Abar0 A Abar) ∧
        (∀ a ∈ Section3.Abar0 A Abar, ∀ c ∈ conjSubgroup s (Section3.Abar0 A Abar),
          a * c = c * a) ∧ orderOf s = 4

@[expose] def Tim77Sec32aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G) (s : G), Sec3Ctx A Abar S₀ B →
    Section3.IsSChoice A Abar S₀ B s →
      Section3.N A Abar s ≤ Section3.Y A Abar s ∧
      (∀ y ∈ Section3.Y A Abar s, y ∈ normalizer (Section3.N A Abar s : Set G)) ∧
      IsElemAbelian 2 (Section3.N A Abar s)

@[expose] def Tim77Sec32bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G) (s : G), Sec3Ctx A Abar S₀ B →
    Section3.IsSChoice A Abar S₀ B s →
      (pCore 2 ↥(Section3.Y A Abar s)).map (Section3.Y A Abar s).subtype ≤
        normalizer (A : Set G) ∧
      ⁅(pCore 2 ↥(Section3.Y A Abar s)).map (Section3.Y A Abar s).subtype, Section3.Y A Abar s⁆ ≤
        Section3.N A Abar s

@[expose] def Tim77Sec41Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G) (s : G), Sec3Ctx A Abar S₀ B →
    Section3.IsSChoice A Abar S₀ B s →
      (∃ d₀ ∈ Section4.D A Abar s, ∀ d ∈ Section4.D A Abar s,
        ∃ y ∈ Section3.Y A Abar s, d = y * d₀ * y⁻¹) ∧
      CFSG.Timmesfeld.IsRootInvolutionSet (Section4.D A Abar s) ∧
      (∀ d ∈ Section4.D A Abar s, ∀ e ∈ Section4.D A Abar s, orderOf (d * e) ≠ 4) ∧
      (∀ d ∈ Section4.D A Abar s,
        IsElemAbelian 2 (Subgroup.closure {e | e ∈ Section4.D A Abar s ∧ e * d = d * e}))

@[expose] def Tim77Sec33Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G) (s : G), Sec3Ctx A Abar S₀ B →
    Section3.IsSChoice A Abar S₀ B s → 2 < Section3.q A Abar →
      Section3.Y A Abar s = Section3.X A Abar

@[expose] def Tim77Sec34Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G) (b s : G), Sec3Ctx A Abar S₀ B →
    Sec3SChoiceAt A Abar S₀ B b s →
      Section3.Y A Abar s = Section3.X A Abar → s = b

@[expose] def Tim77Sec35Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    ¬ B ≤ normalizer (Section3.X A Abar : Set G)

@[expose] def Tim77ExistsNotationStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    ElementaryAbelianTIRootCentralizerHypothesis A → ¬ IsRootType 2 A →
    (¬ ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) →
      ∃ Abar S₀ B : Subgroup G, Section3.Notation A Abar S₀ B

@[expose] def Tim77Sec43Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G) (s : G), Sec3Ctx A Abar S₀ B →
    Section3.IsSChoice A Abar S₀ B s → Section3.q A Abar = 2 →
      Group.IsSolvable ↥(Section3.Y A Abar s) → Section3.Y A Abar s = Section3.X A Abar

@[expose] def Tim77Sec44Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → ∀ b ∈ B, b ≠ 1 →
      ∃ x ∈ Section3.Abar0 A Abar, x ≠ 1 ∧ (orderOf (x * b) = 2 ∨ orderOf (x * b) = 4)

@[expose] def Tim77Sec47Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 →
      ∀ B' : Subgroup G, (∃ g : G, B' = conjSubgroup g A) → B' ≤ S₀ →
        Section3.Abar0 A Abar ≤ normalizer (B' : Set G)

@[expose] def Tim77Sec48Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 →
      ∀ B' C' : Subgroup G, (∃ g : G, B' = conjSubgroup g A) → (∃ g : G, C' = conjSubgroup g A) →
        (∀ b ∈ B', b ≠ 1 → ∀ c ∈ C', c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4) →
          ∀ b ∈ B', ∀ c ∈ C', b * c = c * b

@[expose] def Tim77Sec49Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
      IsTI (Section3.A0 A Abar) ∧
      (∀ a ∈ A, a ∉ Section3.A0 A Abar → ∀ a' ∈ A, a' ∉ Section3.A0 A Abar →
        ∃ h ∈ Section5.H A Abar, h * a * h⁻¹ = a') ∧
      (∀ g ∈ normalizer (A : Set G), ∀ a ∈ Section3.A0 A Abar, g * a * g⁻¹ ∈ Section3.A0 A Abar) ∧
      (∀ x ∈ normalizer (A : Set G), x ≠ 1 → (∃ g : G, x ∈ conjSubgroup g A) →
        Section3.A0 A Abar = A ⊓ centralizer ({x} : Set G) ∨ x ∈ centralizer (A : Set G))

@[expose] def Tim77Sec411Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
      IsElemAbelian 2 (⨆ (g : G) (_ : conjSubgroup g A ≤ S₀), conjSubgroup g A)

@[expose] def Tim77Sec412Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
      ∀ a ∈ A, a ∉ Section3.A0 A Abar → ∀ g : G, ∀ x ∈ conjSubgroup g A,
        orderOf (a * x) = 4 → x ∈ normalizer (A : Set G)

@[expose] def Tim77Sec414Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar → Section3.A0 A Abar ≤ pCore 2 G

@[expose] def Sec415N0 {G : Type} [Group G] (A Abar : Subgroup G) : Subgroup G :=
  ⨆ g : G, conjSubgroup g (Section3.A0 A Abar)

@[expose] def Sec415E {G : Type} [Group G] (A Abar : Subgroup G) : Set G :=
  {t | ∃ g : G, ∃ a ∈ A, a ∉ Section3.A0 A Abar ∧ t = g * a * g⁻¹}

@[expose] def Tim77Sec415aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
      (Sec415N0 A Abar).Normal ∧ IsElemAbelian 2 (Sec415N0 A Abar) ∧
      A ⊓ Sec415N0 A Abar = Section3.A0 A Abar ∧ Sec45Q A Abar B ≤ Sec415N0 A Abar

@[expose] def Tim77Sec415bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
      (∃ e₀ ∈ Sec415E A Abar, ∀ e ∈ Sec415E A Abar,
        ∃ y ∈ Subgroup.normalClosure (A : Set G), e = y * e₀ * y⁻¹) ∧
      CFSG.Timmesfeld.IsRootInvolutionSet (Sec415E A Abar) ∧
      (∀ d ∈ Sec415E A Abar, ∀ e ∈ Sec415E A Abar, orderOf (d * e) ≠ 4) ∧
      (∀ e ∈ Sec415E A Abar,
        IsElemAbelian 2 (Subgroup.closure {f | f ∈ Sec415E A Abar ∧ f * e = e * f}))

@[expose] def Tim77Sec415cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
      ⁅pCore 2 ↥(Subgroup.normalClosure (A : Set G)), ⊤⁆ ≤
        (Sec415N0 A Abar).subgroupOf (Subgroup.normalClosure (A : Set G))

@[expose] def Tim77Sec415Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar → Cor2Alt3 A

@[expose] def Tim77Sec50Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → ¬ Sec4A0LeCenterH A Abar →
      ∃ g ∈ normalizer (A : Set G), g ∉ normalizer (Section3.A0 A Abar : Set G)

@[expose] def Tim77Sec51Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → ¬ Sec4A0LeCenterH A Abar →
      ∀ S : Subgroup G, IsPGroup 2 S → S ≤ normalizer (Section3.A0 A Abar : Set G) →
        (∀ T : Subgroup G, IsPGroup 2 T → T ≤ normalizer (Section3.A0 A Abar : Set G) → S ≤ T →
          T = S) → Section3.Abar0 A Abar ≤ S →
        IsElemAbelian 2 (⨆ h ∈ S, conjSubgroup h (Section3.Abar0 A Abar))

@[expose] def Tim77Sec53Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → ¬ Sec4A0LeCenterH A Abar →
    ∀ [((Section3.M A Abar).subgroupOf (Section3.X A Abar)).Normal],
      Nonempty (↥(Section3.X A Abar) ⧸ (Section3.M A Abar).subgroupOf (Section3.X A Abar) ≃*
        DihedralGroup 3)

@[expose] def Tim77Sec54Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 →
    (∀ Abar' S₀' B' : Subgroup G, Sec3Ctx A Abar' S₀' B' → ¬ Sec4A0LeCenterH A Abar') → False

@[expose] def Tim77Thm1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    ElementaryAbelianTIRootCentralizerHypothesis A →
      IsRootType 2 A ∨
      (∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) ∨
      Cor2Alt3 A

@[expose] def Tim77AlphaBox : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian 2 A → IsTI A →
    IsRootType 2 A → ⁅WAC A, WAC A⁆ ≤ A → ⁅WAC A, WAC A⁆ ≠ ⊥ →
      IsCoveringOf Tim77Cor2AlphaList ↥(Subgroup.normalClosure (A : Set G))

@[expose] def Tim77BetaBox : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian 2 A → IsTI A →
    IsRootType 2 A → ⁅WAC A, WAC A⁆ = ⊥ →
    (∃ S : Sylow 2 G, (S : Subgroup G) ≤ normalizer (A : Set G)) →
    ∃ (r : ℕ) (X : Fin r → Subgroup ↥(Subgroup.normalClosure (A : Set G))),
      (∀ i, (X i).Normal) ∧ (∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) ∧
      ⨆ i, X i = ⊤ ∧ ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)

structure Tim77Leaves : Prop where
  exNotation : Tim77ExistsNotationStatement
  sec31 : Tim77Sec31Statement
  sec33 : Tim77Sec33Statement
  sec34 : Tim77Sec34Statement
  sec35 : Tim77Sec35Statement
  sec415 : Tim77Sec415Statement
  sec54 : Tim77Sec54Statement
  alpha : Tim77AlphaBox
  beta : Tim77BetaBox

end CFSG.RankThree.GF2n.Tim77
