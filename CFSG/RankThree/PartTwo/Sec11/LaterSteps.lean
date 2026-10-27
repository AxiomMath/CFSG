module

public import CFSG.RankThree.PartTwo.Sec11.Final
public import CFSG.RankThree.PartTwo.Sec8.Groups

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

@[expose] noncomputable def sec11YA [Finite G] (a : G) (Y A : Subgroup G) :
    Subgroup (Subgroup.centralizer ({a} : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) :=
  ((Y ⊔ A).subgroupOf (Subgroup.centralizer ({a} : Set G))).map (QuotientGroup.mk' _)

@[expose] def YNotField [Finite G] (c : G) (L : Subgroup G) (e : G) : Prop :=
  ∃ Ye ∈ thetaComponentsAt 3 e, sec11K L e ≤ Ye ∧ ¬ KFacts.InducesStdKind Ye c .field

@[expose] def Item118 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d g : G, A ⊓ L = Subgroup.zpowers d →
      A = Subgroup.closure {c, a, d} → g ∈ Subgroup.normalizer (A : Set G) →
        g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        g * c * g⁻¹ ∈ Subgroup.closure {c, d} →
          d ∈ L.map (MulAut.conj g).toMonoidHom ∧
            inSubgroup perfectResidual
              (Subgroup.centralizer {a} ⊓ L.map (MulAut.conj g).toMonoidHom) ≤ Y ∧
            Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
              (Subgroup.zpowers a : Set G)

@[expose] def Item119 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      A = Subgroup.closure {c, a, d} →
        (KFacts.InducesStdKind Y c .field ∧ Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3))) ∨
          (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
                Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
                  (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
              ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
                Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
                  (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
            Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) ∨
          ((Sec8.IsZ3LThreePi (sec11YA a Y A) ∨ Sec8.IsZ3PGLThreePi (sec11YA a Y A)) ∧
            Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3))) ∨
          ((Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
                CFSG.Blueprint.NativeSporadic.M24) ∨
              Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
                CFSG.Blueprint.NativeSporadic.He)) ∧
            Nonempty (sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a) ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1)) ∧
            Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6))

@[expose] def Item1115 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g → s * a = a * s

@[expose] def Item1116 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      (Subgroup.zpowers s ≠ Subgroup.zpowers c ∨
        Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) →
        9 < orderOf x

@[expose] def Item1117 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
        (∃ a' ∈ A, a' ∉ Subgroup.closure {c, d} ∧
          ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {a', d} ∧ YNotField c L a') ∧
        orderOf x = 9

@[expose] def Item1118 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g → orderOf x = 9

structure Sec11Big (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R Y : Subgroup G) (d x s r g : G) : Prop
    extends Sec11Data G A c L a R Y d x s r g where
  orderOf_x_gt : 9 < orderOf x
  isList : (∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) q) ∨
    (∃ n : ℕ, Sec8.IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) n) ∨
    Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)
  not_field : ¬ KFacts.InducesStdKind Y c .field
  orderOf_g : orderOf g = 3
  exists_inverts : ∃ t ∈ sec11K L a ⊓ Subgroup.normalizer (A : Set G),
    ∀ z ∈ A, t * g * t⁻¹ * z * (t * g * t⁻¹)⁻¹ = g⁻¹ * z * g

@[expose] def SetUp1118 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g → 9 < orderOf x →
      ∃ (a' : G) (Y' : Subgroup G) (r' g' : G), Sec11Big G A c L a' R Y' d x s r' g'

@[expose] def Item1119 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      ∃ (c' : G) (L' : Subgroup G) (a' : G) (R' Y' : Subgroup G) (x' s' r' g' : G),
        Sec11Big G A c' L' a' R' Y' d x' s' r' g' ∧
          Subgroup.normalizer ((sec11P R' g' : Subgroup G) : Set G) ≤
            Subgroup.normalizer ((Subgroup.closure {c', d} : Subgroup G) : Set G)

@[expose] def Item1120 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      sec11P R g ≤ Subgroup.normalizer ((Subgroup.closure {s, x, a} : Subgroup G) : Set G)

@[expose] def Item1123 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}

@[expose] def Item1125 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      Subgroup.zpowers s ≠ Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      ¬ ∃ j ∈ Subgroup.centralizer {g} ⊓ Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓
          Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        ∀ y ∈ Subgroup.closure ({s ^ 3, x ^ 9} : Set G), j * y * j⁻¹ = y⁻¹

@[expose] def Sec11BigNever : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), ¬ Sec11Big G A c L a R Y d x s r g

theorem item1118_of (h1116 : Item1116) (h1117 : Item1117) (hset : SetUp1118)
    (hnever : Sec11BigNever) : Item1118 := by
  intro G _ _ A c L a R Y d x s r g h
  by_cases hs : Subgroup.zpowers s = Subgroup.zpowers c ∧
    Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  · exact (h1117 G A c L a R Y d x s r g h hs.1 hs.2).2
  · exfalso
    have hx : 9 < orderOf x := h1116 G A c L a R Y d x s r g h (by tauto)
    obtain ⟨a', Y', r', g', hbig⟩ := hset G A c L a R Y d x s r g h hx
    exact hnever G A c L a' R Y' d x s r' g' hbig

end CFSG.RankThree.PartTwo.Sec11
