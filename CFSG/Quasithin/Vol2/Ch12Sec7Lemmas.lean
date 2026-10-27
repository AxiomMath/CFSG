module

public import CFSG.Quasithin.Vol2.Ch12Sec7Frame
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Vol2.Ch12Sec7Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

@[expose] def Setup1271 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    IsElemAbelian 2 V ∧ Nat.card ↥V = 2 ^ 6 ∧
    L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧
    Nat.card ↥(autOn (XOf L) V) = 3 ∧
    autOn (XOf L) V ≤ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) ∧
    ∀ x ∈ XOf L, x ∉ Subgroup.centralizer (V : Set G) →
      V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥

@[expose] def Lemma12_7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (h : Hyp1271 G T L V),
    (maxOver (L ⊔ pCoreOf 2 (L ⊔ T)) ((T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T)) = {P1 T L V, P2 T L V} ∧
      P1 T L V ≠ P2 T L V) ∧
    (h.hyp.MVbar = autOn L V ∨
      (h.hyp.MVbar = autOn L V ⊔ autOn T V ∧
        Nonempty (↥h.hyp.MVbar ⧸ CFSG.pCore 3 ↥h.hyp.MVbar ≃* Equiv.Perm (Fin 6)))) ∧
    (IsFPoint L V (V1 T L V) ∧
      (L ⊔ T) ⊓ Subgroup.normalizer (V1 T L V : Set G) = P1 T L V ⊔ T ∧
      Nat.card ↥(autOn (R1 T L V) V) = 4 ∧
      (∀ r ∈ R1 T L V, r ^ 2 ∈ Subgroup.centralizer (V : Set G)) ∧
      (∀ r ∈ R1 T L V, r ∉ Subgroup.centralizer (V : Set G) →
        ⁅V, Subgroup.zpowers r⁆ = V1 T L V) ∧
      V ⊓ Subgroup.centralizer (R1 T L V : Set G) = V1 T L V) ∧
    (IsIrredOnSection (P1 T L V) V (V1 T L V) ∧ IsIrredOnSection (P1 T L V) (V1 T L V) ⊥) ∧
    (IsFLine L V (V2 T L V) ∧
      (L ⊔ T) ⊓ Subgroup.normalizer (V2 T L V : Set G) = P2 T L V ⊔ T ∧
      Nat.card ↥(autOn (R2 T L V) V) = 4 ∧
      (∀ r ∈ R2 T L V, r ^ 2 ∈ Subgroup.centralizer (V : Set G)) ∧
      (∀ r ∈ R2 T L V, r ∉ Subgroup.centralizer (V : Set G) →
        V ⊓ Subgroup.centralizer ({r} : Set G) = V2 T L V) ∧
      ⁅V, R2 T L V⁆ = V2 T L V) ∧
    (oTwoUpper (P1 T L V) = L1 T L V ⊔ XOf L ∧
      {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
        oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} = {L1 T L V, XOf L} ∧
      oTwoUpper (P2 T L V) = L2 T L V ⊔ XOf L ∧
      {I : Subgroup G | I ≤ P2 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
        oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} = {L2 T L V, XOf L}) ∧
    thetaOf (Subgroup.normalizer (L : Set G)) = L

@[expose] def Lemma12_7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (h : Hyp1271 G T L V),
    E3.aSet 2 (autOn T V) = {autOn (R2 T L V) V} ∧ E3.aParam h.hyp.MVbar = 2

@[expose] def Lemma12_7_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    (∃ z ∈ V1 T L V, z ≠ 1 ∧ T ≤ Subgroup.centralizer ({z} : Set G) ∧ ∃ t ∈ V, t ≠ 1 ∧
      (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 ∧
      (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 ∧
      ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t)) ∧
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥(autOn (L ⊓ Subgroup.normalizer (Vt L t : Set G)) V) ≃*
          Matrix.GeneralLinearGroup (Fin 2) F) ∧
        IsNaturalSection (L ⊓ Subgroup.centralizer (Vt L t : Set G)) V (Vt L t)
          ((Subgroup.centralizer (V : Set G)).subgroupOf
            (L ⊓ Subgroup.centralizer (Vt L t : Set G)))
          (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) ∧
      IsIndecomposableUnder (L ⊓ Subgroup.centralizer (Vt L t : Set G)) V ∧
      (V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))⁆ ∧
        V ≤ oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) =
          thetaOf (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) ⧸
            CFSG.pCore 2 ↥(oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) ≃*
          alternatingGroup (Fin 5)) ∧
        Group.IsPerfect ↥(oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))) ∧
      {W : Subgroup G | IsFPoint L V W ∧ W ≤ V2 T L V ∧
          ∃ l ∈ L, W = (Vt L t).map (MulAut.conj l).toMonoidHom}.ncard = 2 ∧
      {W : Subgroup G | IsFPoint L V W ∧ W ≤ V2 T L V ∧
          ∃ l ∈ L, W = (V1 T L V).map (MulAut.conj l).toMonoidHom}.ncard = 3

@[expose] def Lemma12_7_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) ∨
      (IsComponentOf (conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
          (Subgroup.centralizer ({t} : Set G))) (Subgroup.centralizer ({t} : Set G)) ∧
        (Subgroup.center ↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
            (Subgroup.centralizer ({t} : Set G)))).map
          (conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
            (Subgroup.centralizer ({t} : Set G))).subtype = Vt L t ∧
        IsPSL 3 2 2
          (↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
              (Subgroup.centralizer ({t} : Set G))) ⧸
            Subgroup.center ↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
              (Subgroup.centralizer ({t} : Set G)))))

namespace S127

structure Setting1273 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G) : Prop where
  hyp : Hyp1271 G T L V
  t_mem : t ∈ V
  orbit_t : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18
  Gt_le : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)

end S127

@[expose] def Lemma12_7_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Setting1273 G T L V t →
    (∀ i ∈ V, ∀ j ∈ V, (∃ g : G, g * i * g⁻¹ = j) →
        ∃ m ∈ Subgroup.normalizer (L : Set G), m * i * m⁻¹ = j) ∧
    (∀ v ∈ V, ∀ g₁ g₂ : G, v ∈ conjSubgroup V g₁ → v ∈ conjSubgroup V g₂ →
      ∃ c ∈ Subgroup.centralizer ({v} : Set G), conjSubgroup V g₂ = conjSubgroup V (g₁ * c)) ∧
    ∀ g : G, t ∈ conjSubgroup V g → conjSubgroup V g = V

@[expose] def Lemma12_7_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V] (t : G)
    (h : Setting1273 G T L V t),
    E3.mParam h.hyp.hyp.MVbar = 2 ∧
    (2 < E3.rParam V ∧ ∀ hV : IsElemAbelian 2 V, E3.sParam hV = 2) ∧
    (autOn L V < h.hyp.hyp.MVbar →
      ∃ i₁ ∈ h.hyp.hyp.MVbar, ∃ i₂ ∈ h.hyp.hyp.MVbar,
        i₁ ∉ autOn L V ∧ i₂ ∉ autOn L V ∧ orderOf i₁ = 2 ∧ orderOf i₂ = 2 ∧
        (∀ y ∈ h.hyp.hyp.MVbar, y ∉ autOn L V → orderOf y = 2 →
          (∃ m ∈ h.hyp.hyp.MVbar, y = m * i₁ * m⁻¹) ∨ (∃ m ∈ h.hyp.hyp.MVbar, y = m * i₂ * m⁻¹)) ∧
        (¬ ∃ m ∈ h.hyp.hyp.MVbar, i₂ = m * i₁ * m⁻¹) ∧
        autOn (L1 T L V ⊔ T) V ⊓
            Subgroup.centralizer (autOn (L1 T L V ⊔ T) V : Set (MulAut ↥V)) =
          Subgroup.zpowers i₁ ∧
        autOn (L2 T L V ⊔ T) V ⊓
            Subgroup.centralizer (autOn (L2 T L V ⊔ T) V : Set (MulAut ↥V)) =
          Subgroup.zpowers i₂ ∧
        Nat.card ↥(fixV (Subgroup.zpowers i₁)) = 8 ∧ Nat.card ↥(fixV (Subgroup.zpowers i₂)) = 8 ∧
        (∃ l ∈ L, Acts i₂ ((Vt L t).map (MulAut.conj l).toMonoidHom)) ∧
        ∀ l ∈ L, ¬ Acts i₁ ((Vt L t).map (MulAut.conj l).toMonoidHom)) ∧
    (∀ U : Subgroup G, U ≤ V → E3.mQuot V U = 3 →
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
          Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) ∨
      (∃ l ∈ L, U.map (MulAut.conj l).toMonoidHom ≤ V2 T L V ∧
        E3.mQuot (V2 T L V) (U.map (MulAut.conj l).toMonoidHom) = 1 ∧
        Subgroup.normalizer (L : Set G) ⊓
            Subgroup.centralizer (U.map (MulAut.conj l).toMonoidHom : Set G) =
          (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V) ∨
      (∃ y ∈ h.hyp.hyp.MVbar, y ∉ autOn L V ∧ orderOf y = 2 ∧
        U = (fixV (Subgroup.zpowers y)).map V.subtype ∧
        ∃ i ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G),
          (∀ v : ↥V, ((y v : ↥V) : G) = i * v * i⁻¹) ∧
          Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
            Subgroup.zpowers i ⊔
              (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)))) ∧
    ∀ U : Subgroup G, U ≤ V → E3.mQuot V U = 3 →
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∃ y ∈ h.hyp.hyp.MVbar, y ∉ autOn L V ∧ orderOf y = 2 ∧
          (∀ l ∈ L, ¬ Acts y ((Vt L t).map (MulAut.conj l).toMonoidHom)) ∧
          U = (fixV (Subgroup.zpowers y)).map V.subtype

@[expose] def Lemma12_7_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Setting1273 G T L V t →
    E3.wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧ 0 < E3.wParam T V ∧
      Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_7_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Setting1273 G T L V t →
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥

end CFSG.Quasithin.H13
