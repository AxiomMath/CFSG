module

public import CFSG.Sporadic.SuzRecog.C1ModelBase
public import Certificates.Data.CFSGNative.PSL3Four.L34Syl
public import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

@[expose] noncomputable def decSubgroup (l : List Dec) : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (decPerm '' {d : Dec | d ∈ l})

@[expose] noncomputable def tabSubgroup (T : Array Tab) : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (Set.range fun i : Fin T.size => permC 1782 T[i.val]!)

@[expose] noncomputable def l1BasisPerm (i : Nat) : Equiv.Perm (Fin 1782) :=
  decPerm (l1Decs.getD i ([], 1))

@[expose] noncomputable def fixedCard (p : Equiv.Perm (Fin 1782)) : Nat :=
  Nat.card (Function.fixedPoints p)

@[expose] noncomputable def F1Prop : Prop :=
  let S1' := decSubgroup s1pDecs
  let L1 := decSubgroup l1Decs
  let t1 := permC 1782 tTab
  Nat.card S1' = 8192 ∧
    t1 ∈ S1' ∧
    (∀ x : Equiv.Perm (Fin 1782), x ∈ S1' →
      ((∀ y ∈ S1', x * y = y * x) ↔ x = 1 ∨ x = t1)) ∧
    L1 ≤ S1' ∧ CFSG.Open.IsElemAbelian 2 L1 ∧ Nat.card L1 = 16 ∧
    Nat.card ↥(Subgroup.centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ S1') = 1024 ∧
    ∀ e : Equiv.Perm (Fin 1782), e ∈ S1' → e * e = 1 → e ≠ 1 → e ∉ L1 →
      9 ≤ Nat.card ↥{x : Equiv.Perm (Fin 1782) | ∃ g ∈ S1', x = g * e * g⁻¹}

@[expose] noncomputable def F2Prop : Prop :=
  let L1 := decSubgroup l1Decs
  let M1 := decSubgroup m1Decs
  let CL1 := decSubgroup cl1Decs
  let NL1 := decSubgroup nl1Decs
  let b : Fin 4 → Equiv.Perm (Fin 1782) := fun i => l1BasisPerm i.val
  Nat.card ↥{x : Fin 4 → Equiv.Perm (Fin 1782) |
      ∃ g ∈ invE 1, ∀ i, x i = g * b i * g⁻¹} = 1080 ∧
    Nat.card ↥{x : Fin 4 → Equiv.Perm (Fin 1782) |
      (∃ g ∈ invE 1, ∀ i, x i = g * b i * g⁻¹) ∧ ∀ i, x i ∈ L1} = 24 ∧
    Subgroup.centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ invE 1 = CL1 ∧
    Nat.card CL1 = 3072 ∧
    (M1.subgroupOf CL1).Normal ∧
    NL1 ≤ Subgroup.normalizer (L1 : Set (Equiv.Perm (Fin 1782)))

@[expose] noncomputable def F3Prop : Prop :=
  let M1 := decSubgroup m1Decs
  let L1 := decSubgroup l1Decs
  let NL1 := decSubgroup nl1Decs
  let W := permC 1782 w0T
  let orb : Set (Equiv.Perm (Fin 1782)) := {x | ∃ g ∈ NL1, x = g * W * g⁻¹}
  Nat.card ↥orb = 288 ∧
    (∀ x ∈ orb, x ∈ M1) ∧
    (∀ x ∈ orb, x ∉ L1) ∧
    (∀ x ∈ orb, fixedCard x = 42) ∧
    Nat.card {x : M1 // x * x = 1 ∧ x ≠ 1 ∧
      ((x : M1) : Equiv.Perm (Fin 1782)) ∉ L1} = 288

@[expose] noncomputable def F4Prop : Prop :=
  let V0 := tabSubgroup v0Tabs
  let T0 := tabSubgroup t0Tabs
  Nat.card {x : V0 // x * x = 1 ∧ x ≠ 1 ∧
      fixedCard (x : Equiv.Perm (Fin 1782)) = 54} = 27 ∧
    (∀ x : V0, x * x = 1 → x ≠ 1 → fixedCard (x : Equiv.Perm (Fin 1782)) = 54 →
      (x : Equiv.Perm (Fin 1782)) ∈ T0) ∧
    Nat.card {x : T0 // x * x = 1 ∧ x ≠ 1} = 27 ∧
    (∀ x : T0, x * x = 1 → x ≠ 1 → fixedCard (x : Equiv.Perm (Fin 1782)) = 54)

@[expose] noncomputable def F5Prop : Prop :=
  let T0 := tabSubgroup t0Tabs
  let L1 := decSubgroup l1Decs
  let M21 := decSubgroup m21Decs
  let V0 := tabSubgroup v0Tabs
  let K := decSubgroup l1CompDecs
  let ZT := Subgroup.centralizer (T0 : Set (Equiv.Perm (Fin 1782))) ⊓ T0
  let tau := decPerm tauDec
  let b : Fin 4 → Equiv.Perm (Fin 1782) := fun i => l1BasisPerm i.val
  Nat.card ZT = 4 ∧
    L1 ≤ T0 ∧ M21 ≤ T0 ∧
    T0 ≤ Subgroup.normalizer (T0 : Set (Equiv.Perm (Fin 1782))) ∧
    L1 ⊓ M21 = ZT ∧
    (∀ x ∈ T0, x * x = 1 → x ≠ 1 → x ∈ L1 ∨ x ∈ M21) ∧
    (∀ x ∈ L1, x ∉ ZT → ∀ y ∈ M21, y ∉ ZT → x * y ≠ y * x) ∧
    (∀ x ∈ L1, x ∉ ZT →
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ T0) = 16) ∧
    (∀ y ∈ M21, y ∉ ZT →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 1782))) ⊓ T0) = 16) ∧
    Nat.card K = 4 ∧ K ⊓ L1 = ⊥ ∧
    V0 ≤ Subgroup.normalizer (T0 : Set (Equiv.Perm (Fin 1782))) ∧
    tau ∈ V0 ∧
    (∀ i : Fin 4, tau * b i * tau⁻¹ ∈ M21) ∧
    (∀ x ∈ T0, x * x ∈ ZT) ∧
    (∀ x ∈ T0, ∀ y ∈ T0, x * y * x⁻¹ * y⁻¹ ∈ ZT)

@[expose] noncomputable def F6Prop : Prop :=
  let V0 := tabSubgroup v0Tabs
  let L1 := decSubgroup l1Decs
  Nat.card ↥(Subgroup.centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ V0) = 64 ∧
    Nat.card {x : V0 // ∀ y ∈ L1,
      (x : Equiv.Perm (Fin 1782)) * y * (x : Equiv.Perm (Fin 1782))⁻¹ ∈ L1} = 256 ∧
    (∀ d ∈ ntl1Decs, decPerm d ∈ V0 ∧
      ∀ y ∈ L1, decPerm d * y * (decPerm d)⁻¹ ∈ L1)

@[expose] noncomputable def F7Prop : Prop :=
  let T0 := tabSubgroup t0Tabs
  let C0 := tabSubgroup c0Tabs
  let ZT := Subgroup.centralizer (T0 : Set (Equiv.Perm (Fin 1782))) ⊓ T0
  Nat.card C0 = 16 ∧
    (∀ x ∈ C0, ∀ y ∈ C0, x * y = y * x) ∧
    (∀ x ∈ C0, x * x = 1) ∧
    ZT ≤ C0 ∧
    Nat.card (tabSubgroup ct0Tabs) = 192

@[expose] noncomputable def F8Prop : Prop :=
  let T0 := tabSubgroup t0Tabs
  let V0 := tabSubgroup v0Tabs
  let W := permC 1782 w0T
  let T11 : Set (Equiv.Perm (Fin 1782)) := {x | x ∈ T0 ∨ ∃ t ∈ T0, x = W * t}
  let lam0 := decPerm lam0Dec
  let a := decPerm aDec
  (∀ g ∈ V0, ∀ x ∈ T11, g * x * g⁻¹ ∈ T11) ∧
    (∀ x ∈ V0, x * x ∈ T11) ∧
    (∀ x ∈ V0, x * x = W → x * lam0⁻¹ ∈ T11) ∧
    (∀ a' ∈ V0, a' * a' = 1 → a' ≠ 1 → a' ≠ W → fixedCard a' = 42 →
      fixedCard (a' * W) = 42 → a' ∉ T11 ∧ a' * lam0⁻¹ ∉ T11) ∧
    a ∈ V0 ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ W ∧ fixedCard a = 42 ∧ fixedCard (a * W) = 42 ∧
    lam0 ∈ V0 ∧ lam0 * lam0 = W

@[expose] def zPTabs : Array Tab :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41],
    #[17, 15, 6, 3, 12, 14, 2, 11, 8, 16, 10, 7, 4, 13, 5, 1, 9, 0, 20, 19, 18, 38, 36, 27, 24,
      33, 35, 23, 32, 29, 37, 31, 28, 25, 34, 26, 22, 30, 21, 41, 40, 39],
    #[18, 11, 16, 3, 5, 4, 9, 15, 8, 6, 10, 1, 14, 13, 12, 7, 2, 20, 0, 19, 17, 39, 32, 37, 24,
      26, 25, 30, 36, 29, 27, 31, 22, 35, 34, 33, 28, 23, 41, 21, 40, 38],
    #[20, 7, 9, 3, 14, 12, 16, 1, 8, 2, 10, 15, 5, 13, 4, 11, 6, 18, 17, 19, 0, 41, 28, 30, 24,
      35, 33, 37, 22, 29, 23, 31, 36, 26, 34, 25, 32, 27, 39, 38, 40, 21]]

@[expose] noncomputable def tabPerm16 (t : Tab) : Equiv.Perm (Fin 16) := permC 16 t

@[expose] def xor16 (a b : Fin 16) : Fin 16 :=
  ⟨a.val ^^^ b.val, by
    have ha : a.val < 2 ^ 4 := by
      have h : (2 : Nat) ^ 4 = 16 := by norm_num
      omega
    have hb : b.val < 2 ^ 4 := by
      have h : (2 : Nat) ^ 4 = 16 := by norm_num
      omega
    have hxor : a.val ^^^ b.val < 2 ^ 4 := Nat.xor_lt_two_pow (n := 4) ha hb
    have h16 : (2 : Nat) ^ 4 = 16 := by norm_num
    omega⟩

@[expose] noncomputable def X16 (i : Nat) : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure ({tabPerm16 xA, tabPerm16 (xBs[i]!)} : Set (Equiv.Perm (Fin 16)))

@[expose] noncomputable def Tbar16 : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure
    ({tabPerm16 tbarTabs[0]!, tabPerm16 tbarTabs[1]!} : Set (Equiv.Perm (Fin 16)))

@[expose] noncomputable def F9Prop : Prop :=
  (∀ i < 4,
      Nat.card (X16 i) = 60 ∧ Tbar16 ≤ X16 i ∧
        ∀ x ∈ X16 i,
          (orderOf x = 3 ∨ orderOf x = 5) →
            ∀ j : Fin 16, x j = j → j = 0) ∧
    ∀ g : Equiv.Perm (Fin 16),
      (∀ a b : Fin 16, g (xor16 a b) = xor16 (g a) (g b)) →
        orderOf g = 5 →
          (∃ i < 4, g ∈ X16 i) ∨
            60 < Nat.card (Subgroup.closure ((Tbar16 : Set (Equiv.Perm (Fin 16))) ∪ {g}))

@[expose] noncomputable def pgPerm (i : Nat) : Equiv.Perm (Fin 42) := permC 42 pGens[i]!

@[expose] noncomputable def PG : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure ({pgPerm 0, pgPerm 1, pgPerm 2, pgPerm 3} : Set (Equiv.Perm (Fin 42)))

@[expose] noncomputable def zPPerm (i : Nat) : Equiv.Perm (Fin 42) := permC 42 zPTabs[i]!

@[expose] noncomputable def V4Sub (X : Subgroup (Equiv.Perm (Fin 16)))
    (u : Equiv.Perm (Fin 16)) : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure
    (({1, u} : Set (Equiv.Perm (Fin 16))) ∪
      {v : Equiv.Perm (Fin 16) | v ∈ X ∧ orderOf v = 2 ∧ Commute v u})

@[expose] noncomputable def F11Prop : Prop :=
  ∀ i < 4,
    let X := X16 i
    Nat.card {u : X // orderOf (u : Equiv.Perm (Fin 16)) = 2} = 15 ∧
      (∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
        Nat.card (V4Sub X (u : Equiv.Perm (Fin 16))) = 4) ∧
      ∃ V : Fin 5 → Subgroup (Equiv.Perm (Fin 16)),
        (∀ k, V k ≤ X) ∧
          (∀ k, Nat.card (V k) = 4) ∧
          (∀ k l, k ≠ l → V k ≠ V l) ∧
          (∀ k l, k ≠ l → V k ⊓ V l = ⊥) ∧
          (∀ k, ∃ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 ∧
            V k = V4Sub X (u : Equiv.Perm (Fin 16))) ∧
          (∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
            ∃ k, V k = V4Sub X (u : Equiv.Perm (Fin 16))) ∧
          (∀ u : X, orderOf (u : Equiv.Perm (Fin 16)) = 2 →
            ∃ k, (u : Equiv.Perm (Fin 16)) ∈ V k) ∧
          (∀ x : X, orderOf (x : Equiv.Perm (Fin 16)) = 5 →
            Nat.card {y : X // (y * x * y⁻¹ : X) ∈ ({x, x ^ 2, x ^ 3, x ^ 4} : Set X)} = 10) ∧
          (∀ x : X, orderOf (x : Equiv.Perm (Fin 16)) = 3 →
            Nat.card {k : Fin 5 // (x : Equiv.Perm (Fin 16)) ∈
                Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16)))} = 2 ∧
              ∃ y : X, orderOf (y : Equiv.Perm (Fin 16)) = 2 ∧
                (y * x * y⁻¹ : X) ∈ ({x, x ^ 2} : Set X) ∧
                ∃ k l : Fin 5, k ≠ l ∧
                  (x : Equiv.Perm (Fin 16)) ∈
                    Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16))) ∧
                  (x : Equiv.Perm (Fin 16)) ∈
                    Subgroup.normalizer (V l : Set (Equiv.Perm (Fin 16))) ∧
                  (V k).map (MulAut.conj (y : Equiv.Perm (Fin 16))).toMonoidHom = V l) ∧
          (∀ k, Nat.card ↥(Subgroup.normalizer (V k : Set (Equiv.Perm (Fin 16))) ⊓ X) = 12)

@[expose] noncomputable def F1MProp : Prop :=
  let L1 := decSubgroup l1Decs
  let M1 := decSubgroup m1Decs
  Nat.card M1 = 1024 ∧
    ∀ x : Equiv.Perm (Fin 1782), x ∈ L1 ↔ (x ∈ M1 ∧ ∀ y ∈ M1, x * y = y * x)

@[expose] noncomputable def l1Elt (i : Fin 16) : Equiv.Perm (Fin 1782) :=
  ((List.range 4).map fun k => if i.val.testBit k then l1BasisPerm k else 1).prod

@[expose] noncomputable def F6bProp : Prop :=
  ∀ j < 2, ∃ y ∈ tabSubgroup v0Tabs, ∀ i : Fin 16,
    y * l1Elt i * y⁻¹ = l1Elt (tabPerm16 tbarTabs[j]! i)

end CFSG.Sporadic.SuzRecog.SuzL34Cert
