module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperStatements

public section
namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

abbrev Cen (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)
abbrev CenS (H : Subgroup G) : Subgroup G := Subgroup.centralizer (H : Set G)
abbrev Nor (H : Subgroup G) : Subgroup G := Subgroup.normalizer (H : Set G)
abbrev Op (p : ℕ) (H : Subgroup G) : Subgroup G := inSubgroup (pCore p) H
abbrev Opp (p : ℕ) (H : Subgroup G) : Subgroup G := inSubgroup (pPrimeCore p) H
abbrev Lay (H : Subgroup G) : Subgroup G := inSubgroup (fun K _ => layer K) H
abbrev OUpp (p : ℕ) (H : Subgroup G) : Subgroup G :=
  inSubgroup (fun K _ => Subgroup.normalClosure {g : K | ∃ k : ℕ, g ^ (p ^ k) = 1}) H
abbrev OUp (p : ℕ) (H : Subgroup G) : Subgroup G :=
  inSubgroup (fun K _ => Subgroup.normalClosure {g : K | Nat.Coprime p (orderOf g)}) H
abbrev OppE (p : ℕ) (H : Subgroup G) : Subgroup G :=
  ((layer (H ⧸ pPrimeCore p H)).comap (QuotientGroup.mk' (pPrimeCore p H))).map H.subtype

@[expose] def setMul (H K : Subgroup G) : Set G := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}

@[expose] def setMul3 (H K M : Subgroup G) : Set G := {x | ∃ h ∈ H, ∃ k ∈ K, ∃ m ∈ M, x = h * k * m}

@[expose] def IsSylowOf (p : ℕ) (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup p P ∧ Nat.Coprime p (P.relIndex H)

@[expose] def ConjInto (x : G) (H : Subgroup G) : Prop := ∃ g : G, g * x * g⁻¹ ∈ H

abbrev conjBy (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

@[expose] def IsElemAb (p k : ℕ) (H : Subgroup G) : Prop :=
  IsElementaryAbelian p H ∧ Nat.card H = p ^ k

@[expose] def IsExtraspecialPlus (m : ℕ) (T : Subgroup G) : Prop :=
  IsExtraspecialPGroup 2 T ∧ Nat.card T = 2 ^ (2 * m + 1) ∧
    ∃ A : Subgroup G, A ≤ T ∧ IsElemAb 2 (m + 1) A

@[expose] def IsLnq (n p f : ℕ) (H : Subgroup G) : Prop :=
  StatedClassicalModel H .PSL n p f

@[expose] def IsTypeLnq (n p f : ℕ) (H : Subgroup G) : Prop :=
  StatedClassicalModel (H ⧸ Subgroup.center H) .PSL n p f

@[expose] def IsFullMonomial (B : Subgroup G) (b b₁ b₂ : G) : Prop :=
  IsElemAb 3 3 B ∧ B = Subgroup.closure {b, b₁, b₂} ∧
    (∀ n ∈ Nor B, ∀ x ∈ ({b, b₁, b₂} : Set G),
      n * x * n⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) ∧
    (∃ n ∈ Nor B, n * b * n⁻¹ = b⁻¹ ∧ n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂) ∧
    (∃ n ∈ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b ∧ n * b₂ * n⁻¹ = b₂) ∧
    (∃ n ∈ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b)

@[expose] def ControlsFusionIn (B : Subgroup G) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ g : G, g * x * g⁻¹ = y → ∃ n ∈ Nor B, n * x * n⁻¹ = y

structure FF79Hyp [Finite G] (n : ℕ) (b : G) (J : Subgroup G) : Prop where
  ord : orderOf b = 3
  std : FFStandardJ b J
  model : IsTypeLnq n 2 1 J
  cyc : FFCentCyclicSylow J
  nsc : FFNotStronglyClosed b
  rank : localRank 3 G = CFSG.Open.pRank 3 (Cen b)

@[expose] def FF79_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), (n = 4 ∨ n = 5) → ∀ (b : G) (J : Subgroup G),
    FF79Hyp n b J → ∀ B : Subgroup G, IsSylowOf 3 B (Cen b) →
    IsElemAb 3 3 B ∧ IsElemAb 3 2 (B ⊓ J) ∧ Subgroup.zpowers b ⊔ (B ⊓ J) = B ∧
    ((¬ ConjInto b J ∧ ∀ D : Subgroup G, D ≤ B → Nat.card D = 3 →
        ((∃ g ∈ Nor B, conjBy g (Subgroup.zpowers b) = D) ↔ ¬ D ≤ J)) ∨
     (ConjInto b J ∧ ControlsFusionIn B ∧
        ∃ b₁ ∈ B ⊓ J, ∃ b₂ ∈ B ⊓ J, IsFullMonomial B b b₁ b₂))

@[expose] def FF79_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), (n = 4 ∨ n = 5) → ∀ (b : G) (J : Subgroup G),
    FF79Hyp n b J → ∀ B : Subgroup G, IsSylowOf 3 B (Cen b) →
    Odd (Nat.card (Opp 3 (Cen b))) → (Odd (Nat.card (CenS B)) ∨ n = 5) →
    let X := Opp 3 (Cen b)
    X ≤ CenS B ∧ (X.subgroupOf (CenS B)).Normal ∧
      Nat.Coprime (Nat.card X) 6 ∧ Nat.Coprime (X.relIndex (CenS B)) (Nat.card X) ∧
      (∀ A : Subgroup G, A < B → ConjInto b A → Opp 3 (CenS A) = X) ∧
      ((setMul3 (Subgroup.zpowers b) J X = Cen b ∧
          Nat.card (Cen b) = 3 * Nat.card J * Nat.card X) ∨ Even (Nat.card (CenS B)))

@[expose] def FF79_1_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J T T₀ : Subgroup G), IsLnq 5 2 1 J → IsPGroup 2 T →
    J ≤ Nor T → T₀ ≤ T → J ≤ Nor T₀ → ∀ β ∈ J, orderOf β = 3 → T ⊓ Cen β ≤ T₀ → T₀ = T

structure FF79Sec3 [Finite G] (b : G) (J : Subgroup G) : Prop where
  simple : IsSimpleGroup (generalizedFitting G)
  hyp : FF79Hyp 4 b J ∨ FF79Hyp 5 b J
  rank3 : localRank 3 G = 3
  notConj : ¬ ConjInto b J

structure FF79Sec3Data [Finite G] (b : G) (J B A P D : Subgroup G) : Prop where
  sylB : IsSylowOf 3 B (Cen b)
  sylP : IsSylowOf 3 P (Nor B)
  hAP : A ≤ P
  hbA : P = Subgroup.zpowers b ⊔ A
  hB0A : B ⊓ J ≤ A
  hA : Nat.card A = 3 ^ 4 ∧ IsMulCommutative A ∧ (Monoid.exponent A = 3 ∨ Monoid.exponent A = 9)
  hAN : P ≤ Nor A
  hcomm : ⁅Subgroup.zpowers b, A⁆ = B ⊓ J
  sylD : IsSylowOf 2 D (Nor B ⊓ J)
  hD : Nat.card D = 8 ∧ ¬ IsMulCommutative D ∧ ∃ d ∈ D, orderOf d = 4
  hDA : D ≤ Nor A
  hZ : ∀ z ∈ Subgroup.center D, z ≠ 1 → ∀ a ∈ A, z * a * z⁻¹ = a⁻¹

@[expose] def FF79_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J : Subgroup G), FF79Sec3 b J →
    ∀ B : Subgroup G, IsSylowOf 3 B (Cen b) → ∃ A P D : Subgroup G, FF79Sec3Data b J B A P D

@[expose] def FF79ThmAConcl (b : G) : Prop :=
  b ∉ generalizedFitting G ∧ ∀ S : Subgroup G, IsSylowOf 3 S (generalizedFitting G) →
    Nat.card S = 81 ∧ IsMulCommutative S ∧ Monoid.exponent S = 9 ∧
      Nat.card {x : G // x ∈ S ∧ x ^ 3 = 1} = 9

@[expose] def FF79_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B A P D : Subgroup G), FF79Sec3 b J →
    FF79Sec3Data b J B A P D →
    FF79ThmAConcl b ∨
      (IsElemAb 3 4 A ∧ Odd (Nat.card (CenS B)) ∧ J = OUpp 2 (Cen b) ∧ Monoid.exponent P = 3)

structure FF79Sec3Data' [Finite G] (b : G) (J B A P D : Subgroup G) : Prop
    extends FF79Sec3Data b J B A P D where
  elem : IsElemAb 3 4 A
  oddCB : Odd (Nat.card (CenS B))
  hJ : J = OUpp 2 (Cen b)
  expP : Monoid.exponent P = 3

@[expose] def FF79_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B A P D : Subgroup G), FF79Sec3 b J →
    FF79Sec3Data' b J B A P D → ∀ As : Subgroup G, IsSylowOf 3 As (CenS A) → b ∈ Nor As →
    IsMulCommutative As ∧ IsSylowOf 3 (As ⊔ Subgroup.zpowers b) ⊤

@[expose] def FF79TheoremA_simpleK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J : Subgroup G),
    IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
      (FF79Hyp 4 b J ∨ FF79Hyp 5 b J) → ConjInto b J

structure FF79Sec4 [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G) : Prop where
  simple : IsSimpleGroup G
  char2 : IsCharacteristicPType G 2
  hyp : FF79Hyp 5 b J
  conj : ConjInto b J
  sylB : IsSylowOf 3 B (Cen b)
  hb₁ : b₁ ∈ B ⊓ J
  hb₂ : b₂ ∈ B ⊓ J
  mono : IsFullMonomial B b b₁ b₂
  nonab : ∃ x y : G, x * y ≠ y * x
  kp : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G

@[expose] def FF79_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → Odd (Nat.card (Opp 3 (Cen b)))

@[expose] def FF79_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ →
    let β := b₁ * b₂; let γ := b₁ ^ 2 * b₂; let H := OUp 3 (Cen β)
    let K := Lay (H ⊓ Cen b); let L := Lay (H ⊓ Cen γ)
    (Subgroup.zpowers β ⊔ H = Cen β ∧ Subgroup.zpowers β ⊓ H = ⊥) ∧
    IsSylowOf 3 (Subgroup.closure {b, γ}) H ∧
    IsLnq 2 2 2 K ∧ IsLnq 3 2 1 L ∧ b ∈ L ∧ γ ∈ K ∧
    Lay H = K ⊔ L ∧ K ⊓ L = ⊥ ∧ K ≤ CenS L ∧
    (setMul (H ⊓ CenS (Subgroup.closure {b, γ})) (Lay H) = H) ∧
    Opp 3 (CenS B) = Opp 3 H ∧ Opp 3 H = Opp 3 (Cen b)

@[expose] def FF79_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ →
    Odd (Nat.card (CenS B)) ∧
    (setMul3 (Subgroup.zpowers b) (Opp 3 (Cen b)) J = Cen b ∧
      Nat.card (Cen b) = 3 * Nat.card (Opp 3 (Cen b)) * Nat.card J)

end CFSG.RankThree.PartTwo.Sec21.FF79
