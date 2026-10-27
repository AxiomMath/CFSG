module

public import CFSG.Walter.W67.Defs
public import CFSG.Walter.ReeOrder.JT.Defs
public import CFSG.Walter.ReeOrder.Ward.Defs
public import CFSG.CharacterTheory.BlockSectionOrthogonality.IdempotentTwist
public import CFSG.CharacterTheory.Blocks.InnerProduct

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

structure JRGroup (L : Type) [Group L] [Finite L] where
  p : ℕ
  f : ℕ
  [fact_prime : Fact p.Prime]
  p_ne_two : p ≠ 2
  f_pos : 0 < f
  index_ne_two : ∀ N : Subgroup L, N.Normal → N.index ≠ 2
  card_sylow : ∀ P : Sylow 2 L, Nat.card P = 8
  elementary_sylow : ∀ P : Sylow 2 L, IsElementaryAbelian 2 P
  J : L
  orderOf_J : orderOf J = 2
  K : Subgroup L
  le_centralizer : K ≤ Subgroup.centralizer ({J} : Set L)
  J_not_mem : J ∉ K
  centralizer_eq : Subgroup.centralizer ({J} : Set L) = Subgroup.zpowers J ⊔ K
  iso : K ≃* PSL(2, GaloisField p f)

attribute [instance] JRGroup.fact_prime

section JR

variable {L : Type} [Group L] [Finite L]

@[expose] def JRGroup.q (h : JRGroup L) : ℕ := h.p ^ h.f

@[expose] def _root_.CFSG.Walter.Ward.ReeTypeHyp.toJRGroup (h : Ward.ReeTypeHyp L) : JRGroup L :=
  ⟨h.p, h.f, h.p_ne_two, h.f_pos, h.index_ne_two, h.card_sylow, h.elementary_sylow, h.J,
    h.orderOf_J, h.L, h.le_centralizer, h.J_not_mem, h.centralizer_eq, h.iso⟩

@[expose] def JRGroup.toJTHyp (h : JRGroup L) (hq : 5 < h.q) : JT.JTHyp L where
  p := h.p
  f := h.f
  five_lt := hq
  abelian_sylow := fun P => (h.elementary_sylow P).toIsMulCommutative
  index_ne_two := fun N hN => h.index_ne_two N (Subgroup.normal_of_index_eq_two hN) hN
  t := h.J
  orderOf_t := h.orderOf_J
  F := h.K
  le_centralizer := h.le_centralizer
  t_not_mem := h.J_not_mem
  centralizer_eq := h.centralizer_eq
  iso := h.iso

@[expose] def OddMultiplierTrivial (L : Type) [Group L] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (Z : Subgroup E) [Z.Normal], Z ≤ Subgroup.center E →
    Odd (Nat.card Z) → commutator E = ⊤ → Nonempty ((E ⧸ Z) ≃* L) → Z = ⊥

@[expose] def OutCyclic (L : Type) [Group L] : Prop :=
  ∃ α : MulAut L, ∀ β : MulAut L, ∃ (k : ℤ) (g : L), β = α ^ k * MulAut.conj g

@[expose] def cstarSet {X : Type*} [Group X] (a : X) : Set X :=
  {x | x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹}

@[expose] def J1Prop (L : Type) [Group L] [Finite L] : Prop :=
  IsSimpleGroup L ∧ Nat.card L = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 ∧
    ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y

@[expose] def J2Prop (L : Type) [Group L] [Finite L] : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p L, ∃ t : L, orderOf t = 2 ∧
      ∀ x ∈ (P : Subgroup L), t * x * t⁻¹ = x⁻¹) ∧
  (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (P : Sylow p L) (t : L), orderOf t = 2 →
      (P : Subgroup L) ≠ ⊥ → (P : Subgroup L) ≤ Subgroup.centralizer ({t} : Set L) →
      (p = 3 ∨ p = 5) ∧
        (Nat.card (Subgroup.normalizer ((P : Subgroup L) : Set L))).factorization 2 = 2) ∧
  (∀ (p : ℕ) [Fact p.Prime], ∀ P : Sylow p L, (p = 7 ∨ p = 11 ∨ p = 19) →
      let N := Subgroup.normalizer ((P : Subgroup L) : Set L)
      let C := Subgroup.centralizer ((P : Subgroup L) : Set L)
      (∃ g ∈ N, Subgroup.zpowers g ⊔ C = N) ∧
        (C.subgroupOf N).index = if p = 11 then 10 else 6)

@[expose] def J2Extra (L : Type) [Group L] [Finite L] : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p L, Nat.card P = 1 ∨ Nat.card P = p) ∧
  (∀ (p : ℕ) [Fact p.Prime], (p = 7 ∨ p = 11 ∨ p = 19) → ∀ P : Sylow p L,
      Subgroup.centralizer ((P : Subgroup L) : Set L) = P) ∧
  (∀ x : L, x ≠ 1 → Odd (orderOf x) → Group.IsSolvable (Subgroup.centralizer ({x} : Set L)))

@[expose] def J3Prop (L : Type) [Group L] [Finite L] : Prop :=
  (∀ α : MulAut L, ∃ g : L, α = MulAut.conj g) ∧ OddMultiplierTrivial L

@[expose] def JRGroup.R1 (h : JRGroup L) : Prop :=
  (∃ n : ℕ, Odd n ∧ h.q = 3 ^ n) ∧
  (¬ Group.IsSolvable L → Nat.card L = (h.q ^ 3 + 1) * h.q ^ 3 * (h.q - 1)) ∧
  (3 < h.q → IsSimpleGroup L) ∧
  (Group.IsSolvable L → h.q = 3 ∧ Nat.card L = 168 ∧ ∀ S : Sylow 2 L, (S : Subgroup L).Normal ∧
      Subgroup.centralizer ((S : Subgroup L) : Set L) = S)

@[expose] def JRGroup.R2 (_h : JRGroup L) : Prop :=
  (∀ S : Sylow 2 L, Subgroup.centralizer ((S : Subgroup L) : Set L) = S ∧
      Nat.card (Subgroup.normalizer ((S : Subgroup L) : Set L)) = 168) ∧
  ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y

@[expose] def JRGroup.R3 (h : JRGroup L) : Prop :=
  3 < h.q → ∀ P : Sylow 3 L,
    let Pg : Subgroup L := P
    let Z : Subgroup L := (Subgroup.center Pg).map Pg.subtype
    let Z₂ : Subgroup L := (Subgroup.upperCentralSeries Pg 2).map Pg.subtype
    Nat.card Pg = h.q ^ 3 ∧ IsElementaryAbelian 3 Z ∧ Nat.card Z = h.q ∧
    Z₂ = (frattini Pg).map Pg.subtype ∧ Z₂ = (commutator Pg).map Pg.subtype ∧
    Z₂ = Subgroup.closure {x : L | x ∈ Pg ∧ x ^ 3 = 1} ∧ IsMulCommutative Z₂ ∧
    Nat.card Z₂ = h.q ^ 2 ∧
    ∃ W : Subgroup L, IsCyclic W ∧ Nat.card W = h.q - 1 ∧ Pg ⊓ W = ⊥ ∧
      Subgroup.normalizer (Pg : Set L) = Pg ⊔ W ∧
      ∀ t ∈ W, orderOf t = 2 → Z₂ = Z ⊔ (Pg ⊓ Subgroup.centralizer ({t} : Set L)) ∧
        Z ⊓ Subgroup.centralizer ({t} : Set L) = ⊥

@[expose] noncomputable def oddPart {X0 : Type*} [Group X0] (X : Subgroup X0) : Subgroup X0 :=
  (CFSG.pPrimeCore 2 X).map X.subtype

@[expose] def JRGroup.R4 (h : JRGroup L) : Prop :=
  3 < h.q → ∀ t ∈ h.K, orderOf t = 2 →
    let A : Subgroup L := oddPart (h.K ⊓ Subgroup.centralizer ({t} : Set L))
    let V : Subgroup L := Subgroup.closure {h.J, t}
    IsCyclic A ∧ 4 * Nat.card A = h.q + 1 ∧
    Subgroup.centralizer (A : Set L) = V ⊔ A ∧
    ∃ (S : Sylow 2 L) (U : Subgroup L), V ≤ S ∧
      (∀ a ∈ A, a ≠ 1 → cstarSet a = ((S : Subgroup L) ⊔ A : Subgroup L)) ∧
      Nat.card U = 3 ∧
      Subgroup.normalizer (V : Set L) = Subgroup.normalizer (A : Set L) ∧
      Subgroup.normalizer (V : Set L) = U ⊔ (S : Subgroup L) ⊔ A ∧
      ⁅U, (S : Subgroup L)⁆ = V ∧ ⁅U, A⁆ = A ∧
      V ⊔ ((S : Subgroup L) ⊓ Subgroup.centralizer (U : Set L)) = S ∧
      V ⊓ Subgroup.centralizer (U : Set L) = ⊥ ∧
      ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set L) = V ⊔ A ∧
        Subgroup.normalizer (Subgroup.zpowers a : Set L) = Subgroup.normalizer (A : Set L)

@[expose] def JRGroup.R5 (h : JRGroup L) : Prop :=
  3 < h.q → ∀ B : Subgroup L, B ≤ h.K → IsCyclic B → 2 * Nat.card B = h.q - 1 →
    ∃ W : Subgroup L, Nat.card W = 4 ∧ (∀ w ∈ W, w * w = 1) ∧
      Subgroup.normalizer (B : Set L) = W ⊔ B ∧ W ⊓ B = ⊥ ∧
      ∀ b ∈ B, b ≠ 1 → ∃ T : L, T ∈ W ∧ orderOf T = 2 ∧
        Subgroup.centralizer ({b} : Set L) = Subgroup.zpowers T ⊔ B ∧
        W ⊓ Subgroup.centralizer (B : Set L) = Subgroup.zpowers T

@[expose] def JRGroup.R6 (h : JRGroup L) : Prop :=
  3 < h.q → ∀ m : ℕ, m ^ 2 = 3 * h.q → ∀ s : Bool,
    ∃ C : Subgroup L, IsMulCommutative C ∧
      Nat.card C = (if s then h.q + 1 + m else h.q + 1 - m) ∧
      Nat.Coprime (Nat.card C) C.index ∧
      (∃ g ∈ Subgroup.normalizer (C : Set L),
        Subgroup.zpowers g ⊔ Subgroup.centralizer (C : Set L) =
          Subgroup.normalizer (C : Set L)) ∧
      ((Subgroup.centralizer (C : Set L)).subgroupOf (Subgroup.normalizer (C : Set L))).index = 6 ∧
      ∀ c ∈ C, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = C

@[expose] def JRGroup.R7 (_h : JRGroup L) : Prop := OutCyclic L ∧ OddMultiplierTrivial L

end JR

@[expose] def JFacts : Prop := ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q = 5 →
  J1Prop L ∧ J2Prop L ∧ J2Extra L ∧ J3Prop L ∧ OutCyclic L

@[expose] def RFacts : Prop := ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 →
  hL.R1 ∧ hL.R2 ∧ hL.R3 ∧ hL.R4 ∧ hL.R5 ∧ hL.R6 ∧ (3 < hL.q → OutCyclic L)

@[expose] def RMult : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 → 3 < hL.q →
    OddMultiplierTrivial L

variable {G : Type} [Group G] [Finite G]

@[expose] def IH (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (h : Hyp X), Nat.card X < n → Case1 h ∨ Case2 h

structure MinCE (G : Type) [Group G] [Finite G] extends Hyp G where
  ih : IH (Nat.card G)
  not_case1 : ¬ Case1 toHyp
  not_case2 : ¬ Case2 toHyp

namespace Hyp

variable (h : Hyp G)

abbrev H : Subgroup G := Subgroup.centralizer ({h.J} : Set G)

abbrev CK : Subgroup G := h.H ⊓ Subgroup.centralizer (h.K : Set G)

@[expose] noncomputable def F : Subgroup G := oddPart h.CK

abbrev KX (X : Subgroup G) : Subgroup G := h.K ⊓ Subgroup.centralizer (X : Set G)

@[expose] noncomputable def eX (X : Subgroup G) : ℕ := Nat.card ↥(X ⊔ h.F) / Nat.card ↥h.F

end Hyp

structure Frame (h : Hyp G) where
  S : Sylow 2 G
  J_mem : h.J ∈ (S : Subgroup G)
  card_T : Nat.card ↥((S : Subgroup G) ⊓ h.K) = 4

namespace Frame

variable {h : Hyp G} (fr : Frame h)

abbrev T : Subgroup G := (fr.S : Subgroup G) ⊓ h.K

abbrev CS : Subgroup G := Subgroup.centralizer ((fr.S : Subgroup G) : Set G)

@[expose] noncomputable def E : Subgroup G := oddPart fr.CS

@[expose] noncomputable def σ : Finset ℕ := (Nat.card fr.E).primeFactors

@[expose] noncomputable def EX (X : Subgroup G) : Subgroup G :=
  fr.E ⊓ Subgroup.normalizer (X : Set G)

end Frame

structure IsJRSubgroup (L : Subgroup G) (J : G) (K' : Subgroup G) (p g : ℕ) [Fact p.Prime] :
    Prop where
  J_mem : J ∈ L
  orderOf_J : orderOf J = 2
  K_le : K' ≤ L ⊓ Subgroup.centralizer ({J} : Set G)
  J_not_mem : J ∉ K'
  centralizer_eq : L ⊓ Subgroup.centralizer ({J} : Set G) = Subgroup.zpowers J ⊔ K'
  iso : Nonempty (K' ≃* PSL(2, GaloisField p g))
  index_ne_two : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal → (N.subgroupOf L).index ≠ 2
  sylow : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ L ∧ IsElementaryAbelian 2 (S : Subgroup G) ∧
    Nat.card (S : Subgroup G) = 8

structure LSpec (h : Hyp G) (fr : Frame h) (X L : Subgroup G) : Prop where
  le_centralizer : L ≤ Subgroup.centralizer (X : Set G)
  normal : L ≤ Subgroup.normalizer (X : Set G) ∧
    (L.subgroupOf (Subgroup.normalizer (X : Set G))).Normal
  jr : ∃ K' : Subgroup G, IsJRSubgroup L h.J K' h.p (h.f / h.eX X) ∧
    (3 < h.p ^ (h.f / h.eX X) → K' = h.KX X)
  normalizer_eq : h.F ≤ X → Subgroup.normalizer (X : Set G) = L ⊔ fr.E
  centralizer_eq : h.F ≤ X →
    Subgroup.centralizer (X : Set G) = L ⊔ (Subgroup.centralizer (X : Set G) ⊓ fr.E)

structure Std (G : Type) [Group G] [Finite G] extends MinCE G where
  fr : Frame toHyp
  three_lt_q : 3 < toHyp.q
  perfect : commutator G = ⊤
  E_ne_bot : fr.E ≠ ⊥
  F_eq_bot : toHyp.F = ⊥
  L : Subgroup G → Subgroup G
  L_spec : ∀ X : Subgroup G, X ≤ fr.E → X ≠ ⊥ → LSpec toHyp fr X (L X)

namespace Frame

variable {h : Hyp G} (fr : Frame h)

@[expose] noncomputable def A (_fr : Frame h) (T₂ : G) : Subgroup G :=
  oddPart (h.K ⊓ Subgroup.centralizer ({T₂} : Set G))

@[expose] def V (_fr : Frame h) (T₂ : G) : Subgroup G := Subgroup.closure {h.J, T₂}

@[expose] noncomputable def A₀ (T₂ : G) : Subgroup G :=
  fr.A T₂ ⊓ Subgroup.centralizer (fr.E : Set G)

@[expose] noncomputable def A₁ (T₂ : G) : Subgroup G := ⁅fr.E, fr.A T₂⁆

@[expose] noncomputable def D₂ (T₂ : G) : Set G :=
  ((fr.V T₂ ⊔ fr.A T₂ ⊔ fr.E : Subgroup G) : Set G) \
    ((fr.V T₂ ⊔ fr.A₁ T₂ ⊔ fr.E : Subgroup G) : Set G)

end Frame

namespace Std

variable (s : Std G)

noncomputable abbrev A (T₂ : G) : Subgroup G := s.fr.A T₂
abbrev V (T₂ : G) : Subgroup G := s.fr.V T₂
noncomputable abbrev A₀ (T₂ : G) : Subgroup G := s.fr.A₀ T₂
noncomputable abbrev A₁ (T₂ : G) : Subgroup G := s.fr.A₁ T₂
noncomputable abbrev D₂ (T₂ : G) : Set G := s.fr.D₂ T₂

end Std

@[expose] def IsMaximalClass (p : ℕ) (P : Type*) [Group P] : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ Nat.card P = p ^ m ∧ (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥

structure Frame5 (s : Std G) where
  B : Subgroup G
  B_le : B ≤ s.K
  B_cyclic : IsCyclic B
  card_B : 2 * Nat.card B = s.q - 1
  E_le_normalizer_B : s.fr.E ≤ Subgroup.normalizer (B : Set G)
  P₁ : Subgroup G
  P₁_le : P₁ ≤ s.K
  card_P₁ : Nat.card P₁ = s.q
  B_le_normalizer : B ⊔ s.fr.E ≤ Subgroup.normalizer (P₁ : Set G)
  fixedPointFree : ∀ b ∈ B, b ≠ 1 → P₁ ⊓ Subgroup.centralizer ({b} : Set G) = ⊥
  normalizer_eq : Subgroup.normalizer (P₁ : Set G) ⊓ (s.K ⊔ s.fr.E) = P₁ ⊔ B ⊔ s.fr.E

@[expose] def relFix {X N : Type*} [Group X] [Group N] [MulDistribMulAction X N]
    (Y : Subgroup X) (A B : Subgroup N) : Set N :=
  {n | n ∈ A ∧ ∀ y ∈ Y, n⁻¹ * (y • n) ∈ B}

@[expose] def omega1 (p : ℕ) (P₀ : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P₀ ∧ x ^ p = 1}

section CT

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
open scoped Classical

@[expose] noncomputable def invSum {X : Type} [Group X] [Fintype X] (χ : X → ℂ) : ℂ :=
  (Nat.card X : ℂ)⁻¹ * ∑ t ∈ Finset.univ.filter (fun t : X => t ≠ 1 ∧ t * t = 1), χ t

@[expose] def section2 {X : Type} [Group X] (J : X) : Set X :=
  {x | ∃ y : X, x = J * y ∧ y * J = J * y ∧ Odd (orderOf y)}

end CT

structure HypI (G : Type) [Group G] [Finite G] extends Hyp G where
  fr : Frame toHyp
  p_eq_three : p = 3
  odd_f : Odd f
  one_lt_f : 1 < f
  perfect : commutator G = ⊤
  cover : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) =
    (Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓ Subgroup.centralizer (fr.E : Set G)) ⊔
      fr.CS

structure HypII (G : Type) [Group G] [Finite G] extends HypI G where
  T₂ : G
  T₂_mem : T₂ ∈ fr.T
  T₂_order : orderOf T₂ = 2
  U : Subgroup G
  card_U : Nat.card U = 3
  G3a : Subgroup.normalizer (fr.V T₂ : Set G) = U ⊔ Subgroup.centralizer (fr.V T₂ : Set G)
  G3a' : U ≤ Subgroup.centralizer (fr.E : Set G) ∧ ⁅U, fr.V T₂⁆ = fr.V T₂
  G3b : JT.IsInternalDirectProduct (fr.V T₂)
    (((fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) ⊔ fr.A T₂ ⊔ fr.E)
    (Subgroup.centralizer (fr.V T₂ : Set G))
  G3c : ∀ Aα : Subgroup G, Aα ≤ fr.A T₂ → Aα ≠ ⊥ →
    Subgroup.normalizer (Aα : Set G) = Subgroup.normalizer (fr.V T₂ : Set G)
  G3c' : ∀ Aα : Subgroup G, Aα ≤ fr.A₀ T₂ → Aα ≠ ⊥ →
    Subgroup.centralizer (Aα : Set G) = fr.V T₂ ⊔ fr.A T₂ ⊔ fr.E
  G4 : fr.A₀ T₂ ≠ ⊥

section CT7

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace HypI

variable (hI : HypI G)

@[expose] noncomputable def δ : hI.H → ℂ := fun x => if (x : G) ∈ hI.K ⊔ hI.fr.E then 1 else -1

@[expose] def Lset : Set (hI.H → ℂ) :=
  {l | l ∈ CFSG.BlocksIrr hI.H ∧ l 1 = 1 ∧
    ∀ x : hI.H, (x : G) ∈ Subgroup.zpowers hI.J ⊔ hI.K → l x = 1}

@[expose] def PMIrr (X : Type) [Group X] : Set (X → ℂ) :=
  {ψ | ψ ∈ CFSG.BlocksIrr X ∨ -ψ ∈ CFSG.BlocksIrr X}

end HypI

@[expose] def blockL (hI : HypI G) (χ : Fin 4 → (hI.H → ℂ)) (l : hI.H → ℂ) : Set (hI.H → ℂ) :=
  {ψ | ∃ i, ψ = l * χ i ∨ ψ = l * hI.δ * χ i}

structure ChiProps (hI : HypI G) (m : Ideal CFSG.BlocksAlgInt) (χ : Fin 4 → (hI.H → ℂ)) :
    Prop where
  irr : ∀ i, χ i ∈ CFSG.BlocksIrr hI.H
  one : χ 0 = 1
  J_ker : ∀ i, ∀ x : hI.H, χ i ⟨hI.J * x, Subgroup.mul_mem _
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) x.2⟩ = χ i x
  deg : χ 1 1 = ((hI.q : ℂ) - 1) / 2 ∧ χ 2 1 = ((hI.q : ℂ) - 1) / 2 ∧ χ 3 1 = hI.q
  inv : ∀ t : hI.H, (t : G) ∈ hI.K → orderOf t = 2 →
    χ 0 t = 1 ∧ χ 1 t = 1 ∧ χ 2 t = 1 ∧ χ 3 t = -1
  block : ∀ l ∈ hI.Lset, CFSG.BlocksBlockOf m hI.H (l * χ 0) = blockL hI χ l

@[expose] noncomputable def theta (hI : HypI G) (χ : Fin 4 → (hI.H → ℂ)) (l : hI.H → ℂ)
    (j : Fin 4) : hI.H → ℂ :=
  if j = 3 then l * χ 0 - l * hI.δ * χ 0 + l * χ 3 - l * hI.δ * χ 3
  else l * χ 0 - l * hI.δ * χ 0 - l * χ j + l * hI.δ * χ j

structure AlphaData (hI : HypI G) where
  χα : hI.H → ℂ
  χεα : hI.H → ℂ
  irr : χα ∈ CFSG.BlocksIrr hI.H ∧ χεα ∈ CFSG.BlocksIrr hI.H
  deg : χα 1 = (hI.q : ℂ) - 1 ∧ χεα 1 = (hI.q : ℂ) - 1
  J_ker : χα ⟨hI.J, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = (hI.q : ℂ) - 1 ∧
    χεα ⟨hI.J, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = (hI.q : ℂ) - 1
  inv : ∀ t : hI.H, (t : G) ∈ hI.K → orderOf t = 2 → χα t = -2 ∧ χεα t = 2

@[expose] noncomputable def thetaα (hI : HypI G) (α : AlphaData hI) (l : hI.H → ℂ) : hI.H → ℂ :=
  l * α.χα - l * hI.δ * α.χα + l * α.χεα - l * hI.δ * α.χεα

structure AlphaOrbit (hII : HypII G) (m : Ideal CFSG.BlocksAlgInt) where
  α : Fin 3 → AlphaData hII.toHypI
  block : ∀ i, ∀ l ∈ hII.Lset, CFSG.BlocksBlockOf m hII.H (l * (α i).χα) =
    {l * (α i).χα, l * (α i).χεα, l * hII.δ * (α i).χα, l * hII.δ * (α i).χεα}
  distinct : ∀ i j, i ≠ j → (α i).χα ≠ (α j).χα ∧ (α i).χα ≠ (α j).χεα
  assoc : ∀ l ∈ hII.Lset, ∀ i j, ∀ B : Set (G → ℂ),
    CFSG.BlocksBrauerCorr m (Subgroup.zpowers hII.J) hII.H
      (CFSG.BlocksBlockOf m hII.H (l * (α i).χα)) B ↔
    CFSG.BlocksBrauerCorr m (Subgroup.zpowers hII.J) hII.H
      (CFSG.BlocksBlockOf m hII.H (l * (α j).χα)) B

@[expose] noncomputable def eta4 (hI : HypI G) (χ : Fin 4 → (hI.H → ℂ)) (α : AlphaData hI)
    (l : hI.H → ℂ) : hI.H → ℂ :=
  l * hI.δ * χ 0 - l * hI.δ * χ 3 + l * hI.δ * α.χα

structure CohData (hII : HypII G) {m : Ideal CFSG.BlocksAlgInt} (χ : Fin 4 → (hII.H → ℂ))
    (ao : AlphaOrbit hII m) (l : hII.H → ℂ) where
  ψ : Fin 4 → G → ℂ
  ψ' : Fin 4 → G → ℂ
  Φ : Fin 4 → G → ℂ
  xα : ℤ
  k : Fin 4
  ε : ℤ
  pmIrr : ∀ i, ψ i ∈ HypI.PMIrr G ∧ ψ' i ∈ HypI.PMIrr G ∧ Φ i ∈ HypI.PMIrr G
  orth : ∀ i j, CFSG.BlocksInnerProduct (ψ i) (ψ j) = (if i = j then 1 else 0) ∧
    CFSG.BlocksInnerProduct (ψ' i) (ψ' j) = (if i = j then 1 else 0) ∧
    CFSG.BlocksInnerProduct (Φ i) (Φ j) = (if i = j then 1 else 0) ∧
    CFSG.BlocksInnerProduct (ψ i) (ψ' j) = 0 ∧ CFSG.BlocksInnerProduct (ψ i) (Φ j) = 0 ∧
    CFSG.BlocksInnerProduct (ψ' i) (Φ j) = 0
  ind74 : inducedFunction hII.H (theta hII.toHypI χ l 3) = ψ 0 - ψ' 0 + ψ 3 - ψ' 3 ∧
    inducedFunction hII.H (theta hII.toHypI χ l 1) = ψ 0 - ψ' 0 - ψ 1 + ψ' 1 ∧
    inducedFunction hII.H (theta hII.toHypI χ l 2) = ψ 0 - ψ' 0 - ψ 2 + ψ' 2
  ind76 : inducedFunction hII.H (thetaα hII.toHypI (ao.α 0) l) = Φ 0 - Φ 1 + Φ 2 - Φ 3 ∧
    inducedFunction hII.H (thetaα hII.toHypI (ao.α 1) l) = Φ 0 + Φ 1 - Φ 2 - Φ 3 ∧
    inducedFunction hII.H (thetaα hII.toHypI (ao.α 2) l) = Φ 0 - Φ 1 - Φ 2 + Φ 3
  ind78 : inducedFunction hII.H (eta4 hII.toHypI χ (ao.α 0) l) =
    ψ' 0 - ψ' 3 + (ε : ℂ) • Φ k
  ε_sq : ε = 1 ∨ ε = -1
  valJ : (∀ i, ψ i hII.J = (l * χ i) ⟨hII.J, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∧
      ψ' i hII.J = (l * hII.δ * χ i) ⟨hII.J, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) ∧
    Φ 0 hII.J = 3 * ((hII.q : ℂ) - 1) ∧ Φ 1 hII.J = -((hII.q : ℂ) - 1) ∧
    Φ 2 hII.J = -((hII.q : ℂ) - 1) ∧ Φ 3 hII.J = -((hII.q : ℂ) - 1)
  degΦ : ∀ k, Φ k 1 = xα
  principal : l = 1 → ψ 0 = 1

end CT7

structure CTData (q e g : ℕ) where
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  l₀ : ι
  card_ι : Fintype.card ι = e
  x1 : ι → ℤ
  x1' : ι → ℤ
  x4 : ι → ℤ
  x4' : ι → ℤ
  xα : ι → ℤ
  ε : ι → ℤ
  ne_zero : ∀ l, x1 l ≠ 0 ∧ x1' l ≠ 0 ∧ x4 l ≠ 0 ∧ x4' l ≠ 0 ∧ xα l ≠ 0
  ε_sq : ∀ l, ε l = 1 ∨ ε l = -1
  x1_l₀ : x1 l₀ = 1
  r83 : ∀ l, x1 l - x1' l + x4 l - x4' l = 0
  r86 : ∀ l, (g : ℚ) * (1 / x1 l - 1 / x1' l + (q : ℚ) ^ 2 * (1 / x4 l - 1 / x4' l)) =
    (q : ℚ) ^ 2 * ((q : ℚ) - 1) ^ 3 * ((q : ℚ) + 1) ^ 2 * e
  r813 : ∀ l, (g : ℤ) = (q : ℤ) ^ 3 * ((q : ℤ) + 1) * e * xα l
  r816 : ∀ l, x1' l - x4' l + ε l * xα l = 0
  r818 : ∀ l, (1 : ℚ) / x1' l - (q : ℚ) ^ 2 / x4' l + ((q : ℚ) - 1) ^ 2 / (ε l * xα l) = 0
  mod8 : ∀ l, (8 : ℤ) ∣ x1 l + 7
  nonlinear : ∀ l, l ≠ l₀ → x1 l ≠ 1 ∧ x1 l ≠ -1

attribute [instance] CTData.fin CTData.dec

end CFSG.Walter.W67
