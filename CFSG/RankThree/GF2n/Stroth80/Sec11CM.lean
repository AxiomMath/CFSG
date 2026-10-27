module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def IsF4Char2 (Y : Type) [Group Y] : Prop :=
  ∃ x : ℕ, CFSG.Blueprint.LieModel Y .F4 0 2 x

@[expose] def NaturalDualRep {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (X : Subgroup (GL ι K)) (R V Z N : Subgroup G) : Prop :=
  ∃ φ : R →* GL ι K, φ.range = X ∧ φ.ker = N.subgroupOf R ∧
    SectionAct K R V Z φ (fun g => (((g⁻¹ : GL ι K) : Matrix ι ι K))ᵀ)

@[expose] def XbarPre (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Subgroup G :=
  ((Xbar M Q Z B).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype

@[expose] def XbarPreCenter (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Subgroup G :=
  (((Subgroup.center ↥(Xbar M Q Z B)).map (Xbar M Q Z B).subtype).comap
    (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype

theorem mk_mem_Xbar_of_LB (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] (a : ↥M)
    (ha : (a : G) ∈ LB M Q B) (hA : IsA2 Q Z (a : G)) :
    (QuotientGroup.mk a : Mbar M Q) ∈ Xbar M Q Z B := by
  refine Subgroup.subset_closure ⟨⟨a, rfl, hA⟩, 1, ?_⟩
  rw [one_mul, inv_one, mul_one]
  exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

@[expose] def a2Class (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] (a : ↥M)
    (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)) : XbarMod M Q Z B :=
  (QuotientGroup.mk (⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ :
    ↥(Xbar M Q Z B)) : XbarMod M Q Z B)

@[expose] def XbarH (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Subgroup ↥(H0 M Z) :=
  (Xbar M Q Z B).comap
    ((QuotientGroup.mk' (Q.subgroupOf M)).comp
      (Subgroup.inclusion (inf_le_left : H0 M Z ≤ M)))

@[expose] def cmComm (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (K : Type) [Field K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) : Submodule K M₀.E :=
  ⨆ h : XbarH M Q Z B,
    LinearMap.range (((φ h : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)

@[expose] def CMF4Width : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) → IsF4Char2 (XbarMod M Q Z B) → 26 ≤ 2 * n

@[expose] def piPre {K : Type} [Field K] {Q Z : Subgroup G} {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ)
    (V : Submodule K M₀.E) : Subgroup G where
  carrier := {x | x ∈ Q ∧ M₀.π x ∈ V}
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxQ, hxV⟩ := hx
    obtain ⟨hyQ, hyV⟩ := hy
    refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
    rw [M₀.π_mul x hxQ y hyQ]
    exact V.add_mem hxV hyV
  one_mem' := by
    refine ⟨Q.one_mem, ?_⟩
    have h1 : M₀.π 1 = 0 := by
      have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
      rw [one_mul] at h
      apply add_left_cancel (a := M₀.π 1)
      rw [← h, add_zero]
    rw [h1]
    exact V.zero_mem
  inv_mem' := by
    intro x hx
    obtain ⟨hxQ, hxV⟩ := hx
    refine ⟨Q.inv_mem hxQ, ?_⟩
    have h := M₀.π_mul x hxQ x⁻¹ (Q.inv_mem hxQ)
    rw [mul_inv_cancel] at h
    have h1 : M₀.π 1 = 0 := by
      have h2 := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
      rw [one_mul] at h2
      apply add_left_cancel (a := M₀.π 1)
      rw [← h2, add_zero]
    rw [h1] at h
    have hneg : M₀.π x⁻¹ = -M₀.π x := by
      apply eq_neg_of_add_eq_zero_left
      rw [add_comm]
      exact h.symm
    rw [hneg]
    exact V.neg_mem hxV

@[simp] theorem mem_piPre {K : Type} [Field K] {Q Z : Subgroup G} {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ)
    {V : Submodule K M₀.E} {x : G} :
    x ∈ piPre M₀ V ↔ x ∈ Q ∧ M₀.π x ∈ V := Iff.rfl

@[expose] def CMSpTransvAt (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] (m x : ℕ) (a : ↥M)
    (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ x ∧
    ∃ φ : XbarMod M Q Z B ≃* StatedProj (StatedSp m K), ∃ g : ↥(StatedSp m K),
      Matrix.rank (((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
        - 1) = 1 ∧
      φ (a2Class M Q Z B a h) = QuotientGroup.mk g

@[expose] def CMSpStructure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x →
    2 ^ x ≤ Nat.card Z ∧
    (2 ^ x = Nat.card Z →
      ∀ (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)),
        (CMSpTransvAt M Q Z B m x a h →
          Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ (4 * m + 1) ∧
          ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
            (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
            ∃ φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E),
              (∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
                M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y)) ∧
              ∃ W₁ W₂ : Submodule K M₀.E,
                W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ ∧
                (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁) ∧
                (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂) ∧
                (∀ w ∈ W₁, M₀.Qf w = 0) ∧ (∀ w ∈ W₂, M₀.Qf w = 0) ∧
                ∃ (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁)
                  (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K),
                  ρ.range = StatedSp m K ∧
                  (∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
                  ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
                    φ s ((b i : ↥W₁) : M₀.E) =
                      ∑ j, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i •
                        ((b j : ↥W₁) : M₀.E)) ∧
        (¬ CMSpTransvAt M Q Z B m x a h →
          m = 3 ∧ Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ 9 ∧
          (∀ W : Subgroup G, Z ≤ W → W ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆ →
            (∀ g ∈ XbarPre M Q Z B, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
            W = Z ∨ W = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) ∧
          ∃ y : ↥M, (QuotientGroup.mk y : Mbar M Q) ∈ Xbar M Q Z B ∧
            Odd (orderOf (QuotientGroup.mk y : Mbar M Q)) ∧
            ∀ v ∈ Z ⊔ ⁅Q, XbarPre M Q Z B⁆, ⁅(y : G), v⁆ ∈ Z → v ∈ Z))

@[expose] def CMOmegaFiltration : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    (CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)) →
    2 ^ x = Nat.card Z →
    ∃ X₁ X₂ : Subgroup G,
      Z ≤ X₁ ∧ X₁ ≤ X₂ ∧ X₂ ≤ Q ∧ ⁅X₁, XbarPre M Q Z B⁆ ≤ Z ∧
      X₂ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ ∧
      (((CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
          CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
          ∃ X : Subgroup (GL (Fin (2 * m)) K),
            NaturalRep (ι := Fin (2 * m)) K X (XbarPre M Q Z B) X₂ X₁ (Q) ∧
            (∀ W : Submodule K (Fin (2 * m) → K),
              (∀ g ∈ X, ∀ w ∈ W, (g : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *ᵥ w ∈ W) →
                W = ⊥ ∨ W = ⊤)) ∨
        (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x ∧
          ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
              ∃ X : Subgroup (GL (Fin 6) K),
                NaturalRep (ι := Fin 6) K X (XbarPre M Q Z B) X₂ X₁ (Q) ∧
                (∀ W : Submodule K (Fin 6 → K),
                  (∀ g ∈ X, ∀ w ∈ W, (g : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W) →
                    W = ⊥ ∨ W = ⊤)) ∨
            (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
              ∃ X : Subgroup (GL (Fin 8) K),
                NaturalRep (ι := Fin 8) K X (XbarPre M Q Z B) X₂ X₁ (Q)))))

@[expose] def CMLmChain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x →
    3 ≤ m →
    ((∃ X₁ X₂ X₃ X₄ : Subgroup G,
        X₁ = Z ∧ X₁ ≤ X₂ ∧ X₂ ≤ X₃ ∧ X₃ ≤ X₄ ∧ X₄ = Q ∧
        ⁅X₁, XbarPre M Q Z B⁆ ≤ Z ∧
        X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆ ∧ X₃ = X₂ ∧
        X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
          NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁
            (Q) ∧
          NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₄ X₃
            (Q)) ∨
      (m = 4 ∧ ∃ X₁ X₂ : Subgroup G,
        X₁ = Z ∧ X₁ ≤ X₂ ∧ X₂ = Q ∧ ⁅X₁, XbarPre M Q Z B⁆ ≤ Z ∧
        X₂ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
          NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
            (XbarPre M Q Z B) X₂ X₁ (Q)))

@[expose] def CMLmThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n x : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 3 2 x → 2 ^ x = Nat.card Z →
    Lgen M (LB M Q B) ≤ XbarPre M Q Z B

end CFSG.RankThree.GF2n.Stroth80
