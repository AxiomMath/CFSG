module

public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

structure Hyp1223 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  notAlt : ¬ Alt12_2_2 G
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  normalizes : T ≤ Subgroup.normalizer (L : Set G)
  irrPlus : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V

namespace Hyp1223

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem conjClosure_eq (h : Hyp1223 G T L V) : conjClosure L T = L :=
  le_antisymm
    (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (h.normalizes ht) l).1 hl)
    (le_conjClosure L T)

theorem fsu (h : Hyp1223 G T L V) : FSU G T L V where
  simple := h.simple
  nonabelian := h.nonabelian
  qtke := h.qtke
  sylow := h.sylow
  maximal := h.maximal
  faithful := h.faithful
  quasisimple := h.quasisimple
  irrPlus := by rw [h.conjClosure_eq]; exact h.irrPlus

abbrev Z (_ : Hyp1223 G T L V) : Subgroup G := quasithinOmegaOneCenter T

abbrev Q (_ : Hyp1223 G T L V) : Subgroup G := pCoreOf 2 (L ⊔ T)

abbrev M (_ : Hyp1223 G T L V) : Subgroup G := Subgroup.normalizer (L : Set G)

abbrev MV (h : Hyp1223 G T L V) : Subgroup G := h.M ⊓ Subgroup.normalizer (V : Set G)

noncomputable abbrev MVbar (h : Hyp1223 G T L V) : Subgroup (MulAut ↥V) := autOn h.MV V

abbrev Gv (_ : Hyp1223 G T L V) (v : G) : Subgroup G := Subgroup.centralizer ({v} : Set G)

abbrev Mv (h : Hyp1223 G T L V) (v : G) : Subgroup G :=
  h.M ⊓ Subgroup.centralizer ({v} : Set G)

abbrev Lv (_ : Hyp1223 G T L V) (v : G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))

abbrev Tv (_ : Hyp1223 G T L V) (v : G) : Subgroup G := T ⊓ Subgroup.centralizer ({v} : Set G)

end Hyp1223

instance zpowers_subgroupOf_centralizer_normal {G : Type*} [Group G] (z : G) :
    ((Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute (g : G) z := (Subgroup.mem_centralizer_iff.mp g.2 z rfl).symm
  have hgn : (g : G) * (n : G) * (g : G)⁻¹ = n := by
    rw [← hk, (hc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgn]
  exact hn

namespace Hyp1223

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

abbrev Gtilde (h : Hyp1223 G T L V) (z : G) : Type :=
  ↥(h.Gv z) ⧸ (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set G))

end Hyp1223

theorem stmt12_2_13_iff : Stmt12_2_13 ↔
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
      (∃ v ∈ V, v ≠ 1 ∧
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∨
      (∃ n : ℕ, (n = 3 ∨ n = 4) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        LieModel G .PSL (n + 1) 2 1) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        Nonempty (G ≃* alternatingGroup (Fin 9))) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        Nonempty (G ≃* NativeSporadic.M24)) := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem stmt12_4_2_iff : Stmt12_4_2 ↔
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        Nat.card V = 2 ^ 10 →
        ¬ Subgroup.centralizer ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) ≤
          Subgroup.normalizer (L : Set G)) := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem stmt12_6_34_iff : Stmt12_6_34 ↔
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
      (∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) →
        Nat.card V = 2 ^ 4 ∧ L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 4 1 := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem stmt12_7_1_iff : Stmt12_7_1 ↔
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
      (∃ _ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal,
        CFSG.IsQuasisimple (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ∧
        Nat.card (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)) = 3 ∧
        Nonempty ((↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ⧸
            Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ≃*
          alternatingGroup (Fin 6))) →
        Nonempty (G ≃* NativeSporadic.M24) ∨ Nonempty (G ≃* NativeSporadic.He) := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

@[expose] def transvection15 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 4 by decide) 1

@[expose] def Asc94_M24He_L52Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G → orderOf z = 2 →
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
      ↥(Subgroup.centralizer
        ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) →
    (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      g⁻¹ * z * g ≠ z) →
      (LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24) ∨
          Nonempty (G ≃* NativeSporadic.He)) ∧
        ((∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
            ∃ φ : ↥(Subgroup.normalizer (E : Set G)) →* GL (Fin 4) (ZMod 2),
              Function.Surjective φ ∧
              φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf
                (Subgroup.normalizer (E : Set G))) →
          ¬ Nonempty (G ≃* NativeSporadic.He) ∧
            (LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24)))

end CFSG.Quasithin.H13
