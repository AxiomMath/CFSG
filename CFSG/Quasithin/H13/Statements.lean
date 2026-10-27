module

public import CFSG.Quasithin.QTH13Cat
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups

@[expose] def QT13Excluded (G : Type) [Group G] : Prop :=
  (∃ (t : StatedLieTag) (n f : ℕ), 2 ≤ f ∧ StatedLieAdmissible t n 2 f ∧ LieModel G t n 2 f) ∨
    (LieModel G .PSL 4 2 1 ∨ LieModel G .PSL 5 2 1) ∨
    Nonempty (G ≃* alternatingGroup (Fin 9)) ∨
    (Nonempty (G ≃* NativeSporadic.M22) ∨ Nonempty (G ≃* NativeSporadic.M23) ∨
      Nonempty (G ≃* NativeSporadic.M24) ∨ Nonempty (G ≃* NativeSporadic.He) ∨
      Nonempty (G ≃* NativeSporadic.J4))

structure QTH13 (G : Type) [Group G] [Finite G] (T L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  faithful : quasithinIsFaithfulLocal T L
  not_excluded : ¬ QT13Excluded G
  a5 : quasithinO2QuotientIso L (alternatingGroup (Fin 5)) →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      quasithinO2QuotientIso K (alternatingGroup (Fin 5))

@[expose] def ExcludedOrderBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G], QT13Excluded G → Nat.card G ∈ quasithinH13ExcludedOrders

theorem QTH13.of_cat (hB : ExcludedOrderBridge) {G : Type} [Group G] [Finite G]
    {T L : Subgroup G} (h : quasithinQTH13Cat G T L) : QTH13 G T L where
  simple := h.simple
  nonabelian := h.nonabelian
  qtke := h.qtke
  sylow := h.sylow
  faithful := h.faithful
  not_excluded := fun hx => h.not_excluded (hB G hx)
  a5 := h.a5

theorem quasithinO2QuotientIso_iff {G : Type*} [Group G] (L : Subgroup G) (H : Type*) [Group H] :
    quasithinO2QuotientIso L H ↔ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* H) := by
  have hc : CFSG.pCore 2 ↥L = CFSG.Open.pCore 2 ↥L := CFSG.pCore_eq_open (↥L) 2
  constructor
  · rintro ⟨φ, hφ, hker⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (hc.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
  · rintro ⟨e⟩
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
      e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

@[expose] def QT13Five (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
    LieModel Q .PSL 3 2 1 ∨
    Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
    (Group.IsPerfect Q ∧ Nat.card (Subgroup.center Q) = 3 ∧
      Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6))) ∨
    LieModel Q .PSU 3 3 1

@[expose] def Stmt13_1_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Stmt13_1_2_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → QT13Five (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Stmt13_3_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1

@[expose] def Stmt13_6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    quasithinO2QuotientIso L (alternatingGroup (Fin 5)) →
      LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1

@[expose] def Stmt13_8_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 6)) →
      LieModel G .PSp 3 2 1 ∨ LieModel G .PSU 4 3 1

@[expose] def Stmt14_8_1_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      LieModel G .PSp 3 2 1 ∨ LieModel G .G2 0 3 1 ∨
        Nonempty (G ≃* NativeSporadic.HS) ∨ Nonempty (G ≃* NativeSporadic.Ru)

@[expose] def ModelSp6_2 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSp 3 2 1 →
    Nonempty (X ≃* Matrix.symplecticGroup (Fin 3) (ZMod 2))

@[expose] def ModelU4_3 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSU 4 3 1 → Nonempty (X ≃* quasithinPSU 4 3 1)

@[expose] def ModelU4_2 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSU 4 2 1 → Nonempty (X ≃* quasithinPSU 4 2 1)

@[expose] def ModelL4_3 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSL 4 3 1 → Nonempty (X ≃* PSL(4, ZMod 3))

@[expose] def ModelG2_3 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .G2 0 3 1 → Nonempty (X ≃* quasithinG2 (ZMod 3))

@[expose] def ModelHS : Prop :=
  Nonempty (NativeSporadic.HS ≃* quasithinHS)

@[expose] def ModelRu : Prop :=
  Nonempty (NativeSporadic.Ru ≃* quasithinRu)

end CFSG.Quasithin.H13
