module

public import CFSG.Quasithin.H13.U3C137Five
public import CFSG.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem card_of_psl32 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
  rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two]

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_of_a6 {L : Subgroup G}
    (h : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_alt6]

theorem card_of_hatA6 {L : Subgroup G} (h : A6.IsHatA6 L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [h3, Nat.card_congr e.toEquiv, card_alt6] at h2
  rw [h2]

theorem card_of_psu33 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 :=
  card_of_lieModel_PSU_three_three h

theorem not_a6_of_psl32 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := fun h' => by
  have h1 := card_of_psl32 h
  rw [card_of_a6 h'] at h1
  omega

theorem not_hatA6_of_psl32 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    ¬ A6.IsHatA6 L := fun h' => by
  have h1 := card_of_psl32 h
  rw [card_of_hatA6 h'] at h1
  omega

theorem not_psu33_of_psl32 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := fun h' => by
  have h1 := card_of_psl32 h
  rw [card_of_psu33 h'] at h1
  omega

theorem not_psl32_of_a6 {L : Subgroup G}
    (h : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun h' => not_a6_of_psl32 h' h

theorem not_hatA6_of_a6 {L : Subgroup G}
    (h : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) : ¬ A6.IsHatA6 L :=
  fun h' => by
  have h1 := card_of_a6 h
  rw [card_of_hatA6 h'] at h1
  omega

theorem not_psu33_of_a6 {L : Subgroup G}
    (h : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := fun h' => by
  have h1 := card_of_a6 h
  rw [card_of_psu33 h'] at h1
  omega

theorem not_psl32_of_hatA6 {L : Subgroup G} (h : A6.IsHatA6 L) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun h' => not_hatA6_of_psl32 h' h

theorem not_a6_of_hatA6 {L : Subgroup G} (h : A6.IsHatA6 L) :
    ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := fun h' =>
  not_hatA6_of_a6 h' h

theorem not_psu33_of_hatA6 {L : Subgroup G} (h : A6.IsHatA6 L) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := fun h' => by
  have h1 := card_of_hatA6 h
  rw [card_of_psu33 h'] at h1
  omega

theorem not_psl32_of_psu33 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun h' => not_psu33_of_psl32 h' h

theorem not_a6_of_psu33 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := fun h' =>
  not_psu33_of_a6 h' h

theorem not_hatA6_of_psu33 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    ¬ A6.IsHatA6 L := fun h' => not_psu33_of_hatA6 h' h

@[expose] def BlockPart (L : Subgroup G) : Prop :=
  (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsLnBlock L 3) ∧
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) → H13.IsA6Block L) ∧
    (A6.IsHatA6 L → H13.IsHatA6Block L) ∧
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → H13.IsG2Block L)

theorem blockPart_of_psl32 {L : Subgroup G} (hL : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hB : IsLnBlock L 3) : BlockPart L :=
  ⟨fun _ => hB, fun h => (not_a6_of_psl32 hL h).elim, fun h => (not_hatA6_of_psl32 hL h).elim,
    fun h => (not_psu33_of_psl32 hL h).elim⟩

theorem blockPart_of_a6 {L : Subgroup G}
    (hL : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hB : H13.IsA6Block L) : BlockPart L :=
  ⟨fun h => (not_psl32_of_a6 hL h).elim, fun _ => hB, fun h => (not_hatA6_of_a6 hL h).elim,
    fun h => (not_psu33_of_a6 hL h).elim⟩

theorem blockPart_of_hatA6 {L : Subgroup G} (hL : A6.IsHatA6 L) (hB : H13.IsHatA6Block L) :
    BlockPart L :=
  ⟨fun h => (not_psl32_of_hatA6 hL h).elim, fun h => (not_a6_of_hatA6 hL h).elim, fun _ => hB,
    fun h => (not_psu33_of_hatA6 hL h).elim⟩

theorem blockPart_of_psu33 {L : Subgroup G} (hL : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hB : H13.IsG2Block L) : BlockPart L :=
  ⟨fun h => (not_psl32_of_psu33 hL h).elim, fun h => (not_a6_of_psu33 hL h).elim,
    fun h => (not_hatA6_of_psu33 hL h).elim, fun _ => hB⟩

@[expose] def Concl (X T V L P : Subgroup G) : Prop :=
  CharNormal (baum (pCoreOf 2 P)) X ∨ BlockPart L ∨
    (Nat.card ↥(autOn X V) = 12096 ∧ ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧
      l ≤ V ∧ Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      P ≤ normalizer (l : Set G)) ∨
    ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) ∧
      (∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ V ∧
        Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
        P ≤ normalizer (l : Set G)) ∧
      (A6.IsHatA6 L → ¬ oTwoUpper (A6.o2Z L) ≤ P) ∧
      ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V))

theorem statement_of
    (h : ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
      CharTwo X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L →
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨ autOn T V ≤ autOn L V ∨
        ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) →
      T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
      (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
      IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ →
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
        Nat.card ↥⁅V, L⁆ = 8 ∧ ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ centralizer ({u} : Set G)) →
      Concl X T V L P) : C137StatementFive :=
  fun G _ _ X T V L P M => h G X T V L P M

end CFSG.Quasithin.H13.U3.GC137
