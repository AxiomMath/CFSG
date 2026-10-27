module

public import CFSG.Quasithin.Background.AutOnEquiv
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.H13.NQS1345B
public import CFSG.Quasithin.H13.U3L14Blk
public import CFSG.Quasithin.Recognition.HSTypeModels

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_le_o2Z (K : Subgroup G) : pCoreOf 2 K ≤ A6.o2Z K := by
  intro x hx
  have hxK : x ∈ K := LieType.BorelTits.pCoreOf_le 2 K hx
  refine ⟨⟨x, hxK⟩, ?_, rfl⟩
  show ((⟨x, hxK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ center (↥K ⧸ CFSG.pCore 2 ↥K)
  rw [(QuotientGroup.eq_one_iff _).2 ((A6.mem_pCore_iff _).2 hx)]
  exact one_mem _

omit [Finite G] in
theorem relIndex_o2Z_of_center_eq_bot {K : Subgroup G}
    (hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    (A6.o2Z K).relIndex K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  rw [le_antisymm (o2Z_le_pCoreOf_of_center hZK) (pCoreOf_le_o2Z K),
    U3.relIndex_pCoreOf_eq_card]

omit [Finite G] in
theorem relIndex_o2Z_eq (K : Subgroup G) :
    (A6.o2Z K).relIndex K = Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have h1 : (A6.o2Z K).subgroupOf K =
      (center (↥K ⧸ CFSG.pCore 2 ↥K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
    ext k
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨k', hk', hkk'⟩
      have e : k' = k := Subtype.ext hkk'
      rw [← e]
      exact hk'
    · intro h
      exact ⟨k, h, rfl⟩
  rw [relIndex, h1, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    index_eq_card]

omit [Finite G] in
theorem card_autOn_of_type {K W : Subgroup G} (hKW : K ≤ normalizer (W : Set G))
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) :
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) → Nat.card ↥(autOn K W) = 60) ∧
    (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 → Nat.card ↥(autOn K W) = 168) ∧
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) →
      Nat.card ↥(autOn K W) = 360) ∧
    (A6.IsHatA6 K → Nat.card ↥(autOn K W) = 360) := by
  have h1 : Nat.card ↥(autOn K W) = (A6.o2Z K).relIndex K := by
    rw [card_autOn_eq_relIndex hKW, ← ho2Z]
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine ⟨fun he => ?_, fun h3 => ?_, fun he => ?_, fun hh => ?_⟩
  · obtain ⟨e⟩ := he
    rw [h1, relIndex_o2Z_of_center_eq_bot (center_eq_bot_of_simple_types (Or.inl ⟨e⟩)),
      Nat.card_congr e.toEquiv, h60]
  · rw [h1, relIndex_o2Z_of_center_eq_bot (center_eq_bot_of_simple_types (Or.inr (Or.inl h3))),
      card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h3)]
  · obtain ⟨e⟩ := he
    rw [h1, relIndex_o2Z_of_center_eq_bot (center_eq_bot_of_simple_types (Or.inr (Or.inr ⟨e⟩))),
      Nat.card_congr e.toEquiv, h360]
  · obtain ⟨-, -, ⟨e⟩⟩ := hh
    rw [h1, relIndex_o2Z_eq, Nat.card_congr e.toEquiv, h360]

omit [Finite G] in
theorem autOn_mulEquiv_alt {K W : Subgroup G} [IsMulCommutative ↥W] {n : ℕ} (hn : 5 ≤ n)
    (h : AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ n) :
    Nonempty (↥(autOn K W) ≃* ↥(alternatingGroup (Fin n))) := by
  obtain ⟨π, hπ⟩ := h
  have hinj := hπ.injective_of_faithful (A6.altDn_faithful hn)
  exact ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩

omit [Finite G] in
theorem autOn_mulEquiv_A6_of_core {K W : Subgroup G} [IsMulCommutative ↥W]
    (h : FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) :
    Nonempty (↥(autOn K W) ≃* ↥(alternatingGroup (Fin 6))) := by
  obtain ⟨π, hπ⟩ := h
  have hinj := hπ.injective_of_faithful (A6.altCoreModel_faithful (by norm_num))
  exact ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩

omit [Finite G] in
theorem autOn_mulEquiv_SL32 {K W : Subgroup G} [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) :
    Nonempty (↥(autOn K W) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨D⟩ := hnat.toL3Coord
  exact ⟨(MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm⟩

omit [Finite G] in
theorem card_autOn_of_module {K W : Subgroup G} [IsMulCommutative ↥W] :
    (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5 → Nat.card ↥(autOn K W) = 60) ∧
    (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 → Nat.card ↥(autOn K W) = 360) ∧
    (FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥ →
      Nat.card ↥(autOn K W) = 360) ∧
    (BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 → Nat.card ↥(autOn K W) = 168) := by
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨e⟩ := autOn_mulEquiv_alt (by norm_num) h
    rw [Nat.card_congr e.toEquiv, h60]
  · obtain ⟨e⟩ := autOn_mulEquiv_alt (by norm_num) h
    rw [Nat.card_congr e.toEquiv, h360]
  · obtain ⟨e⟩ := autOn_mulEquiv_A6_of_core h
    rw [Nat.card_congr e.toEquiv, h360]
  · obtain ⟨e⟩ := autOn_mulEquiv_SL32 h
    rw [Nat.card_congr e.toEquiv]
    exact HSType.card_SL_three_two

omit [Finite G] in
theorem match13410 {K W : Subgroup G} [IsMulCommutative ↥W] (hKW : K ≤ normalizer (W : Set G))
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K)
    (hmod : (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
      (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
      (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
        FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) ∨
      (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
        BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 ∧ W ⊓ centralizer (K : Set G) = ⊥)) :
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∧
        AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5) ∨
      (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
        BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) ∨
      ((Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K) ∧
        ((AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
          (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
            FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥))) := by
  obtain ⟨c5, c3, c6, cH⟩ := card_autOn_of_type hKW ho2Z
  obtain ⟨m5, m6, mc, m3⟩ := card_autOn_of_module (K := K) (W := W)
  rcases hmod with ⟨h5, -⟩ | h6 | hc | ⟨h3, hn, -⟩
  · have hc60 := m5 h5
    rcases hK with h | h | h | h
    · exact Or.inl ⟨h, h5⟩
    · rw [c3 h] at hc60
      omega
    · rw [c6 h] at hc60
      omega
    · rw [cH h] at hc60
      omega
  · have hc360 := m6 h6.1
    rcases hK with h | h | h | h
    · rw [c5 h] at hc360
      omega
    · rw [c3 h] at hc360
      omega
    · exact Or.inr (Or.inr ⟨Or.inl h, Or.inl h6⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h, Or.inl h6⟩)
  · have hc360 := mc hc.2.2
    rcases hK with h | h | h | h
    · rw [c5 h] at hc360
      omega
    · rw [c3 h] at hc360
      omega
    · exact Or.inr (Or.inr ⟨Or.inl h, Or.inr hc⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h, Or.inr hc⟩)
  · exact Or.inr (Or.inl ⟨h3, hn⟩)

omit [Finite G] in
theorem autOn_mulEquiv_of_inf_eq {K W W' : Subgroup G} (hKW : K ≤ normalizer (W : Set G))
    (hKW' : K ≤ normalizer (W' : Set G))
    (h : K ⊓ centralizer (W : Set G) = K ⊓ centralizer (W' : Set G)) :
    Nonempty (↥(autOn K W) ≃* ↥(autOn K W')) :=
  CFSG.Quasithin.InternalSec.nonempty_autOn_equiv hKW hKW' h

end CFSG.Quasithin.H13.NQS134
