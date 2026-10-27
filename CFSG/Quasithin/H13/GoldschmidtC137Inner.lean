module

public import CFSG.Quasithin.H13.GoldschmidtC137Blk
public import CFSG.Quasithin.H13.GoldschmidtC137Bridge
public import CFSG.Quasithin.Background.C124AsmStmt
public import CFSG.Quasithin.H13.GoldschmidtC137Concl

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjAct_eq_one_iff_gc (V : Subgroup G) (g : ↥(normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem mem_sup_of_autOn_le {X T V L : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hLX : L ≤ X) (hTX : T ≤ X) (hin : autOn T V ≤ autOn L V) {t : G} (ht : t ∈ T) :
    t ∈ L ⊔ (X ⊓ centralizer (V : Set G)) := by
  have h1 : conjAct V ⟨t, hXN (hTX ht)⟩ ∈ autOn T V :=
    ⟨⟨t, hXN (hTX ht)⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  obtain ⟨⟨l, hlN⟩, hl, hleq⟩ := hin h1
  have hlL : l ∈ L := Subgroup.mem_subgroupOf.1 hl
  have h2 : conjAct V ((⟨l, hlN⟩ : ↥(normalizer (V : Set G)))⁻¹ * ⟨t, hXN (hTX ht)⟩) = 1 := by
    rw [map_mul, map_inv, hleq, inv_mul_cancel]
  have h3 := (conjAct_eq_one_iff_gc V _).1 h2
  have h4 : t = l * (l⁻¹ * t) := by group
  rw [h4]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL)
    (Subgroup.mem_sup_right ⟨X.mul_mem (X.inv_mem (hLX hlL)) (hTX ht), h3⟩)

theorem isAltQuotient_of_centralQuot {L : Subgroup G}
    (e : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      alternatingGroup (Fin 6)) : IsAltQuotient L (oTwoZIn L) 6 := by
  let π₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let π₂ := QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  refine ⟨e.toMonoidHom.comp (π₂.comp π₁),
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)),
    ?_⟩
  ext x
  have key : e (π₂ (π₁ x)) = 1 ↔ π₁ x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  refine key.trans ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem isAltQuotient_of_a6 {L : Subgroup G}
    (h : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    IsAltQuotient L (oTwoZIn L) 6 := by
  obtain ⟨e⟩ := h
  have hc : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    have h1 := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
    ext x
    rw [Subgroup.mem_bot]
    constructor
    · intro hx
      have : e x ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
        Subgroup.mem_center_iff.2 fun g => by
          obtain ⟨y, rfl⟩ := e.surjective g
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
      rw [h1, Subgroup.mem_bot] at this
      exact (map_eq_one_iff e e.injective).1 this
    · rintro rfl
      exact Subgroup.one_mem _
  exact isAltQuotient_of_centralQuot
    ((QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e))

theorem isAltQuotient_of_hatA6 {L : Subgroup G} (h : A6.IsHatA6 L) :
    IsAltQuotient L (oTwoZIn L) 6 := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact isAltQuotient_of_centralQuot e

theorem concl_of_c124_inner [Finite G] (hC124 : C124StatementSQTK (G := G))
    {X T V L P : Subgroup G}
    (hX : CharTwo X) (hSQ : SQTKGroup ↥X) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X) (hL2 : CharTwo L)
    (htype : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L)
    (hin : autOn T V ≤ autOn L V) (hTP : T ≤ P) (hPX : P ≤ X) (hred : IsTwoReducedIn X V)
    (hVL : ⁅V, L⁆ ≠ ⊥) : Concl X T V L P := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  have hQP : pCoreOf 2 X ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans hTP)
      (hPX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
    have h3 := Subgroup.relIndex_mul_relIndex T P X hTP hPX
    have h4 : 2 ∣ T.relIndex X := by
      rw [← h3]
      exact Dvd.dvd.mul_right h2 _
    exact hT.2.2 h4
  have hRT : pCoreOf 2 P ≤ T := pCoreOf_two_le_of_sylowIn hTP hT.2.1 hTodd
  have hRL : pCoreOf 2 P ≤ L ⊔ (X ⊓ centralizer (V : Set G)) := fun r hr =>
    mem_sup_of_autOn_le hred.2.1 hLX hT.1 hin (hRT hr)
  have halt : IsAltQuotient L (oTwoZIn L) 6 := htype.elim isAltQuotient_of_a6 isAltQuotient_of_hatA6
  have hcl := hC124 X T V L (pCoreOf 2 P) 6 hX hSQ hred hT hprod hL hL2 hVL halt hQP hRT
    (Or.inr (Or.inr (Or.inl ⟨rfl, hRL⟩)))
  rcases hcl with ⟨C, hC1, hC2, hC3, hC4⟩ | hchi | ⟨-, hA7 | hA6 | hH⟩
  · exact Or.inl ⟨C, hC2, hC1, hC3, hC4⟩
  · rcases htype with ht | ht
    · exact (not_isChiBlock_of_card hchi (Or.inl (card_of_a6 ht))).elim
    · exact (not_isChiBlock_of_card hchi (Or.inr (card_of_hatA6 ht))).elim
  · rcases htype with ht | ht
    · exact (not_isExcA7Block_of_card hA7 (Or.inl (card_of_a6 ht))).elim
    · exact (not_isExcA7Block_of_card hA7 (Or.inr (card_of_hatA6 ht))).elim
  · rcases htype with ht | ht
    · exact Or.inr (Or.inl (blockPart_of_a6 ht (isA6Block_of_isAltBlockType hA6)))
    · have h1 := card_of_isAltBlockType hA6
      rw [card_of_hatA6 ht] at h1
      omega
  · rcases htype with ht | ht
    · have h1 : A6.IsHatA6 L := ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩
      have h2 := card_of_hatA6 h1
      rw [card_of_a6 ht] at h2
      omega
    · exact Or.inr (Or.inl (blockPart_of_hatA6 ht (isHatA6Block_of hH)))

end CFSG.Quasithin.H13.U3.GC137
