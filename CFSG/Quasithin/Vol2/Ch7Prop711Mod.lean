module

public import CFSG.Quasithin.Vol2.Ch10SecB3Five
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases

public section

namespace CFSG.Quasithin.H13.Prop711

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_iff_of_card {L V W : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hWV : W ≤ V) (hcard : Nat.card ↥(autOn L V) = Nat.card ↥(autOn L W)) :
    ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) ↔ l ∈ Subgroup.centralizer (W : Set G) := by
  intro l hl
  refine ⟨fun h => Subgroup.centralizer_le hWV h, fun h => ?_⟩
  obtain ⟨r, hrs, hr⟩ := exists_autOn_restrict hLV hLW hWV
  have hbij : Function.Bijective r := hrs.bijective_of_nat_card_le hcard.le
  set a : ↥(autOn L V) :=
    ⟨A4.actionOn V L hLV ⟨l, hl⟩, (A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, rfl⟩⟩ with ha
  have hra : r a = 1 := by
    apply Subtype.ext
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [hr a w]
    show ((A4.actionOn V L hLV ⟨l, hl⟩ ⟨w, hWV w.2⟩ : ↥V) : G) = w
    rw [A4.actionOn_apply_coe]
    show l * w * l⁻¹ = w
    rw [← Subgroup.mem_centralizer_iff.mp h w w.2, mul_inv_cancel_right]
  have ha1 : a = 1 := hbij.1 (hra.trans (map_one r).symm)
  have h1 : A4.actionOn V L hLV ⟨l, hl⟩ = 1 := congrArg Subtype.val ha1
  exact (A4.actionOn_eq_one_iff hLV ⟨l, hl⟩).mp h1

theorem card_SL_eq {d : ℕ} [NeZero d] {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']
    (h : Nat.card K = Nat.card K') :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin d) K') := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  rw [Matrix.card_SL_field, Matrix.card_SL_field]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  rw [h]

theorem binaryNaturalSL_subgroupOf {L V W : Subgroup G} [IsMulCommutative ↥V]
    [IsMulCommutative ↥W] (hWV : W ≤ V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) {d a : ℕ} [NeZero d] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ a)
    (e : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin d) K)
    (h : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ d a) :
    BinaryNaturalSL (V := ↥V) (autOn L V) (W.subgroupOf V) ⊥ d a := by
  obtain ⟨K', _, _, hK', ⟨e'⟩⟩ := BinaryNaturalSL.exists_equiv h
  have hcard : Nat.card ↥(autOn L V) = Nat.card ↥(autOn L W) := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL d K').toEquiv]
    exact card_SL_eq (hK.trans hK'.symm)
  have hC := mem_centralizer_iff_of_card hLV hLW hWV hcard
  obtain ⟨K'', _, _, hK'', hR⟩ := h
  exact ⟨K'', inferInstance, inferInstance, hK'',
    Vol2.Ch10.SecB.realizes_subgroupOf hWV hLV hLW hC hR⟩

theorem binaryNaturalSp4_subgroupOf {L V W : Subgroup G} [IsMulCommutative ↥V]
    [IsMulCommutative ↥W] (hWV : W ≤ V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ a) (e : ↥(autOn L V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K))
    (h : BinaryNaturalSp4 (V := ↥W) (autOn L W) ⊤ ⊥ a) :
    BinaryNaturalSp4 (V := ↥V) (autOn L V) (W.subgroupOf V) ⊥ a := by
  obtain ⟨K', _, _, hK', ⟨e'⟩⟩ := BinaryNaturalSp4.exists_equiv h
  have hcard : Nat.card ↥(autOn L V) = Nat.card ↥(autOn L W) := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hK']
  have hC := mem_centralizer_iff_of_card hLV hLW hWV hcard
  obtain ⟨K'', _, _, hK'', hR⟩ := h
  exact ⟨K'', inferInstance, inferInstance, hK'',
    Vol2.Ch10.SecB.realizes_subgroupOf hWV hLV hLW hC hR⟩

theorem alternatingNatural_subgroupOf {L V W : Subgroup G} [IsMulCommutative ↥V]
    [IsMulCommutative ↥W] (hWV : W ≤ V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (e : ↥(autOn L V) ≃* alternatingGroup (Fin 6))
    (h : AlternatingNatural (V := ↥W) (autOn L W) ⊤ ⊥ 6) :
    AlternatingNatural (V := ↥V) (autOn L V) (W.subgroupOf V) ⊥ 6 := by
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π :=
    hπ.injective_of_faithful (altDn_faithful_of_five_le (by norm_num))
  have hcard : Nat.card ↥(autOn L V) = Nat.card ↥(autOn L W) := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
  have hC := mem_centralizer_iff_of_card hLV hLW hWV hcard
  exact Vol2.Ch10.SecB.realizes_subgroupOf hWV hLV hLW hC ⟨π, hπ⟩

omit [Finite G] in
theorem isPerfect_autOn {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hL : ⁅L, L⁆ = L) : Group.IsPerfect ↥(autOn L V) := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  exact Group.IsPerfect.ofSurjective (InternalSec.autOnHom_surjective hLV)

end CFSG.Quasithin.H13.Prop711
