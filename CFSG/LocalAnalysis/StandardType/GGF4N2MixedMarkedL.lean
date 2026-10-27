module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedBadLine
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGF4N2ActualH0
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Order
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma33

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

theorem ggF4N2_mixed_L_le_of_pLayer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    {X I : Subgroup G} (hI : I ≤ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({x} : Set G)))
    (hIcard : Nat.card L ≤ Nat.card I) : L ≤ X := by
  have hS : LargeEvenSStar 5 B x L := hR.1.1.2.2.2.2.2.2.1
  have hBsE : IsElemAbelian 5 Bs := hR.1.2.1.2.1
  obtain ⟨hxBs, hxy, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  have hx1 : x ≠ 1 := fun h => hxy (h ▸ Subgroup.one_mem _)
  have hx : orderOf x = 5 := orderOf_eq_prime (hBsE.2 x hxBs) hx1
  have hcomm : ∀ u ∈ Bs, ∀ w ∈ Bs, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hBsE.1.is_comm.comm (⟨u, hu⟩ : ↥Bs) ⟨w, hw⟩)
  have hE : IsElemAbelian 5 (Bs ⊓ L) :=
    ⟨⟨⟨fun u w => Subtype.ext (hcomm u u.2.1 w w.2.1)⟩⟩, fun u hu => hBsE.2 u hu.1⟩
  have hEcard : 5 < Nat.card ↥(Bs ⊓ L) := by
    rw [ggF4N2Bstar_inf_L_card hR hL]
    norm_num
  have hP : LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({x} : Set G)) ≤ L :=
    ggN2_pLayer_le_of_sStar hS hx (ggF4N2OmegaK_outer_solvable hL) inf_le_right hE hEcard inf_le_right
  have hIeq : I = L := Subgroup.eq_of_le_of_card_ge (hI.trans hP) hIcard
  have hlayer : LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      X ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [CFSG.Assembly.LargeEven.largeEvenPLayer_eq_glaPLayer]
    exact sSup_le fun L hL => hL.1
  rw [← hIeq]
  exact (hI.trans hlayer).trans inf_le_left

theorem ggN2_le_pLayer_of_isComponentOf {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H I : Subgroup G} (hI : CFSG.Open.IsComponentOf I H) (hp : p ∣ Nat.card I) :
    I ≤ LargeEvenPLayer p H := by
  rw [largeEvenPLayer_eq_lBalancePLayer]
  exact le_sSup (lBalanceIsPComponent_of_isComponentOf
    (CFSG.Assembly.isComponentOf_iff_open.mpr hI) (not_le_lBalancePrimeCore_of_dvd hp))

open CFSG.Blueprint in
theorem card_quotient_center_of_lieModel_POmegaMinus_four_two {I : Type} [Group I]
    (hI : LieModel (I ⧸ Subgroup.center I) .POmegaMinus 4 2 2) :
    Nat.card (I ⧸ Subgroup.center I) =
      4 ^ 12 * (4 ^ 4 + 1) * (4 ^ 2 - 1) * (4 ^ 4 - 1) * (4 ^ 6 - 1) := by
  rw [hI.card_eq_lieOrd (by norm_num)]
  decide

open CFSG.Blueprint in
theorem ggF4N2_component_le_pLayer_of_lieModel {G : Type} [Group G] [Finite G] {H I : Subgroup G}
    (hI : CFSG.Open.IsComponentOf I H)
    (hIL : LieModel (↥I ⧸ Subgroup.center ↥I) .POmegaMinus 4 2 2) : I ≤ LargeEvenPLayer 5 H := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ggN2_le_pLayer_of_isComponentOf hI
    (Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center ↥I)))
  rw [card_quotient_center_of_lieModel_POmegaMinus_four_two hIL]
  norm_num

open CFSG.Blueprint in
theorem ggF4N2_card_le_of_lieModel {G : Type} [Group G] [Finite G] {L I : Subgroup G}
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hIL : LieModel (↥I ⧸ Subgroup.center ↥I) .POmegaMinus 4 2 2) : Nat.card L ≤ Nat.card I := by
  rw [card_centralImage_POmegaMinus_four_two hL,
    ← card_quotient_center_of_lieModel_POmegaMinus_four_two hIL]
  exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center ↥I))

open CFSG.Blueprint in
theorem ggF4N2_mixed_L_le_of_component_lieModel
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    {X I : Subgroup G} (hI : CFSG.Open.IsComponentOf I (X ⊓ Subgroup.centralizer ({x} : Set G)))
    (hIL : LieModel (↥I ⧸ Subgroup.center ↥I) .POmegaMinus 4 2 2) : L ≤ X :=
  ggF4N2_mixed_L_le_of_pLayer hR hNbr hL (ggF4N2_component_le_pLayer_of_lieModel hI hIL)
    (ggF4N2_card_le_of_lieModel hL hIL)

open CFSG.Blueprint in
theorem ggF4N2_mixed_Kg_le_of_component_lieModel
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    {X I : Subgroup G}
    (hI : CFSG.Open.IsComponentOf I (X ⊓ Subgroup.centralizer ({g * y * g⁻¹} : Set G)))
    (hIL : LieModel (↥I ⧸ Subgroup.center ↥I) .PSL 6 2 2) :
    K.map (MulAut.conj g).toMonoidHom ≤ X := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hKg : GGCentralImage .PSL 6 2 (K.map (MulAut.conj g).toMonoidHom) :=
    ggCentralImage_map_conj hK g
  have hS := ggF4N2_sStar_map_conj hR hNbr hL hK hgN
  obtain ⟨-, -, hyo, -, -, -⟩ := ggF4N2_x_data hR hNbr
  have hgyo : orderOf (g * y * g⁻¹) = 5 := by
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g y (g * y * g⁻¹) by
      rw [SemiconjBy]
      group)]
    exact hyo
  obtain ⟨T, -, hTK, -, -, -, hTel, hTcard, -, -, -⟩ := ggF4N2_psl6_block_torus_data hKg
  have hP : LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({g * y * g⁻¹} : Set G)) ≤
      K.map (MulAut.conj g).toMonoidHom :=
    ggN2_pLayer_le_of_sStar hS hgyo (isSolvable_outer_of_centralImage_PSL_six_two hKg) hTK hTel
      (by rw [hTcard]; norm_num) inf_le_right
  have h5 : 5 ∣ Nat.card I := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center ↥I))
    rw [hIL.card_eq_lieOrd (by norm_num)]
    decide
  have hIK : I ≤ K.map (MulAut.conj g).toMonoidHom :=
    (ggN2_le_pLayer_of_isComponentOf hI h5).trans hP
  obtain ⟨ψ, hadm, hker, hrange⟩ := hKg
  have hD : Nat.card (GaloisField 2 2) = 2 ^ 2 := by
    simpa using GaloisField.card 2 2 (by norm_num)
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin (5 + 1)) (GaloisField 2 2)) = ⊤ :=
    Group.isPerfect_def.mp
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple (m := 5) (F := GaloisField 2 2)
        (by norm_num)).1
  have hKL : LieModel (↥(K.map (MulAut.conj g).toMonoidHom) ⧸
      Subgroup.center ↥(K.map (MulAut.conj g).toMonoidHom)) .PSL 6 2 2 :=
    hrange ▸ LinNonsplit.lieModel_range_sl (k := 5) hD hadm hperf ψ hker
  have hcard : Nat.card (↥I ⧸ Subgroup.center ↥I) = Nat.card (↥(K.map (MulAut.conj g).toMonoidHom) ⧸
      Subgroup.center ↥(K.map (MulAut.conj g).toMonoidHom)) := by
    rw [hIL.card_eq_lieOrd (by norm_num), hKL.card_eq_lieOrd (by norm_num)]
  have hIeq : I = K.map (MulAut.conj g).toMonoidHom :=
    CFSG.EvenSporadicStandard.Induction.eq_of_le_of_cqOrd_eq hIK
      (CFSG.ClassicalInvolution.ModelFacts.native_isQuasisimple hI.2.2)
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hS.2.2.2.1.2.2)
      hcard
  rw [← hIeq]
  exact hI.1.trans inf_le_left

end CFSG.StandardType

end
