module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCommon
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.Quasithin.Background.SmithB45TorF4

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form mem_inner_of_sq_eq_one_of_odd)
open scoped commutatorElement Pointwise

theorem w135c2_four_le_mQuot_ree
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := w135_odd_card_center hctx
  obtain ⟨-, hR⟩ := hlie.reeTitsModel (by decide)
  obtain ⟨a, K, _, _, _, ha, hea, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hR
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hea]
  have hZ : Subgroup.center ↥L = ⊥ := by
    haveI : Group.IsPerfect ↥L := hq.1
    set π : ↥L →* LieType.Ree.reeFixed LieType.Ree.ReeTag.F4 K a :=
      (LieType.Ree.ReeTag.reeFixedEquivReeGamma K a).symm.toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) with hπ
    have hπs : Function.Surjective π :=
      (LieType.Ree.ReeTag.reeFixedEquivReeGamma K a).symm.surjective.comp
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hker : π.ker = Subgroup.center ↥L := by
      ext l
      simp only [MonoidHom.mem_ker, hπ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    have h0 := CFSG.SectionRank.LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki
      CFSG.SectionRank.LargeRee.suzukiBlockInputs ha (by rw [hK']; rfl) π hπs hker.le
      (by rw [hker]; exact hodd)
    rwa [hker] at h0
  have hinner : ∀ α : MulAut (LieType.Ree.ReeTag.F4.reeGamma K a), α * α = 1 →
      α ∈ (MulAut.conj : LieType.Ree.ReeTag.F4.reeGamma K a →*
        MulAut (LieType.Ree.ReeTag.F4.reeGamma K a)).range := by
    have hoddOuter : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (LieType.Ree.ReeTag.F4.reeGamma K a))) := by
      obtain ⟨-, -, -, -, hcard, -⟩ :=
        large_Ree_full_inner_field_automorphism_normal_form a ha K hK'
      rw [hcard]
      exact ⟨a, rfl⟩
    intro α hα
    exact mem_inner_of_sq_eq_one_of_odd hoddOuter (by rw [sq]; exact hα)
  have htL : t ∈ L :=
    w135c2_mem_of_involutory_inner hW hctx hZ e htY ht2 hinner
  set x : ↥L := ⟨t, htL⟩ with hx
  have htt : t * t = 1 := by rw [← sq, ← ht2]; exact pow_orderOf_eq_one t
  have hx2 : x * x = 1 := Subtype.ext htt
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; omega
  have hx1 : x ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hπ1 : CFSG.Quasithin.B42Disp.modelProj L e x ≠ 1 := fun h =>
    hx1 (CFSG.Quasithin.B45Tor.modelProj_injective L hZ e (h.trans (map_one _).symm))
  have hsq : ((CFSG.Quasithin.B42Disp.modelProj L e x :
      ↥(LieType.Ree.ReeTag.F4.reeGamma K a)) :
      CFSG.Blueprint.Chevalley.ModGL LieType.Ree.ReeTag.F4.tag K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, sq, ← map_mul, hx2, map_one, Subgroup.coe_one]
  have hne : ((CFSG.Quasithin.B42Disp.modelProj L e x :
      ↥(LieType.Ree.ReeTag.F4.reeGamma K a)) :
      CFSG.Blueprint.Chevalley.ModGL LieType.Ree.ReeTag.F4.tag K) ≠ 1 :=
    fun h => hπ1 (Subtype.ext h)
  have hindex : 2 ^ (6 * (2 * a + 1)) ≤ (fixV (Subgroup.zpowers t)).index := by
    rcases CFSG.Quasithin.B42F4.isZConj_or_isTConj ha hK'
      (CFSG.Quasithin.B42Disp.modelProj L e x).2 hsq hne with hz | htc
    · exact CFSG.Quasithin.B45Tor.two_pow_le_index_classZ (x := x) ha hK' hW' L hZ e hz
    · exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
        (CFSG.Quasithin.B45Tor.two_pow_le_index_classT (x := x) ha hK' hW' L hZ e htc)
  have := w135c2_le_mQuot_of_two_pow_le_index hW t hindex
  omega

end CFSG.LocalAnalysis.WeakClosure81
