module

public import CFSG.Quasithin.Background.SmithB42Disp
import CFSG.GroupTheory.E3Params
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyInnerAction
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
open CFSG.Quasithin.B42Disp

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

theorem w135c2_mem_normalizer_of_ctx (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hLY : L ≤ Y := hctx.2.2.1
  have hconj : ∀ g ∈ L, t * g * t⁻¹ ∈ L := by
    intro g hg
    have hmem := (w135_normal_of_ctx hctx).conj_mem
      (⟨g, hLY hg⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hg) (⟨t, htY⟩ : ↥Y)
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have htt : t * t = 1 := by
    rw [← sq, ← ht2]
    exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj h, fun h' => ?_⟩
  have h'' := hconj _ h'
  have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
    rw [hti]
    calc t * (t * h * t) * t = (t * t) * h * (t * t) := by simp only [mul_assoc]
      _ = h := by rw [htt, one_mul, mul_one]
  rwa [e] at h''

theorem w135c2_card_range_eq_index (g : MulAut W) :
    Nat.card (Set.range fun v : W => g v * v⁻¹) = (fixV (Subgroup.zpowers g)).index := by
  rw [← CFSG.Quasithin.ker_commHom g, Subgroup.index_ker]
  exact (Nat.card_congr
    (Set.equivOfEq (MonoidHom.coe_range (CFSG.Quasithin.commHom g)))).symm

theorem w135c2_le_mQuot_of_two_pow_le_index (hW : ∀ w : W, w ^ 2 = 1) (g : MulAut W) {k : ℕ}
    (h : 2 ^ k ≤ (fixV (Subgroup.zpowers g)).index) :
    k ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  rw [CFSG.Quasithin.B1.index_eq_two_pow hW] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h

theorem w135c2_mem_of_inner (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (hZ : Subgroup.center ↥L = ⊥) {M : Type*} [Group M] (e : ↥L ⧸ Subgroup.center ↥L ≃* M)
    (ht2 : orderOf t = 2) (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hin : modelAct L e ⟨t, ht⟩ ∈ (MulAut.conj : M →* MulAut M).range) : t ∈ L := by
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hin
  obtain ⟨l, hl⟩ := exists_lift L e m
  have hkey : ∀ y : ↥L,
      CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, ht⟩ y = l * y * l⁻¹ := by
    intro y
    have h1 : modelAct L e ⟨t, ht⟩ (e (QuotientGroup.mk y)) =
        e (QuotientGroup.mk
          (CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, ht⟩ y)) :=
      modelAct_apply_mk L e ⟨t, ht⟩ y
    have h2 : modelAct L e ⟨t, ht⟩ (e (QuotientGroup.mk y)) =
        e (QuotientGroup.mk (l * y * l⁻¹)) := by
      rw [← hm, MulAut.conj_apply, ← hl]
      simp only [map_mul, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have heq : QuotientGroup.mk
          (CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, ht⟩ y) =
        QuotientGroup.mk (l * y * l⁻¹) := e.injective (h1.symm.trans h2)
    have hmem : (CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, ht⟩ y)⁻¹ *
        (l * y * l⁻¹) ∈ Subgroup.center ↥L := QuotientGroup.eq.mp heq
    rw [hZ, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hmem
  refine CFSG.QuasithinUnique.Setup.Family.mem_of_inner_action
    (L := L) (b := t) (l := (l : MulAut W)) (fun w => ?_) ?_ (w135_odd_card_center hctx)
    l.2 ?_ ?_
  · simpa [pow_two] using hW w
  · intro U hU
    exact (hctx.2.2.2.2.2).2.2.2 U hU bot_le le_top
  · have htt : t * t = 1 := by
      rw [← sq, ← ht2]
      exact pow_orderOf_eq_one t
    exact htt
  · intro y hy
    have hc := congrArg (fun z : ↥L => (z : MulAut W)) (hkey ⟨y, hy⟩)
    simpa [CFSG.QuasithinUnique.Setup.X5.coe_conjOn] using hc

theorem w135c2_mem_of_involutory_inner (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (hZ : Subgroup.center ↥L = ⊥) {M : Type*} [Group M] (e : ↥L ⧸ Subgroup.center ↥L ≃* M)
    (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hinner : ∀ α : MulAut M, α * α = 1 → α ∈ (MulAut.conj : M →* MulAut M).range) : t ∈ L := by
  have hN := w135c2_mem_normalizer_of_ctx hctx htY ht2
  refine w135c2_mem_of_inner hW hctx hZ e ht2 hN (hinner _ ?_)
  have htt : t * t = 1 := by
    rw [← sq, ← ht2]
    exact pow_orderOf_eq_one t
  rw [← map_mul]
  have h1 : (⟨t, hN⟩ * ⟨t, hN⟩ : Subgroup.normalizer (L : Set (MulAut W))) = 1 :=
    Subtype.ext htt
  rw [h1, map_one]

end CFSG.LocalAnalysis.WeakClosure81
