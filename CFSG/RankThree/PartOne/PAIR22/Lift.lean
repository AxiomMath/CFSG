module

public import CFSG.RankThree.PartOne.K1320X.CommDistinctX
public import CFSG.RankThree.PartOne.S13K.KFLiftRows
public import CFSG.RankThree.PartOne.K1320X.TwoSub

public section

namespace CFSG.RankThree.PartOne.PAIR22

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K1320X

variable {G : Type} [Group G]

theorem isQuasisimple_conjBy {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) (w : G) :
    CFSG.IsQuasisimple ↥(conjBy w K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective) hq

theorem center_conjBy_eq_bot {K : Subgroup G} (hc : Subgroup.center ↥K = ⊥) (w : G) :
    Subgroup.center ↥(conjBy w K) = ⊥ := by
  let e : K ≃* conjBy w K :=
    K.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  have h : (Subgroup.center K).map (e : K →* conjBy w K) = Subgroup.center (conjBy w K) :=
    Subgroup.map_center_eq e
  rw [← h, hc, Subgroup.map_bot]

theorem ktLift_conj {p : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (h : KtLift p E t K) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    KtLift p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) (conjBy w K) := by
  obtain ⟨hIs, hq, hc, hmov, k, hk, hkK, hkt⟩ := h
  refine ⟨isKt_conj hIs hw, isQuasisimple_conjBy hq w, center_conjBy_eq_bot hc w, ?_, ?_⟩
  · rw [Equivariance.autMovedInG_conj t hw]
    exact Subgroup.map_mono hmov
  · refine ⟨w * k * w⁻¹, (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem hw hk)
      ((Subgroup.normalizer (E : Set G)).inv_mem hw), Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩, ?_⟩
    have h2 := Equivariance.conj_conjAut_normalizerMonoidHom hw ⟨k, hk⟩
    rw [hkt, MulAut.conj_apply] at h2
    exact h2.symm

@[expose] def PairLift (p : ℕ) (E : Subgroup G) (t : MulAut E) : Prop :=
  ∃ K : Subgroup G, KtLift p E t K ∧ CFSG.IsQuasisimple ↥(kZero p E t)

theorem PairLift.conj {p : ℕ} {E : Subgroup G} {t : MulAut E} (h : PairLift p E t) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    PairLift p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  obtain ⟨K, hK, hq⟩ := h
  refine ⟨conjBy w K, ktLift_conj hK hw, ?_⟩
  rw [kZero_conj p t hw]
  exact isQuasisimple_conjBy hq w

theorem PairLift.of_conj {p : ℕ} {E : Subgroup G} {t : MulAut E} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (h : PairLift p E (conjAut E w hw * t * (conjAut E w hw)⁻¹)) : PairLift p E t := by
  have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have h2 := h.conj hw'
  rw [Equivariance.conjAut_inv hw] at h2
  simpa [mul_assoc] using h2

theorem pairLift_of_kfAt [Finite G] {p g : ℕ} {E : Subgroup G} {t : MulAut E}
    (h : KFAt p E g t) : PairLift p E t :=
  ⟨kZero p E t, ktLift_of_liftAt (S13K.KFAt.toLiftAt h), (S13K.KFAt.toLiftAt h).1⟩

end CFSG.RankThree.PartOne.PAIR22
