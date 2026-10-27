module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.AmbientTransport
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def KFAt (p : ℕ) (E : Subgroup G) (f : ℕ) (t : MulAut E) : Prop :=
  (¬ ∃ f' : ℕ, kExceptional p (kZero p E t) f') ∧
    StatedClassicalModel ↥(kZero p E t) .PSL 2 2 f ∧
    E ⊓ Subgroup.centralizer (kZero p E t : Set G) = autFixedInG E t ∧
    autMovedInG E t ≤ kZero p E t ∧
    ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
      k ∈ kZero p E t ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t

@[expose] def KFPair (p : ℕ) (E : Subgroup G) (f : ℕ) (s t : MulAut E) : Prop :=
  (s * t = t * s → kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
    kZero p E s ⊓ kZero p E t = ⊥) ∧
  (orderOf (s * t) = 3 → CentrallyUThree f ↥(kZero p E s ⊔ kZero p E t))

@[expose] def KFPairL (p : ℕ) (E : Subgroup G) (f : ℕ) (s t : MulAut E) : Prop :=
  (s * t = t * s → kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
    kZero p E s ⊓ kZero p E t = ⊥) ∧
  (orderOf (s * t) = 3 → CentrallyLThree f ↥(kZero p E s ⊔ kZero p E t))

namespace Equivariance

omit [Finite G] in
theorem conjAut_inv {E : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    conjAut E w⁻¹ ((Subgroup.normalizer (E : Set G)).inv_mem hw) = (conjAut E w hw)⁻¹ := by
  unfold conjAut
  have : (⟨w⁻¹, (Subgroup.normalizer (E : Set G)).inv_mem hw⟩ : Subgroup.normalizer (E : Set G)) =
      (⟨w, hw⟩ : Subgroup.normalizer (E : Set G))⁻¹ := rfl
  rw [this, map_inv]

end Equivariance

omit [Finite G] in
theorem KFAt.conj {p : ℕ} {E : Subgroup G} {f : ℕ} {t : MulAut E} (h : KFAt p E f t) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    KFAt p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  obtain ⟨hne, hmod, hcent, hmoved, k, hk, hkK, hkt⟩ := h
  have hK := kZero_conj p t hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]
    rintro ⟨f', hf'⟩
    exact hne ⟨f', (Equivariance.kExceptional_conjBy_iff p f' w (kZero p E t)).mp hf'⟩
  · rw [hK]
    exact (Equivariance.statedClassicalModel_conjBy_iff w (kZero p E t)).mpr hmod
  · have hE : conjBy w E = E := Equivariance.conjBy_eq_of_mem_normalizer hw
    rw [hK, Equivariance.centralizer_conjBy, Equivariance.autFixedInG_conj t hw, ← hcent]
    have h1 : conjBy w (E ⊓ Subgroup.centralizer (kZero p E t : Set G)) =
        conjBy w E ⊓ conjBy w (Subgroup.centralizer (kZero p E t : Set G)) := by
      unfold conjBy
      exact Subgroup.map_inf _ _ _ (MulAut.conj w).injective
    rw [h1, hE]
  · rw [hK, Equivariance.autMovedInG_conj t hw]
    exact Subgroup.map_mono hmoved
  · refine ⟨w * k * w⁻¹, (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem hw hk)
      ((Subgroup.normalizer (E : Set G)).inv_mem hw), ?_, ?_⟩
    · rw [hK]
      exact Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
    · have h2 := Equivariance.conj_conjAut_normalizerMonoidHom hw ⟨k, hk⟩
      rw [hkt, MulAut.conj_apply] at h2
      exact h2.symm

omit [Finite G] in
theorem KFAt.of_conj {p : ℕ} {E : Subgroup G} {f : ℕ} {t : MulAut E} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (h : KFAt p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹)) : KFAt p E f t := by
  have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have h2 := h.conj hw'
  rw [Equivariance.conjAut_inv hw] at h2
  simpa [mul_assoc] using h2

omit [Finite G] in
theorem KFPair.conj {p : ℕ} {E : Subgroup G} {f : ℕ} {s t : MulAut E} (h : KFPair p E f s t)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    KFPair p E f (conjAut E w hw * s * (conjAut E w hw)⁻¹)
      (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  obtain ⟨h1, h2⟩ := h
  have hs := kZero_conj p s hw
  have ht := kZero_conj p t hw
  have hprod : conjAut E w hw * s * (conjAut E w hw)⁻¹ * (conjAut E w hw * t * (conjAut E w hw)⁻¹) =
      conjAut E w hw * (s * t) * (conjAut E w hw)⁻¹ := by group
  have hprod' : conjAut E w hw * t * (conjAut E w hw)⁻¹ * (conjAut E w hw * s *
      (conjAut E w hw)⁻¹) = conjAut E w hw * (t * s) * (conjAut E w hw)⁻¹ := by group
  refine ⟨fun hcomm => ?_, fun hord => ?_⟩
  · rw [hprod, hprod'] at hcomm
    have hcomm' : s * t = t * s := by
      have := mul_left_cancel (mul_right_cancel hcomm)
      exact this
    obtain ⟨hc, hi⟩ := h1 hcomm'
    rw [hs, ht, Equivariance.centralizer_conjBy]
    refine ⟨Subgroup.map_mono hc, ?_⟩
    have : conjBy w (kZero p E s ⊓ kZero p E t) = conjBy w ⊥ := by rw [hi]
    unfold conjBy at this ⊢
    rw [← Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hi, Subgroup.map_bot]
  · rw [hprod] at hord
    have hord' : orderOf (s * t) = 3 := by
      rw [← hord]
      exact (MulEquiv.orderOf_eq (MulAut.conj (conjAut E w hw)) (s * t)).symm
    have h3 := h2 hord'
    rw [hs, ht]
    have hsup : conjBy w (kZero p E s ⊔ kZero p E t) =
        conjBy w (kZero p E s) ⊔ conjBy w (kZero p E t) := by
      unfold conjBy
      exact Subgroup.map_sup _ _ _
    let e : ↥(kZero p E s ⊔ kZero p E t) ≃*
        ↥(conjBy w (kZero p E s) ⊔ conjBy w (kZero p E t)) :=
      ((kZero p E s ⊔ kZero p E t).equivMapOfInjective (MulAut.conj w).toMonoidHom
        (MulAut.conj w).injective).trans (MulEquiv.subgroupCongr hsup)
    exact centrallyUThree_of_equiv e h3

omit [Finite G] in
theorem KFPair.of_conj {p : ℕ} {E : Subgroup G} {f : ℕ} {s t : MulAut E} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (h : KFPair p E f (conjAut E w hw * s * (conjAut E w hw)⁻¹)
      (conjAut E w hw * t * (conjAut E w hw)⁻¹)) : KFPair p E f s t := by
  have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have h2 := h.conj hw'
  rw [Equivariance.conjAut_inv hw] at h2
  simpa [mul_assoc] using h2

omit [Finite G] in
theorem KFPairL.conj {p : ℕ} {E : Subgroup G} {f : ℕ} {s t : MulAut E} (h : KFPairL p E f s t)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    KFPairL p E f (conjAut E w hw * s * (conjAut E w hw)⁻¹)
      (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  obtain ⟨h1, h2⟩ := h
  have hs := kZero_conj p s hw
  have ht := kZero_conj p t hw
  have hprod : conjAut E w hw * s * (conjAut E w hw)⁻¹ * (conjAut E w hw * t * (conjAut E w hw)⁻¹) =
      conjAut E w hw * (s * t) * (conjAut E w hw)⁻¹ := by group
  have hprod' : conjAut E w hw * t * (conjAut E w hw)⁻¹ * (conjAut E w hw * s *
      (conjAut E w hw)⁻¹) = conjAut E w hw * (t * s) * (conjAut E w hw)⁻¹ := by group
  refine ⟨fun hcomm => ?_, fun hord => ?_⟩
  · rw [hprod, hprod'] at hcomm
    have hcomm' : s * t = t * s := by
      have := mul_left_cancel (mul_right_cancel hcomm)
      exact this
    obtain ⟨hc, hi⟩ := h1 hcomm'
    rw [hs, ht, Equivariance.centralizer_conjBy]
    refine ⟨Subgroup.map_mono hc, ?_⟩
    have : conjBy w (kZero p E s ⊓ kZero p E t) = conjBy w ⊥ := by rw [hi]
    unfold conjBy at this ⊢
    rw [← Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hi, Subgroup.map_bot]
  · rw [hprod] at hord
    have hord' : orderOf (s * t) = 3 := by
      rw [← hord]
      exact (MulEquiv.orderOf_eq (MulAut.conj (conjAut E w hw)) (s * t)).symm
    have h3 := h2 hord'
    rw [hs, ht]
    have hsup : conjBy w (kZero p E s ⊔ kZero p E t) =
        conjBy w (kZero p E s) ⊔ conjBy w (kZero p E t) := by
      unfold conjBy
      exact Subgroup.map_sup _ _ _
    let e : ↥(kZero p E s ⊔ kZero p E t) ≃*
        ↥(conjBy w (kZero p E s) ⊔ conjBy w (kZero p E t)) :=
      ((kZero p E s ⊔ kZero p E t).equivMapOfInjective (MulAut.conj w).toMonoidHom
        (MulAut.conj w).injective).trans (MulEquiv.subgroupCongr hsup)
    exact centrallyLThree_of_equiv e h3

omit [Finite G] in
theorem KFPairL.of_conj {p : ℕ} {E : Subgroup G} {f : ℕ} {s t : MulAut E} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (h : KFPairL p E f (conjAut E w hw * s * (conjAut E w hw)⁻¹)
      (conjAut E w hw * t * (conjAut E w hw)⁻¹)) : KFPairL p E f s t := by
  have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have h2 := h.conj hw'
  rw [Equivariance.conjAut_inv hw] at h2
  simpa [mul_assoc] using h2

end CFSG.RankThree.PartOne
