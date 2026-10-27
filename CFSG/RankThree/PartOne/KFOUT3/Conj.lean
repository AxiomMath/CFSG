module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KFOUT3.Blocks

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {G : Type} [Group G] {J : Subgroup G}

@[expose] def jConj {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) : ↥J ≃* ↥J where
  toFun j := ⟨u * j * u⁻¹, (Subgroup.mem_normalizer_iff.1 hu j).1 j.2⟩
  invFun j := ⟨u⁻¹ * j * u, (Subgroup.mem_normalizer_iff.1 hu (u⁻¹ * j * u)).2
    (by simp [mul_assoc])⟩
  left_inv j := by apply Subtype.ext; simp [mul_assoc]
  right_inv j := by apply Subtype.ext; simp [mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

theorem jConj_apply {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) (j : ↥J) :
    ((jConj hu j : ↥J) : G) = u * j * u⁻¹ := rfl

@[expose] def jConjQ {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) :
    (↥J ⧸ Subgroup.center ↥J) ≃* (↥J ⧸ Subgroup.center ↥J) :=
  QuotientGroup.congr _ _ (jConj hu) (Subgroup.map_center_eq (jConj hu))

theorem jConjQ_mk {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) (j : ↥J) :
    jConjQ hu (QuotientGroup.mk j) = QuotientGroup.mk (jConj hu j) := rfl

variable {K : Type} [Field K]

@[expose] def conjAut (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K) {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) : MulAut (PSL3 K) :=
  ι.symm.trans ((jConjQ hu).trans ι)

theorem conjAut_apply (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K) {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (j : ↥J) :
    conjAut ι hu (ι (QuotientGroup.mk j)) = ι (QuotientGroup.mk (jConj hu j)) := by
  simp [conjAut, jConjQ_mk]

theorem conjAut_pow_apply (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K) {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (n : ℕ) (j : ↥J) :
    (conjAut ι hu ^ n) (ι (QuotientGroup.mk j)) =
      ι (QuotientGroup.mk (jConj (pow_mem hu n) j)) := by
  induction n generalizing j with
  | zero =>
    simp only [pow_zero, MulAut.one_apply]
    congr 2
    apply Subtype.ext
    simp [jConj_apply]
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, conjAut_apply]
    congr 2
    apply Subtype.ext
    simp only [jConj_apply, pow_succ']
    group

theorem conjAut_pow_eq_one (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K) {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) {n : ℕ} (hun : u ^ n = 1) :
    conjAut ι hu ^ n = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := ι.surjective x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  rw [conjAut_pow_apply, MulAut.one_apply]
  congr 2
  apply Subtype.ext
  simp [jConj_apply, hun]

theorem conjAut_of_mem (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K) {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (huJ : u ∈ J) (x : PSL3 K) :
    conjAut ι hu x = ι (QuotientGroup.mk ⟨u, huJ⟩) * x * (ι (QuotientGroup.mk ⟨u, huJ⟩))⁻¹ := by
  obtain ⟨y, rfl⟩ := ι.surjective x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  rw [conjAut_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 2

section Torus

variable [Finite K] {p : ℕ} {T : Subgroup G} (hTJ : T ≤ J)
  (ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K)
  (hmaps : ∀ (t : G) (ht : t ∈ T), ι (QuotientGroup.mk ⟨t, hTJ ht⟩) ∈ Tbar p K)
  (honto : ∀ s ∈ Tbar p K, ∃ (t : G) (ht : t ∈ T), ι (QuotientGroup.mk ⟨t, hTJ ht⟩) = s)

include hmaps honto in
theorem conjAut_Tbar {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G))
    (hTu : ∀ t ∈ T, u * t * u⁻¹ ∈ T) : ∀ s, s ∈ Tbar p K ↔ conjAut ι hu s ∈ Tbar p K := by
  apply mem_iff_of_forall_mem (Tbar p K) (conjAut ι hu)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := honto s hs
  rw [conjAut_apply]
  exact hmaps (u * t * u⁻¹) (hTu t ht)

omit [Finite K] in
include honto in
theorem conjAut_action {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) {k : ℕ}
    (hk : ∀ t ∈ T, u * t * u⁻¹ = t ^ k) :
    ∀ t ∈ Tor p K, conjAut ι hu (QuotientGroup.mk t) = (QuotientGroup.mk t) ^ k := by
  intro t ht
  obtain ⟨a, ha, hat⟩ := honto (QuotientGroup.mk t) (mem_Tbar_iff.2 ⟨t, ht, rfl⟩)
  rw [← hat, conjAut_apply]
  have h1 : jConj hu ⟨a, hTJ ha⟩ = (⟨a, hTJ ha⟩ : ↥J) ^ k :=
    Subtype.ext (by rw [jConj_apply, Subgroup.coe_pow]; exact hk a ha)
  rw [h1, QuotientGroup.mk_pow, map_pow]

end Torus

end CFSG.RankThree.PartOne.KFOUT3
