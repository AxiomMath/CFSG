module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem c23a_commElt_conj (W : Subgroup G) (t g : G) :
    commElt (conjSubgroup W g) t = conjSubgroup (commElt W (g * t * g⁻¹)) g := by
  apply le_antisymm
  · rw [commElt, Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    change w⁻¹ * t⁻¹ * w * t ∈ conjSubgroup (commElt W (g * t * g⁻¹)) g
    rw [mem_conjSubgroup_iff]
    refine Subgroup.subset_closure ⟨g * w * g⁻¹, mem_conjSubgroup_iff.1 hw, ?_⟩
    show g * (w⁻¹ * t⁻¹ * w * t) * g⁻¹ = _
    group
  · change Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (commElt W (g * t * g⁻¹)) ≤
      commElt (conjSubgroup W g) t
    rw [commElt, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g⁻¹ * v * g, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have h : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rwa [h]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

private theorem c23a_mSub_conjSubgroup (A : Subgroup G) (g : G) :
    mSub (conjSubgroup A g) = mSub A := by
  unfold mSub rk
  rw [E3.card_conjSubgroup]

private theorem c23a_centralizer_singleton_conj (w g : G) :
    conjSubgroup (Subgroup.centralizer ({g * w * g⁻¹} : Set G)) g =
      Subgroup.centralizer ({w} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : g * (x * w) * g⁻¹ = g * (w * x) * g⁻¹ := by
      calc g * (x * w) * g⁻¹ = (g * x * g⁻¹) * (g * w * g⁻¹) := by group
        _ = (g * w * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * (w * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  · intro h
    calc (g * x * g⁻¹) * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [h]
      _ = (g * w * g⁻¹) * (g * x * g⁻¹) := by group

private theorem c23a_mul_comm_conj {t y g : G}
    (h : (g * t * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * t * g⁻¹)) :
    t * y = y * t := by
  have h' : g * (t * y) * g⁻¹ = g * (y * t) * g⁻¹ := by
    calc g * (t * y) * g⁻¹ = (g * t * g⁻¹) * (g * y * g⁻¹) := by group
      _ = (g * y * g⁻¹) * (g * t * g⁻¹) := h
      _ = g * (y * t) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h')

private theorem c23a_mQuot_conj {M V W W' : Subgroup G} (g : G)
    (hrank : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
      (∀ e ∈ E, e ∈ normalizer (W : Set G)) → (∀ e ∈ E, ∀ y ∈ W', e * y = y * e) →
        E3.mQuot E (Subgroup.centralizer (V : Set G)) ≤ 2)
    (E : Subgroup G) (hE : E ≤ conjSubgroup M g) (hEab : IsElemAbelian 2 E)
    (hEnorm : ∀ e ∈ E, e ∈ normalizer ((conjSubgroup W g) : Set G))
    (hEcent : ∀ e ∈ E, ∀ y ∈ conjSubgroup W' g, e * y = y * e) :
    E3.mQuot E (Subgroup.centralizer ((conjSubgroup V g) : Set G)) ≤ 2 := by
  have hE₀le : conjSubgroup E g⁻¹ ≤ M := by
    have h := E3.conjSubgroup_mono_left g⁻¹ hE
    rwa [E3.conjSubgroup_conj_inv M g] at h
  have hE₀ab : IsElemAbelian 2 (conjSubgroup E g⁻¹) :=
    E3.isElemAbelian_conjSubgroup hEab g⁻¹
  have hE₀norm : ∀ e ∈ conjSubgroup E g⁻¹, e ∈ normalizer (W : Set G) := by
    have h := E3.conjSubgroup_mono_left g⁻¹ hEnorm
    rw [E3.conjSubgroup_normalizer (conjSubgroup W g) g⁻¹,
      E3.conjSubgroup_conj_inv W g] at h
    exact h
  have hE₀cent : ∀ e ∈ conjSubgroup E g⁻¹, ∀ y ∈ W', e * y = y * e := by
    intro e he y hy
    have he1 : g⁻¹ * e * g ∈ E := by simpa using mem_conjSubgroup_iff.1 he
    have hy1 : g⁻¹ * y * g ∈ conjSubgroup W' g := by
      rw [mem_conjSubgroup_iff]
      have h : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [h]
    have h1 := hEcent (g⁻¹ * e * g) he1 (g⁻¹ * y * g) hy1
    have h2 : g⁻¹ * (e * y) * g = g⁻¹ * (y * e) * g := by
      calc g⁻¹ * (e * y) * g = (g⁻¹ * e * g) * (g⁻¹ * y * g) := by group
        _ = (g⁻¹ * y * g) * (g⁻¹ * e * g) := h1
        _ = g⁻¹ * (y * e) * g := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hres := hrank (conjSubgroup E g⁻¹) hE₀le hE₀ab hE₀norm hE₀cent
  have hq : E3.mQuot E (Subgroup.centralizer ((conjSubgroup V g) : Set G)) =
      E3.mQuot (conjSubgroup E g⁻¹) (Subgroup.centralizer (V : Set G)) := by
    have h := E3.mQuot_conjSubgroup (conjSubgroup E g⁻¹)
      (Subgroup.centralizer (V : Set G)) g
    rwa [E3.conjSubgroup_inv_conj E g, E3.conjSubgroup_centralizer V g] at h
  rwa [hq]

theorem c23a_pair_conj {M V W W' : Subgroup G} (g : G) (h : C23APair M V W W') :
    C23APair (conjSubgroup M g) (conjSubgroup V g) (conjSubgroup W g) (conjSubgroup W' g) := by
  refine
    { elem := E3.isElemAbelian_conjSubgroup h.elem g
      norm := ?_
      le := E3.conjSubgroup_mono_left g h.le
      le' := E3.conjSubgroup_mono_left g h.le'
      sup := ?_
      three := by rw [c23a_mSub_conjSubgroup W g]; exact h.three
      three' := by rw [c23a_mSub_conjSubgroup W' g]; exact h.three'
      perm := ?_
      cent := ?_
      oneSided := ?_
      rankLe := ?_
      rankLe' := ?_ }
  · rw [← E3.conjSubgroup_normalizer V g]
    exact E3.conjSubgroup_mono_left g h.norm
  · rw [← h.sup]
    exact (Subgroup.map_sup W W' (MulAut.conj g⁻¹).toMonoidHom).symm
  · rintro m' hm'
    have hm : g * m' * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 hm'
    have eW : conjSubgroup (conjSubgroup W g) m' =
        conjSubgroup (conjSubgroup W (g * m' * g⁻¹)) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    have eW' : conjSubgroup (conjSubgroup W' g) m' =
        conjSubgroup (conjSubgroup W' (g * m' * g⁻¹)) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    obtain ⟨hw, hw'⟩ | ⟨hw, hw'⟩ := h.perm (g * m' * g⁻¹) hm
    · left
      exact ⟨by rw [eW, hw], by rw [eW', hw']⟩
    · right
      exact ⟨by rw [eW, hw], by rw [eW', hw']⟩
  · rintro w hw hw1
    have hw₀ : g * w * g⁻¹ ∈ (W : Set G) ∪ (W' : Set G) := by
      rcases hw with hw | hw
      · exact Or.inl (mem_conjSubgroup_iff.1 hw)
      · exact Or.inr (mem_conjSubgroup_iff.1 hw)
    have hw₀1 : g * w * g⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      have h2 : g * w * g⁻¹ = g * 1 * g⁻¹ := by simpa using h1
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← c23a_centralizer_singleton_conj w g]
    exact E3.conjSubgroup_mono_left g (h.cent (g * w * g⁻¹) hw₀ hw₀1)
  · rintro t ht ht2 htV htm
    have ht₀ : g * t * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 ht
    have ht₀2 : ∃ j : ℕ, orderOf (g * t * g⁻¹) = 2 ^ j := by
      obtain ⟨j, hj⟩ := ht2
      exact ⟨j, by rw [show orderOf (g * t * g⁻¹) = orderOf t by
        simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq t, hj]⟩
    have ht₀V : ¬ V ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
      intro hV
      apply htV
      have h1 : conjSubgroup V g ≤
          conjSubgroup (Subgroup.centralizer ({g * t * g⁻¹} : Set G)) g :=
        E3.conjSubgroup_mono_left g hV
      rwa [c23a_centralizer_singleton_conj t g] at h1
    have ht₀m : mSub (commElt V (g * t * g⁻¹)) ≤ 2 := by
      have h1 := htm
      rwa [c23a_commElt_conj V t g,
        c23a_mSub_conjSubgroup (commElt V (g * t * g⁻¹)) g] at h1
    obtain ⟨hconj, h2m⟩ := h.oneSided (g * t * g⁻¹) ht₀ ht₀2 ht₀V ht₀m
    refine ⟨?_, ?_⟩
    · rcases hconj with ⟨hy, hle⟩ | ⟨hy, hle⟩
      · left
        exact ⟨fun y hy' => c23a_mul_comm_conj (hy (g * y * g⁻¹)
            (mem_conjSubgroup_iff.1 hy')),
          by rw [c23a_commElt_conj V t g]; exact E3.conjSubgroup_mono_left g hle⟩
      · right
        exact ⟨fun y hy' => c23a_mul_comm_conj (hy (g * y * g⁻¹)
            (mem_conjSubgroup_iff.1 hy')),
          by rw [c23a_commElt_conj V t g]; exact E3.conjSubgroup_mono_left g hle⟩
    · rwa [c23a_commElt_conj V t g,
        c23a_mSub_conjSubgroup (commElt V (g * t * g⁻¹)) g]
  · intro E hE hEab hEnorm hEcent
    exact c23a_mQuot_conj (M := M) (V := V) (W := W) (W' := W') g h.rankLe
      E hE hEab hEnorm hEcent
  · intro E hE hEab hEnorm hEcent
    exact c23a_mQuot_conj (M := M) (V := V) (W := W') (W' := W) g h.symm.rankLe
      E hE hEab hEnorm hEcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
