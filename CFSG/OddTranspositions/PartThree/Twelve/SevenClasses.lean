module

public import CFSG.OddTranspositions.PartThree.Twelve.SevenForm
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartThree.Nine.Setup

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.Open

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem perpMem_inter_perpMem_eq {d w : G} (hwd : ¬ Commute w d) :
    perpMem D d ∩ perpMem D w = commSet D d ∩ commSet D w := by
  ext x
  constructor
  · rintro ⟨⟨hx, hxd⟩, -, hxw⟩
    refine ⟨⟨hx, hxd, ?_⟩, hx, hxw, ?_⟩
    · rintro rfl
      exact hwd hxw.symm
    · rintro rfl
      exact hwd hxd
  · rintro ⟨⟨hx, hxd, -⟩, -, hxw, -⟩
    exact ⟨⟨hx, hxd⟩, hx, hxw⟩

omit [Finite G] in
theorem lineMem_eq_of_commSet_inter_eq {d w w' : G} (hwd : ¬ Commute w d)
    (hwd' : ¬ Commute w' d) (h : commSet D d ∩ commSet D w = commSet D d ∩ commSet D w') :
    lineMem D d w = lineMem D d w' := by
  ext x
  rw [mem_lineMem, mem_lineMem, perpMem_inter_perpMem_eq hwd, perpMem_inter_perpMem_eq hwd', h]

omit [Finite G] in
theorem lineMem_eq_of_commSet_inter_eq_empty {d w : G} (hwd : ¬ Commute w d)
    (h : commSet D d ∩ commSet D w = ∅) : lineMem D d w = D := by
  ext x
  rw [mem_lineMem, perpMem_inter_perpMem_eq hwd, h]
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, Set.empty_subset _⟩⟩

theorem exists_statedSp_of_isPlusType_iff {k : ℕ} {F : Type} [Field F] [Finite F]
    {Q Q' : QuadraticForm F (Fin k ⊕ Fin k → F)} (hQ : ∀ a b, polar Q a b = spForm k F a b)
    (hQ' : ∀ a b, polar Q' a b = spForm k F a b) (h : IsPlusType Q ↔ IsPlusType Q') :
    ∃ g : StatedSp k F, ∀ v, Q' (spEnd g v) = Q v := by
  have hb : ∀ {P : QuadraticForm F (Fin k ⊕ Fin k → F)},
      (∀ a b, polar P a b = spForm k F a b) → (polarBilin P).Nondegenerate := by
    intro P hP
    have : polarBilin P = spForm k F := LinearMap.ext₂ fun a b => by
      rw [polarBilin_apply_apply, hP]
    rw [this]
    exact spForm_nondegenerate
  have hdim : finrank F (Fin k ⊕ Fin k → F) = 2 * k := by simp [two_mul]
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (hb hQ) (hb hQ') hdim hdim h
  have he : ∀ v, Q' (e v) = Q v := e.map_app
  have hpol : ∀ u v, spForm k F (e u) (e v) = spForm k F u v := by
    intro u v
    rw [← hQ' (e u) (e v), ← hQ u v, polar, polar, ← map_add, he, he, he]
  set g₀ := (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k ⊕ Fin k → F)).symm
    e.toLinearEquiv with hg₀
  have hg₀v : ∀ v, (g₀ : Module.End F (Fin k ⊕ Fin k → F)) v = e v := fun v => rfl
  have hmem : g₀ ∈ (spLin k F).range := by
    rw [range_spLin, CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
    intro u v
    rw [hg₀v, hg₀v]
    exact hpol u v
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, fun v => ?_⟩
  have : spEnd g v = e v := by
    change ((spLin k F g : LinearMap.GeneralLinearGroup F (Fin k ⊕ Fin k → F)) :
      Module.End F (Fin k ⊕ Fin k → F)) v = e v
    rw [hg, hg₀v]
  rw [this, he]

omit [Finite G] in
theorem exists_conj_lineMem_of_isPlusType_iff (hC : HypothesisC D) {hα : hC.alpha = {hC.d}}
    {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (c : SpChart hC hα k F) {w w' : G}
    (hwd : ¬ Commute w hC.d) (hwd' : ¬ Commute w' hC.d)
    {Q Q' : QuadraticForm F (Fin k ⊕ Fin k → F)} (hQ : ∀ a b, polar Q a b = spForm k F a b)
    (hQ' : ∀ a b, polar Q' a b = spForm k F a b)
    (hQw : ∀ z ∈ commSet D hC.d, (z ∈ commSet D w ↔ Q (c.vec z) = 1))
    (hQw' : ∀ z ∈ commSet D hC.d, (z ∈ commSet D w' ↔ Q' (c.vec z) = 1))
    (h : IsPlusType Q ↔ IsPlusType Q') :
    ∃ x : Halpha D hC.alpha, MulAut.conj (x : G) '' lineMem D hC.d w = lineMem D hC.d w' := by
  obtain ⟨g, hg⟩ := exists_statedSp_of_isPlusType_iff hQ hQ' h
  obtain ⟨x, hx⟩ := c.surjective g
  refine ⟨x, ?_⟩
  set φ := MulAut.conj (x : G) with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem _ h⟩
    have := hC.setup.conj_mem (x : G)⁻¹ h
    simpa [mul_assoc] using this
  have hxd : φ hC.d = hC.d := by
    rw [MulAut.conj_apply, (commute_d_of_mem_Halpha hC hα x).eq, mul_inv_cancel_right]
  have hyd : ¬ Commute (φ w) hC.d := fun h' => hwd (by
    rw [← hxd] at h'
    exact (commute_map_iff φ).mp h')
  have hset : commSet D hC.d ∩ commSet D (φ w) = commSet D hC.d ∩ commSet D w' := by
    ext z
    constructor
    · rintro ⟨hzd, hzy⟩
      refine ⟨hzd, (hQw' z hzd).mpr ?_⟩
      obtain ⟨hm, hv⟩ := c.vec_conj x⁻¹ hzd
      have h1 : ((x⁻¹ : Halpha D hC.alpha) : G) * z * ((x⁻¹ : Halpha D hC.alpha) : G)⁻¹ =
          φ.symm z := by
        simp [hφdef, MulAut.conj_symm_apply]
      rw [h1] at hm hv
      have hzw : φ.symm z ∈ commSet D w := by
        rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply]
        exact hzy
      have h2 := (hQw _ hm).mp hzw
      rw [hv, map_inv, hx, ← hg, spEnd_spEnd_inv_apply] at h2
      exact h2
    · rintro ⟨hzd, hzw'⟩
      refine ⟨hzd, ?_⟩
      have h0 := (hQw' z hzd).mp hzw'
      obtain ⟨hm, hv⟩ := c.vec_conj x⁻¹ hzd
      have h1 : ((x⁻¹ : Halpha D hC.alpha) : G) * z * ((x⁻¹ : Halpha D hC.alpha) : G)⁻¹ =
          φ.symm z := by
        simp [hφdef, MulAut.conj_symm_apply]
      rw [h1] at hm hv
      have h2 : Q (c.vec (φ.symm z)) = 1 := by
        rw [hv, map_inv, hx, ← hg, spEnd_spEnd_inv_apply]
        exact h0
      have h3 := (hQw _ hm).mpr h2
      rw [← MulEquiv.apply_symm_apply φ z, mem_commSet_map_iff φ hφD]
      exact h3
  have hline : lineMem D (φ hC.d) (φ w) = φ '' lineMem D hC.d w :=
    lineMem_conj (fun g z hz => hC.setup.conj_mem g hz) (x : G) hC.d w
  rw [← hline, hxd]
  exact lineMem_eq_of_commSet_inter_eq hyd hwd' hset

omit [Finite G] in
theorem SpChart.le_ncard {hC : HypothesisC D} {hα : hC.alpha = {hC.d}} {k : ℕ} {F : Type}
    [Field F] [Finite F] [Finite G] (c : SpChart hC hα k F) :
    Nat.card F ^ (2 * k) - 1 ≤ (commSet D hC.d).ncard := by
  classical
  have hsub : {v : Fin k ⊕ Fin k → F | v ≠ 0} ⊆ c.vec '' commSet D hC.d := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := c.exists_vec v hv
    exact ⟨z, hz, rfl⟩
  have h0 : {v : Fin k ⊕ Fin k → F | v ≠ 0} = Set.univ \ {0} := by
    ext v
    simp
  calc Nat.card F ^ (2 * k) - 1 = {v : Fin k ⊕ Fin k → F | v ≠ 0}.ncard := by
        rw [h0, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, natCard_vec]
    _ ≤ (c.vec '' commSet D hC.d).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (commSet D hC.d).ncard := Set.ncard_image_le (Set.toFinite _)

theorem twelveSeven_sp (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) :
    (∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty →
      (lineMem D hC.d w).ncard = 2 ^ f + 1 ∨ (lineMem D hC.d w).ncard = 2 ^ f - 1) ∧
    (∀ w ∈ D, ∀ w' ∈ D, ¬ Commute w hC.d → ¬ Commute w' hC.d →
      (commSet D hC.d ∩ commSet D w).Nonempty → (commSet D hC.d ∩ commSet D w').Nonempty →
      (lineMem D hC.d w).ncard = (lineMem D hC.d w').ncard →
      ∃ x : Halpha D hC.alpha, MulAut.conj (x : G) '' lineMem D hC.d w = lineMem D hC.d w') ∧
    (∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = 2 ^ f + 1) ∧
    (∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = 2 ^ f - 1) := by
  classical
  obtain ⟨k, F, _, _, _, hnk, hF, ⟨c⟩⟩ := exists_spChart hC hMZ hα hs hSp
  obtain ⟨⟨w₁, hw₁, hw₁d, hl₁⟩, ⟨w₂, hw₂, hw₂d, hl₂⟩⟩ :=
    twelveSeven_sp_exists hIH hC hMZ hα hs hn hf hSp
  have hform : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty →
      ∃ Q : QuadraticForm F (Fin k ⊕ Fin k → F), (∀ a b, polar Q a b = spForm k F a b) ∧
        ∀ z ∈ commSet D hC.d, (z ∈ commSet D w ↔ Q (c.vec z) = 1) := by
    rintro w hw hwd ⟨v, hvd, hvw⟩
    obtain ⟨Q, hQ, hQw, -⟩ := exists_quadraticForm_commSet_inter hIH hC hMZ hα hs hn hf hSp c hnk
      hF hvd hw hwd hvw.2.1.symm
    exact ⟨Q, hQ, hQw⟩
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hbig : 2 ^ f + 1 < D.ncard := by
    have h1 := c.le_ncard
    have h2 : (commSet D hC.d).ncard ≤ D.ncard :=
      Set.ncard_le_ncard (fun z hz => hz.1) (Set.toFinite _)
    have h3 : (2 ^ f) ^ 2 ≤ (2 ^ f) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hF] at h1
    have h4 : 4 * 2 ^ f ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hq
    rw [pow_two] at h3
    generalize (2 ^ f) ^ (2 * k) = A at h1 h3
    generalize 2 ^ f * 2 ^ f = B at h3 h4
    omega
  have hne : ∀ w ∈ D, ¬ Commute w hC.d → (lineMem D hC.d w).ncard ≤ 2 ^ f + 1 →
      (commSet D hC.d ∩ commSet D w).Nonempty := by
    intro w hw hwd hl
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    rw [lineMem_eq_of_commSet_inter_eq_empty hwd h0] at hl
    omega
  have hn₁ := hne w₁ hw₁ hw₁d hl₁.le
  have hn₂ := hne w₂ hw₂ hw₂d (by omega)
  obtain ⟨Q₁, hQ₁, hQw₁⟩ := hform w₁ hw₁ hw₁d hn₁
  obtain ⟨Q₂, hQ₂, hQw₂⟩ := hform w₂ hw₂ hw₂d hn₂
  have hncard : ∀ (x : Halpha D hC.alpha) (S : Set G),
      (MulAut.conj (x : G) '' S).ncard = S.ncard :=
    fun x S => Set.ncard_image_of_injective _ (MulAut.conj (x : G)).injective
  have hdiff : ¬ (IsPlusType Q₁ ↔ IsPlusType Q₂) := by
    intro h
    obtain ⟨x, hx⟩ := exists_conj_lineMem_of_isPlusType_iff hC c hw₁d hw₂d hQ₁ hQ₂ hQw₁
      hQw₂ h
    have := hncard x (lineMem D hC.d w₁)
    rw [hx, hl₂, hl₁] at this
    omega
  have hsize : ∀ w ∈ D, ¬ Commute w hC.d → ∀ Q : QuadraticForm F (Fin k ⊕ Fin k → F),
      (∀ a b, polar Q a b = spForm k F a b) →
      (∀ z ∈ commSet D hC.d, (z ∈ commSet D w ↔ Q (c.vec z) = 1)) →
      ((IsPlusType Q ↔ IsPlusType Q₁) ∧ (lineMem D hC.d w).ncard = 2 ^ f + 1) ∨
        ((IsPlusType Q ↔ IsPlusType Q₂) ∧ (lineMem D hC.d w).ncard = 2 ^ f - 1) := by
    intro w hw hwd Q hQ hQw
    by_cases h : IsPlusType Q ↔ IsPlusType Q₁
    · obtain ⟨x, hx⟩ := exists_conj_lineMem_of_isPlusType_iff hC c hwd hw₁d hQ hQ₁ hQw hQw₁ h
      left
      refine ⟨h, ?_⟩
      rw [← hl₁, ← hx, hncard]
    · have h' : IsPlusType Q ↔ IsPlusType Q₂ := by tauto
      obtain ⟨x, hx⟩ := exists_conj_lineMem_of_isPlusType_iff hC c hwd hw₂d hQ hQ₂ hQw hQw₂ h'
      right
      refine ⟨h', ?_⟩
      rw [← hl₂, ← hx, hncard]
  refine ⟨fun w hw hwd hΓ => ?_, fun w hw w' hw' hwd hwd' hΓ hΓ' heq => ?_,
    ⟨w₁, hw₁, hw₁d, hl₁⟩, ⟨w₂, hw₂, hw₂d, hl₂⟩⟩
  · obtain ⟨Q, hQ, hQw⟩ := hform w hw hwd hΓ
    rcases hsize w hw hwd Q hQ hQw with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · obtain ⟨Q, hQ, hQw⟩ := hform w hw hwd hΓ
    obtain ⟨Q', hQ', hQw'⟩ := hform w' hw' hwd' hΓ'
    have htype : IsPlusType Q ↔ IsPlusType Q' := by
      rcases hsize w hw hwd Q hQ hQw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hsize w' hw' hwd' Q' hQ' hQw' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact h1.trans h3.symm
      · omega
      · omega
      · exact h1.trans h3.symm
    exact exists_conj_lineMem_of_isPlusType_iff hC c hwd hwd' hQ hQ' hQw hQw' htype

end CFSG.OddTranspositions.PartThree
