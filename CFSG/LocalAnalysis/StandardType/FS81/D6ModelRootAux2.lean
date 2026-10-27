module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelRootAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalGroups.Orthogonal CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.GF2n.Smith81 CFSG.SeitzReduction.OmegaPilot

private theorem inf_span_vecE_vecF_vecE_vecF {a b : Fin 6} (hab : a ≠ b) :
    Submodule.span (ZMod 2) {vecE a, vecF b} ⊓
      Submodule.span (ZMod 2) {vecE b, vecF a} = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp h2
  have h : α • vecE a + β • vecF b = γ • vecE b + δ • vecF a := hαβ.trans hγδ.symm
  have hα : α = 0 := by
    have hc := congrArg (fun w : V12 => w (Sum.inl a)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hab] using hc
  have hβ : β = 0 := by
    have hc := congrArg (fun w : V12 => w (Sum.inr b)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hab] using hc
  rw [Submodule.mem_bot, ← hαβ, hα, hβ]
  simp

private theorem inf_span_vecE_vecF_sum {a b : Fin 6} (hab : a ≠ b) :
    Submodule.span (ZMod 2) {vecE a, vecF b} ⊓
      Submodule.span (ZMod 2) {vecE a + vecE b, vecF a + vecF b} = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp h2
  have h : α • vecE a + β • vecF b = γ • (vecE a + vecE b) + δ • (vecF a + vecF b) :=
    hαβ.trans hγδ.symm
  have hγ : γ = 0 := by
    have hc := congrArg (fun w : V12 => w (Sum.inl b)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hab] using hc.symm
  have hδ : δ = 0 := by
    have hc := congrArg (fun w : V12 => w (Sum.inr a)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hab] using hc.symm
  rw [Submodule.mem_bot, ← hαβ]
  simpa [hγ, hδ] using h

private theorem inf_span_vecE_vecF_sum' {a b : Fin 6} (hab : a ≠ b) :
    Submodule.span (ZMod 2) {vecE b, vecF a} ⊓
      Submodule.span (ZMod 2) {vecE a + vecE b, vecF a + vecF b} = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp h2
  have h : α • vecE b + β • vecF a = γ • (vecE a + vecE b) + δ • (vecF a + vecF b) :=
    hαβ.trans hγδ.symm
  have hγ : γ = 0 := by
    have hc := congrArg (fun w : V12 => w (Sum.inl a)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hab] using hc.symm
  have hδ : δ = 0 := by
    have hc := congrArg (fun w : V12 => w (Sum.inr b)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hab] using hc.symm
  rw [Submodule.mem_bot, ← hαβ]
  simpa [hγ, hδ] using h

private theorem eq_sum_of_mem_planeSpan {a b : Fin 6} (hab : a ≠ b) {v : V12}
    (hv : v ∈ planeSpan ({a, b} : Finset (Fin 6))) :
    v = v (Sum.inl a) • vecE a + v (Sum.inl b) • vecE b + v (Sum.inr a) • vecF a +
      v (Sum.inr b) • vecF b := by
  ext i
  rcases i with i | i
  · by_cases hia : i = a
    · subst i
      simp [vecE, vecF, Pi.single_apply, Ne.symm hab]
    · by_cases hib : i = b
      · subst i
        simp [vecE, vecF, Pi.single_apply, hia]
      · have hi : i ∉ ({a, b} : Finset (Fin 6)) := by simp [hia, hib]
        have hz := (mem_planeSpan.mp hv i hi).1
        simp [vecE, vecF, Pi.single_apply, hia, hib, hz]
  · by_cases hia : i = a
    · subst i
      simp [vecE, vecF, Pi.single_apply, Ne.symm hab]
    · by_cases hib : i = b
      · subst i
        simp [vecE, vecF, Pi.single_apply, hia]
      · have hi : i ∉ ({a, b} : Finset (Fin 6)) := by simp [hia, hib]
        have hz := (mem_planeSpan.mp hv i hi).2
        simp [vecE, vecF, Pi.single_apply, hia, hib, hz]

theorem subCommSpace_rootL_empty {a b : Fin 6} (hab : a ≠ b) :
    subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) = planeSpan {a, b} := by
  let P : Submodule (ZMod 2) V12 := planeSpan ({a, b} : Finset (Fin 6))
  have heaP : vecE a ∈ P := by
    change vecE a ∈ planeSpan ({a, b} : Finset (Fin 6))
    rw [mem_planeSpan]
    intro i hi
    have hia : i ≠ a := fun h => hi (by simp [h])
    simp [vecE, Pi.single_apply, hia]
  have hfbP : vecF b ∈ P := by
    change vecF b ∈ planeSpan ({a, b} : Finset (Fin 6))
    rw [mem_planeSpan]
    intro i hi
    have hib : i ≠ b := fun h => hi (by simp [h])
    simp [vecF, Pi.single_apply, hib]
  have hebP : vecE b ∈ P := by
    change vecE b ∈ planeSpan ({a, b} : Finset (Fin 6))
    rw [mem_planeSpan]
    intro i hi
    have hib : i ≠ b := fun h => hi (by simp [h])
    simp [vecE, Pi.single_apply, hib]
  have hfaP : vecF a ∈ P := by
    change vecF a ∈ planeSpan ({a, b} : Finset (Fin 6))
    rw [mem_planeSpan]
    intro i hi
    have hia : i ≠ a := fun h => hi (by simp [h])
    simp [vecF, Pi.single_apply, hia]
  have hxfix : ∀ v : V12, lin (genGL hab ∅) v - v ∈ P := by
    intro v
    rw [lin_genGL_empty_apply hab]
    rw [show v + v (Sum.inl b) • vecE a + v (Sum.inr a) • vecF b - v =
      v (Sum.inl b) • vecE a + v (Sum.inr a) • vecF b by abel]
    exact P.add_mem (P.smul_mem _ heaP) (P.smul_mem _ hfbP)
  have hyfix : ∀ v : V12, lin (genGL hab.symm ∅) v - v ∈ P := by
    intro v
    rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm]
    rw [show v + v (Sum.inl a) • vecE b + v (Sum.inr b) • vecF a - v =
      v (Sum.inl a) • vecE b + v (Sum.inr b) • vecF a by abel]
    exact P.add_mem (P.smul_mem _ hebP) (P.smul_mem _ hfaP)
  let H : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
    { carrier := {z | ∀ v, z v - v ∈ P}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro z w hz hw v
        have h1 := hz (w v)
        have h2 := hw v
        rw [show (z * w) v - v = (z (w v) - w v) + (w v - v) by
          rw [LinearEquiv.mul_apply]; abel]
        exact P.add_mem h1 h2
      inv_mem' := by
        intro z hz v
        have h1 := hz (z⁻¹ v)
        rw [LinearEquiv.apply_inv_apply'] at h1
        rw [show z⁻¹ v - v = -(v - z⁻¹ v) by abel]
        exact P.neg_mem h1 }
  have hsub : rootL ({a, b} : Finset (Fin 6)) ∅ ≤ H := by
    rw [rootL_eq_closure hab ∅]
    refine (Subgroup.closure_le H).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change ∀ v, lin (genGL hab ∅) v - v ∈ P
      exact hxfix
    · change ∀ v, lin (genGL hab.symm ∅) v - v ∈ P
      exact hyfix
  apply le_antisymm
  · rw [subCommSpace]
    refine iSup_le fun z => iSup_le fun hz => ?_
    intro w hw
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
    exact hsub hz v
  · intro v hv
    rw [eq_sum_of_mem_planeSpan hab hv]
    have hxroot : lin (genGL hab ∅) ∈ rootL ({a, b} : Finset (Fin 6)) ∅ := by
      rw [rootL_eq_closure hab ∅]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have hyroot : lin (genGL hab.symm ∅) ∈ rootL ({a, b} : Finset (Fin 6)) ∅ := by
      rw [rootL_eq_closure hab ∅]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hxle : commSpace (lin (genGL hab ∅)) ≤
        subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) :=
      le_iSup₂_of_le (lin (genGL hab ∅)) hxroot le_rfl
    have hyle : commSpace (lin (genGL hab.symm ∅)) ≤
        subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) :=
      le_iSup₂_of_le (lin (genGL hab.symm ∅)) hyroot le_rfl
    have hea : vecE a ∈ subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) :=
      hxle (by rw [(isOrthA2_genGL_empty hab).2]; exact Submodule.subset_span (by simp))
    have hfb : vecF b ∈ subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) :=
      hxle (by rw [(isOrthA2_genGL_empty hab).2]; exact Submodule.subset_span (by simp))
    have heb : vecE b ∈ subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) :=
      hyle (by rw [(isOrthA2_genGL_symm_empty hab).2]; exact Submodule.subset_span (by simp))
    have hfa : vecF a ∈ subCommSpace (rootL ({a, b} : Finset (Fin 6)) ∅) :=
      hyle (by rw [(isOrthA2_genGL_symm_empty hab).2]; exact Submodule.subset_span (by simp))
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hea) (Submodule.smul_mem _ _ heb))
      (Submodule.smul_mem _ _ hfa)) (Submodule.smul_mem _ _ hfb)

theorem isRootS3Like_rootL_empty {a b : Fin 6} (hab : a ≠ b) :
    IsRootS3Like Q12 (rootL ({a, b} : Finset (Fin 6)) ∅) := by
  refine ⟨?_, ?_⟩
  · intro s hs hss hs1
    rcases eq_of_sixWord_involution hab hs hss hs1 with rfl | rfl | rfl
    · exact isTypeA_genGL_empty hab
    · exact isTypeA_genGL_symm_empty hab
    · exact isTypeA_genGL_empty_conj hab
  · intro s hs s' hs' hss hs's hs1 hs'1 hne
    rcases eq_of_sixWord_involution hab hs hss hs1 with rfl | rfl | rfl <;>
      rcases eq_of_sixWord_involution hab hs' hs's hs'1 with rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [(isOrthA2_genGL_empty hab).2, (isOrthA2_genGL_symm_empty hab).2]
      exact inf_span_vecE_vecF_vecE_vecF hab
    · rw [(isOrthA2_genGL_empty hab).2, (isOrthA2_genGL_empty_conj hab).2]
      exact inf_span_vecE_vecF_sum hab
    · rw [inf_comm, (isOrthA2_genGL_empty hab).2, (isOrthA2_genGL_symm_empty hab).2]
      exact inf_span_vecE_vecF_vecE_vecF hab
    · exact absurd rfl hne
    · rw [(isOrthA2_genGL_symm_empty hab).2, (isOrthA2_genGL_empty_conj hab).2]
      exact inf_span_vecE_vecF_sum' hab
    · rw [inf_comm, (isOrthA2_genGL_empty hab).2, (isOrthA2_genGL_empty_conj hab).2]
      exact inf_span_vecE_vecF_sum hab
    · rw [inf_comm, (isOrthA2_genGL_symm_empty hab).2,
        (isOrthA2_genGL_empty_conj hab).2]
      exact inf_span_vecE_vecF_sum' hab
    · exact absurd rfl hne

theorem rootL_apply_eq_self_empty {a b : Fin 6} (hab : a ≠ b) {v : V12}
    (hv : v ∈ planeSpan ({a, b} : Finset (Fin 6))ᶜ) :
    ∀ z ∈ rootL ({a, b} : Finset (Fin 6)) ∅, z v = v := by
  have hb : v (Sum.inl b) = 0 := (mem_planeSpan.mp hv b (by simp)).1
  have ha : v (Sum.inr a) = 0 := (mem_planeSpan.mp hv a (by simp)).2
  have ha' : v (Sum.inl a) = 0 := (mem_planeSpan.mp hv a (by simp)).1
  have hb' : v (Sum.inr b) = 0 := (mem_planeSpan.mp hv b (by simp)).2
  let H : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
    { carrier := {z | z v = v}
      one_mem' := rfl
      mul_mem' := by
        intro z w hz hw
        change (z * w) v = v
        rw [LinearEquiv.mul_apply, hw, hz]
      inv_mem' := by
        intro z hz
        change z⁻¹ v = v
        calc z⁻¹ v = z⁻¹ (z v) := by rw [hz]
          _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id] }
  have hx : lin (genGL hab ∅) ∈ H := by
    change lin (genGL hab ∅) v = v
    rw [lin_genGL_empty_apply hab, hb, ha]
    simp
  have hy : lin (genGL hab.symm ∅) ∈ H := by
    change lin (genGL hab.symm ∅) v = v
    rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm, ha', hb']
    simp
  have hsub : rootL ({a, b} : Finset (Fin 6)) ∅ ≤ H := by
    rw [rootL_eq_closure hab ∅]
    refine (Subgroup.closure_le H).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  intro z hz
  exact hsub hz

theorem rootL_apply_mem_empty {a b : Fin 6} (hab : a ≠ b) {S : Finset (Fin 6)}
    (hS : ({a, b} : Finset (Fin 6)) ⊆ S) :
    ∀ z ∈ rootL ({a, b} : Finset (Fin 6)) ∅, ∀ v ∈ planeSpan S, z v ∈ planeSpan S := by
  let P : Submodule (ZMod 2) V12 := planeSpan S
  have haS : a ∈ S := hS (by simp)
  have hbS : b ∈ S := hS (by simp)
  have memE : ∀ i ∈ S, vecE i ∈ P := by
    intro i hi
    change vecE i ∈ planeSpan S
    rw [mem_planeSpan]
    intro j hj
    have hji : j ≠ i := fun h => hj (by simpa [h] using hi)
    simp [vecE, Pi.single_apply, hji]
  have memF : ∀ i ∈ S, vecF i ∈ P := by
    intro i hi
    change vecF i ∈ planeSpan S
    rw [mem_planeSpan]
    intro j hj
    have hji : j ≠ i := fun h => hj (by simpa [h] using hi)
    simp [vecF, Pi.single_apply, hji]
  have hea : vecE a ∈ P := memE a haS
  have hfb : vecF b ∈ P := memF b hbS
  have heb : vecE b ∈ P := memE b hbS
  have hfa : vecF a ∈ P := memF a haS
  have hxinv : (lin (genGL hab ∅))⁻¹ = lin (genGL hab ∅) :=
    inv_eq_of_mul_eq_one_right (lin_genGL_empty_sq hab)
  have hyinv : (lin (genGL hab.symm ∅))⁻¹ = lin (genGL hab.symm ∅) :=
    inv_eq_of_mul_eq_one_right (lin_genGL_symm_empty_sq hab)
  let H : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
    { carrier := {z | (∀ v ∈ P, z v ∈ P) ∧ (∀ v ∈ P, z⁻¹ v ∈ P)}
      one_mem' := by
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;> simpa using hv
      mul_mem' := by
        intro z w hz hw
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · change (z * w) v ∈ P
          rw [LinearEquiv.mul_apply]
          exact hz.1 (w v) (hw.1 v hv)
        · change (z * w)⁻¹ v ∈ P
          rw [mul_inv_rev, LinearEquiv.mul_apply]
          exact hw.2 (z⁻¹ v) (hz.2 v hv)
      inv_mem' := by
        intro z hz
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · change z⁻¹ v ∈ P
          exact hz.2 v hv
        · change (z⁻¹)⁻¹ v ∈ P
          rw [inv_inv]
          exact hz.1 v hv }
  have hxP : lin (genGL hab ∅) ∈ H := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · change lin (genGL hab ∅) v ∈ P
      rw [lin_genGL_empty_apply hab]
      exact P.add_mem (P.add_mem hv (P.smul_mem _ hea)) (P.smul_mem _ hfb)
    · rw [hxinv]
      change lin (genGL hab ∅) v ∈ P
      rw [lin_genGL_empty_apply hab]
      exact P.add_mem (P.add_mem hv (P.smul_mem _ hea)) (P.smul_mem _ hfb)
  have hyP : lin (genGL hab.symm ∅) ∈ H := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · change lin (genGL hab.symm ∅) v ∈ P
      rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm]
      exact P.add_mem (P.add_mem hv (P.smul_mem _ heb)) (P.smul_mem _ hfa)
    · rw [hyinv]
      change lin (genGL hab.symm ∅) v ∈ P
      rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm]
      exact P.add_mem (P.add_mem hv (P.smul_mem _ heb)) (P.smul_mem _ hfa)
  have hsub : rootL ({a, b} : Finset (Fin 6)) ∅ ≤ H := by
    rw [rootL_eq_closure hab ∅]
    refine (Subgroup.closure_le H).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxP
    · exact hyP
  intro z hz v hv
  exact (hsub hz).1 v hv

end CFSG.StandardType.FrameRoute.FS81.D6M
