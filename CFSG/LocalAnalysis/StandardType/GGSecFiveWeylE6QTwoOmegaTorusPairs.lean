module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaTorusStep
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentRotation

public section

namespace CFSG.StandardType.E6QTwo

open Module QuadraticMap CFSG.Open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA
open CFSG.ClassicalGroups.Orthogonal (PolarNondegOn map_of_mem polar_map_of_mem
  polar_smul_left_eq polar_smul_right_eq)
open CFSG.AGLEmbedding.OmegaMinusCent (AnisoPair add_self_eq_zero' polar_self_zero
  zmod_two_cases finrank_inf_perp)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private lemma plane_eq_span (P : AnisoPair Q) :
    P.plane = Submodule.span (ZMod 2) {P.a, P.b} := by
  have hle : Submodule.span (ZMod 2) {P.a, P.b} ≤ P.plane := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact AnisoPair.a_mem_plane P
    · exact AnisoPair.b_mem_plane P
  have hfin : finrank (ZMod 2) (Submodule.span (ZMod 2) {P.a, P.b}) =
      finrank (ZMod 2) P.plane := by
    rw [AnisoPair.finrank_plane P, ← Matrix.range_cons_cons_empty P.a P.b ![],
      finrank_span_eq_card P.linearIndependent_pair, Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

private lemma orthogonal_plane_eq_perp (P : AnisoPair Q) :
    LinearMap.BilinForm.orthogonal (polarBilin Q) P.plane = P.perp := by
  rw [plane_eq_span P]
  ext u
  rw [LinearMap.BilinForm.mem_orthogonal_iff, AnisoPair.mem_perp P]
  constructor
  · intro h
    exact ⟨by
      have h1 := h P.a (Submodule.subset_span (by simp))
      rwa [QuadraticMap.polarBilin_apply_apply] at h1,
      by
      have h1 := h P.b (Submodule.subset_span (by simp))
      rwa [QuadraticMap.polarBilin_apply_apply] at h1⟩
  · rintro ⟨h1, h2⟩ x hx
    rw [Submodule.mem_span_pair] at hx
    obtain ⟨s, t, rfl⟩ := hx
    rw [QuadraticMap.polarBilin_apply_apply, polar_add_left, polar_smul_left_eq,
      polar_smul_left_eq, h1, h2]
    simp

theorem exists_anisoPair_plane_eq_of_isBlock {b : V ≃ₗ[ZMod 2] V}
    (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hb3 : b ^ 3 = 1)
    {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W) :
    ∃ P : AnisoPair Q, P.plane = W := by
  obtain ⟨hWnd, hW0, hbW, -, hfpf, hmin⟩ := hW
  have hex : ∃ a ∈ W, polar Q a (b a) ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ∀ v ∈ W, ∀ w ∈ W, polar Q v w = 0 := by
      intro v hv w hw
      have h1 : polar Q (v + w) (b (v + w)) = 0 := h (v + w) (W.add_mem hv hw)
      have h2 : polar Q (v + w) (b (v + w)) =
          polar Q v (b v) + polar Q v (b w) + polar Q w (b v) + polar Q w (b w) := by
        rw [map_add, polar_add_left, polar_add_right, polar_add_right]
        abel
      rw [h2] at h1
      have hv0 := h v hv
      have hw0 := h w hw
      rw [hv0, hw0, zero_add, add_zero] at h1
      have h4 : polar Q v (b w) = polar Q w (b v) := by
        have hneg : polar Q v (b w) = -(polar Q w (b v)) := eq_neg_of_add_eq_zero_left h1
        rw [hneg]
        exact neg_eq_of_add_eq_zero_right (add_self_eq_zero' _)
      have hb2 : (b ^ 2) v = v + b v := by
        have h := orbitSum_eq_zero hb3 hbW hfpf hv
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
          LinearEquiv.coe_one, id_eq] at h
        rw [← neg_eq_of_add_eq_zero_right (add_self_eq_zero' (v + b v))]
        exact eq_neg_of_add_eq_zero_right h
      have h5 : polar Q w (b v) = polar Q (b w) (b (b v)) :=
        (polar_map_of_mem hbO w (b v)).symm
      have h6 : polar Q (b w) (b (b v)) = polar Q (b w) ((b ^ 2) v) := by
        rw [pow_two, LinearEquiv.mul_apply]
      have h7 : polar Q (b w) ((b ^ 2) v) = polar Q (b w) (v + b v) := by rw [hb2]
      have h8 : polar Q (b w) (v + b v) = polar Q (b w) v + polar Q (b w) (b v) := by
        rw [polar_add_right]
      have h9 : polar Q (b w) (b v) = polar Q w v := polar_map_of_mem hbO w v
      have h10 : polar Q (b w) v = polar Q v (b w) := polar_comm ..
      have h11 : polar Q v (b w) = polar Q v (b w) + polar Q w v := by
        calc polar Q v (b w) = polar Q w (b v) := h4
          _ = polar Q (b w) (b (b v)) := h5
          _ = polar Q (b w) ((b ^ 2) v) := h6
          _ = polar Q (b w) (v + b v) := h7
          _ = polar Q (b w) v + polar Q (b w) (b v) := h8
          _ = polar Q (b w) v + polar Q w v := by rw [h9]
          _ = polar Q v (b w) + polar Q w v := by rw [h10]
      have h12 : polar Q w v = 0 := by
        have h := congrArg (fun x => polar Q v (b w) + x) h11.symm
        rw [add_self_eq_zero'] at h
        rw [← add_assoc, add_self_eq_zero', zero_add] at h
        exact h
      rw [polar_comm]
      exact h12
    have hWbot : W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      have h1 : ∀ u ∈ W, polar Q u w = 0 := by
        intro u hu
        rw [polar_comm]
        exact hzero w hw u hu
      exact (nondeg_iff.1 hWnd) w hw h1
    exact hW0 hWbot
  obtain ⟨a, haW, hpa⟩ := hex
  have hpa1 : polar Q a (b a) = 1 := (zmod_two_cases _).resolve_left hpa
  have hb2 : (b ^ 2) a = a + b a := by
    have h := orbitSum_eq_zero hb3 hbW hfpf haW
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq] at h
    rw [← neg_eq_of_add_eq_zero_right (add_self_eq_zero' (a + b a))]
    exact eq_neg_of_add_eq_zero_right h
  have hQba_eq : Q (b a) = Q a := map_of_mem hbO a
  have hQb2a_eq : Q ((b ^ 2) a) = Q a := map_of_mem (pow_mem hbO 2) a
  have hQsum : Q (a + b a) = Q a + Q (b a) + polar Q a (b a) :=
    QuadraticMap.map_add Q a (b a)
  have hQa : Q a = 1 := by
    have h1 : Q a = Q a + Q (b a) + 1 := by
      calc Q a = Q ((b ^ 2) a) := hQb2a_eq.symm
        _ = Q (a + b a) := by rw [hb2]
        _ = Q a + Q (b a) + polar Q a (b a) := hQsum
        _ = Q a + Q (b a) + 1 := by rw [hpa1]
    rw [hQba_eq] at h1
    rw [add_self_eq_zero', zero_add] at h1
    exact h1
  have hQba : Q (b a) = 1 := hQba_eq.trans hQa
  let P : AnisoPair Q := {
    a := a
    b := b a
    Q_a := hQa
    Q_b := hQba
    polar_ab := hpa1
  }
  have hbp : b (b a) = a + b a := by
    change (b ^ 2) a = a + b a
    exact hb2
  have hplane : P.plane = W := by
    rw [plane_eq_span P]
    refine hmin (Submodule.span (ZMod 2) {P.a, P.b}) ?_ ?_ ?_ ?_
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact haW
      · exact hbW _ haW
    · intro h
      have h1 : a ∈ Submodule.span (ZMod 2) {a, b a} :=
        Submodule.subset_span (by simp)
      rw [h, Submodule.mem_bot] at h1
      rw [h1] at hpa
      simp at hpa
    · rw [nondeg_iff]
      intro w hw hperp
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hw
      have h1 := hperp P.a (Submodule.subset_span (by left; rfl))
      have h2 := hperp P.b (Submodule.subset_span (by right; rfl))
      rw [QuadraticMap.polarBilin_apply_apply] at h1 h2
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        P.polar_aa, P.polar_ab] at h1
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        P.polar_ba, P.polar_bb] at h2
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at h1 h2
      rw [h1, h2, zero_smul, zero_smul, add_zero]
    · have hle2 : Submodule.span (ZMod 2) {a, b a} ≤
          (Submodule.span (ZMod 2) {a, b a}).comap b.toLinearMap := by
        rw [Submodule.span_le]
        rintro x (rfl | rfl)
        · exact Submodule.subset_span (by simp)
        · show b (b a) ∈ Submodule.span (ZMod 2) {a, b a}
          rw [hbp]
          exact Submodule.add_mem _ (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))
      intro w hw
      exact hle2 hw
  exact ⟨P, hplane⟩

private lemma no_anisoPair_of_maximal_bot (hQ : (polarBilin Q).Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : Nondeg (polarBilin Q) U)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEU : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) U))
    (hE : IsElemAbelian 3 E)
    (hmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ F →
      F ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) U) →
      IsElemAbelian 3 F → F = E) (hne : E = ⊥) :
    ∀ P : AnisoPair Q, P.a ∈ U → P.b ∈ U → False := by
  intro P ha hb
  have hYea : IsElemAbelian 3 (Subgroup.zpowers P.rot) :=
    CFSG.Open.isElemAbelian_zpowers (p := 3) P.rot_pow_three
  have hYU : Subgroup.zpowers P.rot ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨P.rot_mem, ?_⟩)
    rw [mem_ptw]
    intro x hx
    have ha' : polar Q P.a x = 0 := by
      have h := hx P.a ha
      rwa [QuadraticMap.polarBilin_apply_apply] at h
    have hb' : polar Q P.b x = 0 := by
      have h := hx P.b hb
      rwa [QuadraticMap.polarBilin_apply_apply] at h
    exact P.rot_apply_of_orth ha' hb'
  have hYbot : Subgroup.zpowers P.rot = ⊥ := by
    have h1 := hmax _ (by rw [hne]; exact bot_le) hYU hYea
    rw [hne] at h1
    exact h1
  have hrot1 : P.rot = 1 := by
    have h2 : P.rot ∈ Subgroup.zpowers P.rot := Subgroup.mem_zpowers P.rot
    rw [hYbot] at h2
    exact Subgroup.mem_bot.1 h2
  have h3 := P.rot_a_ne
  rw [hrot1] at h3
  exact h3 rfl

theorem exists_pairs_of_maximal (hQ : (polarBilin Q).Nondegenerate) :
    ∀ (n : ℕ) (U : Submodule (ZMod 2) V), finrank (ZMod 2) U = n →
      Nondeg (polarBilin Q) U → ∀ E : Subgroup (V ≃ₗ[ZMod 2] V),
      E ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) U) →
      IsElemAbelian 3 E →
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ F →
        F ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓
          ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) U) →
        IsElemAbelian 3 F → F = E) →
      ∃ Ps : List (AnisoPair Q), Ps.Pairwise AnisoPair.Orth ∧
        (∀ P ∈ Ps, P.a ∈ U ∧ P.b ∈ U) ∧ Nat.card E = 3 ^ Ps.length ∧
        ∃ U' : Submodule (ZMod 2) V, U' ≤ U ∧ PolarNondegOn Q U' ∧
          finrank (ZMod 2) U' + 2 * Ps.length = n ∧
          (∀ y ∈ U', ∀ P ∈ Ps, polar Q P.a y = 0 ∧ polar Q P.b y = 0) ∧
          ∀ P : AnisoPair Q, P.a ∈ U' → P.b ∈ U' → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU E hEU hE hmax
  by_cases hne : E = ⊥
  · refine ⟨[], List.Pairwise.nil, by simp, ?_, U, le_rfl, ?_, ?_, by simp, ?_⟩
    · simp [hne]
    · intro x hx hxperp
      exact (nondeg_iff.1 hU) x hx (fun u hu => by
        rw [QuadraticMap.polarBilin_apply_apply, polar_comm]
        exact hxperp u hu)
    · simp [hn]
    · exact no_anisoPair_of_maximal_bot hQ hU hEU hE hmax hne
  · obtain ⟨b, W, hbE, hblock, hWU, hU'nd, hU'lt, hKsupp, hKmax, hEeq, hcardE⟩ :=
      exists_block_step_of_maximal (polarBilin_symm Q) hQ Nat.prime_three (by norm_num)
        (isRestrClosed_orthogonalGroup Q) hU hEU hE hmax hne
    have hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      (Subgroup.mem_inf.1 (hEU hbE)).1
    have hb3 : b ^ 3 = 1 := hE.2 b hbE
    obtain ⟨P, hPplane⟩ := exists_anisoPair_plane_eq_of_isBlock hbO hb3 hblock
    set U' : Submodule (ZMod 2) V := U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W
      with hU'def
    have hn' : finrank (ZMod 2) U' < n := by
      rw [← hn]
      exact hU'lt
    obtain ⟨Ps', hPs'orth, hPs'U', hPs'card, U'', hU''U', hU''nd, hU''dim,
      hU''perp, hU''noPair⟩ :=
      ih (finrank (ZMod 2) U') hn' U' rfl hU'nd (E ⊓ ptw W) hKsupp
        (hE.mono inf_le_left) hKmax
    have hPperp : LinearMap.BilinForm.orthogonal (polarBilin Q) W = P.perp := by
      rw [← orthogonal_plane_eq_perp P, hPplane]
    have hPorth : ∀ P' ∈ Ps', P.Orth P' := by
      intro P' hP'
      obtain ⟨ha', hb'⟩ := hPs'U' P' hP'
      have haW : P'.a ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
        (Submodule.mem_inf.1 ha').2
      have hbW : P'.b ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
        (Submodule.mem_inf.1 hb').2
      rw [hPperp] at haW hbW
      rw [AnisoPair.mem_perp P] at haW hbW
      exact ⟨haW.1, hbW.1, haW.2, hbW.2⟩
    have hPsorth : (P :: Ps').Pairwise AnisoPair.Orth :=
      List.pairwise_cons.2 ⟨hPorth, hPs'orth⟩
    have hPsU : ∀ P' ∈ P :: Ps', P'.a ∈ U ∧ P'.b ∈ U := by
      intro P' hP'
      rcases List.mem_cons.1 hP' with hP'eq | hP''
      · subst P'
        exact ⟨hWU (hPplane ▸ AnisoPair.a_mem_plane P),
          hWU (hPplane ▸ AnisoPair.b_mem_plane P)⟩
      · exact ⟨(Submodule.mem_inf.1 (hPs'U' P' hP'').1).1,
          (Submodule.mem_inf.1 (hPs'U' P' hP'').2).1⟩
    have hcard : Nat.card E = 3 ^ (P :: Ps').length := by
      rw [hcardE, hPs'card, List.length_cons, pow_succ']
    have hU''U : U'' ≤ U := hU''U'.trans inf_le_left
    have hdim : finrank (ZMod 2) U'' + 2 * (P :: Ps').length = n := by
      have h1 : finrank (ZMod 2) U = finrank (ZMod 2) ↥(U ⊓ P.perp) + 2 :=
        finrank_inf_perp P (hWU (hPplane ▸ AnisoPair.a_mem_plane P))
          (hWU (hPplane ▸ AnisoPair.b_mem_plane P))
      have hU'eq : U' = U ⊓ P.perp := by
        rw [hU'def, hPperp]
      rw [hU'eq] at hU''dim
      rw [List.length_cons, ← hn]
      omega
    have hperp : ∀ y ∈ U'', ∀ P' ∈ P :: Ps',
        polar Q P'.a y = 0 ∧ polar Q P'.b y = 0 := by
      intro y hy P' hP'
      rcases List.mem_cons.1 hP' with hP'eq | hP''
      · subst P'
        have hyW : y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
          (Submodule.mem_inf.1 (hU''U' hy)).2
        rw [hPperp] at hyW
        exact (AnisoPair.mem_perp P).1 hyW
      · exact hU''perp y hy P' hP''
    exact ⟨P :: Ps', hPsorth, hPsU, hcard, U'', hU''U, hU''nd, hdim, hperp, hU''noPair⟩

end CFSG.StandardType.E6QTwo

end
