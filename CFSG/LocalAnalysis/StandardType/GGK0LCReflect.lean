module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LCAct
public import CFSG.LocalAnalysis.StandardType.GGK0LCAffine

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace KacPt

private lemma lk0xlcrefl_lam_reflect_eq {τ : Tag} (K : KacPt τ) (j : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) :
    K.lam (reflect τ j γ) = K.lam γ - (∑ m, τ.cartan j m * γ m) * K.s j := by
  have hsplit : reflect τ j γ =
      γ + (-(∑ m, τ.cartan j m * γ m)) • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [reflect, sub_eq_add_neg, ← neg_smul]
  rw [hsplit, lam_add, lam_smul, lam_single]
  ring

private lemma lk0xlcrefl_shift_node_zero {τ : Tag} (K : KacPt τ) (j : Fin τ.rank)
    (hj : K.s j = 0) (hz : simple τ j ∈ K.stab) (γ : Fin τ.rank → ℤ) :
    K.shift (simple τ j) γ = 0 := by
  have hspec := shift_spec K hz γ
  have hlam : K.lam (simple τ j • γ) = K.lam γ := by
    rw [simple_smul, lk0xlcrefl_lam_reflect_eq, hj]
    ring
  rw [hlam, sub_self, mul_eq_zero] at hspec
  exact hspec.resolve_left (by
    have : (0 : ℤ) < (K.p : ℤ) := by exact_mod_cast K.p_pos
    exact ne_of_gt this)

private lemma lk0xlcrefl_simple_mul_self {τ : Tag}
    (i : Fin τ.rank) : simple τ i * simple τ i = 1 := by
  refine ext_single fun k => ?_
  rw [mul_smul, simple_smul, simple_smul, reflect_reflect, one_smul]

private lemma lk0xlcrefl_smul_ext {τ : Tag} {w : WeylGroup τ} {i : Fin τ.rank}
    (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = theta τ) (γ : Fin τ.rank → ℤ) :
    (w * simple τ i * w⁻¹) • γ =
      γ - (∑ j, τ.cartan i j * (w⁻¹ • γ) j) • theta τ := by
  rw [mul_smul, mul_smul, simple_smul, reflect, smul_sub, smul_inv_smul, smul_comm, hw]

private lemma lk0xlcrefl_shift_ext {τ : Tag} (K : KacPt τ) (h0 : K.s0 = 0) {w : WeylGroup τ}
    {i : Fin τ.rank} (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = theta τ)
    (hz : (w * simple τ i * w⁻¹) ∈ K.stab) (γ : Fin τ.rank → ℤ) :
    K.shift (w * simple τ i * w⁻¹) γ = ∑ j, τ.cartan i j * (w⁻¹ • γ) j := by
  have hspec := shift_spec K hz γ
  have hlam : K.lam ((w * simple τ i * w⁻¹) • γ) =
      K.lam γ - (∑ j, τ.cartan i j * (w⁻¹ • γ) j) * K.lam (theta τ) := by
    rw [lk0xlcrefl_smul_ext hw γ, sub_eq_add_neg, ← neg_smul, lam_add, lam_smul]
    ring
  have htheta : K.lam (theta τ) = (K.p : ℤ) := by
    rw [lam_theta, h0]
    ring
  rw [hlam, htheta] at hspec
  have hpc : (K.p : ℤ) * K.shift (w * simple τ i * w⁻¹) γ =
      (K.p : ℤ) * (∑ j, τ.cartan i j * (w⁻¹ • γ) j) := by
    rw [hspec]
    ring
  exact mul_left_cancel₀ (by
    have : (0 : ℤ) < (K.p : ℤ) := by exact_mod_cast K.p_pos
    exact ne_of_gt this) hpc

private lemma lk0xlcrefl_act_node {τ : Tag} (K : KacPt τ) (j : Fin τ.rank)
    (hshift : ∀ γ : Fin τ.rank → ℤ, K.shift (simple τ j) γ = 0) (a : AffPair τ) :
    K.act (simple τ j) a = (reflect τ j a.1, a.2) := by
  rw [act, simple_smul, hshift a.1, add_zero]

private lemma lk0xlcrefl_act_ext {τ : Tag} (K : KacPt τ) (h0 : K.s0 = 0) {w : WeylGroup τ}
    {i : Fin τ.rank} (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = theta τ)
    (hz : (w * simple τ i * w⁻¹) ∈ K.stab) (a : AffPair τ) :
    K.act (w * simple τ i * w⁻¹) a =
      (a.1 - (∑ j, τ.cartan i j * (w⁻¹ • a.1) j) • theta τ,
        a.2 + ∑ j, τ.cartan i j * (w⁻¹ • a.1) j) := by
  rw [act, lk0xlcrefl_smul_ext hw a.1, lk0xlcrefl_shift_ext K h0 hw hz a.1]


theorem refl_le_stab
    {τ : Tag} (K : KacPt τ) : K.refl ≤ K.stab := by
  refine (Subgroup.closure_le K.stab).2 ?_
  rintro r ⟨w, i, hw, rfl⟩
  intro v
  have hker : (K.p : ℤ) ∣ K.lam (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := hw.2
  have hsmul : (w * simple τ i * w⁻¹) • v =
      v - (∑ j, τ.cartan i j * (w⁻¹ • v) j) •
        (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    rw [mul_smul, mul_smul, simple_smul, reflect, smul_sub, smul_inv_smul, smul_comm]
  have hlam : K.lam ((w * simple τ i * w⁻¹) • v) =
      K.lam v - (∑ j, τ.cartan i j * (w⁻¹ • v) j) *
        K.lam (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    rw [hsmul, sub_eq_add_neg, ← neg_smul, lam_add, lam_smul]
    ring
  rw [hlam]
  rcases hker with ⟨d, hd⟩
  exact ⟨-((∑ j, τ.cartan i j * (w⁻¹ • v) j) * d), by rw [hd]; ring⟩

theorem exists_refl_node
    {τ : Tag} (K : KacPt τ) (j : Fin τ.rank) (hj : K.s j = 0) :
    ∃ r ∈ K.refl, K.act r (simpleAff j) = -(simpleAff j) ∧ r * r = 1 ∧
      ∀ a : AffPair τ, IsRoot τ a.1 → AffPos a → a ≠ simpleAff j → AffPos (K.act r a) := by
  have hker : (1 : WeylGroup τ) • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ K.kerRoots := by
    refine ⟨?_, ?_⟩
    · simpa using isRoot_single τ j
    · rw [one_smul, lam_single, hj]
      exact dvd_zero _
  have hmem : simple τ j ∈ K.refl :=
    Subgroup.subset_closure ⟨1, j, hker, by rw [one_mul, inv_one, mul_one]⟩
  have hz : simple τ j ∈ K.stab := refl_le_stab K hmem
  have hshift : ∀ γ : Fin τ.rank → ℤ, K.shift (simple τ j) γ = 0 :=
    fun γ => lk0xlcrefl_shift_node_zero K j hj hz γ
  refine ⟨simple τ j, hmem, ?_, ?_, ?_⟩
  · rw [lk0xlcrefl_act_node K j hshift]
    simp only [simpleAff, Prod.fst, Prod.snd]
    rw [reflect_single_self τ j]
    simp
  · exact lk0xlcrefl_simple_mul_self j
  · intro a ha hpos hne
    rw [lk0xlcrefl_act_node K j hshift]
    rcases hpos with hk | ⟨hk, hht⟩
    · exact Or.inl hk
    · refine Or.inr ⟨hk, ?_⟩
      have hne' : a.1 ≠ (Pi.single j 1 : Fin τ.rank → ℤ) := by
        intro h
        exact hne (by ext <;> simp [simpleAff, h, hk])
      exact height_reflect_pos ha hht hne'

theorem exists_refl_ext
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) (h0 : K.s0 = 0) :
    ∃ r ∈ K.refl, K.act r (extAff τ) = -(extAff τ) ∧ r * r = 1 ∧
      ∀ a : AffPair τ, IsRoot τ a.1 → AffPos a → a ≠ extAff τ → AffPos (K.act r a) := by
  obtain ⟨w, i, hwi⟩ := isRoot_iff_exists_smul_single.1 hT.2.1
  have hker : w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ K.kerRoots := by
    refine ⟨?_, ?_⟩
    · rw [hwi]
      exact hT.2.1
    · rw [hwi, lam_theta, h0]
      simp
  have hmem : w * simple τ i * w⁻¹ ∈ K.refl :=
    Subgroup.subset_closure ⟨w, i, hker, rfl⟩
  have hz : w * simple τ i * w⁻¹ ∈ K.stab := refl_le_stab K hmem
  have hw1 : w⁻¹ • (theta τ) = (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [← hwi, inv_smul_smul]
  have hcneg : (∑ j, τ.cartan i j * (w⁻¹ • (-theta τ)) j) = -2 := by
    have hneg : w⁻¹ • (-theta τ) = -(Pi.single i 1 : Fin τ.rank → ℤ) := by
      rw [smul_neg, hw1]
    rw [hneg]
    rw [Finset.sum_eq_single i]
    · simp [τ.cartan_self]
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  refine ⟨w * simple τ i * w⁻¹, hmem, ?_, ?_, ?_⟩
  · rw [lk0xlcrefl_act_ext K h0 hwi hz]
    simp only [extAff, Prod.fst, Prod.snd]
    rw [hcneg]
    have h1 : -theta τ - (-2 : ℤ) • theta τ = theta τ := by module
    rw [h1]
    simp
  · have hs : simple τ i * simple τ i = 1 := lk0xlcrefl_simple_mul_self i
    calc (w * simple τ i * w⁻¹) * (w * simple τ i * w⁻¹)
        = w * (simple τ i * simple τ i) * w⁻¹ := by group
      _ = 1 := by rw [hs]; group
  · intro a ha hpos hne
    obtain ⟨i0, hi0⟩ := exists_ncoord_pos_of_ne_ext hT ha hpos hne
    refine aff_pos_of_ncoord_pos (i := i0) hT ?_ ?_
    · show IsRoot τ ((w * simple τ i * w⁻¹) • a.1)
      exact IsRoot.smul ha _
    · rw [lk0xlcrefl_act_ext K h0 hwi hz]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Prod.fst, Prod.snd,
        theta]
      ring_nf
      linarith [hi0]

end KacPt

end CFSG.StandardType.GGK0LC

end
