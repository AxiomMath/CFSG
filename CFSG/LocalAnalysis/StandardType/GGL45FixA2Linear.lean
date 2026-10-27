module

public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Mark
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Centre
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinear
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem gffa2_linear_clauseB {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) (X : Type) [Group X] [Finite X]
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) K))
    (hX : commutator X = ⊤) (ψ : MulAut X)
    (hind : ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K)),
      ∃ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K)) Set.univ,
        orderOf f = 3 ∧ LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹))
    (Q : Subgroup X) (hQ : IsComponentOf Q (ggAutFixedSubgroup ψ))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X)) :
    Subgroup.center Q = ⊥ ∧ LargeEvenMarking Q fun lab' _ _ _ _ _ => GGLabelA2 lab' := by
  obtain ⟨f, hf, u, hu, hord, hind'⟩ := hind
  obtain ⟨σ, hσ⟩ := LinearFieldFix.exists_induced hf
  have hσord : orderOf σ = 3 :=
    (LinearFieldFix.orderOf_eq_of_mk_matAct (by norm_num : 2 ≤ 3)
      (LinearFieldFix.slMapStable 3 K) hσ).trans hord
  have hdvd : 3 ∣ n := by
    have h := (_root_.CFSG.LocalAnalysis.GLTheoremA.FQ.card_fixedPoints_field
      (m := n) (by omega) hK σ).1
    rwa [hσord] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = 3 * m :=
    ⟨n / 3, (Nat.mul_div_cancel' hdvd).symm⟩
  have hm1 : 1 ≤ m := by omega
  have hn3 : 3 ≤ n := by omega
  have hmEven : Even m := gffa2_even_of_linear h3 hm
  have hn1 : 1 ≤ n := by omega
  have hZ' : Subgroup.center X = ⊥ :=
    gffa2_center_eq_bot_of_card_dvd
      (gffa2_card_center_dvd_linear (K := K) (n := n) ⟨hX⟩ hn3 hK θ) hZ
  obtain ⟨E⟩ := gffa2_fixedEquiv θ hZ' ψ f u hind'
  obtain ⟨E'⟩ := gffa2_commutator_equiv E
  have hraw0 := ggRawFieldFixStd_linear (l := 2) le_rfl hn1 hK (p := 3)
    (LinearFieldFix.isSimpleGroup_proj (d := 3) (by norm_num) K)
    (LinearFieldFix.exists_noncomm_proj (d := 3) (by norm_num) K) f hf hord
  have hraw : LargeEvenRawDatum ⟨.A, 2, n / 3⟩
      (fun R₀ _ _ _ => IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        Nonempty (↥Q ≃* R₀)) :=
    largeEvenRawDatum_mono (fun R₀ _ I₀ F₀ h => by
      obtain ⟨hs, hna, θ₀, -⟩ := h
      refine ⟨hs, hna, ?_⟩
      exact gffa2_component_equiv
        (E'.trans ((MulEquiv.subgroupCongr (by
          simp only [ggFixDer, gffa2_fixSub_eq])).trans θ₀)) hs hQ) hraw0
  have hn3' : n / 3 = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m (by norm_num)
  rw [hn3'] at hraw
  obtain ⟨hlab, hA2⟩ := gffa2_label_linear hmEven hm1
  exact gffa2_marking hlab hA2 hraw

theorem gffa2_linear_kgraw {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGL45FieldFixKGRaw 3 ⟨.A, 2, n⟩ (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K))) := by
  refine ⟨fun _ _ A hA => gffa2_rank_linear hK A hA,
    fun X _ _ θ hX ψ _ hind Q hQ => ⟨?_, ?_⟩⟩
  · intro htor
    exact absurd htor (by rintro (h | h | h | h) <;> cases h)
  · intro _ _ hZ
    exact gffa2_linear_clauseB hn hK h3 X θ hX ψ hind Q hQ hZ

end CFSG.StandardType
