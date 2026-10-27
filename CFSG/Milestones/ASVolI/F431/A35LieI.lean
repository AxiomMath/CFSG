module

public import CFSG.Milestones.ASVolI.F431.L35

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section LieI

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_lieI_hnc {K' : Type} [Group K'] [Finite K']
    (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (θ : E ≃* K') {N1 N2 : Subgroup K'}
    (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) {T : Subgroup K'}
    {z₀ t₀ : K'} (L : F431LieI T N1 N2 z₀ t₀) {zb : E} (hzb : zb ∈ M₁) (hθz : θ zb = z₀)
    (hbz : burnsideF4d_bOne β ε ⟨zb, hzb⟩ = z) {r : ℕ} (hr1 : ¬ r ∣ Nat.card N1)
    (hr2 : r ∣ Nat.card (Subgroup.centralizer ({t₀} : Set K'))) :
    ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) z₀)
      (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) t₀) := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  obtain ⟨hC, hr, -, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  set b1 := (burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1) with hb1
  set b2 := (burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2) with hb2
  have hz₀ : z₀ ∈ N1 := by
    rw [← hθz]
    exact (h1 zb).2 hzb
  have hφz : amalgamMap b1 b2 z₀ = z := by
    rw [amalgamMap_of_mem₁ _ _ hz₀, ← hbz]
    show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨z₀, hz₀⟩) = _
    congr 1
    apply Subtype.ext
    rw [burnsideF4m_psi_apply]
    show θ.symm z₀ = zb
    rw [← hθz, MulEquiv.symm_apply_apply]
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 z₀} : Set M) ≤ b1.range := by
    rw [hφz, hr]
    exact hyp.hb
  exact L.not_conj_of_card hC hb hr1 hr2

theorem burnsideF4m_F_4_35_of_lieI {K' : Type} [Group K'] [Finite K']
    (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4)
    (θ : E ≃* K') {N1 N2 : Subgroup K'} (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁)
    (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) {T : Subgroup K'} {z₀ t₀ : K'}
    (L : F431LieI T N1 N2 z₀ t₀)
    (hnc : ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) z₀)
      (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) t₀))
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hi2 : i * i = 1)
    (hj1 : j ≠ 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  haveI := hyp.amalgam.finite
  refine ⟨burnsideF4j_F_4_35_forward hyp i j hi hj, fun h => ?_⟩
  obtain ⟨hC, -, -, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hiT := burnsideF4m_theta_S_le hyp.amalgam θ h1 h2 L.sylow L.T_le₁ L.T_le₂ hi
  have hjT := burnsideF4m_theta_S_le hyp.amalgam θ h1 h2 L.sylow L.T_le₁ L.T_le₂ hj
  have hord : ∀ x : ↥(M₁ ⊓ M₂), x ≠ 1 → x * x = 1 → orderOf (θ (x : E)) = 2 := by
    intro x hx1 hx2
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul]
      have : (x : E) * x = 1 := congrArg Subtype.val hx2
      rw [this, map_one]
    · intro h0
      apply hx1
      apply Subtype.ext
      exact θ.injective (h0.trans (map_one θ).symm)
  have hφ : ∀ (x : ↥(M₁ ⊓ M₂)) (hx : θ (x : E) ∈ N1),
      amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (θ (x : E)) = bM β ε x := by
    intro x hx
    rw [amalgamMap_of_mem₁ _ _ hx]
    show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨θ x, hx⟩) =
      burnsideF4d_bOne β ε ⟨x, x.2.1⟩
    congr 1
    exact Subtype.ext (by rw [burnsideF4m_psi_apply]; simp)
  have hK := (L.lemma_F435 hC hnc hiT hjT (hord i hi1 hi2) (hord j hj1 hj2)).mpr (by
    rw [hφ i (L.T_le₁ hiT), hφ j (L.T_le₁ hjT)]
    exact h)
  have hE : IsConj (i : E) (j : E) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hK
    refine isConj_iff.mpr ⟨θ.symm c, θ.injective ?_⟩
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  have hiG : (i : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hi).1
  have hjG : (j : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hj).1
  exact burnsideF4m_isConj_Gp_of_two hyp.amalgam hL3 hSp hyp.not_G2d hiG hjG
    (fun h0 => hi1 (Subtype.ext h0)) (congrArg Subtype.val hi2) hE

end LieI

end CFSG.ASVolI
