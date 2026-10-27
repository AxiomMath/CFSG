module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L82.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L82

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup {X Y : Subgroup G} {a : G} (hX : a ∈ Subgroup.normalizer (X : Set G))
    (hY : a ∈ Subgroup.normalizer (Y : Set G)) :
    a ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_sup, hX, hY]

theorem conj_mem_inf_of_mem_inf_centralizer
    (h : Counterexample p A θ) {b : G} (hb : b ∈ A)
    (hb1 : b ≠ 1) {J W₀ : Subgroup G}
    (hΩ : IsRegFam A (θ b) (lcal (θ b)) (E ⊔ Subgroup.zpowers b)) (hJ : J ∈ lcal (θ b))
    (hDW : thetaOf θ A ≤ W₀) {c : G} (hc : c ∈ J ⊓ Subgroup.centralizer (E : Set G)) {x : G}
    (hx : x ∈ W₀ ⊓ J) : c * x * c⁻¹ ∈ W₀ ⊓ J := by
  obtain ⟨hcJ, hcE⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hxW, hxJ⟩ := Subgroup.mem_inf.mp hx
  have hdp := hΩ.isDirectProduct
  have hcb : c ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq_singleton]
    exact h.isFunctor.le_centralizer b hb hb1 (lcal_le hJ hcJ)
  have hcN : c ∈ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) := by
    rw [hΩ.stabilizer J hJ, centralizer_sup]
    exact Subgroup.mem_inf.mpr ⟨hcE, hcb⟩
  have hcmem : c ∈ projIn (lcal (θ b)) J (θ b ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [projIn_centralizer_eq hdp (fun a ha J' hJ' => hΩ.map_conj_mem a ha J' hJ') hJ]
    exact Subgroup.mem_inf.mpr ⟨hcJ, hcN⟩
  obtain ⟨y, hy, hyc⟩ := (hdp.mem_projIn_iff hJ).mp hcmem
  have hyD : (y : G) ∈ W₀ := hDW (by rwa [← h.isFunctor.inf_centralizer_self hb hb1])
  obtain ⟨l, hl, hyl⟩ : ∃ l ∈ sSup (lcal (θ b) \ {J}), (y : G) = c * l := by
    have hy' : (y : G) ∈ J ⊔ sSup (lcal (θ b) \ {J}) := by
      rw [(hdp.isDirectPair hJ).sup_eq]
      exact y.2
    obtain ⟨j, hj, l, hl, hjl⟩ :=
      (mem_sup_iff_of_commute (hdp.commute_sSup_diff hJ)).mp hy'
    have h1 := hdp.coord_mul hJ hj hl
    have hyeq : (⟨j * l, mul_mem (hdp.le hJ hj) (hdp.sSup_diff_le _ Set.sdiff_subset hl)⟩ :
        ↥(θ b)) = y := Subtype.ext hjl
    rw [hyeq, hyc] at h1
    exact ⟨l, hl, by rw [← hjl, h1]⟩
  have hlx : l * x * l⁻¹ = x := by
    have := (hdp.commute_sSup_diff hJ x hxJ l hl).eq
    rw [mul_inv_eq_iff_eq_mul, ← this]
  have hconj : c * x * c⁻¹ = y * x * (y : G)⁻¹ := by
    rw [hyl, mul_inv_rev]
    calc c * x * c⁻¹ = c * (l * x * l⁻¹) * c⁻¹ := by rw [hlx]
      _ = c * l * x * (l⁻¹ * c⁻¹) := by group
  rw [hconj]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hyD hxW) (inv_mem hyD), ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hdp.le_normalizer hJ y.2) x).mp hxJ

theorem mem_lcalA_of_mem_lcal
    (h : Counterexample p A θ) (hB : TypeB p A θ E K) {b : G}
    (hb : b ∈ A) (hbE : b ∉ E) {J : Subgroup G} (hJ : J ∈ lcal (θ b)) :
    J ∈ lcalA (θ b) E := by
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem E)
  have hF := h.zpowers_mem_E1 hb hb1
  have hFE : Subgroup.zpowers b ≠ E := fun heq => hbE (heq ▸ Subgroup.mem_zpowers b)
  have hθ := h.isFunctor.thetaOf_zpowers hb hb1
  have hΩ : IsRegFam A (θ b) (lcal (θ b)) (E ⊔ Subgroup.zpowers b) := by
    have := h.isRegFam_line_of_typeB hB.toTypeBCore hF hFE
    rwa [hθ] at this
  have hperm : ∀ a ∈ A, ∀ J' ∈ lcal (θ b), J'.map (MulAut.conj a).toMonoidHom ∈ lcal (θ b) :=
    fun a ha J' hJ' => hΩ.map_conj_mem a ha J' hJ'
  have hsmA : smear J A = thetaOf θ A := by
    rw [smear_eq_centralizer_of_transitive hΩ.isDirectProduct hperm hJ (hΩ.transitive J hJ),
      h.isFunctor.inf_centralizer_self hb hb1]
  exact T515f.mem_lcalA_of_le (h.kSetting_apply hb hb1) hB.mem.1
    ⟨hJ, by rw [hsmA]; exact h.not_isSolvable_D⟩

theorem fitting_smear_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    (hB : TypeB p A θ E K) {b : G} (hb : b ∈ A) (hbE : b ∉ E) {J : Subgroup G}
    (hJ : J ∈ lcal (θ b)) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J E) ≤ thetaOf θ A ⊔ zOf S := by
  have hE := hB.mem
  have hEA : E ≤ A := hE.1
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem E)
  have hF := h.zpowers_mem_E1 hb hb1
  have hFE : Subgroup.zpowers b ≠ E := fun heq => hbE (heq ▸ Subgroup.mem_zpowers b)
  have hθ := h.isFunctor.thetaOf_zpowers hb hb1
  have hΩ : IsRegFam A (θ b) (lcal (θ b)) (E ⊔ Subgroup.zpowers b) := by
    have := h.isRegFam_line_of_typeB hB.toTypeBCore hF hFE
    rwa [hθ] at this
  have hKS : KSetting p E (θ b) :=
    ⟨h.prime, h.isElemAbelian_of_le hEA, hEA.trans (h.isFunctor.normalized b hb hb1),
      h.hypC b hb hb1⟩
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) :=
    le_sup_left.trans ((hΩ.stabilizer J hJ).symm.le.trans inf_le_right)
  have hJE : J ∈ lcalA (θ b) E := mem_lcalA_of_mem_lcal h hB hb hbE hJ
  set W₀ : Subgroup G := thetaOf θ A ⊔ zOf S with hW₀
  have hDW : thetaOf θ A ≤ W₀ := le_sup_left
  have hZW : zOf S ≤ W₀ := le_sup_right
  have hAW : A ≤ Subgroup.normalizer (W₀ : Set G) := fun a ha =>
    mem_normalizer_sup (h.isFunctor.normalizes_thetaOf le_rfl ha)
      (mem_normalizer_zOf (Counterexample.normalizes_of_isSr hS ha))
  have hYJ : W₀ ⊓ J ≤ J := inf_le_right
  have hY1 : W₀ ⊓ J ≠ ⊥ := by
    have hInd : J ∈ Ind (θ b) := by
      have := h.ind_eq_lcal_line_of_typeB hB.toTypeBCore hF hFE
      rw [hθ] at this
      exact this ▸ hJ
    have hZJ := h.lemma_7_4_b hr hS hb hb1 (Or.inr ⟨E, K, hB.toTypeBCore, hbE⟩) hInd
    intro hbot
    apply hZJ
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf_right J hZW
  have key : ∀ c ∈ J ⊓ Subgroup.centralizer (E : Set G), ∀ x ∈ W₀ ⊓ J, c * x * c⁻¹ ∈ W₀ ⊓ J :=
    fun c hc x hx => conj_mem_inf_of_mem_inf_centralizer h hb hb1 hΩ hJ hDW hc hx
  have hnorm : J ⊓ Subgroup.centralizer ((E ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) :
      Set G) ≤ Subgroup.normalizer ((W₀ ⊓ J : Subgroup G) : Set G) := by
    rw [inf_eq_left.mpr hEJ]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key c hc x, fun hx => ?_⟩
    have := key c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using this
  have hYns : ¬ Group.IsSolvable (W₀ ⊓ J : Subgroup G) := fun hsolv =>
    hY1 (eq_bot_of_isSolvable_of_normalized hKS hJE hYJ hsolv hnorm)
  have hEY : E ≤ Subgroup.normalizer ((W₀ ⊓ J : Subgroup G) : Set G) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hAW (hEA he), hEJ he⟩)
  have hYB : signalizerMcBrideHypothesisB p (W₀ ⊓ J : Subgroup G) :=
    hypB_mono (hYJ.trans (lcal_le hJ)) (h.hypC b hb hb1)
  have hN1 := inf_centralizer_ne_bot_of_not_isSolvable h.prime (h.isElemAbelian_of_le hEA) hEY
    hYB hYns
  have hNle : (W₀ ⊓ J) ⊓ Subgroup.centralizer (E : Set G) ≤ smear J E := by
    rw [smear_eq_inf_centralizer hEJ]
    exact inf_le_inf_right _ inf_le_right
  have hNn : (((W₀ ⊓ J) ⊓ Subgroup.centralizer (E : Set G)).subgroupOf (smear J E)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNle]
    intro n c hn hc
    rw [smear_eq_inf_centralizer hEJ] at hc
    obtain ⟨hnY, hnE⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨key c hc n hnY,
      mul_mem (mul_mem (Subgroup.mem_inf.mp hc).2 hnE) (inv_mem (Subgroup.mem_inf.mp hc).2)⟩
  exact (fitting_smear_le_of_normal hKS hJE hNle hNn hN1).trans (inf_le_left.trans inf_le_left)

end L82

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
