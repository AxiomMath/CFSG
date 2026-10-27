module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.GenPi

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T614

private theorem exists_mul_of_mem_sup_aux {Γ : Type*} [Group Γ] {H B : Subgroup Γ}
    (hBH : B ≤ Subgroup.normalizer (H : Set Γ)) {x : Γ} (hx : x ∈ H ⊔ B) :
    ∃ h ∈ H, ∃ b ∈ B, x = h * b := by
  have hx' : x ∈ ((H ⊔ B : Subgroup Γ) : Set Γ) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H B hBH] at hx'
  obtain ⟨h, hh, b, hb, rfl⟩ := hx'
  exact ⟨h, hh, b, hb, rfl⟩

end T614

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem Setting614.not_mem_of_ne (S : Setting614 p A θ E) (h : Counterexample p A θ)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {f : G} (hf : f ∈ F)
    (hf1 : f ≠ 1) : f ∉ E := fun hfE => hFE (by
  rw [h.line_eq_zpowers hF hf hf1]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfE)
    (by rw [S.mem.2, h.card_zpowers (hF.1 hf) hf1, pow_one]))

theorem nonempty_mulEquiv_thetaOf
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    (hkOf : ∀ a ∈ A, a ∉ E → kOf (θ a) = θ a) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G} (hL : L ∈ lcal (θ b)) : Nonempty (↥L ≃* ↥(thetaOf θ B)) := by
  have hbA : b ∈ A := hB.1 hb
  have hbE : b ∉ E := not_mem_of_mem_complement hEB hb hb1
  have hline := h.zpowers_mem_E1 hbA hb1
  have hsol : sol (θ b) = ⊥ := h.sol_apply hbA hb1
  have hX : IsDirectProduct (lcal (θ b)) (θ b) := by
    have := isDirectProduct_lcal_kOf hsol
    rwa [hkOf b hbA hbE] at this
  have hAN : A ≤ Subgroup.normalizer (θ b : Set G) := h.isFunctor.normalized b hbA hb1
  have hLz : L ∈ lcal (thetaOf θ (Subgroup.zpowers b)) := by
    rwa [h.isFunctor.thetaOf_zpowers hbA hb1]
  have hNz : A ⊓ Subgroup.normalizer (L : Set G) = Subgroup.zpowers b ⊔ E := by
    rw [← S.bN_eq _ hline]
    exact (h.lemma_6_9_b hline.1 (h.ne_bot_of_mem_E1 hline) L hLz).symm
  have hperm : ∀ c ∈ B, ∀ J ∈ lcal (θ b), J.map (MulAut.conj c).toMonoidHom ∈ lcal (θ b) :=
    fun c hc J hJ => map_conj_mem_lcal hJ (hAN (hB.1 hc))
  have htrans : ∀ K ∈ lcal (θ b), ∃ c ∈ B, K = L.map (MulAut.conj c).toMonoidHom := by
    intro K hK
    have hK' : K ∈ lcal (thetaOf θ (Subgroup.zpowers b)) := by
      rwa [h.isFunctor.thetaOf_zpowers hbA hb1]
    obtain ⟨a, haA, rfl⟩ := h.exists_conj_eq_of_mem_lcal hline.1 (h.ne_bot_of_mem_E1 hline) hLz hK'
    have haEB : a ∈ E ⊔ B := (S.sup_eq h hB hEB).symm ▸ haA
    have hcomm : ∀ e ∈ E, ∀ β ∈ B, Commute e β := fun e he β hβ =>
      h.comm_of_mem_A (S.mem.1 he) (hB.1 hβ)
    obtain ⟨e, he, β, hβ, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp haEB
    refine ⟨β, hβ, ?_⟩
    have hLβ : L.map (MulAut.conj β).toMonoidHom ∈ lcal (thetaOf θ (Subgroup.zpowers b)) :=
      map_conj_mem_lcal hLz ((h.isFunctor.normalizes_thetaOf hline.1) (hB.1 hβ))
    have heN : e ∈ Subgroup.normalizer
        ((L.map (MulAut.conj β).toMonoidHom : Subgroup G) : Set G) := by
      have h1 := h.lemma_6_9_b hline.1 (h.ne_bot_of_mem_E1 hline) _ hLβ
      rw [S.bN_eq _ hline] at h1
      exact (Subgroup.mem_inf.mp (h1 ▸ Subgroup.mem_sup_right he)).2
    rw [← T517.map_conj_map_conj]
    exact L69.map_conj_eq_self_iff.mpr heN
  have hker : B ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    intro x hx
    have h1 : x ∈ B ⊓ (Subgroup.zpowers b ⊔ E) := by
      rw [← hNz]
      exact ⟨hx.1, hB.1 hx.1, hx.2⟩
    rw [h.inf_sup_eq_of_le S.mem.1 hB.1 hEB (Subgroup.zpowers_le.mpr hb)] at h1
    have hLc : L ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [centralizer_zpowers_eq_singleton]
      exact (lcal_le hL).trans (h.isFunctor.le_centralizer b hbA hb1)
    exact Subgroup.le_centralizer_iff.mp hLc h1
  obtain ⟨e⟩ := T614.nonempty_mulEquiv_inf_centralizer hX hperm hL htrans hker
  have hD : θ b ⊓ Subgroup.centralizer (B : Set G) = thetaOf θ B := by
    rw [h.isFunctor.inf_centralizer_eq_thetaOf hbA hb1 hB.1,
      sup_eq_right.mpr (Subgroup.zpowers_le.mpr hb)]
  exact ⟨e.symm.trans (MulEquiv.subgroupCongr hD)⟩

theorem isWreath_of_mem_lcal
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    (hkOf : ∀ a ∈ A, a ∉ E → kOf (θ a) = θ a) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {L : Subgroup G}
    (hL : L ∈ lcal (thetaOf θ F)) :
    IsWreath (thetaOf θ F ⊔ A) L A (E ⊔ F) (A ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  have hF0 : F ≠ ⊥ := h.ne_bot_of_mem_E1 hF
  obtain ⟨a, haA, ha1, haF⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  have haE : a ∉ E :=
    S.not_mem_of_ne h hF hFE (haF ▸ Subgroup.mem_zpowers a) ha1
  have hHF : thetaOf θ F = θ a := by rw [← haF]; exact h.isFunctor.thetaOf_zpowers haA ha1
  have hsol : sol (thetaOf θ F) = ⊥ := h.sol_thetaOf hF.1 hF0
  have hdp : IsDirectProduct (lcal (thetaOf θ F)) (thetaOf θ F) := by
    have := isDirectProduct_lcal_kOf hsol
    rwa [hHF, hkOf a haA haE, ← hHF] at this
  have hAN : A ≤ Subgroup.normalizer (thetaOf θ F : Set G) :=
    h.isFunctor.normalizes_thetaOf hF.1
  have htrans : ∀ J ∈ lcal (thetaOf θ F), ∃ c ∈ A, J = L.map (MulAut.conj c).toMonoidHom :=
    fun J hJ => h.exists_conj_eq_of_mem_lcal hF.1 hF0 hL hJ
  have hset : {K | ∃ g ∈ thetaOf θ F ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} =
      lcal (thetaOf θ F) := by
    ext K
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, c, hc, rfl⟩ := T614.exists_mul_of_mem_sup_aux hAN hg
      have hLc : L.map (MulAut.conj c).toMonoidHom ∈ lcal (thetaOf θ F) :=
        map_conj_mem_lcal hL (hAN hc)
      rw [← T517.map_conj_map_conj,
        L69.map_conj_eq_self_iff.mpr (hdp.le_normalizer hLc hx)]
      exact hLc
    · intro hK
      obtain ⟨c, hc, rfl⟩ := htrans K hK
      exact ⟨c, Subgroup.mem_sup_right hc, rfl⟩
  have hsupr : (⨆ g ∈ thetaOf θ F ⊔ A, L.map (MulAut.conj g).toMonoidHom) = thetaOf θ F := by
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      have hmem : L.map (MulAut.conj g).toMonoidHom ∈
          {K | ∃ g ∈ thetaOf θ F ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} := ⟨g, hg, rfl⟩
      rw [hset] at hmem
      exact lcal_le hmem
    · calc thetaOf θ F = sSup (lcal (thetaOf θ F)) := hdp.sSup_eq.symm
        _ ≤ _ := by
          refine sSup_le fun J hJ => ?_
          have hmem : J ∈ {K | ∃ g ∈ thetaOf θ F ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} := by
            rw [hset]
            exact hJ
          obtain ⟨g, hg, hgJ⟩ := hmem
          rw [hgJ]
          exact le_iSup₂_of_le g hg le_rfl
  refine ⟨h.elemAbelian.1, le_sup_right, (lcal_le hL).trans le_sup_left, ?_, ?_, ?_, rfl⟩
  · refine le_antisymm (sup_le_sup_right (lcal_le hL) A) (sup_le ?_ le_sup_right)
    calc thetaOf θ F = sSup (lcal (thetaOf θ F)) := hdp.sSup_eq.symm
      _ ≤ L ⊔ A := by
        refine sSup_le fun J hJ => ?_
        obtain ⟨c, hc, rfl⟩ := htrans J hJ
        rintro x ⟨y, hy, rfl⟩
        show c * y * c⁻¹ ∈ L ⊔ A
        exact mul_mem (mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hy))
          (inv_mem (Subgroup.mem_sup_right hc))
  · rw [hsupr, hset]
    exact hdp
  · rw [sup_comm, ← S.bN_eq F hF]
    exact h.lemma_6_9_b hF.1 hF0 L hL

theorem exists_simple_K
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    (hS : (sSet p A θ 1).Nonempty) (hkOf : ∀ a ∈ A, a ∉ E → kOf (θ a) = θ a) :
    ∃ K : Subgroup G, (IsSimpleGroup K ∧ ¬ IsMulCommutative K) ∧
      ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → ∀ L ∈ lcal (thetaOf θ F),
        Nonempty (↥L ≃* ↥K) := by
  have key : ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → ∀ L ∈ lcal (thetaOf θ F),
      ∃ B ∈ signalizerFunctorEk p 2 A, E ⊓ B = ⊥ ∧ ∃ f ∈ B, f ≠ 1 ∧ f ∈ F ∧ L ∈ lcal (θ f) := by
    intro F hF hFE L hL
    obtain ⟨f, hf, hf1⟩ := h.exists_ne_one_of_mem_E1 hF
    have hfE : f ∉ E := S.not_mem_of_ne h hF hFE hf hf1
    obtain ⟨B, hB, hEB, hfB⟩ := S.exists_complement h (hF.1 hf) hfE
    refine ⟨B, hB, hEB, f, hfB, hf1, hf, ?_⟩
    rwa [h.thetaOf_line hF hf hf1] at hL
  have comp : ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → ∀ L ∈ lcal (thetaOf θ F),
      ∀ F' ∈ signalizerFunctorEk p 1 A, F' ≠ E → ∀ L' ∈ lcal (thetaOf θ F'),
        Nonempty (↥L ≃* ↥L') := by
    intro F hF hFE L hL F' hF' hF'E L' hL'
    obtain ⟨B, hB, hEB, f, hfB, hf1, -, hLf⟩ := key F hF hFE L hL
    obtain ⟨B', hB', hEB', f', hf'B', hf'1, -, hLf'⟩ := key F' hF' hF'E L' hL'
    obtain ⟨e1⟩ := nonempty_mulEquiv_thetaOf h S hkOf hB hEB hfB hf1 hLf
    obtain ⟨e2⟩ := nonempty_mulEquiv_thetaOf h S hkOf hB' hEB' hf'B' hf'1 hLf'
    by_cases hBB : B = B'
    · subst hBB
      exact ⟨e1.trans e2.symm⟩
    · obtain ⟨ℓ, hℓ, hℓ1⟩ := h.exists_ne_one_of_mem_E1 (h.inf_mem_E1_of_ne_E2 hB hB' hBB)
      have hℓA : ℓ ∈ A := hB.1 hℓ.1
      have hℓz := h.zpowers_mem_E1 hℓA hℓ1
      obtain ⟨M, hM⟩ := h.lcal_thetaOf_nonempty hℓz.1 (h.ne_bot_of_mem_E1 hℓz)
      rw [h.isFunctor.thetaOf_zpowers hℓA hℓ1] at hM
      obtain ⟨e3⟩ := nonempty_mulEquiv_thetaOf h S hkOf hB hEB hℓ.1 hℓ1 hM
      obtain ⟨e4⟩ := nonempty_mulEquiv_thetaOf h S hkOf hB' hEB' hℓ.2 hℓ1 hM
      exact ⟨e1.trans (e3.symm.trans (e4.trans e2.symm))⟩
  obtain ⟨F₀, hF₀, hF₀E⟩ := S.exists_line_ne h hS
  obtain ⟨L₀, hL₀⟩ := h.lcal_thetaOf_nonempty hF₀.1 (h.ne_bot_of_mem_E1 hF₀)
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hL₀
  exact ⟨L₀, ⟨hs, hnc⟩, fun F hF hFE L hL => comp F hF hFE L hL F₀ hF₀ hF₀E L₀ hL₀⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
