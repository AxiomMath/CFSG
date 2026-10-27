module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M3

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

open Classical in
@[expose] noncomputable def thetaStar {G : Type*} [Group G] (θ : G → Subgroup G)
    (E W : Subgroup G) : G → Subgroup G :=
  fun a => if a ∈ E then W else kOf (θ a)

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

omit [Finite G] in
theorem thetaStar_of_mem {a : G} (ha : a ∈ E) {W : Subgroup G} : thetaStar θ E W a = W := by
  simp [thetaStar, ha]

omit [Finite G] in
theorem thetaStar_of_not_mem {a : G} (ha : a ∉ E) {W : Subgroup G} :
    thetaStar θ E W a = kOf (θ a) := by
  simp [thetaStar, ha]

theorem isFunctor_thetaStar
    (h : Counterexample p A θ) (S : Setting614 p A θ E) {W : Subgroup G}
    (hW : ∀ B ∈ signalizerFunctorEk p 2 A, E ⊓ B = ⊥ → wTilde θ E B = W) :
    IsFunctor p A (thetaStar θ E W) := by
  obtain ⟨B₀, hB₀, hEB₀⟩ := S.exists_complement_some h
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 S.mem
  obtain ⟨hWE, hWN⟩ := h.wTilde_le S hB₀ hEB₀
  rw [hW B₀ hB₀ hEB₀] at hWE hWN
  have hWc : W ≤ Subgroup.centralizer (E : Set G) :=
    hWE.trans (h.isFunctor.thetaOf_le_centralizer S.mem.1)
  have hbal : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      thetaStar θ E W a ⊓ Subgroup.centralizer {b} ≤ thetaStar θ E W b := by
    intro a ha ha1 b hb hb1
    have hEcent : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) =
        Subgroup.centralizer (E : Set G) := by
      intro e he he1
      rw [← centralizer_zpowers_eq_singleton, h.line_eq_zpowers S.mem he he1]
    by_cases haE : a ∈ E <;> by_cases hbE : b ∈ E
    · rw [thetaStar_of_mem haE, thetaStar_of_mem hbE]
      exact inf_le_left
    ·
      obtain ⟨B, hB, hEB, hbB⟩ := S.exists_complement h hb hbE
      rw [thetaStar_of_mem haE, thetaStar_of_not_mem hbE, ← hW B hB hEB,
        (h.wTilde_properties S hB hEB).1 b hbB hb1]
      exact inf_le_left
    ·
      obtain ⟨B, hB, hEB, haB⟩ := S.exists_complement h ha haE
      rw [thetaStar_of_not_mem haE, thetaStar_of_mem hbE, hEcent b hbE hb1,
        ← hW B hB hEB, ← h.thetaTilde_eq_inf_centralizer S.mem.1 ha ha1]
      exact le_thetaSup haB ha1
    · by_cases hab : Subgroup.zpowers a = Subgroup.zpowers b
      · rw [thetaStar_of_not_mem haE, thetaStar_of_not_mem hbE,
          h.isFunctor.eq_of_zpowers_eq ha ha1 hb hb1 hab]
        exact inf_le_left
      · have hba : b ∉ Subgroup.zpowers a := fun hmem =>
          hab (h.line_eq_zpowers (h.zpowers_mem_E1 ha ha1) hmem hb1)
        have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
          inf_eq_bot_of_not_le h.prime (h.card_zpowers hb hb1)
            fun hle => hba (hle (Subgroup.mem_zpowers b))
        have hT := h.zpowers_sup_mem_E2 ha hb ha1 hb1 hdisj
        have haT : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
          Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
        have hbT : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
        rw [thetaStar_of_not_mem haE, thetaStar_of_not_mem hbE]
        by_cases hET : E ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b
        ·
          rintro x ⟨hxK, hxc⟩
          have hxa : x ∈ Subgroup.centralizer {a} :=
            h.isFunctor.le_centralizer a ha ha1 (kOf_le _ hxK)
          have hxE : x ∈ Subgroup.centralizer (E : Set G) := by
            have : x ∈ Subgroup.centralizer
                ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
              rw [centralizer_sup, centralizer_zpowers_eq_singleton,
                centralizer_zpowers_eq_singleton]
              exact ⟨hxa, hxc⟩
            exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hET) this
          obtain ⟨Ba, hBa, hEBa, haBa⟩ := S.exists_complement h ha haE
          obtain ⟨Bb, hBb, hEBb, hbBb⟩ := S.exists_complement h hb hbE
          have hxW : x ∈ W := by
            rw [← hW Ba hBa hEBa]
            refine le_thetaSup (θ := thetaTilde θ E) haBa ha1 ?_
            rw [h.thetaTilde_eq_inf_centralizer S.mem.1 ha ha1]
            exact ⟨hxK, hxE⟩
          have : x ∈ wTilde θ E Bb ⊓ Subgroup.centralizer {b} := ⟨hW Bb hBb hEBb ▸ hxW, hxc⟩
          rw [(h.wTilde_properties S hBb hEBb).1 b hbBb hb1] at this
          exact this.1
        · have hET' : E ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥ := by
            rw [inf_comm]
            exact inf_eq_bot_of_not_le h.prime (S.mem.2.trans (pow_one p)) hET
          exact (h.isFunctor_kOf S hT hET').balance a haT ha1 b hbT hb1
  refine ⟨fun a ha ha1 => ?_, fun a ha ha1 => ?_, fun a ha ha1 => ?_, hbal⟩
  · by_cases haE : a ∈ E
    · rw [thetaStar_of_mem haE]
      exact hWc.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haE))
    · rw [thetaStar_of_not_mem haE]
      exact (kOf_le _).trans (h.isFunctor.le_centralizer a ha ha1)
  · by_cases haE : a ∈ E
    · rw [thetaStar_of_mem haE]
      exact (h.isFunctor.coprime_thetaOf S.mem.1 hE0).coprime_dvd_right
        (Subgroup.card_dvd_of_le hWE)
    · rw [thetaStar_of_not_mem haE]
      exact (h.isFunctor.coprime a ha ha1).coprime_dvd_right
        (Subgroup.card_dvd_of_le (kOf_le _))
  · by_cases haE : a ∈ E
    · rw [thetaStar_of_mem haE]
      exact hWN
    · rw [thetaStar_of_not_mem haE]
      exact le_normalizer_kOf_of_le_normalizer (h.isFunctor.normalized a ha ha1)

theorem kOf_thetaOf_le_wTilde
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    kOf (thetaOf θ E) ≤ wTilde θ E B := by
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 S.mem
  have hBN : B ≤ Subgroup.normalizer (thetaOf θ E : Set G) :=
    hB.1.trans (h.isFunctor.normalizes_thetaOf S.mem.1)
  have hgen := iSup_inf_centralizer h.prime (h.isElemAbelian_of_le hB.1) hB.2.ge
    (le_normalizer_kOf_of_le_normalizer hBN)
    ((h.isFunctor.coprime_thetaOf S.mem.1 hE0).coprime_dvd_right
      (Subgroup.card_dvd_of_le (kOf_le _)))
  rw [← hgen]
  exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
    (h.kOf_thetaOf_inf_centralizer_le S hB hEB hb hb1).trans (le_thetaSup hb hb1)

theorem kOf_eq_and_wTilde_eq
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {W : Subgroup G}
    (hW : ∀ B ∈ signalizerFunctorEk p 2 A, E ⊓ B = ⊥ → wTilde θ E B = W) :
    (∀ a ∈ A, a ∉ E → kOf (θ a) = θ a) ∧ W = thetaOf θ E := by
  have hfun := h.isFunctor_thetaStar S hW
  obtain ⟨B₀, hB₀, hEB₀⟩ := S.exists_complement_some h
  have hWE : W ≤ thetaOf θ E := by
    rw [← hW B₀ hB₀ hEB₀]
    exact (h.wTilde_le S hB₀ hEB₀).1
  have hKW : kOf (thetaOf θ E) ≤ W := hW B₀ hB₀ hEB₀ ▸ h.kOf_thetaOf_le_wTilde S hB₀ hEB₀
  have heq := h.eq_of_kOf_le_of_le hfun (fun a ha ha1 => ?_) fun a ha ha1 => ?_
  · refine ⟨fun a ha haE => ?_, ?_⟩
    · have ha1 : a ≠ 1 := fun e => haE (e ▸ E.one_mem)
      rw [← thetaStar_of_not_mem (W := W) haE]
      exact heq a ha ha1
    · obtain ⟨e, he, he1⟩ := h.exists_ne_one_of_mem_E1 S.mem
      have h1 := heq e (S.mem.1 he) he1
      rw [thetaStar_of_mem he, ← h.thetaOf_line S.mem he he1] at h1
      exact h1
  · by_cases haE : a ∈ E
    · rw [thetaStar_of_mem haE, ← h.thetaOf_line S.mem haE ha1]
      exact hKW
    · rw [thetaStar_of_not_mem haE]
  · by_cases haE : a ∈ E
    · rw [thetaStar_of_mem haE]
      exact hWE.trans (thetaOf_le_apply haE ha1)
    · rw [thetaStar_of_not_mem haE]
      exact kOf_le _

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
