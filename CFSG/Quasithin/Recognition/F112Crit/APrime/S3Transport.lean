module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type} [Group G] {G₀ G₁ G₂ T : Subgroup G}

theorem mem_nbrs_smul {δ ε : CosetGeom G₀ G₁ G₂} (g : ↥G₀) :
    ε ∈ nbrs (g • δ) ↔ g⁻¹ • ε ∈ nbrs δ := by
  have h := smul_adj (G₀ := G₀) (G₁ := G₁) (G₂ := G₂) g (u := δ) (v := g⁻¹ • ε)
  simpa [nbrs] using h

theorem nbrs_smul (g : ↥G₀) (δ : CosetGeom G₀ G₁ G₂) :
    nbrs (g • δ) = g • nbrs δ := by
  ext ε
  rw [Set.mem_smul_set, mem_nbrs_smul]
  constructor
  · intro h
    exact ⟨g⁻¹ • ε, h, by simp⟩
  · rintro ⟨ε', hε', rfl⟩
    simpa using hε'

theorem charTwo_conjSub (g : G) {H : Subgroup G} (h : CharTwo H) :
    CharTwo (conjSub g H) := by
  unfold CharTwo at h ⊢
  rw [pCoreOf_conjSub, conjSub_centralizer, ← conjSub_inf]
  exact conjSub_mono g h

theorem relIndex_conjSub (g : G) (A B : Subgroup G) :
    (conjSub g A).relIndex (conjSub g B) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective

theorem exists_pow_two_eq_one_conj {t : G} (g : G)
    (h : ∃ k : ℕ, t ^ 2 ^ k = 1) : ∃ k : ℕ, (g * t * g⁻¹) ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [← MulAut.conj_apply, ← map_pow, hk, map_one]

theorem S3Point.smul {δ : CosetGeom G₀ G₁ G₂} (h : S3Point G₀ G₁ G₂ δ) (g : ↥G₀) :
    S3Point G₀ G₁ G₂ (g • δ) where
  charTwo := by
    rw [stab_smul]
    exact charTwo_conjSub (g : G) h.charTwo
  ncard_nbrs := by
    rw [nbrs_smul, Set.ncard_smul_set]
    exact h.ncard_nbrs
  le_pCoreOf_of_le_ballStab := by
    intro P hPball hP
    have hle : conjSub (g : G)⁻¹ P ≤ ballStab 1 δ := by
      rw [ballStab_smul (g := g) 1 δ] at hPball
      exact (le_conjSub_iff (g := (g : G))).mp hPball
    have hp := h.le_pCoreOf_of_le_ballStab (conjSub (g : G)⁻¹ P) hle (F7.isPGroup_conjSub hP)
    rw [stab_smul, pCoreOf_conjSub, ← conjSub_inv_conjSub (g := (g : G)) P]
    exact conjSub_mono (g : G) hp
  relIndex_le_two := by
    intro ε hε P hPle hP
    have hε' : g⁻¹ • ε ∈ nbrs δ := (mem_nbrs_smul g).mp hε
    have hPle' : conjSub (g : G)⁻¹ P ≤ stab δ ⊓ stab (g⁻¹ • ε) := by
      refine le_inf ?_ ?_
      · have h1 : P ≤ conjSub (g : G) (stab δ) := by
          rw [← stab_smul (g := g) (γ := δ)]
          exact hPle.trans inf_le_left
        exact (le_conjSub_iff (g := (g : G))).mp h1
      · have h2 : P ≤ conjSub (g : G) (stab (g⁻¹ • ε)) := by
          have hthis : P ≤ stab ε := hPle.trans inf_le_right
          rwa [← smul_inv_smul g ε, stab_smul] at hthis
        exact (le_conjSub_iff (g := (g : G))).mp h2
    have hmain := h.relIndex_le_two (g⁻¹ • ε) hε' (conjSub (g : G)⁻¹ P) hPle'
      (F7.isPGroup_conjSub hP)
    rw [stab_smul, pCoreOf_conjSub, ← conjSub_inv_conjSub (g := (g : G)) P, ← conjSub_inf,
      relIndex_conjSub]
    exact hmain
  exists_two_elt := by
    intro ε hε
    obtain ⟨t, ht, hpow, htnot⟩ := h.exists_two_elt (g⁻¹ • ε) ((mem_nbrs_smul g).mp hε)
    refine ⟨(g : G) * t * (g : G)⁻¹, ?_, ?_, ?_⟩
    · have hmem : (g : G) * t * (g : G)⁻¹ ∈
          conjSub (g : G) (stab δ ⊓ stab (g⁻¹ • ε)) := mul_mem_conjSub ht
      rw [conjSub_inf, ← stab_smul (g := g) (γ := δ),
        ← stab_smul (g := g) (γ := g⁻¹ • ε), smul_inv_smul] at hmem
      exact hmem
    · exact exists_pow_two_eq_one_conj (g : G) hpow
    · intro hconj
      apply htnot
      rw [stab_smul, pCoreOf_conjSub] at hconj
      have hmem := mem_conjSub.mp hconj
      have e : (g : G)⁻¹ * ((g : G) * t * (g : G)⁻¹) * (g : G) = t := by group
      rwa [e] at hmem
  smul_ne := by
    intro f hfstab hfpow hfnot ε hε hfε ε' hε' hne
    set f' : ↥G₀ := g⁻¹ * f * g with hf'def
    have hf'coe : (f' : G) = (g : G)⁻¹ * (f : G) * (g : G) := by
      simp [hf'def]
    have hf'stab : (f' : G) ∈ stab δ := by
      rw [hf'coe]
      exact mem_conjSub.mp (by rwa [stab_smul] at hfstab)
    have hf'pow : ∃ k : ℕ, (f' : G) ^ 2 ^ k = 1 := by
      rw [hf'coe]
      simpa using exists_pow_two_eq_one_conj (g := (g : G)⁻¹) hfpow
    have hf'not : (f' : G) ∉ pCoreOf 2 (stab δ) := by
      intro hmem
      apply hfnot
      rw [stab_smul, pCoreOf_conjSub]
      have hconj := mul_mem_conjSub (g := (g : G)) hmem
      rw [hf'coe] at hconj
      have e : (g : G) * ((g : G)⁻¹ * (f : G) * (g : G)) * (g : G)⁻¹ = (f : G) := by group
      rwa [e] at hconj
    have hne' : g⁻¹ • ε' ≠ g⁻¹ • ε := by
      intro h
      exact hne (by simpa using congrArg (fun x => g • x) h)
    have hε'' : g⁻¹ • ε' ∈ nbrs δ := (mem_nbrs_smul g).mp hε'
    have hε0 : g⁻¹ • ε ∈ nbrs δ := (mem_nbrs_smul g).mp hε
    intro hfε'
    refine h.smul_ne f' hf'stab hf'pow hf'not (g⁻¹ • ε) hε0 ?_ (g⁻¹ • ε') hε'' hne' ?_
    · rw [hf'def, mul_smul, mul_smul, smul_inv_smul, hfε]
    · rw [hf'def, mul_smul, mul_smul, smul_inv_smul, hfε']
  exists_swap := by
    intro ε₁ hε₁ ε₂ hε₂ hne
    have hne' : g⁻¹ • ε₁ ≠ g⁻¹ • ε₂ := by
      intro h
      exact hne (by simpa using congrArg (fun x => g • x) h)
    obtain ⟨k, hk, hk1, hk2⟩ := h.exists_swap (g⁻¹ • ε₁) ((mem_nbrs_smul g).mp hε₁)
      (g⁻¹ • ε₂) ((mem_nbrs_smul g).mp hε₂) hne'
    refine ⟨g * k * g⁻¹, ?_, ?_, ?_⟩
    · rw [stab_smul]
      simpa using mul_mem_conjSub hk
    · rw [mul_smul, mul_smul, hk1, smul_inv_smul]
    · rw [mul_smul, mul_smul, hk2, smul_inv_smul]
  exists_swap_fix := by
    intro ε hε ε₁ hε₁ ε₂ hε₂ h1 h2 h12
    have h1' : g⁻¹ • ε₁ ≠ g⁻¹ • ε := by
      intro h
      exact h1 (by simpa using congrArg (fun x => g • x) h)
    have h2' : g⁻¹ • ε₂ ≠ g⁻¹ • ε := by
      intro h
      exact h2 (by simpa using congrArg (fun x => g • x) h)
    have h12' : g⁻¹ • ε₁ ≠ g⁻¹ • ε₂ := by
      intro h
      exact h12 (by simpa using congrArg (fun x => g • x) h)
    obtain ⟨k, hk, hk0, hk1, hk2⟩ := h.exists_swap_fix (g⁻¹ • ε) ((mem_nbrs_smul g).mp hε)
      (g⁻¹ • ε₁) ((mem_nbrs_smul g).mp hε₁) (g⁻¹ • ε₂) ((mem_nbrs_smul g).mp hε₂) h1' h2' h12'
    refine ⟨g * k * g⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [stab_smul]
      simpa using mul_mem_conjSub hk
    · rw [mul_smul, mul_smul, hk0, smul_inv_smul]
    · rw [mul_smul, mul_smul, hk1, smul_inv_smul]
    · rw [mul_smul, mul_smul, hk2, smul_inv_smul]
  transitive_of_normal := by
    intro N hNle hNnorm hwit ε hε ε' hε'
    have hN'le : conjSub (g : G)⁻¹ N ≤ stab δ := by
      have h1 : N ≤ conjSub (g : G) (stab δ) := by
        rw [← stab_smul (g := g) (γ := δ)]
        exact hNle
      exact (le_conjSub_iff (g := (g : G))).mp h1
    have hN'norm : stab δ ≤ Subgroup.normalizer (conjSub (g : G)⁻¹ N : Set G) := by
      have h1 : conjSub (g : G) (stab δ) ≤ Subgroup.normalizer (N : Set G) := by
        rw [← stab_smul (g := g) (γ := δ)]
        exact hNnorm
      have h2 := (conjSub_le_iff (g := (g : G))).mp h1
      rwa [← conjSub_normalizer] at h2
    obtain ⟨f, hfN, hfpow, hfnot⟩ := hwit
    have hf'N : (g : G)⁻¹ * f * (g : G) ∈ conjSub (g : G)⁻¹ N := by
      simpa using mul_mem_conjSub (g := (g : G)⁻¹) hfN
    have hf'pow : ∃ k : ℕ, ((g : G)⁻¹ * f * (g : G)) ^ 2 ^ k = 1 := by
      simpa using exists_pow_two_eq_one_conj (g := (g : G)⁻¹) hfpow
    have hf'not : (g : G)⁻¹ * f * (g : G) ∉ pCoreOf 2 (stab δ) := by
      intro hmem
      apply hfnot
      rw [stab_smul, pCoreOf_conjSub]
      have hconj := mul_mem_conjSub (g := (g : G)) hmem
      have e : (g : G) * ((g : G)⁻¹ * f * (g : G)) * (g : G)⁻¹ = f := by group
      rwa [e] at hconj
    obtain ⟨k, hkN, hksmul⟩ := h.transitive_of_normal (conjSub (g : G)⁻¹ N) hN'le hN'norm
      ⟨(g : G)⁻¹ * f * (g : G), hf'N, hf'pow, hf'not⟩
      (g⁻¹ • ε) ((mem_nbrs_smul g).mp hε) (g⁻¹ • ε') ((mem_nbrs_smul g).mp hε')
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · have hmem := mul_mem_conjSub (g := (g : G)) hkN
      rwa [conjSub_inv_conjSub] at hmem
    · rw [mul_smul, mul_smul, hksmul, smul_inv_smul]

theorem LocalS3.of_s3Point_γ₁ (hyp : AmalgamHyp G₀ G₁ G₂ T)
    (h : S3Point G₀ G₁ G₂ (γ₁ G₀ G₁ G₂)) : LocalS3 G₀ G₁ G₂ where
  sup_stab := by
    intro γ ε hγε
    obtain ⟨g, hg | hg⟩ := exists_smul_edge hγε
    · rw [← hg.1, ← hg.2, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂,
        ← conjSub_sup, ← hyp.gen]
      exact F7.conjSub_eq_of_mem g.2
    · rw [sup_comm, ← hg.1, ← hg.2, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂,
        ← conjSub_sup, ← hyp.gen]
      exact F7.conjSub_eq_of_mem g.2
  point := by
    intro δ hδ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hδ
    rw [hg]
    exact h.smul g

end CFSG.Quasithin.F112Crit.APrime

end
