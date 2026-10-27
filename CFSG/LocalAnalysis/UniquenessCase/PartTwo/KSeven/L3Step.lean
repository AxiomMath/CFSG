module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Generate
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L3Fixed
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3U3Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open Subgroup

@[expose] def GoodL3 (J : Type) [Group J] : Prop :=
  Finite J ∧ 3 ∣ Nat.card J ∧ ¬ 9 ∣ Nat.card J ∧ ¬ 7 ∣ Nat.card J ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 2 ∧
      Nonempty (J ≃* projectiveSL 3 K)

theorem goodL3_of_mulEquiv (J J' : Type) [Group J] [Group J'] (e : J ≃* J') (h : GoodL3 J) :
    GoodL3 J' := by
  obtain ⟨hfin, h3, h9, h7, ⟨K, hK, hKf, hq, ⟨f⟩⟩⟩ := h
  have hcard : Nat.card J' = Nat.card J := (Nat.card_congr e.toEquiv).symm
  haveI : Finite J := hfin
  refine ⟨Finite.of_equiv J e.toEquiv, ?_, ?_, ?_,
    ⟨K, hK, hKf, hq, ⟨e.symm.trans f⟩⟩⟩
  · rw [hcard]; exact h3
  · rw [hcard]; exact h9
  · rw [hcard]; exact h7

theorem l3_stepConcl_zpowers {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 2) (h9 : ¬ 9 ∣ Nat.card (projectiveSL 3 K))
    (h7 : ¬ 7 ∣ Nat.card (projectiveSL 3 K)) (σ : K ≃+* K) (hσ : orderOf σ = 7)
    (hK : Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ 7)
    (Z : Subgroup (projectiveSL 3 K)) (hZ3 : Nat.card Z = 3)
    (hZ : ∀ w ∈ Subgroup.zpowers (fieldAut 3 K σ), ∀ z ∈ Z, w z = z) :
    StepConcl GoodL3 (Subgroup.zpowers (fieldAut 3 K σ)) Z := by
  classical
  set k := semilinearFixedSubfield σ with hk
  set W₀ : Subgroup (MulAut (projectiveSL 3 K)) :=
    Subgroup.zpowers (fieldAut 3 K σ) with hWdef
  set F : Subgroup (projectiveSL 3 K) := fixedBy W₀ with hFdef
  set j : projectiveSL 3 ↥k →* projectiveSL 3 K :=
    CFSG.RankThree.PartOne.linearSubfieldInclusion 3 k with hjdef
  have hinj : Function.Injective j :=
    CFSG.RankThree.PartOne.linearSubfieldInclusion_injective (by norm_num : 0 < 3) k
  have hFrange : F = j.range :=
    fixedBy_zpowers_fieldAut_eq_range σ hσ h7
  have hZF : Z ≤ F := by
    intro z hz
    rw [hFdef, hWdef, mem_fixedBy]
    exact fun w hw => hZ w hw z hz
  have hWcard : Nat.card W₀ = 7 := by
    rw [hWdef, Nat.card_zpowers,
      CFSG.RankThree.PartOne.KCLinearSubfield.orderOf_fieldAut (n := 3) (by norm_num) σ, hσ]
  have hW : IsPGroup 7 W₀ := IsPGroup.of_card (by rw [hWcard, pow_one])
  have hperf_of (L : Type) [Field L] : Group.IsPerfect (projectiveSL 3 L) := by
    have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) L) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num : 3 ≤ 3)
    haveI := hSL
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (scalars 3 L))
      (QuotientGroup.mk'_surjective (scalars 3 L))
  have hFperf_range : Group.IsPerfect ↥j.range := by
    haveI : Group.IsPerfect (projectiveSL 3 ↥k) := hperf_of ↥k
    exact Group.IsPerfect.ofSurjective (f := (MonoidHom.ofInjective hinj).toMonoidHom)
      (MonoidHom.ofInjective hinj).surjective
  have hFperf : Group.IsPerfect ↥F :=
    Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hFrange).symm.toMonoidHom)
      (MulEquiv.subgroupCongr hFrange).symm.surjective
  have hcomm : ⁅F, F⁆ = F := by
    haveI : Group.IsPerfect ↥F := hFperf
    exact Subgroup.commutator_eq_self (H := F)
  have hkmod : Nat.card ↥k % 3 = 2 := by
    have h := hq
    rw [hK, Nat.pow_mod] at h
    have hcases : Nat.card ↥k % 3 = 0 ∨ Nat.card ↥k % 3 = 1 ∨ Nat.card ↥k % 3 = 2 := by
      have hlt : Nat.card ↥k % 3 < 3 := Nat.mod_lt _ (by norm_num)
      omega
    rcases hcases with h0 | h1 | h2
    · rw [h0] at h; norm_num at h
    · rw [h1] at h; norm_num at h
    · exact h2
  obtain ⟨h3F, h9F, h7F⟩ := card_facts_of_le (J := projectiveSL 3 K) hZF hZ3 h9 h7
  have hGoodF : GoodL3 ↥F := by
    refine ⟨inferInstance, h3F, h9F, h7F, ⟨↥k, inferInstance, inferInstance, hkmod, ?_⟩⟩
    exact ⟨(MulEquiv.subgroupCongr hFrange).trans (MonoidHom.ofInjective hinj).symm⟩
  have hGoodStep : GoodL3 ↥⁅F, F⁆ :=
    goodL3_of_mulEquiv ↥F ↥⁅F, F⁆ (MulEquiv.subgroupCongr hcomm.symm) hGoodF
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨fn, hp, hcardK'⟩ := FiniteField.card K (ringChar K)
  let p := ringChar K
  let f : ℕ := (fn : ℕ)
  have hf : 1 ≤ f := fn.pos
  have hcardK : Nat.card K = p ^ f := by
    rw [Nat.card_eq_fintype_card, hcardK']
  have hq' : p ^ f % 3 = 2 := by
    rw [← hcardK]
    exact hq
  have hLie : CFSG.Blueprint.LieModel (projectiveSL 3 K) .PSL 3 p f := by
    refine Or.inl ⟨by decide, ?_⟩
    refine ⟨⟨hp, hf, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance,
      hcardK, ?_⟩
    exact ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)⟩
  obtain ⟨C, hC_cent, hCcyc, hCcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.exists_cyclic_le_centralizer_of_card_three
      (S := projectiveSL 3 K) (p := p) (f := f) (D := Z) (Or.inl ⟨hq', hLie⟩) hZ3
  have hC_norm : C ≤ normalizer (Z : Set (projectiveSL 3 K)) :=
    hC_cent.trans (Subgroup.centralizer_le_normalizer (Z : Set (projectiveSL 3 K)))
  have hCcardK : Nat.card C = Nat.card K ^ 2 - 1 := by
    rw [hCcard, ← hcardK]
  have hnorm_ge : Nat.card K ^ 2 - 1 ≤
      Nat.card (normalizer (Z : Set (projectiveSL 3 K))) := by
    rw [← hCcardK]
    exact Subgroup.card_le_of_le hC_norm
  have hFcard : Nat.card F = Nat.card (projectiveSL 3 ↥k) := by
    have h1 : Nat.card F = Nat.card ↥j.range :=
      Nat.card_congr (MulEquiv.subgroupCongr hFrange).toEquiv
    exact h1.trans (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hSLcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) ↥k) =
      Nat.card ↥k ^ 3 * ((Nat.card ↥k ^ 2 - 1) * (Nat.card ↥k ^ 3 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ↥k) (n := 3)
      (by norm_num)]
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide]
    norm_num
  have hprojle : Nat.card (projectiveSL 3 ↥k) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) ↥k) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_projectiveSL]
    exact Nat.div_le_self _ _
  have hSLle : Nat.card (Matrix.SpecialLinearGroup (Fin 3) ↥k) ≤ Nat.card ↥k ^ 8 := by
    rw [hSLcard]
    calc Nat.card ↥k ^ 3 * ((Nat.card ↥k ^ 2 - 1) * (Nat.card ↥k ^ 3 - 1))
        ≤ Nat.card ↥k ^ 3 * (Nat.card ↥k ^ 2 * Nat.card ↥k ^ 3) := by
          gcongr
          · exact Nat.sub_le _ _
          · exact Nat.sub_le _ _
      _ = Nat.card ↥k ^ 8 := by ring
  have hFle : Nat.card F ≤ Nat.card ↥k ^ 8 := hFcard.trans_le (hprojle.trans hSLle)
  have hq0 : 2 ≤ Nat.card ↥k := by
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hcases : Nat.card ↥k = 0 ∨ Nat.card ↥k = 1 ∨ 2 ≤ Nat.card ↥k := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0] at hK; omega
    · rw [h1] at hkmod; norm_num at hkmod
    · exact h2
  have hKsq : Nat.card K ^ 2 = Nat.card ↥k ^ 14 := by
    rw [hK, ← pow_mul]
  have hbig : Nat.card ↥k ^ 8 < Nat.card K ^ 2 - 1 := by
    rw [hKsq]
    have hq0pos : 0 < Nat.card ↥k := by omega
    have hq6 : 64 ≤ Nat.card ↥k ^ 6 := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ Nat.card ↥k ^ 6 := Nat.pow_le_pow_left hq0 6
    have hsplit : Nat.card ↥k ^ 14 = Nat.card ↥k ^ 8 * Nat.card ↥k ^ 6 := by
      rw [← pow_add]
    have h1 : 1 ≤ Nat.card ↥k ^ 8 := Nat.one_le_pow 8 (Nat.card ↥k) hq0pos
    have h2 : Nat.card ↥k ^ 8 + 1 < Nat.card ↥k ^ 14 := by nlinarith
    omega
  have hcard : Nat.card F < Nat.card (normalizer (Z : Set (projectiveSL 3 K))) :=
    hFle.trans_lt (hbig.trans_le hnorm_ge)
  have hrig : ∀ α : MulAut (projectiveSL 3 K),
      (∀ x ∈ fixedBy W₀, α x = x) → α ∈ W₀ := by
    intro α hα
    rw [hWdef]
    exact mem_zpowers_fieldAut_of_fixes σ hσ h7 α (by simpa [hWdef, hFdef] using hα)
  have hpair : ∀ n : projectiveSL 3 K,
      (fixedBy W₀).map (MulAut.conj n).toMonoidHom ≠ fixedBy W₀ →
      fixedBy W₀ ⊔ (fixedBy W₀).map (MulAut.conj n).toMonoidHom = ⊤ := by
    intro n hn
    exact fixedBy_sup_conj_eq_top σ hσ hK h7 n (by simpa [hWdef] using hn)
  have hgen : normalizer (Z : Set (projectiveSL 3 K)) ⊔ F = ⊤ := by
    have hcenter : Subgroup.center (projectiveSL 3 K) = ⊥ :=
      CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num : 3 ≤ 3)
    have h7' : ¬ 7 ∣ Nat.card (projectiveSL 3 K) := h7
    have h := normalizer_sup_fixedBy_eq_top (J := projectiveSL 3 K) hcenter h7' W₀ hW hrig Z
      hcard hpair
    simpa [hFdef] using h
  unfold StepConcl
  refine ⟨?_, ?_, ?_⟩
  · simpa [hFdef] using hGoodStep
  · simpa [hFdef] using (hcomm ▸ hZF)
  · rw [← hcomm] at hgen
    simpa [hFdef] using hgen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
