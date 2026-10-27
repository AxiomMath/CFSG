module

public import CFSG.Milestones.ASVolI.A3Aut.C5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBL3
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section C5L3

variable {K : Type} [Field K]

theorem burnsideAut_c5L3_fieldAut_mem_U {m : ℕ} (σ : K ≃+* K) {u : LinearFlag.projectiveSL m K}
    (hu : u ∈ LinearFlag.projUnitriangular m K) :
    LinearFlag.fieldAut m K σ u ∈ LinearFlag.projUnitriangular m K := by
  obtain ⟨U, hU, rfl⟩ := hu
  rw [LinearFlag.fieldAut_proj]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨hlow, hdiag⟩ := LinearFlag.mem_unitriangular.1 hU
  refine LinearFlag.mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hlow i j hij, map_zero]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hdiag i, map_one]

theorem burnsideAut_c5L3_map_fieldAut_U {m : ℕ} (σ : K ≃+* K) :
    (LinearFlag.projUnitriangular m K).map (LinearFlag.fieldAut m K σ).toMonoidHom =
      LinearFlag.projUnitriangular m K := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact burnsideAut_c5L3_fieldAut_mem_U σ hy
  · refine ⟨LinearFlag.fieldAut m K σ⁻¹ x, burnsideAut_c5L3_fieldAut_mem_U σ⁻¹ hx, ?_⟩
    change (LinearFlag.fieldAut m K σ * LinearFlag.fieldAut m K σ⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem burnsideAut_c5L3_isSylow [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (LinearFlag.projUnitriangular 3 K) ⊤ := by
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  rw [← hP]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem burnsideAut_c5_card_units_odd [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : Odd (Nat.card Kˣ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have he : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨k, hk⟩ := he
  exact ⟨k - 1, by omega⟩

theorem burnsideAut_c5L3_inn_relIndex_odd [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    ¬ 2 ∣ (MulAut.conj : LinearFlag.projectiveSL 3 K →* MulAut (LinearFlag.projectiveSL 3 K)).range.relIndex
      (LinearFlag.linearAutGroup 3 K) := by
  rw [LinearFlag.linearAutGroup_eq_range, ← Subgroup.index_comap]
  have hle : (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker ≤
      (MulAut.conj : LinearFlag.projectiveSL 3 K →* MulAut (LinearFlag.projectiveSL 3 K)).range.comap
        (LinearFlag.conjAut 3 K) := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA
    have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have h1 := congrArg Units.val hA
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    obtain ⟨g, hgA⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 3) K,
        Matrix.SpecialLinearGroup.toGL g = A := ⟨⟨_, hdet⟩, Units.ext rfl⟩
    rw [Subgroup.mem_comap, ← hgA, LinearFlag.conjAut_toGL]
    exact ⟨_, rfl⟩
  have h1 := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).range ∣ Nat.card Kˣ :=
    Subgroup.card_subgroup_dvd_card _
  intro h3
  exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat (burnsideAut_c5_card_units_odd hn hK)
    (h1.trans h2))) (even_iff_two_dvd.2 h3)

theorem burnsideAut_c5L3_conjAut_isInnDiag {S : Type} [Group S] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (e : S ≃* LinearFlag.projectiveSL 3 K) (A : GL (Fin 3) K) :
    ChA.IsInnDiagAut S (MulAut.congr e.symm (LinearFlag.conjAut 3 K A)) := by
  have he : (e.trans (burnsideA26_statedToProjSL 3 K).symm).trans (burnsideA26_statedToProjSL 3 K) =
      e := MulEquiv.ext fun x => (burnsideA26_statedToProjSL 3 K).apply_symm_apply (e x)
  refine Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance,
    e.trans (burnsideA26_statedToProjSL 3 K).symm, A, hK, ?_⟩)
  have h := burnsideA26_isProjConjAut (e.trans (burnsideA26_statedToProjSL 3 K).symm) A
  rwa [he] at h

theorem burnsideAut_c5L3_odd_mem [Finite K] {α : MulAut (LinearFlag.projectiveSL 3 K)}
    (hα : Odd (orderOf α)) :
    α ∈ LinearFlag.linearAutGroup 3 K ⊔ (LinearFlag.fieldAut 3 K).range := by
  obtain ⟨A, σ, h⟩ := burnsideA26_ln_odd (by norm_num : 3 ≤ 3)
    (burnsideA26_statedToProjSL 3 K).symm α hα
  have h1 : MulAut.congr ((burnsideA26_statedToProjSL 3 K).symm.trans
      (burnsideA26_statedToProjSL 3 K)) α = α := by
    ext x
    simp [MulAut.congr_apply]
  rw [h1] at h
  rw [h]
  exact Subgroup.mul_mem_sup (LinearFlag.conjAut_mem_linearAutGroup A) ⟨σ, rfl⟩

theorem burnsideAut_c5L3_isProjFieldAut (σ : K ≃+* K) :
    ChA.IsProjFieldAut (StatedSL 3 K) σ
      (MulAut.congr (burnsideA26_statedToProjSL 3 K).symm (LinearFlag.fieldAut 3 K σ)) := by
  have h := burnsideA26_isProjFieldAut (MulEquiv.refl (StatedProj (StatedSL 3 K))) σ
  have h1 : MulAut.congr (MulEquiv.refl (StatedProj (StatedSL 3 K)))
      (MulAut.congr ((MulEquiv.refl _).trans (burnsideA26_statedToProjSL 3 K)).symm
        (LinearFlag.fieldAut 3 K σ)) =
      MulAut.congr (burnsideA26_statedToProjSL 3 K).symm (LinearFlag.fieldAut 3 K σ) := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h1] at h

theorem burnsideAut_a315_L3 {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hn : 2 ≤ n)
    (hL : CFSG.Quasithin.IsPSL 3 2 n ↥L) : ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L := Or.inr (Or.inl hL)
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hL
  haveI : CharP K 2 := burnsideA26_charP_two hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUsyl := burnsideAut_c5L3_isSylow (K := K)
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow (e₀.trans (burnsideA26_statedToProjSL 3 K))
    (burnsideAut_isSylowTwoOf_subgroupOf h.sylow) hUsyl
  have hMZ := burnsideAut_c5_center_eq_bot h e
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  refine burnsideAut_case5_of_model2 h n hn hLie hMZ e he hUsyl
    (IM := LinearFlag.linearAutGroup 3 K) (ΦM := (LinearFlag.fieldAut 3 K).range)
    (CFSG.RankThree.PartTwo.KFacts.innAut_le_linearAutGroup 3 K)
    (burnsideAut_c5L3_inn_relIndex_odd (by omega) hK) ?_ ?_ ?_ ?_ ?_ ?_
    (burnsideAut_solvBorel_projectiveSL3 hK4) ?_
  ·
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.1 hx
    exact Subgroup.subset_closure (burnsideAut_c5L3_conjAut_isInnDiag hK e A)
  ·
    rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  ·
    rintro _ ⟨σ, rfl⟩
    exact CFSG.RankThree.PartTwo.KFacts.standardFieldGraph_le_normalizer
      (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_standardFieldGraph σ)
  ·
    rw [eq_bot_iff]
    rintro _ ⟨hI, ⟨σ, rfl⟩⟩
    rw [(CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_linearAutGroup_iff (by norm_num)).1 hI,
      map_one]
    exact Subgroup.one_mem _
  ·
    rintro _ ⟨σ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (burnsideAut_c5L3_map_fieldAut_U σ)
  ·
    intro b hb
    exact burnsideAut_c5L3_odd_mem (burnsideAut_c5_odd_orderOf h e hb)
  ·
    intro ε hε F hF _ _
    obtain ⟨hcyc, hdvd, σ, -, hpin⟩ := burnsideAut_pinned_of_field (LinearFlag.fieldAut 3 K)
      (CFSG.RankThree.PartOne.KCLinearSubfield.fieldAut_injective (by norm_num)) hcard.2
      (burnsideA26_statedToProjSL 3 K).symm hUsyl burnsideAut_c5L3_map_fieldAut_U
      (fun σ mg => ChA.IsProjFieldAut (StatedSL 3 K) σ mg) burnsideAut_c5L3_isProjFieldAut ε hε F hF
    refine ⟨hcyc, ?_, Or.inr (Or.inl ⟨K, inferInstance, inferInstance,
      ε.trans (burnsideA26_statedToProjSL 3 K).symm, σ, hK, hpin⟩)⟩
    rwa [hcard.1] at hdvd

end C5L3

end CFSG.ASVolI
