module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvGraphInv
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthCentCoord
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LargeExtraspecial.BridgeNat

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalBlocks Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog

private theorem ggOmW5b_polar_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (u v : V) :
    Q (u + v) - Q u - Q v = QuadraticMap.polar Q u v := by
  simp only [QuadraticMap.map_add]
  abel

private theorem ggOmW5b_quad_form_transvection_invariant {K V : Type} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (v : V) (hv : Q v = 1) (u : V) :
    Q (u + (QuadraticMap.polar Q u v) • v) = Q u := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [QuadraticMap.map_add, QuadraticMap.map_smul, QuadraticMap.polar_smul_right, hv]
  simp only [mul_one, smul_eq_mul]
  rw [add_assoc, ← two_mul, h2, zero_mul, add_zero]

private theorem ggOmW5b_even_card {ι K : Type} [Fintype ι] [Field K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) :
    Even (Fintype.card ι) := by
  have hAlt : (QuadraticMap.polarBilin Φ).IsAlt := by
    intro x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
      ← Nat.cast_smul_eq_nsmul (R := K) 2 (Φ x), CharP.cast_eq_zero, zero_smul]
  have h := LinearMap.BilinForm.IsAlt.even_finrank hAlt hΦ
  rwa [Module.finrank_fintype_fun_eq_card] at h

private theorem ggOmW5b_card_arith {n : ℕ} (h8 : 8 ≤ n) (he : Even n) :
    ∃ k : ℕ, n = 2 * k ∧ 3 ≤ k ∧ (n - 2) / 2 = k - 1 := by
  obtain ⟨k, hk⟩ := he
  have hk' : n = 2 * k := by omega
  refine ⟨k, hk', by omega, ?_⟩
  rw [hk']
  omega

private theorem ggOmW5b_commutator_eq_top_of_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : commutator H = ⊤) : commutator G = ⊤ := by
  have hmap : (commutator G).map e.toMonoidHom = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  rw [h] at hmap
  rw [Subgroup.eq_top_iff']
  intro x
  have hx : e x ∈ (commutator G).map e.toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_top _
  rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hx

private theorem ggOmW5b_reindex_nondegenerate {ι K : Type} [Field K]
    {d : ℕ} (e : ι ≃ Fin d) (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) :
    (QuadraticMap.polarBilin (reindexQuadraticForm e Φ)).Nondegenerate := by
  exact CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv
    (reindexQuadraticIsometry e Φ) hΦ

private theorem ggOmW5b_reindex_value {ι K : Type} [Field K]
    {d : ℕ} (e : ι ≃ Fin d) (Φ : QuadraticForm K (ι → K)) (v : ι → K)
    (hv : Φ v = 1) :
    reindexQuadraticForm e Φ (reindexVectorEquiv (K := K) e v) = 1 := by
  rw [reindexQuadraticForm_map, hv]

private theorem ggOmW5b_reindex_transvection {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {d : ℕ} (e : ι ≃ Fin d) (Φ : QuadraticForm K (ι → K)) (t : GL ι K)
    (v : ι → K)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    ∀ u : Fin d → K,
      ((reindexMatrixEquiv e t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u =
        u + (reindexQuadraticForm e Φ (u + reindexVectorEquiv e v) -
          reindexQuadraticForm e Φ u - reindexQuadraticForm e Φ
            (reindexVectorEquiv e v)) • reindexVectorEquiv e v := by
  intro u
  obtain ⟨w, rfl⟩ := (reindexVectorEquiv (K := K) e).surjective u
  have hmat : (↑(reindexMatrixEquiv e t) : Matrix (Fin d) (Fin d) K) *ᵥ
        reindexVectorEquiv e w = reindexVectorEquiv e ((t : Matrix ι ι K) *ᵥ w) := by
    rw [← matrixLinearEquiv_apply, reindexMatrixEquiv_mulVec]
  rw [hmat, ht w, map_add, map_smul]
  rw [← map_add, reindexQuadraticForm_map, reindexQuadraticForm_map, reindexQuadraticForm_map]

private theorem ggOmW5b_reindex_mem_derived_iff {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] {d : ℕ} (e : ι ≃ Fin d) (Φ : QuadraticForm K (ι → K)) (t : GL ι K) :
    reindexMatrixEquiv e t ∈ matrixDerived (reindexQuadraticForm e Φ) ↔
      t ∈ StatedOmega ⇑Φ := by
  rw [← stated_derived_reindex e Φ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem ggOmW5b_map_centralizer_singleton {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map f.toMonoidHom =
      Subgroup.centralizer ({f x} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg f h
  · intro h
    simpa using congrArg f.symm h

private theorem ggOmW5b_map_centralizer {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (C : Subgroup G) :
    (Subgroup.centralizer (C : Set G)).map f.toMonoidHom =
      Subgroup.centralizer ((C.map f.toMonoidHom : Subgroup H) : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h c hc
    rcases hc with ⟨d, hd, rfl⟩
    simpa using congrArg f (h d hd)
  · intro h d hd
    simpa using congrArg f.symm (h (f d) (Subgroup.mem_map_of_mem f.toMonoidHom hd))

private theorem ggOmW5b_map_pCoreOf {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (C : Subgroup G) (p : ℕ) :
    (pCoreOf p C).map f.toMonoidHom = pCoreOf p (C.map f.toMonoidHom) := by
  exact (CFSG.LargeExtraspecial.Bridge.pCoreOf_map p f C).symm

private theorem ggOmW5b_nonempty_equiv_trans {G H P : Type} [Group G] [Group H] [Group P]
    (e : G ≃* H) (h : Nonempty (H ≃* P)) : Nonempty (G ≃* P) := by
  obtain ⟨g⟩ := h
  exact ⟨e.trans g⟩

private theorem ggOmW5bB_gl_ext_of_mulVec {K : Type} [Field K] {d : ℕ}
    {g h : GL (Fin d) K}
    (H : ∀ x : Fin d → K, (g : Matrix (Fin d) (Fin d) K) *ᵥ x =
      (h : Matrix (Fin d) (Fin d) K) *ᵥ x) :
    g = h := by
  exact Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, H x]))

private theorem ggOmW5b_fin_eq_symmetryGL {K : Type} [Field K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) (t : GL (Fin d) K) (hv : Q v = 1)
    (ht : ∀ u : Fin d → K, (t : Matrix (Fin d) (Fin d) K) *ᵥ u =
      u + (Q (u + v) - Q u - Q v) • v) :
    t = symmetryGL Q v := by
  apply ggOmW5bB_gl_ext_of_mulVec
  intro u
  rw [ht u, symmetryGL_mulVec_of_charTwo hv u, ggOmW5b_polar_apply Q u v,
    QuadraticMap.polar_comm Q v u]

private theorem ggOmW5b_fin_symmetryGL_not_mem_derived {K : Type} [Field K]
    [CharP K 2] {k : ℕ} (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (v : Fin (2 * k) → K)
    (hv : Q v = 1) :
    symmetryGL Q v ∉ matrixDerived Q := by
  intro h
  have hv0 : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  letI : Invertible (Q v) := invertibleOfNonzero hv0
  have h2 : CFSG.ClassicalGroups.Orthogonal.reflect Q v ∈
      CFSG.RankThree.Classical2.orthDerived Q := by
    rw [CFSG.RankThree.Classical2.orthDerived, ← matrixLinearIso_symmetryGL]
    exact (CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff
      Q (symmetryGL Q v)).mp h
  have h3 : CFSG.ClassicalGroups.Orthogonal.reflect Q v ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ h2
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at h3
  have h4 : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q v)) = 1 := by
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
    exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ v
  rw [h4] at h3
  exact (by decide : ¬ Even 1) h3.2

private theorem ggOmW5bB_orthDerived_relIndex_two_of_threeSingular {K : Type} [Field K]
    [Fintype K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    (CFSG.RankThree.Classical2.orthDerived Q).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := by
  have hd : 0 < Module.finrank K (Fin d → K) := by
    obtain ⟨T, hT3, -⟩ := hT
    have hle := Submodule.finrank_le T
    omega
  let _ : Nontrivial (Fin d → K) := Module.nontrivial_of_finrank_pos hd
  have hEq : CFSG.RankThree.Classical2.orthDerived Q =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
  rw [hEq]
  exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ

private theorem ggOmW5bB_orthDerived_relIndex_two_of_six {K : Type} [Field K]
    [Fintype K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K (Fin d → K) = 6)
    (hts : ∀ U : Submodule K (Fin d → K), Module.finrank K U = 3 →
      ∃ u ∈ U, Q u ≠ 0) :
    (CFSG.RankThree.Classical2.orthDerived Q).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := by
  have hd : 0 < Module.finrank K (Fin d → K) := by omega
  let _ : Nontrivial (Fin d → K) := Module.nontrivial_of_finrank_pos hd
  have hle := CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six
    hQ hdim hts
  have hEq : CFSG.RankThree.Classical2.orthDerived Q =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ) hle
  rw [hEq]
  exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ

private theorem ggOmW5bB_matrixDerived_relIndex_two {K : Type} [Field K] [Fintype K]
    [CharP K 2] {k : ℕ} (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (matrixDerived Q).relIndex (matrixIsometries Q) = 2 := by
  classical
  have hmapD : (matrixDerived Q).map
      (matrixLinearIso (d := 2 * k) (K := K)).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived Q :=
    CFSG.RankThree.PartOne.AUTSL.map_matrixDerived_linearIso (Q := Q)
  have hmapI : (matrixIsometries Q).map
      (matrixLinearIso (d := 2 * k) (K := K)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.matrixIsometries_map Q
  have hrel : (CFSG.RankThree.Classical2.orthDerived Q).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := by
    by_cases hT : ∃ T : Submodule K (Fin (2 * k) → K),
        Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
    · exact ggOmW5bB_orthDerived_relIndex_two_of_threeSingular Q hQ hT
    · have hk3 : k = 3 := by
        by_contra hkne
        have h4 : 4 ≤ k := by omega
        have hdim : Module.finrank K (Fin (2 * k) → K) = 2 * k := by
          rw [Module.finrank_fintype_fun_eq_card]
          simp
        obtain ⟨T, hT3, hTQ⟩ :=
          CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ h4 hdim
        exact hT ⟨T, hT3, hTQ⟩
      have hdim6 : Module.finrank K (Fin (2 * k) → K) = 6 := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp only [Fintype.card_fin]
        omega
      have hts : ∀ U : Submodule K (Fin (2 * k) → K), Module.finrank K U = 3 →
          ∃ u ∈ U, Q u ≠ 0 := by
        intro U hU
        by_contra h
        push Not at h
        exact hT ⟨U, hU, h⟩
      exact ggOmW5bB_orthDerived_relIndex_two_of_six Q hQ hdim6 hts
  calc
    (matrixDerived Q).relIndex (matrixIsometries Q)
        = ((matrixDerived Q).map
            (matrixLinearIso (d := 2 * k) (K := K)).toMonoidHom).relIndex
            ((matrixIsometries Q).map
              (matrixLinearIso (d := 2 * k) (K := K)).toMonoidHom) :=
          (Subgroup.relIndex_map_map_of_injective (matrixDerived Q) (matrixIsometries Q)
            (matrixLinearIso (d := 2 * k) (K := K)).injective).symm
    _ = (CFSG.RankThree.Classical2.orthDerived Q).relIndex
          (TauCeti.QuadraticMap.orthogonalGroup Q) := by rw [hmapD, hmapI]
    _ = 2 := hrel

private theorem ggOmW5bB_mul_mem_of_relIndex_two {G : Type} [Group G] {D O : Subgroup G}
    (h : D.relIndex O = 2) {x y : G} (hx : x ∈ O) (hy : y ∈ O) (hxD : x ∉ D)
    (hyD : y ∉ D) :
    x * y ∈ D := by
  have h2 : (D.subgroupOf O).index = 2 := h
  have hm : (⟨x, hx⟩ * ⟨y, hy⟩ : O) ∈ D.subgroupOf O :=
    (Subgroup.mul_mem_iff_of_index_two h2).mpr (by
      simp only [Subgroup.mem_subgroupOf]
      exact iff_of_false hxD hyD)
  exact hm

private theorem ggOmW5b_fin_index_two {K : Type} [Field K] [Fintype K] [CharP K 2] {k : ℕ}
    (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∀ x y, x ∈ matrixIsometries Q → y ∈ matrixIsometries Q → x ∉ matrixDerived Q →
      y ∉ matrixDerived Q → x * y ∈ matrixDerived Q := by
  intro x y hx hy hxn hyn
  exact ggOmW5bB_mul_mem_of_relIndex_two
    (ggOmW5bB_matrixDerived_relIndex_two hk Q hQ) hx hy hxn hyn

private theorem ggOmW5b_fin_centralizer_eq {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    Subgroup.centralizer ({symmetryGL Q v} : Set (GL (Fin d) K)) ⊓ matrixDerived Q =
      matrixDerived Q ⊓ symmetryCentralizer Q v := by
  ext g
  simp only [Subgroup.mem_inf, symmetryCentralizer,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hc, hD⟩
    exact ⟨hD, matrixDerived_le_isometries Q hD, hc⟩
  · rintro ⟨hD, -, hc⟩
    exact ⟨hc, hD⟩

private theorem ggOmW5b_fin_sp_equiv {K : Type} [Field K] [Fintype K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (v : Fin (2 * k) → K) (hv : Q v = 1)
    (hidx : ∀ x y, x ∈ matrixIsometries Q → y ∈ matrixIsometries Q → x ∉ matrixDerived Q →
      y ∉ matrixDerived Q → x * y ∈ matrixDerived Q)
    (hz : symmetryGL Q v ∉ matrixDerived Q) :
    Nonempty (↥(Subgroup.centralizer ({symmetryGL Q v} : Set (GL (Fin (2 * k)) K)) ⊓
      matrixDerived Q) ≃* StatedSp (k - 1) K) := by
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord.coord_centralizer_equiv
      Q hQ v hv hidx hz
  exact ⟨(MulEquiv.subgroupCongr (ggOmW5b_fin_centralizer_eq Q v)).trans e⟩

private theorem ggOmW5b_statedSp_simple {K : Type} [Field K] [Fintype K] [CharP K 2]
    (m : ℕ) (hm : 3 ≤ m) : IsSimpleGroup (StatedSp m K) := by
  obtain ⟨k, -, hkcard⟩ := FiniteField.card K 2
  rcases Nat.lt_or_ge (k : ℕ) 2 with hk | hk
  · have hk1 : (k : ℕ) = 1 := by
      have := k.pos
      omega
    have hcard : Nat.card K = 2 := by
      rw [Nat.card_eq_fintype_card, hkcard, hk1]
      norm_num
    exact CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_two hcard hm
  · have h4 : 4 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hkcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk
    exact CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le h4 (by omega)

private theorem ggOmW5b_statedSp_commutator_top {K : Type} [Field K] [Fintype K] [CharP K 2]
    (m : ℕ) (hm : 3 ≤ m) : commutator ↥(StatedSp m K) = ⊤ := by
  have hF : (Infinite K ∨ 4 ≤ Nat.card K) ∨ Nat.card K = 3 ∧ 2 ≤ m ∨
      Nat.card K = 2 ∧ 3 ≤ m := by
    obtain ⟨k, -, hkcard⟩ := FiniteField.card K 2
    rcases Nat.lt_or_ge (k : ℕ) 2 with hk | hk
    · have hk1 : (k : ℕ) = 1 := by
        have := k.pos
        omega
      have h2 : Nat.card K = 2 := by
        rw [Nat.card_eq_fintype_card, hkcard, hk1]
        norm_num
      exact Or.inr (Or.inr ⟨h2, hm⟩)
    · have h4 : 4 ≤ Nat.card K := by
        rw [Nat.card_eq_fintype_card, hkcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk
      exact Or.inl (Or.inr h4)
  have hperf := (CFSG.LieType.Universal.Symplectic.isQuasisimple m K (by omega) hF).1
  haveI : Group.IsPerfect ↥(StatedSp m K) := hperf
  exact Group.IsPerfect.commutator_eq_top

private theorem ggOmW5b_statedSp_pCore_bot {K : Type} [Field K] [Fintype K] [CharP K 2]
    (m : ℕ) (hm : 3 ≤ m) : pCoreOf 2 (⊤ : Subgroup (StatedSp m K)) = ⊥ := by
  haveI : IsSimpleGroup (StatedSp m K) := ggOmW5b_statedSp_simple m hm
  have hnormal : (pCoreOf 2 (⊤ : Subgroup (StatedSp m K))).Normal := by
    rw [pCoreOf]
    exact Subgroup.Normal.map pCore_normal (⊤ : Subgroup (StatedSp m K)).subtype
      (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  have hp : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup (StatedSp m K))) := by
    rw [pCoreOf]
    exact pCore_isPGroup.map (⊤ : Subgroup (StatedSp m K)).subtype
  have hy : orderOf (CFSG.SeitzReduction.SymplecticPilot.nsElt (K := K)
      (⟨0, by omega⟩ : Fin m)) = 3 :=
    CFSG.SeitzReduction.SymplecticPilot.orderOf_nsElt _
  exact CFSG.SeitzReduction.SymplecticPilot.eq_bot_of_normal_of_isPGroup_of_orderOf_three
    hy _ hnormal hp

private theorem ggOmW5b_center_statedSp_bot {K : Type} [Field K] [CharP K 2]
    (m : ℕ) : Subgroup.center (StatedSp m K) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

private theorem ggOmW5bC_q_expand {K U : Type} [Field K] [AddCommGroup U] [Module K U]
    (q : QuadraticForm K U) (x u : U) (c : K) :
    q (x + (c * QuadraticMap.polarBilin q x u) • u) =
      q x + (QuadraticMap.polarBilin q x u) * (QuadraticMap.polarBilin q x u) *
        (c * c * q u + c) := by
  rw [QuadraticMap.map_add q, QuadraticMap.map_smul q,
    QuadraticMap.polar_smul_right q, ← QuadraticMap.polarBilin_apply_apply q]
  simp only [smul_eq_mul]
  ring

private theorem ggOmW5bC_basis_pair_add_ne_zero {K U : Type} [Field K] [AddCommGroup U]
    [Module K U] {n : ℕ} (b : Module.Basis (Fin n) K U) {i j : Fin n} (hij : i ≠ j) :
    b i + b j ≠ 0 := by
  intro h
  have h1 : b.repr (b i + b j) = b.repr 0 := by rw [h]
  rw [map_add, map_zero, b.repr_self, b.repr_self] at h1
  have h2 := congrArg (fun f : Fin n →₀ K => f i) h1
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,
    Finsupp.coe_zero, Pi.zero_apply, add_zero] at h2
  exact one_ne_zero h2

private theorem ggOmW5bC_basis_three_add_ne_zero {K U : Type} [Field K] [AddCommGroup U]
    [Module K U] {n : ℕ} (b : Module.Basis (Fin n) K U) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) :
    b i + b j + b l ≠ 0 := by
  intro h
  have h1 : b.repr (b i + b j + b l) = b.repr 0 := by rw [h]
  rw [map_add, map_add, map_zero, b.repr_self, b.repr_self, b.repr_self] at h1
  have h2 := congrArg (fun f : Fin n →₀ K => f i) h1
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,
    Finsupp.single_eq_of_ne hil, Finsupp.coe_zero, Pi.zero_apply, add_zero] at h2
  exact one_ne_zero h2

private theorem ggOmW5b_no_transvection_invariant_quadratic {K U : Type} [Field K]
    [CharP K 2] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (q : QuadraticForm K U) (B : LinearMap.BilinForm K U) (hB : B.Nondegenerate)
    (hpol : B = QuadraticMap.polarBilin q) (h4 : 4 ≤ Module.finrank K U)
    (hfix : ∀ (x u : U) (c : K), q (x + (c * B x u) • u) = q x) : False := by
  have hpol_apply : ∀ a c : U, QuadraticMap.polar q a c = B a c := fun a c => by
    rw [hpol]
    exact (QuadraticMap.polarBilin_apply_apply q a c).symm
  have hfix' : ∀ (x u : U) (c : K),
      q (x + (c * QuadraticMap.polarBilin q x u) • u) = q x := by
    intro x u c
    rw [← hpol]
    exact hfix x u c
  have hqu : ∀ u : U, u ≠ 0 → q u = 1 := by
    intro u hu
    obtain ⟨x, hx⟩ : ∃ x : U, B x u ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (hB.2 u h)
    have hxu : QuadraticMap.polarBilin q x u ≠ 0 := by
      rw [← hpol]
      exact hx
    have h1 := hfix' x u 1
    have h2 := ggOmW5bC_q_expand q x u 1
    simp only [one_mul] at h1 h2
    rw [h1] at h2
    have h3 : (QuadraticMap.polarBilin q x u) * (QuadraticMap.polarBilin q x u) *
        (q u + 1) = 0 := by
      exact add_left_cancel (by rw [add_zero]; exact h2.symm)
    have hb2 : (QuadraticMap.polarBilin q x u) * (QuadraticMap.polarBilin q x u) ≠ 0 :=
      mul_ne_zero hxu hxu
    have hq1 : q u + 1 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hb2
      · exact h
    have hneg := add_eq_zero_iff_eq_neg.mp hq1
    simpa only [CharTwo.neg_eq] using hneg
  set b := Module.finBasis K U with hbfin
  let i0 : Fin (Module.finrank K U) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K U) := ⟨1, by omega⟩
  let i2 : Fin (Module.finrank K U) := ⟨2, by omega⟩
  let x : U := b i0
  let y : U := b i1
  let z : U := b i2
  have hx0 : x ≠ 0 := (b.linearIndependent).ne_zero i0
  have hy0 : y ≠ 0 := (b.linearIndependent).ne_zero i1
  have hz0 : z ≠ 0 := (b.linearIndependent).ne_zero i2
  have hi01 : i0 ≠ i1 := by
    intro h
    have hv : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp only [i0, i1] at hv
    omega
  have hi02 : i0 ≠ i2 := by
    intro h
    have hv : (i0 : ℕ) = (i2 : ℕ) := congrArg Fin.val h
    simp only [i0, i2] at hv
    omega
  have hi12 : i1 ≠ i2 := by
    intro h
    have hv : (i1 : ℕ) = (i2 : ℕ) := congrArg Fin.val h
    simp only [i1, i2] at hv
    omega
  have hxy : x + y ≠ 0 :=
    ggOmW5bC_basis_pair_add_ne_zero b (i := i0) (j := i1) hi01
  have hxz : x + z ≠ 0 :=
    ggOmW5bC_basis_pair_add_ne_zero b (i := i0) (j := i2) hi02
  have hyz : y + z ≠ 0 :=
    ggOmW5bC_basis_pair_add_ne_zero b (i := i1) (j := i2) hi12
  have hxyz : x + y + z ≠ 0 :=
    ggOmW5bC_basis_three_add_ne_zero b (i := i0) (j := i1) (l := i2) hi01 hi02
  have hqx : q x = 1 := hqu x hx0
  have hqy : q y = 1 := hqu y hy0
  have hqz : q z = 1 := hqu z hz0
  have hqxy : q (x + y) = 1 := hqu (x + y) hxy
  have hqxz : q (x + z) = 1 := hqu (x + z) hxz
  have hqyz : q (y + z) = 1 := hqu (y + z) hyz
  have hqxyz : q (x + y + z) = 1 := hqu (x + y + z) hxyz
  have hBxz : B x z = 1 := by
    have h := QuadraticMap.map_add q x z
    rw [hqxz, hqx, hqz, hpol_apply x z] at h
    rw [CharTwo.add_self_eq_zero (1 : K), zero_add] at h
    exact h.symm
  have hByz : B y z = 1 := by
    have h := QuadraticMap.map_add q y z
    rw [hqyz, hqy, hqz, hpol_apply y z] at h
    rw [CharTwo.add_self_eq_zero (1 : K), zero_add] at h
    exact h.symm
  have hBxyz : B (x + y) z = 1 := by
    have h := QuadraticMap.map_add q (x + y) z
    rw [hqxyz, hqxy, hqz, hpol_apply (x + y) z] at h
    rw [CharTwo.add_self_eq_zero (1 : K), zero_add] at h
    exact h.symm
  have hBadd : B (x + y) z = B x z + B y z := by
    rw [map_add]
    rfl
  rw [hBadd, hBxz, hByz, CharTwo.add_self_eq_zero (1 : K)] at hBxyz
  exact zero_ne_one hBxyz

private theorem ggOmW5b_fin_fixes_v {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (v : Fin (2 * k) → K) (hv : Q v = 1)
    (h : GL (Fin (2 * k)) K)
    (hh : h ∈ Subgroup.centralizer ({symmetryGL Q v} : Set (GL (Fin (2 * k)) K)) ⊓
      matrixDerived Q) :
    (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v = v := by
  have hg : h ∈ matrixIsometries Q := matrixDerived_le_isometries Q hh.2
  exact (mem_centralizer_symmetryGL_iff hQ hv hg).mp hh.1

private theorem ggOmW5bC_restrict_onto {K : Type} [Field K] [Fintype K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (v : Fin (2 * k) → K) (hv : Q v = 1)
    (hidx : ∀ x y, x ∈ matrixIsometries Q → y ∈ matrixIsometries Q → x ∉ matrixDerived Q →
      y ∉ matrixDerived Q → x * y ∈ matrixDerived Q)
    (hz : symmetryGL Q v ∉ matrixDerived Q) :
    ∀ g : ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q v)),
      ∃ h : ↥(matrixDerived Q ⊓ symmetryCentralizer Q v),
        symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) = g := by
  let ρ : symmetryCentralizer Q v →*
      ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q v)) :=
    (symmetryRestrict hQ hv).codRestrict _ (symmetryRestrict_mem hQ hv)
  have hsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : LinearMap.GeneralLinearGroup K (vQuot Q v)) ∈
        (symmetryRestrict hQ hv).range := by
      rw [CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord.range_symmetryRestrict'
        hQ hv]
      exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, Subtype.ext hg⟩
  have hρ : ∀ s, ρ s = 1 ↔ symmetryRestrict hQ hv s = 1 := fun s =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : ∀ s : symmetryCentralizer Q v, ρ s = 1 → s = 1 ∨
      (s : GL (Fin (2 * k)) K) = symmetryGL Q v := by
    intro s hs
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv ((hρ s).mp hs) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  have hz1 : ρ ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ = 1 := by
    rw [hρ, ← MonoidHom.mem_ker, ker_symmetryRestrict hQ hv]
    exact Subgroup.mem_zpowers _
  have hbij :=
    CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord.bijective_restrict_of_index_two
      (matrixIsometries Q) (matrixDerived Q) (symmetryCentralizer Q v) inf_le_left hidx
      (symmetryGL Q v) symmetryGL_mem_symmetryCentralizer hz ρ hsurj hker hz1
  intro g
  obtain ⟨h, hh⟩ := hbij.2 g
  refine ⟨h, ?_⟩
  exact congrArg Subtype.val hh

private theorem ggOmW5bC_restrict_mk_eq_of_mulVec_eq {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (v : Fin (2 * k) → K) (hv : Q v = 1) (g : symmetryCentralizer Q v) (x : vPerp Q v)
    (hx : (g.1 : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ (x : Fin (2 * k) → K) =
      (x : Fin (2 * k) → K)) :
    ((symmetryRestrict hQ hv g : vQuot Q v →ₗ[K] vQuot Q v) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x := by
  rw [symmetryRestrict_mk]
  congr 1
  apply Subtype.ext
  change matrixLinearEquiv g.1 (x : Fin (2 * k) → K) = (x : Fin (2 * k) → K)
  rw [matrixLinearEquiv_apply, hx]

private theorem ggOmW5b_fin_fixed_in_perp {K : Type} [Field K] [Fintype K] [CharP K 2] {k : ℕ}
    (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (v w : Fin (2 * k) → K)
    (hv : Q v = 1)
    (hw : QuadraticMap.polar Q w v = 0)
    (hfix : ∀ h : GL (Fin (2 * k)) K,
      h ∈ (matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) →
      (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w) :
    w ∈ Submodule.span K ({v} : Set (Fin (2 * k) → K)) := by
  by_cases hwspan : w ∈ Submodule.span K ({v} : Set (Fin (2 * k) → K))
  · exact hwspan
  · exfalso
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [QuadraticMap.map_zero] at hv
      exact zero_ne_one hv
    have hwperp : w ∈ vPerp Q v := by
      rw [mem_vPerp, QuadraticMap.polar_comm]
      exact hw
    let a : vQuot Q v := Submodule.Quotient.mk (⟨w, hwperp⟩ : vPerp Q v)
    have ha0 : a ≠ 0 := by
      intro h
      apply hwspan
      have h' : (⟨w, hwperp⟩ : vPerp Q v) ∈ vLine Q v := by
        rw [← Submodule.Quotient.mk_eq_zero]
        exact h
      simpa [vLine] using h'
    obtain ⟨b, hb⟩ : ∃ b : vQuot Q v, vQuotForm Q v a b ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 ((vQuotForm_nondegenerate hQ hv0).1 a h)
    have hb0 : b ≠ 0 := fun hb0 => hb (by rw [hb0, map_zero])
    let τ : ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q v)) :=
      ⟨CFSG.ClassicalGroups.Alternating.symplecticTransvection (vQuotForm Q v)
          (vQuotForm_isAlt Q v) b 1,
        CFSG.ClassicalGroups.Alternating.symplecticTransvection_mem_bilinIsometryGroup
          (vQuotForm_isAlt Q v) b 1⟩
    obtain ⟨h, hh⟩ := ggOmW5bC_restrict_onto Q hQ v hv
      (ggOmW5b_fin_index_two hk Q hQ)
      (ggOmW5b_fin_symmetryGL_not_mem_derived Q hQ v hv) τ
    have hfixa : (h.1 : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w := hfix h.1 h.2
    have hineq : ((symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) :
        vQuot Q v →ₗ[K] vQuot Q v) a) = a :=
      ggOmW5bC_restrict_mk_eq_of_mulVec_eq Q hQ v hv
        (Subgroup.inclusion inf_le_right h) (⟨w, hwperp⟩ : vPerp Q v) (by
          simpa using hfixa)
    have hτa : ((symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) :
        vQuot Q v →ₗ[K] vQuot Q v) a) =
        ((τ.val : LinearMap.GeneralLinearGroup K (vQuot Q v)) :
          vQuot Q v →ₗ[K] vQuot Q v) a := by
      rw [hh]
    have hτmove :
        ((τ.val : LinearMap.GeneralLinearGroup K (vQuot Q v)) :
          vQuot Q v →ₗ[K] vQuot Q v) a ≠ a := by
      intro hcontra
      have happ :
          ((τ.val : LinearMap.GeneralLinearGroup K (vQuot Q v)) :
            vQuot Q v →ₗ[K] vQuot Q v) a =
          a + (1 * vQuotForm Q v a b) • b :=
        CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply
          (vQuotForm_isAlt Q v) b 1 a
      have hzero : (1 * vQuotForm Q v a b) • b = 0 := by
        have h4 : a + (1 * vQuotForm Q v a b) • b = a + 0 := by
          rw [happ] at hcontra
          simpa using hcontra
        exact add_left_cancel h4
      exact smul_ne_zero (mul_ne_zero one_ne_zero hb) hb0 hzero
    exact hτmove (hτa.symm.trans hineq)

private theorem ggOmW5bC_polar_self_v {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v : Fin (2 * k) → K) (hv : Q v = 1) :
    QuadraticMap.polar Q v v = 0 := by
  rw [QuadraticMap.polar_self, hv, two_nsmul]
  exact CharTwo.add_self_eq_zero 1

private noncomputable def ggOmW5bC_sec {K : Type} [Field K] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K) :
    vPerp Q v →ₗ[K] (Fin (2 * k) → K) :=
  (vPerp Q v).subtype +
    ((QuadraticMap.polarBilin Q w).comp (vPerp Q v).subtype).smulRight
      ((QuadraticMap.polar Q w v)⁻¹ • v)

private theorem ggOmW5bC_sec_apply {K : Type} [Field K] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K) (x : vPerp Q v) :
    ggOmW5bC_sec Q v w x =
      (x : Fin (2 * k) → K) +
        QuadraticMap.polar Q w (x : Fin (2 * k) → K) •
          ((QuadraticMap.polar Q w v)⁻¹ • v) := rfl

private theorem ggOmW5bC_sec_vLine {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K)
    (hw : QuadraticMap.polar Q w v ≠ 0) {x : vPerp Q v} (hx : x ∈ vLine Q v) :
    ggOmW5bC_sec Q v w x = 0 := by
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hx
  have hxlam : (x : Fin (2 * k) → K) = lam • v := by simpa using hlam.symm
  rw [ggOmW5bC_sec_apply, hxlam, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  field_simp
  rw [show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, mul_zero]

private noncomputable def ggOmW5bC_sBarV {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K)
    (hw : QuadraticMap.polar Q w v ≠ 0) : vQuot Q v →ₗ[K] (Fin (2 * k) → K) :=
  (vLine Q v).liftQ (ggOmW5bC_sec Q v w)
    (fun x hx => by rw [LinearMap.mem_ker]; exact ggOmW5bC_sec_vLine Q v w hw hx)

private theorem ggOmW5bC_sBarV_mk {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K)
    (hw : QuadraticMap.polar Q w v ≠ 0) (x : vPerp Q v) :
    ggOmW5bC_sBarV Q v w hw (Submodule.Quotient.mk x) = ggOmW5bC_sec Q v w x := by
  rw [ggOmW5bC_sBarV]
  exact Submodule.liftQ_apply (vLine Q v) (ggOmW5bC_sec Q v w) x

private theorem ggOmW5bC_sec_polar {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K)
    (hv : Q v = 1) (x y : vPerp Q v) :
    QuadraticMap.polar Q (ggOmW5bC_sec Q v w x) (ggOmW5bC_sec Q v w y) =
      QuadraticMap.polar Q x y := by
  simp only [ggOmW5bC_sec_apply, QuadraticMap.polar_add_left,
    QuadraticMap.polar_add_right,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq]
  rw [QuadraticMap.polar_comm Q x v, (mem_vPerp Q v).mp x.2,
    (mem_vPerp Q v).mp y.2, ggOmW5bC_polar_self_v Q v hv]
  ring

private noncomputable def ggOmW5bC_qU {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K)
    (hw : QuadraticMap.polar Q w v ≠ 0) : QuadraticForm K (vQuot Q v) :=
  Q.comp (ggOmW5bC_sBarV Q v w hw)

private theorem ggOmW5bC_qU_polar {K : Type} [Field K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (v w : Fin (2 * k) → K)
    (hv : Q v = 1) (hw : QuadraticMap.polar Q w v ≠ 0) :
    QuadraticMap.polarBilin (ggOmW5bC_qU Q v w hw) = vQuotForm Q v := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      rw [vQuotForm_mk, QuadraticMap.polarBilin_apply_apply]
      change QuadraticMap.polar (ggOmW5bC_qU Q v w hw)
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = QuadraticMap.polar Q x y
      change QuadraticMap.polar (Q.comp (ggOmW5bC_sBarV Q v w hw))
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = QuadraticMap.polar Q x y
      rw [QuadraticMap.polar, QuadraticMap.polar, QuadraticMap.comp_apply,
        QuadraticMap.comp_apply, QuadraticMap.comp_apply,
        map_add (ggOmW5bC_sBarV Q v w hw) (Submodule.Quotient.mk x)
          (Submodule.Quotient.mk y)]
      exact ggOmW5bC_sec_polar Q v w hv x y

private theorem ggOmW5bC_sec_equivariant {K : Type} [Field K] [CharP K 2]
    {k : ℕ} (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (v w : Fin (2 * k) → K) (hv : Q v = 1)
    {h : GL (Fin (2 * k)) K} (hh : h ∈ matrixDerived Q ⊓ symmetryCentralizer Q v)
    (hwfix : h *ᵥ w = w) (x z : vPerp Q v)
    (hz : (z : Fin (2 * k) → K) = h *ᵥ (x : Fin (2 * k) → K)) :
    ggOmW5bC_sec Q v w z = h *ᵥ ggOmW5bC_sec Q v w x := by
  have hfixv : h *ᵥ v = v :=
    ggOmW5b_fin_fixes_v Q hQ v hv h (Subgroup.mem_inf.mpr ⟨hh.2.2, hh.1⟩)
  have hO : h ∈ matrixIsometries Q := matrixDerived_le_isometries Q hh.1
  have hwx : QuadraticMap.polar Q w (h *ᵥ (x : Fin (2 * k) → K)) =
      QuadraticMap.polar Q w (x : Fin (2 * k) → K) := by
    have h1 := polar_mulVec_of_mem hO w (x : Fin (2 * k) → K)
    rw [hwfix] at h1
    exact h1
  rw [ggOmW5bC_sec_apply, ggOmW5bC_sec_apply, hz, hwx]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hfixv]

private theorem ggOmW5bC_qU_invariant {K : Type} [Field K] [CharP K 2]
    {k : ℕ} (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (v w : Fin (2 * k) → K) (hv : Q v = 1) (hw : QuadraticMap.polar Q w v ≠ 0)
    (hfix : ∀ h : GL (Fin (2 * k)) K,
      h ∈ (matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) →
      (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w)
    (h : ↥(matrixDerived Q ⊓ symmetryCentralizer Q v)) (b : vQuot Q v) :
    ggOmW5bC_qU Q v w hw
      (((symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) :
        LinearMap.GeneralLinearGroup K (vQuot Q v)) : vQuot Q v →ₗ[K] vQuot Q v) b) =
    ggOmW5bC_qU Q v w hw b := by
  have hwfix : (h.1 : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w := hfix h.1 h.2
  have hsec : ∀ x : vPerp Q v,
      ggOmW5bC_sBarV Q v w hw
        (((symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) :
          LinearMap.GeneralLinearGroup K (vQuot Q v)) : vQuot Q v →ₗ[K] vQuot Q v)
            (Submodule.Quotient.mk x)) =
      (h.1 : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ
        ggOmW5bC_sBarV Q v w hw (Submodule.Quotient.mk x) := by
    intro x
    have hev : matrixLinearEquiv (Subgroup.inclusion inf_le_right h).1 v = v := by
      rw [matrixLinearEquiv_apply]
      exact fix_of_mem_symmetryCentralizer hQ hv (Subgroup.inclusion inf_le_right h).2
    rw [symmetryRestrict_mk, ggOmW5bC_sBarV_mk, ggOmW5bC_sBarV_mk]
    refine ggOmW5bC_sec_equivariant Q hQ v w hv h.2 hwfix x
      (perpEquivOfFix (e := matrixLinearEquiv (Subgroup.inclusion inf_le_right h).1) hev
        (polar_mulVec_of_mem (Subgroup.inclusion inf_le_right h).2.1) x) ?_
    rfl
  induction b using Submodule.Quotient.induction_on with
  | H x =>
    change Q (ggOmW5bC_sBarV Q v w hw
        (((symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) :
          LinearMap.GeneralLinearGroup K (vQuot Q v)) : vQuot Q v →ₗ[K] vQuot Q v)
            (Submodule.Quotient.mk x))) =
      Q (ggOmW5bC_sBarV Q v w hw (Submodule.Quotient.mk x))
    rw [hsec x]
    exact (mem_matrixIsometries_iff Q h.1).mp (matrixDerived_le_isometries Q h.2.1) _

private theorem ggOmW5bC_qU_transvection_invariant {K : Type} [Field K] [Fintype K]
    [CharP K 2] {k : ℕ} (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (v w : Fin (2 * k) → K)
    (hv : Q v = 1) (hw : QuadraticMap.polar Q w v ≠ 0)
    (hfix : ∀ h : GL (Fin (2 * k)) K,
      h ∈ (matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) →
      (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w)
    (x u : vQuot Q v) (c : K) :
    ggOmW5bC_qU Q v w hw (x + (c * vQuotForm Q v x u) • u) = ggOmW5bC_qU Q v w hw x := by
  let τ : ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q v)) :=
    ⟨CFSG.ClassicalGroups.Alternating.symplecticTransvection (vQuotForm Q v)
        (vQuotForm_isAlt Q v) u c,
      CFSG.ClassicalGroups.Alternating.symplecticTransvection_mem_bilinIsometryGroup
        (vQuotForm_isAlt Q v) u c⟩
  obtain ⟨h, hh⟩ := ggOmW5bC_restrict_onto Q hQ v hv
    (ggOmW5b_fin_index_two hk Q hQ) (ggOmW5b_fin_symmetryGL_not_mem_derived Q hQ v hv) τ
  have hτ : ((symmetryRestrict hQ hv (Subgroup.inclusion inf_le_right h) :
      LinearMap.GeneralLinearGroup K (vQuot Q v)) : vQuot Q v →ₗ[K] vQuot Q v) x =
      x + (c * vQuotForm Q v x u) • u := by
    rw [hh]
    exact CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply
      (vQuotForm_isAlt Q v) u c x
  rw [← hτ]
  exact ggOmW5bC_qU_invariant Q hQ v w hv hw hfix h x

private theorem ggOmW5b_fin_fixed_not_perp {K : Type} [Field K] [Fintype K] [CharP K 2] {k : ℕ}
    (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (v w : Fin (2 * k) → K)
    (hv : Q v = 1)
    (hw : QuadraticMap.polar Q w v ≠ 0)
    (hfix : ∀ h : GL (Fin (2 * k)) K,
      h ∈ (matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) →
      (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w) :
    False := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  refine ggOmW5b_no_transvection_invariant_quadratic (ggOmW5bC_qU Q v w hw)
    (vQuotForm Q v) (vQuotForm_nondegenerate hQ hv0) ?_ ?_ ?_
  · exact (ggOmW5bC_qU_polar Q v w hv hw).symm
  · have hfr := finrank_vQuot hQ hv
    omega
  · intro x u c
    exact ggOmW5bC_qU_transvection_invariant hk Q hQ v w hv hw hfix x u c

private theorem ggOmW5b_fin_fixed_vectors {K : Type} [Field K] [Fintype K] [CharP K 2] {k : ℕ}
    (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (v : Fin (2 * k) → K)
    (hv : Q v = 1)
    (w : Fin (2 * k) → K)
    (hfix : ∀ h : GL (Fin (2 * k)) K,
      h ∈ (matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) →
      (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ w = w) :
    w ∈ Submodule.span K ({v} : Set (Fin (2 * k) → K)) := by
  by_cases hw : QuadraticMap.polar Q w v = 0
  · exact ggOmW5b_fin_fixed_in_perp hk Q hQ v w hv hw hfix
  · exact (ggOmW5b_fin_fixed_not_perp hk Q hQ v w hv hw hfix).elim

private theorem ggOmW5b_fin_double_centralizer {K : Type} [Field K] [Fintype K] [CharP K 2]
    {k : ℕ} (hk : 3 ≤ k) (Q : QuadraticForm K (Fin (2 * k) → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (v : Fin (2 * k) → K) (hv : Q v = 1) :
    matrixDerived Q ⊓ Subgroup.centralizer
      ((matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) :
        Set (GL (Fin (2 * k)) K)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hgO : g ∈ matrixIsometries Q := matrixDerived_le_isometries Q hg.1
  have hfixg : ∀ h : GL (Fin (2 * k)) K,
      h ∈ (matrixDerived Q ⊓ symmetryCentralizer Q v : Subgroup (GL (Fin (2 * k)) K)) →
      (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ
        ((g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v) =
        (g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v := by
    intro h hh
    have hfixv : (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v = v :=
      ggOmW5b_fin_fixes_v Q hQ v hv h (Subgroup.mem_inf.mpr ⟨hh.2.2, hh.1⟩)
    have hcomm : h * g = g * h :=
      (Subgroup.mem_centralizer_iff.mp hg.2) h hh
    have hmat : (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *
        (g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) =
        (g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *
          (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) := by
      rw [← Units.val_mul, hcomm, Units.val_mul]
    calc (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ
          ((g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v)
        = ((h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *
            (g : Matrix (Fin (2 * k)) (Fin (2 * k)) K)) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
      _ = ((g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *
            (h : Matrix (Fin (2 * k)) (Fin (2 * k)) K)) *ᵥ v := by rw [hmat]
      _ = (g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ
            ((h : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec]
      _ = (g : Matrix (Fin (2 * k)) (Fin (2 * k)) K) *ᵥ v := by rw [hfixv]
  have hgvspan : (g : Matrix _ _ K) *ᵥ v ∈
      Submodule.span K ({v} : Set (Fin (2 * k) → K)) :=
    ggOmW5b_fin_fixed_vectors hk Q hQ v hv ((g : Matrix _ _ K) *ᵥ v) hfixg
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hgvspan
  have hQgv : Q ((g : Matrix _ _ K) *ᵥ v) = 1 := by
    rw [← hv]
    exact (mem_matrixIsometries_iff Q g).mp hgO v
  rw [← hlam, QuadraticMap.map_smul, hv, smul_eq_mul, mul_one] at hQgv
  have hlam1 : lam = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h4 : (lam - 1) ^ 2 = 0 := by linear_combination hQgv + (1 - lam) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4)
  have hgv : (g : Matrix _ _ K) *ᵥ v = v := by
    rw [← hlam, hlam1, one_smul]
  have hgsym : g ∈ symmetryCentralizer Q v :=
    ⟨hgO, (mem_centralizer_symmetryGL_iff hQ hv hgO).mpr hgv⟩
  have hidx := ggOmW5b_fin_index_two hk Q hQ
  have hz := ggOmW5b_fin_symmetryGL_not_mem_derived Q hQ v hv
  obtain ⟨e⟩ := ggOmW5b_fin_sp_equiv Q hQ v hv hidx hz
  let C1 : Subgroup (GL (Fin (2 * k)) K) :=
    Subgroup.centralizer ({symmetryGL Q v} : Set (GL (Fin (2 * k)) K)) ⊓ matrixDerived Q
  have hC1 : C1 = matrixDerived Q ⊓ symmetryCentralizer Q v :=
    ggOmW5b_fin_centralizer_eq Q v
  have hg1 : g ∈ C1 := by
    rw [hC1]
    exact Subgroup.mem_inf.mpr ⟨hg.1, hgsym⟩
  let g1 : C1 := ⟨g, hg1⟩
  have hcent : e g1 ∈ Subgroup.center (StatedSp (k - 1) K) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨b1, rfl⟩ := e.surjective b
    change e b1 * e g1 = e g1 * e b1
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hbC : (b1 : GL (Fin (2 * k)) K) ∈ matrixDerived Q ⊓ symmetryCentralizer Q v := by
      rw [← hC1]
      exact b1.2
    simpa only [Subgroup.coe_mul] using
      (Subgroup.mem_centralizer_iff.mp hg.2) (b1 : GL (Fin (2 * k)) K) hbC
  rw [ggOmW5b_center_statedSp_bot (K := K) (k - 1)] at hcent
  rw [Subgroup.mem_bot] at hcent
  have hg1one : g1 = 1 := e.injective (by rw [hcent, map_one])
  have hgone : g = 1 := by
    change (g1 : GL (Fin (2 * k)) K) = 1
    rw [hg1one]
    rfl
  exact hgone

private theorem ggOmW5b_mem_matrixOrthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    t ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ := by
  intro u
  rw [ht u, ggOmW5b_polar_apply Φ u v]
  exact ggOmW5b_quad_form_transvection_invariant Φ v hv u

private theorem ggOmW5b_reindex_map_derived {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] {d : ℕ} (e : ι ≃ Fin d) (Φ : QuadraticForm K (ι → K)) :
    (StatedOmega ⇑Φ).map (reindexMatrixEquiv e).toMonoidHom =
      matrixDerived (reindexQuadraticForm e Φ) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have h := ggOmW5b_reindex_mem_derived_iff e Φ ((reindexMatrixEquiv e).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private theorem ggOmW5b_reindex_inf_centralizer {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] {d : ℕ} (e : ι ≃ Fin d) (Φ : QuadraticForm K (ι → K)) (t : GL ι K) :
    (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ).map
        (reindexMatrixEquiv e).toMonoidHom =
      Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin d) K)) ⊓
        matrixDerived (reindexQuadraticForm e Φ) := by
  rw [Subgroup.map_inf (Subgroup.centralizer ({t} : Set (GL ι K))) (StatedOmega ⇑Φ)
        (reindexMatrixEquiv e).toMonoidHom (reindexMatrixEquiv e).injective,
      ggOmW5b_map_centralizer_singleton (reindexMatrixEquiv e) t,
      ggOmW5b_reindex_map_derived e Φ]

private theorem ggOmW5b_card_pCoreOf_eq_of_equiv {G H : Type} [Group G] [Group H]
    {A : Subgroup G} {B : Subgroup H} (e : ↥A ≃* ↥B) (p : ℕ) :
    Nat.card (pCoreOf p A) = Nat.card (pCoreOf p B) := by
  have hA' : Nat.card (pCoreOf p A) = Nat.card (CFSG.pCore p ↥A) := by
    rw [show pCoreOf p A = (CFSG.pCore p ↥A).map A.subtype from rfl]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pCore p ↥A) A.subtype
      A.subtype_injective).toEquiv).symm
  have hB' : Nat.card (pCoreOf p B) = Nat.card (CFSG.pCore p ↥B) := by
    rw [show pCoreOf p B = (CFSG.pCore p ↥B).map B.subtype from rfl]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pCore p ↥B) B.subtype
      B.subtype_injective).toEquiv).symm
  rw [hA', hB', ← CFSG.pCore_map_iso p e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pCore p ↥A) e.toMonoidHom
    e.injective).toEquiv

private theorem ggOmW5b_pCoreOf_bot_of_equiv {G H : Type} [Group G] [Group H]
    {A : Subgroup G} {B : Subgroup H} (e : ↥A ≃* ↥B) (hB : pCoreOf 2 B = ⊥) :
    pCoreOf 2 A = ⊥ := by
  have hcard := ggOmW5b_card_pCoreOf_eq_of_equiv e 2
  rw [hB, Subgroup.card_bot] at hcard
  exact (Subgroup.card_eq_one (H := pCoreOf 2 A)).mp hcard

private theorem ggOmW5b_not_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    t ∉ StatedOmega ⇑Φ := by
  obtain ⟨k, hcard, hk3, harith⟩ := ggOmW5b_card_arith h8 (ggOmW5b_even_card Φ hΦ)
  let e : ι ≃ Fin (2 * k) := Fintype.equivFinOfCardEq hcard
  let Q : QuadraticForm K (Fin (2 * k) → K) := reindexQuadraticForm e Φ
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate := ggOmW5b_reindex_nondegenerate e Φ hΦ
  let v' : Fin (2 * k) → K := reindexVectorEquiv (K := K) e v
  have hv' : Q v' = 1 := ggOmW5b_reindex_value e Φ v hv
  have ht' := ggOmW5b_reindex_transvection e Φ t v ht
  have heq : reindexMatrixEquiv e t = symmetryGL Q v' :=
    ggOmW5b_fin_eq_symmetryGL Q v' (reindexMatrixEquiv e t) hv' ht'
  have hz : symmetryGL Q v' ∉ matrixDerived Q :=
    ggOmW5b_fin_symmetryGL_not_mem_derived Q hQ v' hv'
  intro hmem
  have hmem' : reindexMatrixEquiv e t ∈ matrixDerived Q :=
    (ggOmW5b_reindex_mem_derived_iff e Φ t).mpr hmem
  rw [heq] at hmem'
  exact hz hmem'

private theorem ggOmW5b_centralizer_equiv_sp {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    Nonempty (↥(Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ) ≃*
      ↥(StatedSp ((Fintype.card ι - 2) / 2) K)) := by
  obtain ⟨k, hcard, hk3, harith⟩ := ggOmW5b_card_arith h8 (ggOmW5b_even_card Φ hΦ)
  let e : ι ≃ Fin (2 * k) := Fintype.equivFinOfCardEq hcard
  let Q : QuadraticForm K (Fin (2 * k) → K) := reindexQuadraticForm e Φ
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate := ggOmW5b_reindex_nondegenerate e Φ hΦ
  let v' : Fin (2 * k) → K := reindexVectorEquiv (K := K) e v
  have hv' : Q v' = 1 := ggOmW5b_reindex_value e Φ v hv
  have ht' := ggOmW5b_reindex_transvection e Φ t v ht
  have heq : reindexMatrixEquiv e t = symmetryGL Q v' :=
    ggOmW5b_fin_eq_symmetryGL Q v' (reindexMatrixEquiv e t) hv' ht'
  have hidx := ggOmW5b_fin_index_two hk3 Q hQ
  have hz : symmetryGL Q v' ∉ matrixDerived Q :=
    ggOmW5b_fin_symmetryGL_not_mem_derived Q hQ v' hv'
  have hsp := ggOmW5b_fin_sp_equiv Q hQ v' hv' hidx hz
  have hA : (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ).map
        (reindexMatrixEquiv e).toMonoidHom =
      Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin (2 * k)) K)) ⊓
        matrixDerived Q :=
    ggOmW5b_reindex_inf_centralizer e Φ t
  have hAB : Nonempty
      (↥(Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ) ≃*
        ↥(Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin (2 * k)) K)) ⊓
          matrixDerived Q)) := by
    refine ⟨?_⟩
    rw [← hA]
    exact Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ)
      (reindexMatrixEquiv e).toMonoidHom (reindexMatrixEquiv e).injective
  have hB' : Nonempty (↥(Subgroup.centralizer ({reindexMatrixEquiv e t} :
      Set (GL (Fin (2 * k)) K)) ⊓ matrixDerived Q) ≃* StatedSp (k - 1) K) := by
    rw [heq]
    exact hsp
  have hcomp : Nonempty (↥(Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ) ≃*
      StatedSp (k - 1) K) :=
    hAB.elim fun e1 => ggOmW5b_nonempty_equiv_trans e1 hB'
  rw [harith]
  exact hcomp

private theorem ggOmW5b_commutator_top {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    commutator ↥(Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ) = ⊤ := by
  obtain ⟨e⟩ := ggOmW5b_centralizer_equiv_sp Φ hΦ h8 t v hv ht
  refine ggOmW5b_commutator_eq_top_of_equiv e ?_
  refine ggOmW5b_statedSp_commutator_top ((Fintype.card ι - 2) / 2) ?_
  obtain ⟨k, hcard, hk3, harith⟩ := ggOmW5b_card_arith h8 (ggOmW5b_even_card Φ hΦ)
  rw [harith]
  omega

private theorem ggOmW5b_pCore_bot {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    pCoreOf 2 (Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ) = ⊥ := by
  obtain ⟨k, hcard, hk3, harith⟩ := ggOmW5b_card_arith h8 (ggOmW5b_even_card Φ hΦ)
  let e : ι ≃ Fin (2 * k) := Fintype.equivFinOfCardEq hcard
  let Q : QuadraticForm K (Fin (2 * k) → K) := reindexQuadraticForm e Φ
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate := ggOmW5b_reindex_nondegenerate e Φ hΦ
  let v' : Fin (2 * k) → K := reindexVectorEquiv (K := K) e v
  have hv' : Q v' = 1 := ggOmW5b_reindex_value e Φ v hv
  have ht' := ggOmW5b_reindex_transvection e Φ t v ht
  have heq : reindexMatrixEquiv e t = symmetryGL Q v' :=
    ggOmW5b_fin_eq_symmetryGL Q v' (reindexMatrixEquiv e t) hv' ht'
  have hidx := ggOmW5b_fin_index_two hk3 Q hQ
  have hz : symmetryGL Q v' ∉ matrixDerived Q :=
    ggOmW5b_fin_symmetryGL_not_mem_derived Q hQ v' hv'
  have hsp := ggOmW5b_fin_sp_equiv Q hQ v' hv' hidx hz
  have htop : pCoreOf 2 (⊤ : Subgroup (StatedSp (k - 1) K)) = ⊥ :=
    ggOmW5b_statedSp_pCore_bot (k - 1) (by omega)
  have hBbot : pCoreOf 2 (Subgroup.centralizer ({symmetryGL Q v'} :
      Set (GL (Fin (2 * k)) K)) ⊓ matrixDerived Q) = ⊥ := by
    obtain ⟨g⟩ := hsp
    exact ggOmW5b_pCoreOf_bot_of_equiv (g.trans (Subgroup.topEquiv).symm) htop
  have hBbot' : pCoreOf 2 (Subgroup.centralizer ({reindexMatrixEquiv e t} :
      Set (GL (Fin (2 * k)) K)) ⊓ matrixDerived Q) = ⊥ := by
    rw [heq]
    exact hBbot
  have hCmap : (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ).map
        (reindexMatrixEquiv e).toMonoidHom =
      Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin (2 * k)) K)) ⊓
        matrixDerived Q :=
    ggOmW5b_reindex_inf_centralizer e Φ t
  have hm := ggOmW5b_map_pCoreOf (reindexMatrixEquiv e)
    (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ) 2
  rw [hCmap, hBbot'] at hm
  exact Subgroup.map_injective (reindexMatrixEquiv e).injective
    (hm.trans (Subgroup.map_bot (reindexMatrixEquiv e).toMonoidHom).symm)

private theorem ggOmW5b_double_centralizer_transport {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (D C : Subgroup G)
    (h : (D.map f.toMonoidHom) ⊓
      Subgroup.centralizer ((C.map f.toMonoidHom : Subgroup H) : Set H) = ⊥) :
    D ⊓ Subgroup.centralizer (C : Set G) = ⊥ := by
  have hmap : (D ⊓ Subgroup.centralizer (C : Set G)).map f.toMonoidHom =
      D.map f.toMonoidHom ⊓
        Subgroup.centralizer ((C.map f.toMonoidHom : Subgroup H) : Set H) := by
    rw [Subgroup.map_inf D (Subgroup.centralizer (C : Set G)) f.toMonoidHom f.injective,
      ggOmW5b_map_centralizer f C]
  exact Subgroup.map_injective f.injective
    ((hmap.trans h).trans (Subgroup.map_bot f.toMonoidHom).symm)

private theorem ggOmW5b_double_centralizer {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    StatedOmega ⇑Φ ⊓ Subgroup.centralizer
      ((Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ : Subgroup (GL ι K)) : Set (GL ι K)) = ⊥ := by
  obtain ⟨k, hcard, hk3, harith⟩ := ggOmW5b_card_arith h8 (ggOmW5b_even_card Φ hΦ)
  let e : ι ≃ Fin (2 * k) := Fintype.equivFinOfCardEq hcard
  let Q : QuadraticForm K (Fin (2 * k) → K) := reindexQuadraticForm e Φ
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate := ggOmW5b_reindex_nondegenerate e Φ hΦ
  let v' : Fin (2 * k) → K := reindexVectorEquiv (K := K) e v
  have hv' : Q v' = 1 := ggOmW5b_reindex_value e Φ v hv
  have ht' := ggOmW5b_reindex_transvection e Φ t v ht
  have heq : reindexMatrixEquiv e t = symmetryGL Q v' :=
    ggOmW5b_fin_eq_symmetryGL Q v' (reindexMatrixEquiv e t) hv' ht'
  have hCeq : (matrixDerived Q ⊓ symmetryCentralizer Q v' : Subgroup (GL (Fin (2 * k)) K)) =
      Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin (2 * k)) K)) ⊓
        matrixDerived Q := by
    rw [heq, ggOmW5b_fin_centralizer_eq]
  have hfin : matrixDerived Q ⊓ Subgroup.centralizer
      ((Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin (2 * k)) K)) ⊓
        matrixDerived Q : Subgroup (GL (Fin (2 * k)) K)) :
        Set (GL (Fin (2 * k)) K)) = ⊥ := by
    rw [← hCeq]
    exact ggOmW5b_fin_double_centralizer hk3 Q hQ v' hv'
  have hCmap : (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ).map
        (reindexMatrixEquiv e).toMonoidHom =
      Subgroup.centralizer ({reindexMatrixEquiv e t} : Set (GL (Fin (2 * k)) K)) ⊓
        matrixDerived Q :=
    ggOmW5b_reindex_inf_centralizer e Φ t
  refine ggOmW5b_double_centralizer_transport (reindexMatrixEquiv e) (StatedOmega ⇑Φ)
    (Subgroup.centralizer ({t} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ) ?_
  rw [ggOmW5b_reindex_map_derived e Φ, hCmap]
  exact hfin

theorem centralizer_transvection {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (t : GL ι K) (v : ι → K) (hv : Φ v = 1)
    (ht : ∀ u : ι → K, (t : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v) :
    t ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ ∧ t ∉ StatedOmega ⇑Φ ∧
      commutator ↥(Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ) = ⊤ ∧
      pCoreOf 2 (Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ) = ⊥ ∧
      StatedOmega ⇑Φ ⊓ Subgroup.centralizer
        ((Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ : Subgroup (GL ι K)) : Set (GL ι K)) = ⊥ ∧
      Nonempty (↥(Subgroup.centralizer {t} ⊓ StatedOmega ⇑Φ) ≃*
        ↥(StatedSp ((Fintype.card ι - 2) / 2) K)) := by
  exact ⟨ggOmW5b_mem_matrixOrthogonal Φ t v hv ht,
    ggOmW5b_not_mem_statedOmega Φ hΦ h8 t v hv ht,
    ggOmW5b_commutator_top Φ hΦ h8 t v hv ht,
    ggOmW5b_pCore_bot Φ hΦ h8 t v hv ht,
    ggOmW5b_double_centralizer Φ hΦ h8 t v hv ht,
    ggOmW5b_centralizer_equiv_sp Φ hΦ h8 t v hv ht⟩

end CFSG.StandardType.ClassicalBlocks
