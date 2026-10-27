module

public import CFSG.Quasithin.H13.NQCatLieOverRank2

public section

namespace CFSG.Quasithin.Lie2Parabolic

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13

variable {Y : Type} [Group Y] [Finite Y]

section Radical

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat CFSG.Quasithin.H13.NQCat.Sp4
  CFSG.LieType.BorelTits
open scoped commutatorElement

theorem pCoreOf_map_of_injective {X X' : Type*} [Group X] [Group X'] (φ : X →* X')
    (hφ : Function.Injective φ) (A : Subgroup X) :
    pCoreOf 2 (A.map φ) = (pCoreOf 2 A).map φ := by
  let ψ : ↥A ≃* ↥(A.map φ) := A.equivMapOfInjective φ hφ
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ψ, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem commutator_pCoreOf_map_iff {X X' : Type*} [Group X] [Group X'] (φ : X →* X')
    (hφ : Function.Injective φ) (A : Subgroup X) :
    ⁅pCoreOf 2 (A.map φ), A.map φ⁆ = pCoreOf 2 (A.map φ) ↔ ⁅pCoreOf 2 A, A⁆ = pCoreOf 2 A := by
  rw [pCoreOf_map_of_injective φ hφ, ← Subgroup.map_commutator]
  exact (Subgroup.map_injective hφ).eq_iff

theorem commutator_pCoreOf_congr {X X' : Type*} [Group X] [Group X'] {A : Subgroup X}
    {A' : Subgroup X'} (e : ↥A ≃* ↥A') :
    ⁅pCoreOf 2 A, A⁆ = pCoreOf 2 A ↔ ⁅pCoreOf 2 A', A'⁆ = pCoreOf 2 A' := by
  have h1 := commutator_pCoreOf_map_iff A.subtype A.subtype_injective ⊤
  have h2 := commutator_pCoreOf_map_iff A'.subtype A'.subtype_injective ⊤
  have h3 := commutator_pCoreOf_map_iff e.toMonoidHom e.injective ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1 h2
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h3
  exact h1.trans (h3.symm.trans h2.symm)

theorem root_mem_commutator_of {F G : Type*} [Field F] [Group G] {A B : Subgroup G}
    (x : F → G) (hmul : ∀ s t, x s * x t = x (s + t)) (d : G) (w : F) (hw : w ≠ 1)
    (hconj : ∀ t, d * x t * d⁻¹ = x (w * t)) (hdB : d ∈ B) (hxA : ∀ t, x t ∈ A) (t : F) :
    x t ∈ ⁅A, B⁆ := by
  have h0 : x 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h
  have hinv : ∀ t, (x t)⁻¹ = x (-t) := fun t => by
    rw [inv_eq_iff_mul_eq_one, hmul, add_neg_cancel, h0]
  have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have key : ⁅x (t / (1 - w)), d⁆ = x t := by
    have e : ⁅x (t / (1 - w)), d⁆ = x (t / (1 - w)) * (d * (x (t / (1 - w)))⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e, hinv, hconj, hmul]
    congr 1
    field_simp
    ring
  rw [← key]
  exact Subgroup.commutator_mem_commutator (hxA _) hdB

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem blkIdx_root (t : K) :
    blkIdx (sigma2 0) (spMat (xA t)) = 1 ∧ blkIdx (sigma2 0) (spMat (xAB t)) = 1 ∧
      blkIdx (sigma2 0) (spMat (xC t)) = 1 ∧ blkIdx (sigma2 1) (spMat (xB t)) = 1 ∧
      blkIdx (sigma2 1) (spMat (xAB t)) = 1 ∧ blkIdx (sigma2 1) (spMat (xC t)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [blkIdx, sigma2, spMat_xA, spMat_xB, spMat_xAB, spMat_xC]

omit [Finite K] [CharP K 2] in
theorem spMat_prod_apply (x c₀ c₁ c₂ : K) :
    spMat (xA x * xC c₀ * xAB c₁ * xB c₂) (Sum.inl 0) (Sum.inl 1) = x ∧
      spMat (xA x * xC c₀ * xAB c₁ * xB c₂) (Sum.inl 1) (Sum.inr 1) = c₂ := by
  simp only [spMat_mul, spMat_xA, spMat_xC, spMat_xAB, spMat_xB]
  constructor <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply, one_apply]

theorem mem_pCoreOf_perfectCore_Q2 {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (j : Fin 2)
    {g : CFSG.Assembly.LowTwoRank.StatedSp 2 K} (hg : g ∈ perfectCore (Q2 K j)) :
    g ∈ pCoreOf 2 (perfectCore (Q2 K j)) ↔ blkIdx (sigma2 j) (spMat g) = 1 := by
  have hK4 := exists_finset_card_four_of_card hf hK
  have := sl2_isSimple hK4
  have hcore : CFSG.Open.pCore 2 ↥(perfectCore (Q2 K j)) = (blkN j).ker := by
    exact pCore_two_eq_ker (sl2_nonabelian hK4) (blkN j) (blkN_surjective hK4 j)
      (blkN_ker_isPGroup ⟨f, hK⟩ j)
  show g ∈ (CFSG.Open.pCore 2 ↥(perfectCore (Q2 K j))).map (perfectCore (Q2 K j)).subtype ↔ _
  rw [hcore, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : blkN j y = 1 := MonoidHom.mem_ker.mp hy
    show blkIdx (sigma2 j) (spMat y.1) = 1
    rw [← blkN_coe, h1]
    rfl
  · intro h
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    rw [blkN_coe]
    exact h

theorem commutator_pCoreOf_perfectCore_Q2 {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (j : Fin 2) :
    ⁅pCoreOf 2 (perfectCore (Q2 K j)), perfectCore (Q2 K j)⁆ =
      pCoreOf 2 (perfectCore (Q2 K j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 := exists_finset_card_four_of_card hf hK
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_pCoreOf 2 _)) ?_
  have hmem : ∀ {g} (hg : g ∈ perfectCore (Q2 K j)),
      g ∈ pCoreOf 2 (perfectCore (Q2 K j)) ↔ blkIdx (sigma2 j) (spMat g) = 1 :=
    fun hg => mem_pCoreOf_perfectCore_Q2 hf hK j hg
  have hUC := Sp4.unipotent_le_perfectCore hK4 j
  obtain ⟨s, hs1⟩ := exists_unit_ne_one hK4
  have hsi1 := units_inv_ne_one hs1
  have hsq : ∀ x : K, x ≠ 1 → x ^ 2 ≠ 1 := fun x hx h =>
    hx (CharTwo.sq_injective (h.trans (one_pow 2).symm))
  have hdC : spLevi j (dg2 s) ∈ perfectCore (Q2 K j) := spLevi_mem_perfectCore hK4 j _
  have hrel : ∀ c : K, ⁅xA (1 : K), xB c⁆ = xAB c * xC c := fun c => by
    rw [comm_xA_xB, one_mul, one_pow, one_mul]
  have h0 : ∀ y : K → CFSG.Assembly.LowTwoRank.StatedSp 2 K, (∀ s t, y s * y t = y (s + t)) →
      y 0 = 1 := fun y hy => by
    have h := hy 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h
  intro g hg
  have hgC := pCoreOf_le 2 _ hg
  have hblk := (hmem hgC).mp hg
  obtain ⟨x, c₀, c₁, c₂, rfl⟩ := exists_eq_prod_of_mem_unipotent
    (blkN_ker j ⟨_, hgC⟩ (Subtype.ext hblk))
  have hent := spMat_prod_apply x c₀ c₁ c₂
  rcases fin_two_cases j with rfl | rfl
  ·
    have hc₂ : c₂ = 0 := by
      have := congrFun₂ hblk 0 1
      simp only [blkIdx, sigma2, submatrix_apply] at this
      simpa [hent.2] using this
    have hA : ∀ t, xA t ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ :=
      root_mem_commutator_of xA xA_mul _ _ hsi1 (conj_zero_xA s) hdC
        (fun t => (hmem (hUC (xA_mem t))).mpr (blkIdx_root t).1)
    have hAB : ∀ t, xAB t ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ :=
      root_mem_commutator_of xAB xAB_mul _ _ hs1 (conj_zero_xAB s) hdC
        (fun t => (hmem (hUC (xAB_mem t))).mpr (blkIdx_root t).2.1)
    have hC : xC c₀ ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ := by
      have e : xC c₀ = (xAB c₀)⁻¹ * ⁅xA (1 : K), xB c₀⁆ := by rw [hrel, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (hAB c₀)) (Subgroup.commutator_mem_commutator
        ((hmem (hUC (xA_mem 1))).mpr (blkIdx_root 1).1) (hUC (xB_mem c₀)))
    rw [hc₂, h0 xB xB_mul, mul_one]
    exact mul_mem (mul_mem (hA x) hC) (hAB c₁)
  ·
    have hx : x = 0 := by
      have := congrFun₂ hblk 0 1
      simp only [blkIdx, sigma2, submatrix_apply] at this
      simpa [hent.1] using this
    have hB : ∀ t, xB t ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 1)), perfectCore (Q2 K 1)⁆ :=
      root_mem_commutator_of xB xB_mul _ _ (hsq _ hsi1) (conj_one_xB s) hdC
        (fun t => (hmem (hUC (xB_mem t))).mpr (blkIdx_root t).2.2.2.1)
    have hC : ∀ t, xC t ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 1)), perfectCore (Q2 K 1)⁆ :=
      root_mem_commutator_of xC xC_mul _ _ (hsq _ hs1) (conj_one_xC s) hdC
        (fun t => (hmem (hUC (xC_mem t))).mpr (blkIdx_root t).2.2.2.2.2)
    have hAB : xAB c₁ ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 1)), perfectCore (Q2 K 1)⁆ := by
      have e : xAB c₁ = ⁅xA (1 : K), xB c₁⁆ * (xC c₁)⁻¹ := by rw [hrel, mul_inv_cancel_right]
      rw [e, ← Subgroup.commutator_comm]
      refine mul_mem (Subgroup.commutator_mem_commutator (hUC (xA_mem 1))
        ((hmem (hUC (xB_mem c₁))).mpr (blkIdx_root c₁).2.2.2.1)) ?_
      rw [Subgroup.commutator_comm]
      exact inv_mem (hC c₁)
    rw [hx, h0 xA xA_mul, one_mul]
    exact mul_mem (mul_mem (hC c₀) hAB) (hB c₂)

omit [Finite Y] in
theorem exists_sylow_of_isMaxParabolic2 {P : Subgroup Y}
    (hP : IsMaxParabolic2 (⊤ : Subgroup Y) P) :
    ∃ S : Subgroup Y, IsSylowTwoOf S ⊤ ∧ Subgroup.normalizer (S : Set Y) ≤ P ∧ P ⋖ ⊤ := by
  obtain ⟨⟨-, S, hS, hSP⟩, hne, hmax⟩ := hP
  have hSP' : Subgroup.normalizer (S : Set Y) ≤ P := by simpa using hSP
  refine ⟨S, hS, hSP', lt_top_iff_ne_top.mpr hne, fun Q hPQ hQ => ?_⟩
  have hQP : Q = P := hmax Q ⟨le_top, S, hS, by simpa using hSP'.trans hPQ.le⟩ hQ.ne hPQ.le
  exact hPQ.ne hQP.symm

theorem commutator_pCoreOf_perfectCore {f : ℕ} (hf : 2 ≤ f) (h : IsPSp4 2 f Y)
    {P : Subgroup Y} (hP : IsMaxParabolic2 (⊤ : Subgroup Y) P) :
    ⁅pCoreOf 2 (perfectCore P), perfectCore P⁆ = pCoreOf 2 (perfectCore P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSP, hPcov⟩ := exists_sylow_of_isMaxParabolic2 hP
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨U, hU⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hU ▸ isSylowTwoOf_top_of_sylow U
  have hS₁ : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map _, ?_⟩
    have h1 := hS.2.2
    rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h1
    rwa [show ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  obtain ⟨g, hg⟩ := NQCat.exists_conj_map_eq hS₁ hU₀
  set E : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    e.trans (MulAut.conj g) with hE
  have hSE : S.map E.toMonoidHom = projUnipotent 2 K := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hPE : projUnipotent 2 K ≤ P.map E.toMonoidHom := by
    rw [← hSE]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans hSP)
  have hPEcov : P.map E.toMonoidHom ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective E.toMonoidHom E.surjective]
    exact (apply_covBy_apply_iff (MulEquiv.mapSubgroup E)).mpr hPcov
  obtain ⟨j, hj⟩ := ((symplectic_two_residualOvergroupsAt ⟨f, hK⟩).2.2.1 _ hPE).mp hPEcov
  let ψ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj 2 K)
      ⟨proj_injective_charTwo, QuotientGroup.mk'_surjective _⟩
  have hj' : P.map E.toMonoidHom = (Q2 K j).map ψ.toMonoidHom := hj
  rw [← commutator_pCoreOf_map_iff E.toMonoidHom E.injective,
    CFSG.Quasithin.map_perfectCore, hj', ← CFSG.Quasithin.map_perfectCore,
    commutator_pCoreOf_map_iff ψ.toMonoidHom ψ.injective]
  exact commutator_pCoreOf_perfectCore_Q2 hf hK j

end Radical

end CFSG.Quasithin.Lie2Parabolic
