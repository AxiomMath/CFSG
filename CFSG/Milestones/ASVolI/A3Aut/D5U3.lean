module

public import CFSG.Milestones.ASVolI.A3Aut.D5Base
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped commutatorElement Matrix

section D5U3Generic

theorem burnsideAut_d5_isPerfect {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ∃ x y : S, x * y ≠ y * x) : Group.IsPerfect S := by
  obtain ⟨x, y, hxy⟩ := h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hb | ht
  · exfalso
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator S := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact ⟨ht⟩

theorem burnsideAut_d5_sylow_eq_of_mem {X : Type} [Group X] [Finite X] {q k : ℕ}
    (hB : fusionBenderBorel X q k) {P Q : Sylow 2 X} {t : X} (ht : t ≠ 1)
    (htP : t ∈ (P : Subgroup X)) (htQ : t ∈ (Q : Subgroup X)) : P = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P Q
  by_cases hg : g ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)
  · exact (Sylow.smul_eq_iff_mem_normalizer.2 hg).symm
  · exfalso
    set N := Subgroup.normalizer ((P : Subgroup X) : Set X) with hN
    have hg' : g⁻¹ ∉ N := fun h => hg (by simpa using N.inv_mem h)
    have hodd := (hB P).1.2.2 g⁻¹ hg'
    rw [inv_inv] at hodd
    have htN : t ∈ N := Subgroup.le_normalizer htP
    have htN' : t ∈ N.map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htQ
      obtain ⟨s, hs, rfl⟩ := htQ
      exact ⟨s, Subgroup.le_normalizer hs, rfl⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨t, htP⟩
    have hj' : orderOf t = 2 ^ j :=
      (Subgroup.orderOf_coe (⟨t, htP⟩ : ↥(P : Subgroup X))).trans hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact ht (orderOf_eq_one_iff.mp (by rw [hj', pow_zero]))
    have h2 : 2 ∣ Nat.card ↥(N ⊓ N.map (MulAut.conj g).toMonoidHom) :=
      (dvd_pow_self 2 hj0).trans (hj' ▸ Subgroup.orderOf_dvd_natCard _ ⟨htN, htN'⟩)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem burnsideAut_d5_map_sylow_eq {X : Type} [Group X] [Finite X] {q k : ℕ}
    (hB : fusionBenderBorel X q k) {Q : Sylow 2 X} {t : X} (ht : t ≠ 1)
    (htQ : t ∈ (Q : Subgroup X)) (φ : MulAut X) (hφt : φ t = t) :
    (Q : Subgroup X).map φ.toMonoidHom = Q := by
  have h1 := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv φ
    (X := (Q : Subgroup X)) (Y := ⊤)).2 (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q)
  rw [Subgroup.map_top_of_surjective _ φ.surjective] at h1
  obtain ⟨h2, h3⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : h2.toSylow h3 = Q := by
    refine burnsideAut_d5_sylow_eq_of_mem hB ht ?_ htQ
    rw [IsPGroup.toSylow_coe]
    exact ⟨t, htQ, hφt⟩
  have h5 := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) h4
  simpa only [IsPGroup.toSylow_coe] using h5

end D5U3Generic

section D5U3Model

variable {n : ℕ} {K : Type} [Field K]

theorem burnsideAut_d5u3_fusionIsBender [Finite K] (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n) :
    fusionIsBenderGroup (unitaryPSU hu 3) := by
  let e' : unitaryPSU hu 3 ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) :=
    unitaryPSUEquiv hu (by norm_num)
  exact Or.inr (Or.inl ⟨n, hn, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hu.card)⟩⟩)

theorem burnsideAut_d5u3_exists_fixed_involution (hu : UnitaryFieldData 2 n K) :
    ∃ t : unitaryPSU hu 3, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ σ : K ≃+* K, psuField hu σ t = t := by
  haveI : CharP K 2 := hu.charP
  set P : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hPdef
  have hPP : P * P = 1 := by
    rw [hPdef]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPmap : ∀ g : K → K, g 0 = 0 → g 1 = 1 → P.map g = P := by
    intro g h0 h1
    rw [hPdef]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1]
  have hPT : Pᵀ = P := by
    rw [hPdef]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdet : P.det = 1 := by
    rw [hPdef, Matrix.det_fin_three]
    simp [CharTwo.neg_eq]
  let A : GL (Fin 3) K := ⟨P, P, hPP, hPP⟩
  have hA : A ∈ unitarySU 2 n K 3 := by
    rw [mem_unitarySU_iff hu]
    refine ⟨hdet, ?_⟩
    change (P.map hu.bar)ᵀ * P = 1
    rw [hPmap _ (map_zero _) (map_one _), hPT, hPP]
  refine ⟨unitaryProj hu 3 ⟨A, hA⟩, ?_, ?_, ?_⟩
  · intro h1
    have hmem : (⟨A, hA⟩ : unitarySU 2 n K 3) ∈ unitaryScalars hu 3 := by
      rw [← ker_unitaryProj]
      exact h1
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hmem
    have h2 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    simp [A, hPdef, Matrix.GeneralLinearGroup.coe_scalar] at h2
    exact c.ne_zero h2.symm
  · rw [← map_pow]
    have h1 : (⟨A, hA⟩ : unitarySU 2 n K 3) ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one, sq]
      exact hPP
    rw [h1, map_one]
  · intro σ
    change psuField hu σ ((⟨A, hA⟩ : unitarySU 2 n K 3) : unitaryPSU hu 3) = _
    rw [psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut]
    exact hPmap _ (map_zero σ) (map_one σ)

theorem burnsideAut_d5u3_inn_relIndex_odd (hu : UnitaryFieldData 2 n K)
    [Finite (unitaryPSU hu 3)] :
    ¬ 2 ∣ (MulAut.conj : unitaryPSU hu 3 →* MulAut (unitaryPSU hu 3)).range.relIndex
      (psuConj hu).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut (unitaryPSU hu 3)) :=
    Finite.of_injective (fun e : MulAut (unitaryPSU hu 3) => (e : unitaryPSU hu 3 → unitaryPSU hu 3))
      (fun a b hab => MulEquiv.ext (congrFun hab))
  haveI := burnsideAut_inn_normal' (unitaryPSU hu 3)
  have hpow : ∀ A : unitaryIsom3 hu, (psuConj hu A) ^ (2 ^ n + 1) ∈
      (MulAut.conj : unitaryPSU hu 3 →* MulAut (unitaryPSU hu 3)).range := by
    intro A
    have hdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ^ (2 ^ n + 1) = 1 := by
      have h1 := norm_det_of_mem_unitaryIsom3 A.2
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at h1
      rw [pow_succ', ← h1]
    have hmem : ((A ^ (2 ^ n + 1) : unitaryIsom3 hu) : GL (Fin 3) K) ∈ unitarySU 2 n K 3 := by
      rw [mem_unitarySU_iff hu]
      refine ⟨?_, (A ^ (2 ^ n + 1)).2⟩
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow, hdet]
    refine ⟨((⟨_, hmem⟩ : unitarySU 2 n K 3) : unitaryPSU hu 3), ?_⟩
    rw [conj_mk_eq_psuConj, ← map_pow]
  intro h2
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(psuConj hu).range ⧸
    (MulAut.conj : unitaryPSU hu 3 →* MulAut (unitaryPSU hu 3)).range.subgroupOf
      (psuConj hu).range) 2 h2
  obtain ⟨⟨_, ⟨A, rfl⟩⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have h3 : (QuotientGroup.mk (⟨psuConj hu A, ⟨A, rfl⟩⟩ : ↥(psuConj hu).range) :
      ↥(psuConj hu).range ⧸ (MulAut.conj : unitaryPSU hu 3 →* MulAut (unitaryPSU hu 3)).range.subgroupOf
        (psuConj hu).range) ^ (2 ^ n + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hpow A
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hy] at h4
  have h5 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := hu.one_le; omega)
  omega

end D5U3Model

theorem burnsideAut_a315_U3 {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hn : 2 ≤ n)
    (hL : CFSG.Quasithin.IsPSU 3 2 n ↥L) : ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L := Or.inr (Or.inr (Or.inl hL))
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hL
  have hu : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K 2 := hu.charP
  have hq : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨e₁⟩ : Nonempty (↥L ≃* unitaryPSU hu 3) :=
    ⟨e₀.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm⟩
  haveI : Finite (unitaryPSU hu 3) := Finite.of_equiv _ e₁.toEquiv
  haveI : IsSimpleGroup (unitaryPSU hu 3) := by
    haveI := h.simple
    exact MulEquiv.isSimpleGroup e₁.symm
  have hnab : ∃ a b : unitaryPSU hu 3, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨e₁ a, e₁ b, fun h' => hab (e₁.injective (by rw [map_mul, map_mul, h']))⟩
  have hMZ : Subgroup.center (unitaryPSU hu 3) = ⊥ := burnsideAut_center_eq_bot hnab
  haveI : Group.IsPerfect (unitaryPSU hu 3) := burnsideAut_d5_isPerfect hnab
  have hBen := burnsideAut_d5u3_fusionIsBender hu hn
  obtain ⟨qB, kB, -, hBor⟩ :=
    CFSG.QuasithinUnique.Unc25G2.BenderBorel.exists_borel_of_bender hBen
  obtain ⟨t, ht1, ht2, htσ⟩ := burnsideAut_d5u3_exists_fixed_involution hu
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1]; rfl)
  obtain ⟨Q₀, hQ₀⟩ := htp.exists_le_sylow
  have htQ₀ : t ∈ (Q₀ : Subgroup (unitaryPSU hu 3)) := hQ₀ (Subgroup.mem_zpowers t)
  have hUsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q₀
  have hφU : ∀ σ : RingAut K,
      (Q₀ : Subgroup (unitaryPSU hu 3)).map (psuField hu σ).toMonoidHom = Q₀ := fun σ =>
    burnsideAut_d5_map_sylow_eq hBor ht1 htQ₀ (psuField hu σ) (htσ σ)
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow e₁
    (burnsideAut_isSylowTwoOf_subgroupOf h.sylow) hUsyl
  have hcard : Nat.card K = 2 ^ (2 * n) := hu.card
  obtain ⟨hcardAut, hcycAut⟩ := card_ringAut_and_isCyclic Nat.prime_two K hcard
  have hinj : Function.Injective (psuField hu) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact psuField_mem_range_psuConj_iff.mp (by rw [hσ]; exact Subgroup.one_mem _)
  have hP : ∀ σ : RingAut K, ChA.IsProjFieldAut (StatedSU 3 (2 ^ n) K) σ
      (MulAut.congr (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)) (psuField hu σ)) := by
    intro σ
    have h1 := burnsideA26_isProjFieldAut_u3 hu (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)) σ
    have h2 : MulAut.congr ((unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).trans
        (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm).symm (psuField hu σ) =
          psuField hu σ := by
      ext x
      simp [MulAut.congr_apply]
    rw [h2] at h1
    exact h1
  refine burnsideAut_case5_of_model2 h n hn hLie hMZ e he hUsyl
    (IM := (psuConj hu).range) (ΦM := (psuField hu).range) (stdPinnedPSU3 hu).inn_le
    (burnsideAut_d5u3_inn_relIndex_odd hu) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    refine Subgroup.subset_closure (show ChA.IsInnDiagAut ↥L _ from Or.inr (Or.inr
      ⟨n, K, inferInstance, inferInstance, e.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)),
        (A : GL (Fin 3) K), hK, ?_⟩))
    have h1 := burnsideA26_isProjConjAut_u3 hu
      (e.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3))) A
    have h2 : MulAut.congr ((e.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3))).trans
        (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm).symm (psuConj hu A) =
          MulAut.congr e.symm (psuConj hu A) := by
      ext x
      simp [MulAut.congr_apply]
    rw [h2] at h1
    exact h1
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  · haveI : (psuConj hu).range.Normal := (stdPinnedPSU3_stable (h := hu) hq).normal
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rw [eq_bot_iff]
    rintro _ ⟨hI, ⟨σ, rfl⟩⟩
    rw [psuField_mem_range_psuConj_iff.mp hI, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨σ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (hφU σ)
  · intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq (MulAut.congr e (MulAut.conjNormal b))
    rw [hAσ]
    exact Subgroup.mul_mem_sup ⟨A, rfl⟩ ⟨σ, rfl⟩
  · intro Y hUY hY
    exact CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hBen Q₀ hUY
      (burnsideAut_ne_top_of_isSolvable hY)
  · intro ε hε F hF hFodd _
    obtain ⟨hcycF, hdvd, σ, hord, hpin⟩ := burnsideAut_pinned_of_field (psuField hu) hinj hcycAut
      (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)) hUsyl hφU
      (fun σ mg => ChA.IsProjFieldAut (StatedSU 3 (2 ^ n) K) σ mg) hP ε hε F hF
    have hF2 : Nat.Coprime (Nat.card F) 2 := Nat.coprime_two_right.2 hFodd
    refine ⟨hcycF, ?_, Or.inr (Or.inr (Or.inl ⟨K, inferInstance, inferInstance,
      ε.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)), σ, hK, ?_⟩))⟩
    · rw [hcardAut] at hdvd
      exact hF2.dvd_mul_left.1 hdvd
    · exact burnsideAut_d5_pinned_mono hpin fun mg hmg => ⟨hord ▸ hF2, hmg⟩

end CFSG.ASVolI
