module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofTransport
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofOuter
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSeitz
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaith
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofStep1917
public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSeitz199
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

theorem seitz199_of_seitzThree
    (hA : SeitzThreeLThreePi) (hT : SeitzThreeTriality) (hO : Seitz199Outer) : Seitz199 := by
  intro X _ _ D hD3 hD9 hcase
  have hD := Item19ResProof.isElemAbelian_of_pow_three hD3 hD9
  rcases hcase with ⟨hq, hSL, hnot⟩ | ⟨p, f, hp3, hmod⟩
  · by_cases hfix : FixCube D
    · obtain ⟨q, K, _, _, ⟨hKq, hq1, ⟨ι⟩⟩ | ⟨hKq, hq2, ⟨ι⟩⟩⟩ := hSL
      · exact Item19ResProof.closure_fixSet_sl_of_fixCube hKq hq1 ι D hD hD9 hfix
      · obtain ⟨p, f, hU, hq3, hq2', ⟨ι'⟩⟩ := Item19ResProof.exists_unitary_model hq hKq hq2 ι
        exact Item19ResProof.closure_fixSet_su_of_fixCube hU hq3 hq2' ι' D hD hD9 hfix
    have hnfix : ∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s := by
      unfold FixCube at hfix
      push Not at hfix
      obtain ⟨e, he, s, hs3, hsD, hes⟩ := hfix
      exact ⟨e, he, s, hs3, hsD, hes⟩
    by_cases hinn : D ≤ (MulAut.conj : X →* MulAut X).range
    · obtain ⟨q, K, _, _, ⟨hKq, hq1, ⟨ι⟩⟩ | ⟨hKq, hq2, ⟨ι⟩⟩⟩ := hSL
      · have hq4 : q ≠ 4 := by
          rintro rfl
          exact hnot ⟨Item19ResProof.nonempty_mulEquiv_sl34 hKq ι, hinn⟩
        have h := SeitzScopeProof.kGenTwoMod_and_card_center_sl_scope hA hq hKq hq1 hq4 ι
        exact Item19ResProof.closure_fixSet_of_inner h.2 h.1 hD hD9 hinn hnfix
      · obtain ⟨p, f, hU, hq3, hq2', ⟨ι'⟩⟩ := Item19ResProof.exists_unitary_model hq hKq hq2 ι
        have h := SeitzScopeProof.kGenTwoMod_and_card_center_su_scope hA hq hU hq3 hq2' ι'
        exact Item19ResProof.closure_fixSet_of_inner h.2 h.1 hD hD9 hinn hnfix
    · exact hO X D hD3 hD9 hq hSL hinn hnfix
  · exact SeitzScopeProof.closure_fixSet_of_trialityD4_scope hT hp3 hmod D hD hD9

namespace SeitzScopeProof

open Item19Res5Proof

theorem seitz199Outer_linear_scope (hA : SeitzThreeLThreePi)
    {X : Type} [Group X] [Finite X] (D : Subgroup (MulAut X)) (hD3 : ∀ φ ∈ D, φ ^ 3 = 1)
    (hD9 : Nat.card D = 9) (hX : CFSG.IsQuasisimple X) {q : ℕ} {K : Type} [Field K] [Finite K]
    (hKq : Nat.card K = q) (hq1 : q % 3 = 1) (ι : X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)
    (hinn : ¬ D ≤ (MulAut.conj : X →* MulAut X).range)
    (hnfix : ∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) :
    Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x = x} = ⊤ := by
  set ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    ι.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm with hψ
  have hD := Item19ResProof.isElemAbelian_of_pow_three hD3 hD9
  have hE := isElemAbelian_mapAut hD ψ
  have hE9 : Nat.card (mapAut ψ D) = 9 := by rw [card_mapAut, hD9]
  have hEout : ¬ mapAut ψ D ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) K →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) K)).range := fun h =>
    hinn (le_range_conj_of_mapAut ψ h)
  have hEH := exists_moved_mapAut ψ hnfix
  by_cases hall : ∀ φ ∈ mapAut ψ D, ∃ g : GL (Fin 3) K, IsConjBy φ g
  · have hq2 : 2 ≤ q := by
      rw [← hKq]
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have h4 : 4 ≤ Nat.card K := by omega
    exact (closure_fixSet_mapAut_eq_top_iff ψ D).mp
      (closure_fixSet_sl_of_conj_outer h4 (mapAut ψ D) hE hE9 hEout hall hEH)
  · obtain ⟨φ, hφ, hφn⟩ := not_forall₂.1 hall
    have hφ3 : φ ^ 3 = 1 := hE.2 φ hφ
    obtain ⟨σ, g, hσ, hsemi⟩ := (exists_isConjBy_or_semiBy φ hφ3).resolve_left hφn
    have hq4 : q ≠ 4 := by
      rintro rfl
      have := Fintype.ofFinite K
      obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
      rw [← Nat.card_eq_fintype_card, hKq] at hcard
      have hp2 : p = 2 ∧ (n : ℕ) = 2 := by
        have h1 : p ∣ 2 ^ 2 := ⟨p ^ ((n : ℕ) - 1), by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hcard, ← pow_succ']
          congr 1
          have := n.pos
          omega⟩
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow h1)
        subst hp2
        refine ⟨rfl, ?_⟩
        have h2 : (2 : ℕ) ^ (n : ℕ) = 2 ^ 2 := by rw [← hcard]; norm_num
        exact Nat.pow_right_injective (le_refl 2) h2
      obtain ⟨rfl, hn2⟩ := hp2
      obtain ⟨h3, -⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (f := 2)
        (by norm_num) (by rw [hKq]; norm_num) hσ
      omega
    obtain ⟨hgen, hZ3⟩ := SeitzScopeProof.kGenTwoMod_and_card_center_sl_scope hA hX hKq hq1 hq4 ι
    obtain ⟨e, he, s, hs3, hsD, hes⟩ := hnfix
    have hs'E : MulAut.conj (ψ s) ∈ mapAut ψ D := by
      rw [← congr_conj]; exact ⟨_, hsD, rfl⟩
    have hcomm : MulAut.conj (ψ s) * φ = φ * MulAut.conj (ψ s) :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hs'E⟩ ⟨φ, hφ⟩)
    have hs'3 : (ψ s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    have hφs : φ (ψ s) ≠ ψ s := by
      intro hfix
      have hnot : φ ∉ Subgroup.zpowers (MulAut.conj (ψ s)) := by
        rintro ⟨n, rfl⟩
        exact hφn (isConjBy_conj_zpow (ψ s) n)
      have hc1 : MulAut.conj (ψ s) ≠ 1 := by
        intro h1
        have he' : MulAut.congr ψ e ∈ mapAut ψ D := ⟨e, he, rfl⟩
        have hfix' := apply_eq_self_of_conj_eq_one (hE.2 _ he') h1
        rw [congr_apply', MulEquiv.symm_apply_apply] at hfix'
        exact hes (ψ.injective hfix')
      have hle : mapAut ψ D ≤ MulAction.stabilizer (MulAut _) (ψ s) :=
        le_of_card_nine hE9 hs'E hφ (hE.2 _ hs'E) hc1 hnot
          (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_apply]; group)
          (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hfix)
      have h1 := hle (⟨e, he, rfl⟩ : MulAut.congr ψ e ∈ mapAut ψ D)
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, congr_apply',
        MulEquiv.symm_apply_apply] at h1
      exact hes (ψ.injective h1)
    obtain ⟨t', ht'φ, ht'c, ht'1⟩ := exists_fixed_of_semiBy hσ hsemi hφ3 hs'3 hcomm hφs
    have hφ₀ : MulAut.congr ψ.symm φ ∈ D := mem_mapAut.1 hφ
    have hφ₀1 : MulAut.congr ψ.symm φ ≠ 1 := by
      intro h1
      apply hφn
      have hφ1 : φ = 1 := by
        have := congrArg (MulAut.congr ψ) h1
        rwa [congr_congr_symm, map_one] at this
      refine ⟨1, fun t => ?_⟩
      rw [hφ1]
      simp
    have ht : ψ.symm t' ∈ Subgroup.closure (fixSet D) := by
      refine Subgroup.subset_closure ⟨MulAut.congr ψ.symm φ, hφ₀, hφ₀1, ?_⟩
      rw [congr_apply', MulEquiv.symm_symm, MulEquiv.apply_symm_apply, ht'φ]
    have hcm : s * ψ.symm t' * s⁻¹ * (ψ.symm t')⁻¹ =
        ψ.symm (ψ s * t' * (ψ s)⁻¹ * t'⁻¹) := by
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    have htc : s * ψ.symm t' * s⁻¹ * (ψ.symm t')⁻¹ ∈ Subgroup.center X := by
      rw [hcm]; exact mem_center_map ψ.symm ht'c
    have ht1 : s * ψ.symm t' * s⁻¹ * (ψ.symm t')⁻¹ ≠ 1 := by
      rw [hcm]
      intro h1
      apply ht'1
      have := congrArg ψ h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact closure_fixSet_of_cover hgen hZ3 hD hD9 he hsD hes ht htc ht1

end SeitzScopeProof

theorem seitz199Outer_of_seitzThree (hA : SeitzThreeLThreePi) (hU : Seitz199OuterUnitary) :
    Seitz199Outer := by
  intro X _ _ D hD3 hD9 hX hSL hinn hnfix
  obtain ⟨q, K, _, _, ⟨hKq, hq1, ⟨ι⟩⟩ | ⟨hKq, hq2, ⟨ι⟩⟩⟩ := hSL
  · exact SeitzScopeProof.seitz199Outer_linear_scope hA D hD3 hD9 hX hKq hq1 ι hinn hnfix
  · exact hU X D hD3 hD9 hX ⟨q, K, inferInstance, inferInstance, hKq, hq2, ⟨ι⟩⟩ hinn hnfix

theorem seitz199Outer_of_seitzField
    (hF : SeitzThreeLThreePiField) (hU : Seitz199OuterUnitary) : Seitz199Outer :=
  seitz199Outer_of_seitzThree (SeitzScopeProof.seitzThreeLThreePi_of_field hF) hU

theorem seitzL3PiGap_of_seitzField
    (hF : SeitzThreeLThreePiField) : SeitzL3PiGap :=
  seitzL3PiGap_of_seitzThree (SeitzScopeProof.seitzThreeLThreePi_of_field hF)

open Item19Res4Proof in
theorem ks1917XGen_of_seitzThree
    (hA : SeitzThreeLThreePi) (hT : SeitzThreeTriality) (hF : KS1917XGenFaithful) :
    KS1917XGen := by
  intro G _ _ X E c hXp hXq hEX hEab hE27 hcE htype
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := Step1910Proof.quotAct hEX with hρ
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := hEab.2
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  set O := CFSG.Open.pCoreOf 2 X with hO
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hEO : E ≤ Subgroup.normalizer (O : Set G) :=
    hEX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hout : Sec4.InducesOuterTheta c X := by
    rcases htype with ⟨p, e, _, -, -, -, hind⟩ | ⟨n, -, -, hout⟩
    · exact KFacts.InducesStdKind.inducesOuterTheta X hind (by decide)
    · exact hout
  have hcout := quotAct_not_mem_range_conj hEX hcE hout
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hE27]
  have hdvd : Nat.card ρ.range ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_range_dvd ρ
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  ·
    exfalso
    apply hcout
    have hbot : ρ.range = ⊥ := Subgroup.card_eq_one.mp (by rw [hk]; rfl)
    have hc1 : ρ ⟨c, hcE⟩ = 1 := by
      have : ρ ⟨c, hcE⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    exact ⟨1, by rw [map_one, hc1]⟩
  ·
    have hker9 : Nat.card ρ.ker = 9 := by
      rw [hk] at hcard
      omega
    set F : Subgroup G := ρ.ker.map E.subtype with hF
    have hFE : F ≤ E := Subgroup.map_subtype_le _
    have hF9 : Nat.card F = 9 := by
      rw [hF, Subgroup.card_map_of_injective E.subtype_injective, hker9]
    have hFX : ∀ b ∈ F, ∀ x ∈ X, x⁻¹ * (b * x * b⁻¹) ∈ O := by
      rintro _ ⟨b, hb, rfl⟩ x hx
      exact (quotAct_eq_one_iff hEX b).mp hb x hx
    have h := Step199Proof.le_inf_centralizer_sup hOX (hE3.to_le hFE) hO3 (hFE.trans hEO) hFX
    refine h.trans (sup_le_sup_right ?_ _)
    exact le_sup_of_le_right (le_iSup_of_le (⟨F, hFE, hF9⟩ :
      {F : Subgroup G // F ≤ E ∧ Nat.card F = 9}) le_rfl)
  ·
    have hker3 : Nat.card ρ.ker = 3 := by
      rw [hk] at hcard
      omega
    have hEb := isElemAbelian_range_quotAct hEX hEab
    have hnin : ¬ ρ.range ≤
        (MulAut.conj : X ⧸ CFSG.pCore 2 X →* MulAut (X ⧸ CFSG.pCore 2 X)).range :=
      fun h => hcout (h ⟨_, rfl⟩)
    have hgen : Subgroup.closure
        (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet ρ.range) = ⊤ := by
      rcases htype with ⟨p, e, hpF, he, hpe, hiso, -⟩ | ⟨n, -, hD4, -⟩
      · have h2 : 2 < p ^ (3 * e) := by
          calc 2 < p ^ e := hpe
            _ ≤ (p ^ e) ^ 3 := Nat.le_self_pow (by norm_num) _
            _ = p ^ (3 * e) := by rw [← pow_mul, mul_comm]
        exact SeitzScopeProof.closure_fixSet_of_lThreePi hA (by omega) h2 hiso (by omega) _ hEb
          (by rw [hk]; norm_num)
      · exact SeitzScopeProof.closure_fixSet_of_trialityD4_scope hT (by norm_num) hD4 _ hEb
          (by rw [hk]; norm_num)
    exact (le_iSup_sup_of_closure_eq_top hEX hE3 hEexp hE27 hker3 hgen).trans
      (sup_le_sup_right le_sup_right _)
  ·
    have hker1 : Nat.card ρ.ker = 1 := by
      rw [hk] at hcard
      omega
    refine hF G X E c hXp hXq hEX hEab hE27 hcE ?_ htype
    intro a ha hax
    have hmem : (⟨a, ha⟩ : E) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, quotAct_eq_one_iff]
      intro x hx
      exact (commutator_mem_pCoreOf_iff hx).mp (hax x hx)
    have hbot : ρ.ker = ⊥ := Subgroup.card_eq_one.mp hker1
    rw [hbot] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

theorem ks1917XGen_of_seitzThree_parts
    (hA : SeitzThreeLThreePi) (hT : SeitzThreeTriality) (hU : KS1917XGenFaithfulUnitary)
    (hD : KS1917XGenFaithfulD4) : KS1917XGen :=
  ks1917XGen_of_seitzThree hA hT (ks1917XGenFaithful_of_cases hU hD)

theorem ks1917XGen_of_seitzField
    (hF : SeitzThreeLThreePiField) (hT : SeitzThreeTriality) (hU : KS1917XGenFaithfulUnitary)
    (hD : KS1917XGenFaithfulD4) : KS1917XGen :=
  ks1917XGen_of_seitzThree_parts (SeitzScopeProof.seitzThreeLThreePi_of_field hF) hT hU hD

end CFSG.RankThree.PartTwo.Sec19
