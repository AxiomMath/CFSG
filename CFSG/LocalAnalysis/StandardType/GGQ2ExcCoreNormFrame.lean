module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompE8
import CFSG.HardMathSupport.Timmesfeld.Torality.E8Chain

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.LangRat CFSG.StandardType.QTwoCav CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups


variable {τ : Tag}

section Frame

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}

theorem rootSL2_WSL_mem_commutator_of_frame (hS : NegLangTwo S) {Ψ : Set (Fin τ.rank → ℤ)}
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hν : 4 ≤ ν)
    (hψ : IsSLFrame ψ σ) (hsub : frameRoots σ ⊆ Ψ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ frameRoots σ) :
    rootSL2 τ L γ WSL ∈ ⁅rootSpan τ L Ψ ⊓ S.Γ, rootSpan τ L Ψ ⊓ S.Γ⁆ := by
  obtain ⟨hq, hAlg, hρ⟩ := hS
  have : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  have hν3 : 3 ≤ ν := by omega
  have hker : ψ.ker ≠ ⊤ := frame_ker_ne_top_of_isSLFrame (by omega) hψ
  have hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν3 ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) := odd_card_ker_of_frame_of_isSLFrame hν3 hker
  have hπ : ∀ x y, x ≠ y → S.ρ (σ x y) = σ y x := by
    intro x y hxy
    rw [hρ _ (hψ.isRoot x y hxy), hψ.neg x y]
  obtain ⟨K, hKfield, hKfin, hKalg, -⟩ := S.exists_fixedField
  let : Field K := hKfield
  let : Finite K := hKfin
  let : Algebra K L := hKalg
  have hKclos : IsAlgClosure K L := ⟨inferInstance, ⟨fun c => by
    obtain ⟨n, hnpos, hc⟩ := hAlg c
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X, ?_, ?_⟩
    · have hq1 : 1 < S.D.q ^ n := Nat.one_lt_pow hnpos.ne' S.hqpow.1.one_lt
      exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hc, sub_self]⟩⟩
  let : IsAlgClosure K L := hKclos
  obtain ⟨F', hcomm, hperf⟩ := exists_unitary_source_perfect_of_frame_of_rho S hν3 hψ 1 hπ
    (k' := K) (r := 2) (e := 1) Nat.prime_two (by norm_num) (by rw [hq]; norm_num) (by
      intro hconj
      have hfst : ν = 3 := by simpa using congrArg Prod.fst hconj
      omega)
  have hγroot : IsRoot τ γ := hψ.frameRoots_isRoot γ hγ
  have hgframe : rootSL2 τ L γ WSL ∈ rootSpan τ L (frameRoots σ) := by
    refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hγroot WSL)
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hγ
    · obtain ⟨j, k, hjk, rfl⟩ := hγ
      exact ⟨k, j, hjk.symm, (hψ.neg j k).symm⟩
  have hmodel : rootSL2 τ L γ WSL ∈ S.D.model :=
    rootSL2_WSL_mem_model_of_rho S hγroot (Or.inr (hρ γ hγroot))
  have hgfix : S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ WSL :=
    (S.D.mem_model.1 hmodel).2
  have hg2 : rootSL2 τ L γ WSL ^ 2 = 1 := by
    rw [pow_two]
    exact rootSL2_WSL_mul_self γ
  exact map_eqLocus_le_commutator_of_frame S hψ hsub hkercenter hodd F' hcomm hperf hgframe
    hgfix hg2

end Frame

section Pair

variable {L : Type} [Field L]

theorem exists_a2Hom_of_iform_eq_neg_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hγ : IsRoot τ γ) (hαγ : iform α γ = -1) :
    ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L α ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L γ := by
  have hadj : iform γ α = -1 := by rw [iform_comm, hαγ]
  rcases hτ with rfl | rfl | rfl
  ·
    have hN : Tag.E6.artifactRoots.length = 72 := Tag.length_artifactRoots Tag.E6
    obtain ⟨v, hv0, hv1⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_weyl_pair_of_tables
        (N := 72) hN
        (s := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e6FiveChain)
        (tab := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e6ChainTab)
        (fun k _ =>
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e6ChainTab_ok k (by omega))
        hα hγ hadj
    obtain ⟨θ, h1, h2⟩ := exists_normalized_a2Frame
      ((CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e6FiveFrame (L := L)).transport v)
    refine ⟨θ, ?_, ?_⟩
    · rw [h1]
      show rootSL2 Tag.E6 L
        (v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 0 1) = rootSL2 Tag.E6 L α
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e6FiveRoot01]
      exact congrArg _ hv0
    · rw [h2]
      show rootSL2 Tag.E6 L
        (v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 1 2) = rootSL2 Tag.E6 L γ
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e6FiveRoot12]
      exact congrArg _ hv1
  ·
    have hN : Tag.E7.artifactRoots.length = 126 := Tag.length_artifactRoots Tag.E7
    obtain ⟨v, hv0, hv1⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_weyl_pair_of_tables
        (N := 126) hN
        (s := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e7FiveChain)
        (tab := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e7ChainTab)
        (fun k _ => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e7ChainTab_ok k)
        hα hγ hadj
    obtain ⟨θ, h1, h2⟩ := exists_normalized_a2Frame
      ((CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e7FiveFrame (L := L)).transport v)
    refine ⟨θ, ?_, ?_⟩
    · rw [h1]
      show rootSL2 Tag.E7 L (v • CFSG.RankThree.PartOne.KE.sigmaRoot 1 0 1) =
        rootSL2 Tag.E7 L α
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e7FiveRoot01]
      exact congrArg _ hv0
    · rw [h2]
      show rootSL2 Tag.E7 L (v • CFSG.RankThree.PartOne.KE.sigmaRoot 1 1 2) =
        rootSL2 Tag.E7 L γ
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.e7FiveRoot12]
      exact congrArg _ hv1
  ·
    obtain ⟨u, -, hu0⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Torality.e8_level_step 0 hα
        (by intro j hj; exact absurd hj (Nat.not_lt_zero _))
    have huγ : IsRoot Tag.E8 (u⁻¹ • γ) := IsRoot.smul hγ u⁻¹
    have hcand : CFSG.HardMathSupport.Timmesfeld.Torality.e8Cand 1 (u⁻¹ • γ) := by
      intro j hj
      have hj' : (j : ℕ) < 1 := hj
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      have h1 : iform (u⁻¹ • γ)
          (CFSG.HardMathSupport.Timmesfeld.Torality.e8s 0) = iform γ α := by
        rw [← hu0,
          ← iform_smul u (u⁻¹ • γ) (CFSG.HardMathSupport.Timmesfeld.Torality.e8s 0),
          smul_inv_smul]
      rw [h1, iform_comm, hαγ]
      simp
    obtain ⟨w, hw0, hw1⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Torality.e8_level_step 1 huγ hcand
    obtain ⟨θ, h1, h2⟩ := exists_normalized_a2Frame
      (isA2Frame_rhoSigmaE8 (L := L) (u * w))
    refine ⟨θ, ?_, ?_⟩
    · rw [h1]
      rw [CFSG.RankThree.PartOne.KE.sigmaRootE8_eq_smul (u * w) 0 1,
        CFSG.RankThree.PartOne.KE.e8chainRoot13_values.1]
      have h0 : (Pi.single (CFSG.RankThree.PartOne.KE.e8Index 0) 1 :
          Fin Tag.E8.rank → ℤ) = CFSG.HardMathSupport.Timmesfeld.Torality.e8s 0 := by
        simp [CFSG.HardMathSupport.Timmesfeld.Torality.e8s,
          CFSG.HardMathSupport.Timmesfeld.Torality.e8idx,
          CFSG.RankThree.PartOne.KE.e8Index]
      rw [h0, mul_smul, hw0 0 (by decide), hu0]
    · rw [h2]
      rw [CFSG.RankThree.PartOne.KE.sigmaRootE8_eq_smul (u * w) 1 2,
        CFSG.RankThree.PartOne.KE.e8chainRoot13_values.2.1]
      have h0 : (Pi.single (CFSG.RankThree.PartOne.KE.e8Index 2) 1 :
          Fin Tag.E8.rank → ℤ) = CFSG.HardMathSupport.Timmesfeld.Torality.e8s 1 := by
        simp [CFSG.HardMathSupport.Timmesfeld.Torality.e8s,
          CFSG.HardMathSupport.Timmesfeld.Torality.e8idx,
          CFSG.RankThree.PartOne.KE.e8Index]
      rw [h0, mul_smul, hw1, smul_inv_smul]

theorem frameRoots_subset_of_succ {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ)
    (hsucc : ∀ (c : Fin ν) (h : (c : ℕ) + 1 < ν), σ c ⟨c + 1, h⟩ ∈ Ψ) :
    frameRoots σ ⊆ Ψ := by
  have key : ∀ i j : Fin ν, i < j → σ i j ∈ Ψ := by
    intro i j hij
    have hkey : ∀ n : ℕ, ∀ i j : Fin ν, (j : ℕ) = (i : ℕ) + n + 1 → σ i j ∈ Ψ := by
      intro n
      induction n with
      | zero =>
        intro i j h
        have hj : j = ⟨(i : ℕ) + 1, by omega⟩ := Fin.ext (by simpa using h)
        rw [hj]
        exact hsucc i (by omega)
      | succ n ih =>
        intro i j h
        have hi1 : (i : ℕ) + 1 < ν := by omega
        set m : Fin ν := ⟨(i : ℕ) + 1, hi1⟩ with hm
        have hmj : (j : ℕ) = (m : ℕ) + n + 1 := by
          have hmv : (m : ℕ) = (i : ℕ) + 1 := rfl
          omega
        have h2 : σ i m ∈ Ψ := by
          rw [hm]
          exact hsucc i hi1
        have h1 : σ m j ∈ Ψ := ih m j hmj
        have hroot : IsRoot τ (σ i m + σ m j) := by
          rw [hψ.add i m j]
          exact hψ.isRoot i j (by omega)
        rw [← hψ.add i m j]
        exact hΨ.add_mem (σ i m) h2 (σ m j) h1 hroot
    exact hkey ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
  rintro r ⟨i, j, hij, rfl⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt
  · rw [hψ.neg j i]
    exact hΨ.neg_mem _ (key j i hgt)

theorem exists_slFrame_of_three_le_compRank (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    (h3 : 3 ≤ compRank Ψ) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ),
      4 ≤ ν ∧ IsSLFrame ψ σ ∧ frameRoots σ ⊆ Ψ := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hαβ, hβγ, hαγ⟩ :=
    exists_chain3_simpleRoots (Or.inr hτ) hΨ hne h3
  have hαr : IsRoot τ α := simpleRoots_isRoot hα
  have hβr : IsRoot τ β := simpleRoots_isRoot hβ
  have hγr : IsRoot τ γ := simpleRoots_isRoot hγ
  have hα2 : iform α α = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr hτ) hαr
  have hβ2 : iform β β = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr hτ) hβr
  have hγ2 : iform γ γ = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr hτ) hγr
  have hβα : iform β α = -1 := by rw [iform_comm, hαβ]
  have hγβ : iform γ β = -1 := by rw [iform_comm, hβγ]
  have hγα : iform γ α = 0 := by rw [iform_comm, hαγ]
  let β' : Fin 3 → Fin τ.rank → ℤ := ![α, β, γ]
  have hβ'mem : ∀ c : Fin 3, β' c ∈ Ψ := by
    intro c
    fin_cases c
    · simpa [β'] using simpleRoots_subset hα
    · simpa [β'] using simpleRoots_subset hβ
    · simpa [β'] using simpleRoots_subset hγ
  have hβ'root : ∀ c : Fin 3, IsRoot τ (β' c) := by
    intro c
    fin_cases c
    · simpa [β'] using hαr
    · simpa [β'] using hβr
    · simpa [β'] using hγr
  have hG : ∀ c d : Fin 3, iform (β' c) (β' d) = chainGram c d := by
    intro c d
    fin_cases c <;> fin_cases d <;>
      simp [β', chainGram, hα2, hβ2, hγ2, hαβ, hβα, hβγ, hγβ, hαγ, hγα]
  have hθ : ∀ (c : Fin 3) (h : (c : ℕ) + 1 < 3), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (β' c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (β' ⟨c + 1, h⟩) := by
    intro c h
    fin_cases c
    · have e0 : β' 0 = α := by simp [β']
      have e1 : β' (1 : Fin 3) = β := by simp [β']
      simpa [e0, e1] using exists_a2Hom_of_iform_eq_neg_one hτ hαr hβr hαβ
    · have e1 : β' (1 : Fin 3) = β := by simp [β']
      have e2 : β' (2 : Fin 3) = γ := by simp [β']
      simpa [e1, e2] using exists_a2Hom_of_iform_eq_neg_one hτ hβr hγr hβγ
    · simp at h
  obtain ⟨ψ, hψ⟩ := exists_chainHom (Or.inr hτ) β' hβ'root hG hθ
  have hframe : IsSLFrame ψ (chainσ β') :=
    isSLFrame_chainHom (Or.inr hτ) hβ'root hG hψ
  refine ⟨3 + 1, ψ, chainσ β', by omega, hframe, ?_⟩
  refine frameRoots_subset_of_succ hframe hΨ ?_
  intro c h
  have hc : (c : ℕ) < 3 := by omega
  have hgoal : chainσ β' c ⟨(c : ℕ) + 1, h⟩ = β' ⟨(c : ℕ), hc⟩ := by
    rw [chainσ_of_val_eq β' (a := c) (b := ⟨(c : ℕ) + 1, h⟩) rfl]
  rw [hgoal]
  exact hβ'mem ⟨(c : ℕ), hc⟩

end Pair

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
