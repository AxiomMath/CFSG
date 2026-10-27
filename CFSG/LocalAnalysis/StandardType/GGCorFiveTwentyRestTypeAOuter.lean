module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

section Main

variable [Finite K]

theorem ggTorusWeylNormInner_coprime [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGTorusWeylNormInner p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ φ₀ hφ₀
  obtain ⟨F, hFmul, hF1, hFswap, hFW, hFA, hFinj, hFsw⟩ :=
    exists_weylModel_psl hp hp2 hpK hd hpd hsec hψ hker hperf hA hAI hr
  have hex : ∀ σ, ∃ σ', φ₀ * F σ * φ₀⁻¹ = F σ' := fun σ =>
    let ⟨σ', h⟩ := hFW _ ((Subgroup.mem_normalizer_iff.mp hφ₀ (F σ)).mp (hFA σ))
    ⟨σ', h⟩
  choose α hα using hex
  have hαmul : ∀ σ τ, α (σ * τ) = α σ * α τ := by
    intro σ τ
    apply hFinj
    rw [← hα (σ * τ), hFmul σ τ, hFmul (α σ) (α τ), ← hα σ, ← hα τ]
    group
  let αh : Equiv.Perm (Fin d) →* Equiv.Perm (Fin d) :=
    { toFun := α
      map_one' := by
        apply hFinj
        rw [← hα 1, hF1]
        group
      map_mul' := hαmul }
  have hαh : ∀ σ, αh σ = α σ := fun _ => rfl
  have hαinj : Function.Injective αh := by
    intro σ τ h
    rw [hαh, hαh] at h
    apply hFinj
    have h1 : φ₀ * F σ * φ₀⁻¹ = φ₀ * F τ * φ₀⁻¹ := by
      rw [hα, hα, h]
    exact mul_left_cancel (mul_right_cancel h1)
  have hαswap : ∀ σ : Equiv.Perm (Fin d), σ.IsSwap → (αh σ).IsSwap := by
    rintro σ ⟨i, j, hij, rfl⟩
    rw [hαh]
    obtain ⟨-, -, -, -, hps⟩ := hFswap i j hij
    have h1 := hps.conj φ₀
    rw [hα] at h1
    exact hFsw _ h1
  obtain ⟨π₀, hπ₀⟩ := exists_eq_conj_of_isSwap (by omega) αh hαinj hαswap
  have hinv : F π₀ = (F π₀⁻¹)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hFmul, mul_inv_cancel, hF1]
  refine ⟨F π₀⁻¹, hFA _, fun v hv => ?_⟩
  obtain ⟨σ, rfl⟩ := hFW v hv
  have hασ : α σ = π₀ * σ * π₀⁻¹ := by
    rw [← hαh]
    exact hπ₀ σ
  rw [hα, hασ, hFmul, hFmul, hinv]
  group

theorem ggTorusWeylNormInner_small (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusWeylNormInner p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

end Main

theorem recipeLinear_weylNormInner {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I ∧ GGTorusWeylNormInner p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggTorusPseudoReflGen_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusPseudoReflGen_small hp hpK (by omega) hd3 hpd'),
      ggTorusWeylNormInner_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusWeylNormInner_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggTorusPseudoReflGen_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusPseudoReflGen_coprime hp hp2 hpK hd4 hpd' hsec),
      ggTorusWeylNormInner_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusWeylNormInner_coprime hp hp2 hpK hd4 hpd' hsec)⟩

theorem largeEvenLabelAll_weylNormInner_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I ∧ GGTorusWeylNormInner p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_weylNormInner hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_weylNormInner hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_weylNormInner hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end TypeA

theorem ggInnerOnWeylInputOn_typeA : GGInnerOnWeylInputOn GGTypeALabel :=
  ggInnerOnWeylInputOn_of_labels fun _ _ hp hlab h =>
    TypeA.largeEvenLabelAll_weylNormInner_typeA hp hlab h

theorem ggCorFiveTwentyOuterInputOn_typeA : GGCorFiveTwentyOuterInputOn GGTypeALabel :=
  ggCorFiveTwentyOuterInputOn_of_inner ggInnerOnWeylInputOn_typeA

theorem ggCorFiveTwentyOuterInput_of_rest
    (h : GGCorFiveTwentyOuterInputOn fun p lab => ¬ GGTypeALabel p lab) :
    GGCorFiveTwentyOuterInput :=
  ggCorFiveTwentyOuterInput_of_on ggCorFiveTwentyOuterInputOn_typeA h

end CFSG.StandardType

end
