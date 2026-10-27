module

public import CFSG.OddTranspositions.PartFour.SpPlaneSL2
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.OddTranspositions.PartFour.UnitaryClass
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURoot
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Open CFSG.LocalAnalysis.WeakClosure81 CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits

private theorem rootGroupU_single_add_smul_ne_zero {d : ℕ} {K : Type} [Field K]
    {i j : Fin d} (hij : i ≠ j) (c : K) :
    (Pi.single i 1 + c • Pi.single j 1 : Fin d → K) ≠ 0 := by
  intro h
  have h' := congrFun h i
  have h1 : (1 : K) = 0 := by
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne hij] using h'
  exact one_ne_zero h1

private theorem rootGroupU_herm_pair {n : ℕ} {K : Type} [Field K] {σ : K ≃+* K}
    {i j : Fin n} (hij : i ≠ j) (c d : K) :
    herm σ (Pi.single i 1 + c • Pi.single j 1)
      (Pi.single i 1 + d • Pi.single j 1) = 1 + σ c * d := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    herm_single_left, herm_single_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij),
    map_add, map_mul, map_zero, map_one, one_mul, mul_zero, zero_mul, mul_one,
    add_zero, zero_add]
  ring

private theorem rootGroupU_herm_disjoint {n : ℕ} {K : Type} [Field K] {σ : K ≃+* K}
    {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (c d : K) :
    herm σ (Pi.single i 1 + c • Pi.single j 1)
      (Pi.single k 1 + d • Pi.single l 1) = 0 := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    herm_single_left, herm_single_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same, Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hil,
    Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjl, Pi.single_eq_of_ne (Ne.symm hik),
    Pi.single_eq_of_ne (Ne.symm hil), Pi.single_eq_of_ne (Ne.symm hjk),
    Pi.single_eq_of_ne (Ne.symm hjl), map_add, map_mul, map_zero, map_one, one_mul,
    mul_zero, zero_mul, mul_one, add_zero, zero_add]

private theorem rootGroupU_centre_pair {d : ℕ} {K : Type} [Field K] [CharP K 2]
    {σ : K ≃+* K} {i j : Fin d} (hij : i ≠ j) {ω : K}
    (hω1 : σ ω * ω = 1) (hω : ω ≠ 1) :
    (Pi.single i 1 + (1 : K) • Pi.single j 1 : Fin d → K) ≠ 0 ∧
      (Pi.single i 1 + ω • Pi.single j 1) ≠ 0 ∧
      herm σ (Pi.single i 1 + (1 : K) • Pi.single j 1)
        (Pi.single i 1 + (1 : K) • Pi.single j 1) = 0 ∧
      herm σ (Pi.single i 1 + ω • Pi.single j 1)
        (Pi.single i 1 + ω • Pi.single j 1) = 0 ∧
      herm σ (Pi.single i 1 + (1 : K) • Pi.single j 1)
        (Pi.single i 1 + ω • Pi.single j 1) ≠ 0 := by
  have hq := rootGroupU_single_add_smul_ne_zero hij (1 : K)
  have hq' := rootGroupU_single_add_smul_ne_zero hij ω
  have hi : herm σ (Pi.single i 1 + (1 : K) • Pi.single j 1)
      (Pi.single i 1 + (1 : K) • Pi.single j 1) = 0 := by
    rw [rootGroupU_herm_pair (σ := σ) hij (1 : K) (1 : K), map_one, one_mul]
    exact CharTwo.add_self_eq_zero 1
  have hi' : herm σ (Pi.single i 1 + ω • Pi.single j 1)
      (Pi.single i 1 + ω • Pi.single j 1) = 0 := by
    rw [rootGroupU_herm_pair (σ := σ) hij ω ω, hω1]
    exact CharTwo.add_self_eq_zero 1
  have hn : herm σ (Pi.single i 1 + (1 : K) • Pi.single j 1)
      (Pi.single i 1 + ω • Pi.single j 1) ≠ 0 := by
    rw [rootGroupU_herm_pair (σ := σ) hij (1 : K) ω, map_one, one_mul]
    intro h
    exact hω (CharTwo.add_eq_zero.mp h).symm
  exact ⟨hq, hq', hi, hi', hn⟩

private theorem rootGroupU_four_indices {d : ℕ} (hd : 4 ≤ d) :
    ∃ i₀ i₁ i₂ i₃ : Fin d, i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₀ ≠ i₃ ∧
      i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ := by
  let i₀ : Fin d := ⟨0, by omega⟩
  let i₁ : Fin d := ⟨1, by omega⟩
  let i₂ : Fin d := ⟨2, by omega⟩
  let i₃ : Fin d := ⟨3, by omega⟩
  refine ⟨i₀, i₁, i₂, i₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [i₀, i₁] using rootGroupU_fin_ne (by omega) (by omega) (by omega)
  · simpa [i₀, i₂] using rootGroupU_fin_ne (by omega) (by omega) (by omega)
  · simpa [i₀, i₃] using rootGroupU_fin_ne (by omega) (by omega) (by omega)
  · simpa [i₁, i₂] using rootGroupU_fin_ne (by omega) (by omega) (by omega)
  · simpa [i₁, i₃] using rootGroupU_fin_ne (by omega) (by omega) (by omega)
  · simpa [i₂, i₃] using rootGroupU_fin_ne (by omega) (by omega) (by omega)

private theorem rootGroupU_four_centres {d : ℕ} {K : Type} [Field K] [CharP K 2]
    {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) (hd : 4 ≤ d) :
    ∃ c₁ c₂ c₃ c₄ : Fin d → K,
      c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ c₃ ≠ 0 ∧ c₄ ≠ 0 ∧
      herm σ c₁ c₁ = 0 ∧ herm σ c₂ c₂ = 0 ∧
      herm σ c₃ c₃ = 0 ∧ herm σ c₄ c₄ = 0 ∧
      herm σ c₁ c₂ ≠ 0 ∧ herm σ c₃ c₄ ≠ 0 ∧
      herm σ c₁ c₃ = 0 ∧ herm σ c₁ c₄ = 0 ∧
      herm σ c₂ c₃ = 0 ∧ herm σ c₂ c₄ = 0 := by
  obtain ⟨ω, hω1, hω⟩ := hσ.exists_norm_one_ne_one
  obtain ⟨i₀, i₁, i₂, i₃, h01, h02, h03, h12, h13, h23⟩ := rootGroupU_four_indices hd
  obtain ⟨hc1, hc2, hi1, hi2, hn12⟩ :=
    rootGroupU_centre_pair (σ := σ) (i := i₀) (j := i₁) h01 hω1 hω
  obtain ⟨hc3, hc4, hi3, hi4, hn34⟩ :=
    rootGroupU_centre_pair (σ := σ) (i := i₂) (j := i₃) h23 hω1 hω
  have ho13 := rootGroupU_herm_disjoint (σ := σ) h02 h03 h12 h13 (1 : K) (1 : K)
  have ho14 := rootGroupU_herm_disjoint (σ := σ) h02 h03 h12 h13 (1 : K) ω
  have ho23 := rootGroupU_herm_disjoint (σ := σ) h02 h03 h12 h13 ω (1 : K)
  have ho24 := rootGroupU_herm_disjoint (σ := σ) h02 h03 h12 h13 ω ω
  refine ⟨Pi.single i₀ 1 + (1 : K) • Pi.single i₁ 1,
    Pi.single i₀ 1 + ω • Pi.single i₁ 1,
    Pi.single i₂ 1 + (1 : K) • Pi.single i₃ 1,
    Pi.single i₂ 1 + ω • Pi.single i₃ 1, ?_⟩
  exact ⟨hc1, hc2, hc3, hc4, hi1, hi2, hi3, hi4, hn12, hn34,
    ho13, ho14, ho23, ho24⟩

private theorem rootGroupU_model_subgroup {m n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = (2 ^ n) ^ 2) {c : Fin m → F} (hc0 : c ≠ 0)
    (hc : herm (unitaryInvolution F 2 n) c c = 0) :
    ∃ R : Subgroup (StatedProj (StatedSU m (2 ^ n) F)),
      (R : Set (StatedProj (StatedSU m (2 ^ n) F))) =
        insert 1 (Vmem {y | ∃ c' : Fin m → F, c' ≠ 0 ∧
          herm (unitaryInvolution F 2 n) c' c' = 0 ∧
            y = kFactsSuProjTv hF m c' 1} (kFactsSuProjTv hF m c 1)) := by
  refine ⟨spUFixRootU hF m c, ?_⟩
  ext y
  rw [SetLike.mem_coe, mem_spUFixRootU hF hc]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Set.mem_insert_iff]
    by_cases hs0 : s = 0
    · left
      unfold kFactsSuProjTv
      rw [hs0, kFacts_suTv_zero_param hF hc, map_one]
    · right
      rw [Vmem_setOf_kFactsSuProjTv hF hc0 hc]
      exact ⟨s, hs0, hs, rfl⟩
  · intro hy
    rw [Set.mem_insert_iff] at hy
    rcases hy with h1 | hV
    · refine ⟨0, by simp, ?_⟩
      rw [h1]
      unfold kFactsSuProjTv
      rw [kFacts_suTv_zero_param hF hc, map_one]
    · rw [Vmem_setOf_kFactsSuProjTv hF hc0 hc] at hV
      obtain ⟨s, -, hs, rfl⟩ := hV
      exact ⟨s, hs, rfl⟩

private theorem rootGroupU_model_ncard {m n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = (2 ^ n) ^ 2) {c : Fin m → F} (hc0 : c ≠ 0)
    (hc : herm (unitaryInvolution F 2 n) c c = 0) :
    (Vmem {y | ∃ c' : Fin m → F, c' ≠ 0 ∧
      herm (unitaryInvolution F 2 n) c' c' = 0 ∧
        y = kFactsSuProjTv hF m c' 1} (kFactsSuProjTv hF m c 1)).ncard =
      2 ^ n - 1 := by
  rw [Vmem_setOf_kFactsSuProjTv hF hc0 hc]
  let B : Set F := {s | s ≠ 0 ∧ s + unitaryInvolution F 2 n s = 0}
  have hB : B.ncard = 2 ^ n - 1 := by
    have h0 : (0 : F) ∈ {s : F | s + unitaryInvolution F 2 n s = 0} := by simp
    have hcard : ({s : F | s + unitaryInvolution F 2 n s = 0} : Set F).ncard = 2 ^ n := by
      rw [← Nat.card_coe_set_eq]
      exact kFacts_card_traceZero hF
    have hdiff := Set.ncard_diff_singleton_of_mem h0
    rw [hcard] at hdiff
    have hset : B = {s : F | s + unitaryInvolution F 2 n s = 0} \ {0} := by
      ext s
      simp only [B, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hs0, hs⟩
        exact ⟨hs, hs0⟩
      · rintro ⟨hs, hs0⟩
        exact ⟨hs0, hs⟩
    rw [hset, hdiff]
  have hset : {y | ∃ s : F, s ≠ 0 ∧ s + unitaryInvolution F 2 n s = 0 ∧
      y = kFactsSuProjTv hF m c s} =
      (fun s : F => kFactsSuProjTv hF m c s) '' B := by
    ext y
    exact ⟨fun ⟨s, hs0, hs, hys⟩ => ⟨s, ⟨hs0, hs⟩, hys.symm⟩,
      fun ⟨s, ⟨hs0, hs⟩, hys⟩ => ⟨s, hs0, hs, hys.symm⟩⟩
  have hinj : Set.InjOn (fun s : F => kFactsSuProjTv hF m c s) B := by
    intro s hs s' hs' h
    exact kFacts_suProjTv_injective hF hc0 hc hs.2 hs'.2 h
  rw [hset, hinj.ncard_image]
  exact hB

private theorem rootGroupU_four_model {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 4 ≤ d) :
    ∃ t ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
        herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1},
      ∃ u ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
          herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1},
        ∃ v ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
            herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1},
          ∃ w ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
              herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1},
            ¬ Commute t u ∧ ¬ Commute v w ∧ Commute v t ∧ Commute v u ∧
              Commute w t ∧ Commute w u := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨c₁, c₂, c₃, c₄, hc1, hc2, hc3, hc4, hi1, hi2, hi3, hi4, hn12, hn34,
    ho13, ho14, ho23, ho24⟩ := rootGroupU_four_centres (σ := unitaryInvolution K 2 f) hσ hd
  have ht : (1 : K) + unitaryInvolution K 2 f 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hcomm : ∀ {c a : Fin d → K}, c ≠ 0 → herm (unitaryInvolution K 2 f) c c = 0 →
      a ≠ 0 → herm (unitaryInvolution K 2 f) a a = 0 →
      herm (unitaryInvolution K 2 f) c a = 0 →
      Commute (kFactsSuProjTv hK d c 1) (kFactsSuProjTv hK d a 1) := by
    intro c a hc0 hc ha0 ha hca
    exact (commute_kFactsSuProjTv_iff hK hc0 hc ha0 ha one_ne_zero ht
      one_ne_zero ht).mpr hca
  have hnc : ∀ {c a : Fin d → K}, c ≠ 0 → herm (unitaryInvolution K 2 f) c c = 0 →
      a ≠ 0 → herm (unitaryInvolution K 2 f) a a = 0 →
      herm (unitaryInvolution K 2 f) c a ≠ 0 →
      ¬ Commute (kFactsSuProjTv hK d c 1) (kFactsSuProjTv hK d a 1) := by
    intro c a hc0 hc ha0 ha hca hcomm'
    exact hca ((commute_kFactsSuProjTv_iff hK hc0 hc ha0 ha one_ne_zero ht
      one_ne_zero ht).mp hcomm')
  have hσinv := hσ.invol
  refine ⟨kFactsSuProjTv hK d c₁ 1, ⟨c₁, hc1, hi1, rfl⟩,
    kFactsSuProjTv hK d c₂ 1, ⟨c₂, hc2, hi2, rfl⟩,
    kFactsSuProjTv hK d c₃ 1, ⟨c₃, hc3, hi3, rfl⟩,
    kFactsSuProjTv hK d c₄ 1, ⟨c₄, hc4, hi4, rfl⟩, ?_⟩
  exact ⟨hnc hc1 hi1 hc2 hi2 hn12, hnc hc3 hi3 hc4 hi4 hn34,
    hcomm hc3 hi3 hc1 hi1 (herm_eq_zero_comm (unitaryInvolution K 2 f) hσinv ho13),
    hcomm hc3 hi3 hc2 hi2 (herm_eq_zero_comm (unitaryInvolution K 2 f) hσinv ho23),
    hcomm hc4 hi4 hc1 hi1 (herm_eq_zero_comm (unitaryInvolution K 2 f) hσinv ho14),
    hcomm hc4 hi4 hc2 hi2 (herm_eq_zero_comm (unitaryInvolution K 2 f) hσinv ho24)⟩

private theorem rootGroupU_data {X : Type} [Group X] {s : X} {d f : ℕ}
    (hZ : Subgroup.center X = ⊥) (hd : 3 ≤ d) (hs : IsUnitaryTransvection X d f s) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (hK : Nat.card K = (2 ^ f) ^ 2)
      (φ : X ≃* StatedProj (StatedSU d (2 ^ f) K)) (e₀ : Fin d → K),
      e₀ ≠ 0 ∧ herm (unitaryInvolution K 2 f) e₀ e₀ = 0 ∧
        φ s = kFactsSuProjTv hK d e₀ 1 ∧
        φ '' {y | IsConj s y} =
          {y | ∃ c : Fin d → K, c ≠ 0 ∧
            herm (unitaryInvolution K 2 f) c c = 0 ∧
              y = kFactsSuProjTv hK d c 1} := by
  obtain ⟨K, hKfield, hKfin, hKchar, hK, φ, e₀, he₀0, he₀i, hφs⟩ :=
    exists_mulEquiv_of_isUnitaryTransvection hZ hs
  refine ⟨K, hKfield, hKfin, hKchar, hK, φ, e₀, he₀0, he₀i, hφs, ?_⟩
  rw [CFSG.Fischer.image_setOf_isConj φ s, hφs]
  exact setOf_isConj_kFactsSuProjTv hK hd he₀0 he₀i

theorem exists_subgroup_eq_insert_Vmem_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {d f : ℕ} (hd : 3 ≤ d)
    (hs : IsUnitaryTransvection X d f s) {x : X} (hx : x ∈ {y | IsConj s y}) :
    ∃ R : Subgroup X, (R : Set X) = insert 1 (Vmem {y | IsConj s y} x) := by
  obtain ⟨K, hKfield, hKfin, hKchar, hK, φ, e₀, he₀0, he₀i, hφs, hclass⟩ :=
    rootGroupU_data hZ hd hs
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hxS : φ x ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
      herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1} := by
    rw [← hclass]
    exact ⟨x, hx, rfl⟩
  obtain ⟨c, hc0, hc, hφx⟩ := hxS
  have hV : φ '' Vmem {y | IsConj s y} x =
      Vmem {y | ∃ c' : Fin d → K, c' ≠ 0 ∧
        herm (unitaryInvolution K 2 f) c' c' = 0 ∧
          y = kFactsSuProjTv hK d c' 1} (kFactsSuProjTv hK d c 1) := by
    have h := Vmem_image_mulEquiv φ {y | IsConj s y} x
    rw [hclass] at h
    rw [← h, hφx]
  obtain ⟨R₀, hR₀⟩ := rootGroupU_model_subgroup hK hc0 hc
  refine ⟨R₀.comap φ.toMonoidHom, ?_⟩
  have himg : φ '' insert 1 (Vmem {y | IsConj s y} x) =
      insert 1 (Vmem {y | ∃ c' : Fin d → K, c' ≠ 0 ∧
        herm (unitaryInvolution K 2 f) c' c' = 0 ∧
          y = kFactsSuProjTv hK d c' 1} (kFactsSuProjTv hK d c 1)) := by
    rw [Set.image_insert_eq, map_one, hV]
  ext y
  rw [Subgroup.coe_comap, Set.mem_preimage, hR₀]
  constructor
  · intro hy
    rw [← himg] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [φ.injective hzy] at hz
  · intro hy
    rw [← himg]
    exact ⟨y, hy, rfl⟩

theorem ncard_Vmem_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {d f : ℕ} (hd : 3 ≤ d)
    (hs : IsUnitaryTransvection X d f s) {x : X} (hx : x ∈ {y | IsConj s y}) :
    (Vmem {y | IsConj s y} x).ncard = 2 ^ f - 1 := by
  obtain ⟨K, hKfield, hKfin, hKchar, hK, φ, e₀, he₀0, he₀i, hφs, hclass⟩ :=
    rootGroupU_data hZ hd hs
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hxS : φ x ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
      herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1} := by
    rw [← hclass]
    exact ⟨x, hx, rfl⟩
  obtain ⟨c, hc0, hc, hφx⟩ := hxS
  have hV : φ '' Vmem {y | IsConj s y} x =
      Vmem {y | ∃ c' : Fin d → K, c' ≠ 0 ∧
        herm (unitaryInvolution K 2 f) c' c' = 0 ∧
          y = kFactsSuProjTv hK d c' 1} (kFactsSuProjTv hK d c 1) := by
    have h := Vmem_image_mulEquiv φ {y | IsConj s y} x
    rw [hclass] at h
    rw [← h, hφx]
  have hnc : (Vmem {y | IsConj s y} x).ncard =
      (Vmem {y | ∃ c' : Fin d → K, c' ≠ 0 ∧
        herm (unitaryInvolution K 2 f) c' c' = 0 ∧
          y = kFactsSuProjTv hK d c' 1} (kFactsSuProjTv hK d c 1)).ncard := by
    rw [← Set.ncard_image_of_injective (Vmem {y | IsConj s y} x) φ.injective, hV]
  rw [hnc]
  exact rootGroupU_model_ncard hK hc0 hc

theorem exists_four_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {d f : ℕ} (hd : 4 ≤ d)
    (hs : IsUnitaryTransvection X d f s) :
    ∃ t ∈ {y | IsConj s y}, ∃ u ∈ {y | IsConj s y}, ∃ v ∈ {y | IsConj s y},
      ∃ w ∈ {y | IsConj s y}, ¬ Commute t u ∧ ¬ Commute v w ∧
        Commute v t ∧ Commute v u ∧ Commute w t ∧ Commute w u := by
  obtain ⟨K, hKfield, hKfin, hKchar, hK, φ, e₀, he₀0, he₀i, hφs, hclass⟩ :=
    rootGroupU_data hZ (by omega) hs
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨t', ht', u', hu', v', hv', w', hw', htu, hvw, hvt, hvu, hwt, hwu⟩ :=
    rootGroupU_four_model hK hd
  have hclass' : φ.symm '' {y | ∃ c : Fin d → K, c ≠ 0 ∧
      herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1} =
      {y | IsConj s y} := by
    rw [← hclass]
    exact CFSG.Fischer.image_symm_image φ {y | IsConj s y}
  have hmem : ∀ z ∈ {y | ∃ c : Fin d → K, c ≠ 0 ∧
      herm (unitaryInvolution K 2 f) c c = 0 ∧ y = kFactsSuProjTv hK d c 1},
      φ.symm z ∈ {y | IsConj s y} := by
    intro z hz
    rw [← hclass']
    exact ⟨z, hz, rfl⟩
  have hcomm : ∀ {z z' : StatedProj (StatedSU d (2 ^ f) K)}, Commute z z' →
      Commute (φ.symm z) (φ.symm z') := fun h => by
    simpa using h.map φ.symm.toMonoidHom
  have hnc : ∀ {z z' : StatedProj (StatedSU d (2 ^ f) K)}, ¬ Commute z z' →
      ¬ Commute (φ.symm z) (φ.symm z') := fun h hc' => h (by
    simpa using hc'.map φ.toMonoidHom)
  exact ⟨φ.symm t', hmem t' ht', φ.symm u', hmem u' hu', φ.symm v', hmem v' hv',
    φ.symm w', hmem w' hw', hnc htu, hnc hvw, hcomm hvt, hcomm hvu, hcomm hwt, hcomm hwu⟩

end CFSG.OddTranspositions.PartFour
