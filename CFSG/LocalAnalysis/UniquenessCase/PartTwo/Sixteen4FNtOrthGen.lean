module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.BorelTits CFSG.Open

private theorem w183S16ntPolar_quadPlusPolar {r : ℕ} {K : Type} [Field K]
    (v w : Fin r ⊕ Fin r → K) :
    s16ntPolar (StatedQuadPlus r K) v w = quadPlusPolar r K v w := by
  rw [s16ntPolar, w183Qadd]
  ring

private theorem w183Gen_congr {K : Type} [Field K] {ι : Type}
    {Q : (ι → K) → K} {P P' : (ι → K) → (ι → K) → K}
    (h : ∀ v w, P v w = P' v w) (S : Set (ι → K)) :
    w183Gen Q P S ↔ w183Gen Q P' S := by
  constructor
  · intro hg T hST hcl
    exact hg T hST fun v hv w hw qv qw hp => hcl v hv w hw qv qw ((h v w).symm.trans hp)
  · intro hg T hST hcl
    exact hg T hST fun v hv w hw qv qw hp => hcl v hv w hw qv qw ((h v w).trans hp)

private theorem w183S16ntNormOneGen_iff {r : ℕ} {K : Type} [Field K]
    (S : Set (Fin r ⊕ Fin r → K)) :
    S16ntNormOneGen (StatedQuadPlus r K) S ↔
      w183Gen (StatedQuadPlus r K) (quadPlusPolar r K) S :=
  w183Gen_congr (fun v w => w183S16ntPolar_quadPlusPolar v w) S

private theorem w183NonemptyOfGen {K : Type} [Field K] {ι : Type}
    {Q : (ι → K) → K} {P : (ι → K) → (ι → K) → K} {S : Set (ι → K)}
    (hgen : w183Gen Q P S) (hex : ∃ v, Q v = 1) : S.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨v, hv⟩ := hex
  have hmem : v ∈ (∅ : Set (ι → K)) :=
    hgen ∅ (by simp [h]) (by intro a ha; exact absurd ha (by simp)) hv
  simpa using hmem

private theorem w183StatedQuadPlus_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K')
    (r : ℕ) (v : Fin r ⊕ Fin r → K) :
    e (StatedQuadPlus r K v) =
      StatedQuadPlus r K' (w183PiEquiv e (Fin r ⊕ Fin r) v) := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, map_sum, map_mul,
    w183PiEquiv_apply]

private theorem w183QuadPlusPolar_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K')
    (r : ℕ) (v w : Fin r ⊕ Fin r → K) :
    e (quadPlusPolar r K v w) =
      quadPlusPolar r K' (w183PiEquiv e (Fin r ⊕ Fin r) v)
        (w183PiEquiv e (Fin r ⊕ Fin r) w) := by
  simp only [quadPlusPolar, map_sum, map_add, map_mul, w183PiEquiv_apply]

private theorem w183ExistsNormOnePlus (r : ℕ) (K : Type) [Field K] :
    ∃ v : Fin (r + 1) ⊕ Fin (r + 1) → K, StatedQuadPlus (r + 1) K v = 1 := by
  refine ⟨w183PlusX r K + w183PlusY r K, ?_⟩
  have h := w183PlusForm (r := r) (K := K) (0 : Fin r ⊕ Fin r → K) 1 1
  simp only [w183PlusExt_zero, zero_add, one_smul, mul_one] at h
  simpa [w183Qzero (r := r) (K := K)] using h

theorem s16nt_gen_plus {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2) :
    ∃ S : Set (Fin r ⊕ Fin r → K), S.ncard ≤ 2 * r + 1 ∧ (∀ v ∈ S, StatedQuadPlus r K v = 1) ∧
      S16ntNormOneGen (StatedQuadPlus r K) S := by
  classical
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := w183EqZeroOrOne hK
  let e : K ≃+* ZMod 2 := CFSG.Quasithin.G64.ringEquivZModTwo K hK
  obtain ⟨S₀, hS₀card, hS₀q, hS₀gen⟩ := s16nt_gen_base_plus
  have hgenZ : w183Gen (StatedQuadPlus 3 (ZMod 2)) (quadPlusPolar 3 (ZMod 2)) S₀ :=
    (w183S16ntNormOneGen_iff S₀).mp hS₀gen
  have hgenK : w183Gen (StatedQuadPlus 3 K) (quadPlusPolar 3 K)
      ((w183PiEquiv e (Fin 3 ⊕ Fin 3)).symm '' S₀) := by
    have h := w183GenMapRingEquiv e (StatedQuadPlus 3 K) (StatedQuadPlus 3 (ZMod 2))
      (quadPlusPolar 3 K) (quadPlusPolar 3 (ZMod 2))
      (fun v => w183StatedQuadPlus_map e 3 v)
      (fun v w => w183QuadPlusPolar_map e 3 v w) hgenZ
    rwa [← Equiv.image_symm_eq_preimage (w183PiEquiv e (Fin 3 ⊕ Fin 3)) S₀] at h
  have hcard : ((w183PiEquiv e (Fin 3 ⊕ Fin 3)).symm '' S₀).ncard ≤ 2 * 3 + 1 := by
    rw [Set.ncard_image_of_injective S₀ (w183PiEquiv e (Fin 3 ⊕ Fin 3)).symm.injective]
    omega
  have hq : ∀ v ∈ ((w183PiEquiv e (Fin 3 ⊕ Fin 3)).symm '' S₀),
      StatedQuadPlus 3 K v = 1 := by
    rintro v ⟨s, hs, rfl⟩
    have h1 : e (StatedQuadPlus 3 K ((w183PiEquiv e (Fin 3 ⊕ Fin 3)).symm s)) = 1 := by
      rw [w183StatedQuadPlus_map, Equiv.apply_symm_apply]
      exact hS₀q s hs
    exact e.injective (by rw [h1, map_one])
  have hne : ((w183PiEquiv e (Fin 3 ⊕ Fin 3)).symm '' S₀).Nonempty :=
    w183NonemptyOfGen hgenK (by simpa using w183ExistsNormOnePlus 2 K)
  let C : ℕ → Prop := fun n => ∃ S : Set (Fin n ⊕ Fin n → K),
      S.Nonempty ∧ S.ncard ≤ 2 * n + 1 ∧ (∀ v ∈ S, StatedQuadPlus n K v = 1) ∧
        w183Gen (StatedQuadPlus n K) (quadPlusPolar n K) S
  have hbase : C 3 := ⟨_, hne, hcard, hq, hgenK⟩
  have hstep : ∀ n, 3 ≤ n → C n → C (n + 1) := by
    intro n hn hCn
    obtain ⟨S, hSne, hScard, hSq, hSgen⟩ := hCn
    obtain ⟨S', hS'card, hS'q, hS'gen⟩ :=
      w183PlusStep (K := K) h01 hn hSne hSq hSgen
    exact ⟨S', w183NonemptyOfGen hS'gen (by simpa using w183ExistsNormOnePlus n K),
      by omega, hS'q, hS'gen⟩
  have hmain : ∀ n, 3 ≤ n → C n :=
    Nat.le_induction (m := 3) (P := fun n _ => C n) hbase hstep
  obtain ⟨S, _, hScard, hSq, hSgen⟩ := hmain r hr
  exact ⟨S, hScard, hSq, (w183S16ntNormOneGen_iff S).mpr hSgen⟩

theorem s16nt_gen_minus {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 2 ≤ r)
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ S : Set (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K), S.ncard ≤ 2 * r ∧
      (∀ v ∈ S, StatedQuadMinus r K b c v = 1) ∧ S16ntNormOneGen (StatedQuadMinus r K b c) S :=
  s16nt_gen_minus_main hr hK hirr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
