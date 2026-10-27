module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenMinusAux2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.BorelTits CFSG.Open

private theorem w183Gen_congrM {K : Type} [Field K] {ι : Type}
    {Q : (ι → K) → K} {P P' : (ι → K) → (ι → K) → K}
    (h : ∀ v w, P v w = P' v w) (S : Set (ι → K)) :
    w183Gen Q P S ↔ w183Gen Q P' S := by
  constructor
  · intro hg T hST hcl
    exact hg T hST fun v hv w hw qv qw hp => hcl v hv w hw qv qw ((h v w).symm.trans hp)
  · intro hg T hST hcl
    exact hg T hST fun v hv w hw qv qw hp => hcl v hv w hw qv qw ((h v w).trans hp)

private theorem w183NonemptyOfGenM {K : Type} [Field K] {ι : Type}
    {Q : (ι → K) → K} {P : (ι → K) → (ι → K) → K} {S : Set (ι → K)}
    (hgen : w183Gen Q P S) (hex : ∃ v, Q v = 1) : S.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨v, hv⟩ := hex
  have hmem : v ∈ (∅ : Set (ι → K)) :=
    hgen ∅ (by simp [h]) (by intro a ha; exact absurd ha (by simp)) hv
  simpa using hmem

private theorem w183S16ntPolar_quadMinusPolar {n : ℕ} {K : Type} [Field K] [Finite K]
    (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    (v w : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2) → K) :
    s16ntPolar (StatedQuadMinus n K 1 1) v w = quadMinusPolar n K 1 1 v w := by
  simp only [s16ntPolar]
  change (quadMinusForm n K 1 1 hirr).Q (v + w) -
      (quadMinusForm n K 1 1 hirr).Q v -
      (quadMinusForm n K 1 1 hirr).Q w = quadMinusPolar n K 1 1 v w
  rw [(quadMinusForm n K 1 1 hirr).Q_add v w]
  have hp : (quadMinusForm n K 1 1 hirr).polar.β v w = quadMinusPolar n K 1 1 v w := rfl
  rw [hp]
  ring

private theorem w183S16ntNormOneGen_iffM {n : ℕ} {K : Type} [Field K] [Finite K]
    (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    (S : Set (Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2) → K)) :
    S16ntNormOneGen (StatedQuadMinus n K 1 1) S ↔
      w183Gen (StatedQuadMinus n K 1 1) (quadMinusPolar n K 1 1) S :=
  w183Gen_congrM (fun v w => w183S16ntPolar_quadMinusPolar hirr v w) S

theorem s16nt_gen_minus_main {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 2 ≤ r)
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ S : Set (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K), S.ncard ≤ 2 * r ∧
      (∀ v ∈ S, StatedQuadMinus r K b c v = 1) ∧ S16ntNormOneGen (StatedQuadMinus r K b c) S := by
  classical
  have h2 : (2 : K) = 0 := by
    rcases w183EqZeroOrOne hK (2 : K) with h | h
    · exact h
    · exfalso
      have h1 : (1 : K) = 0 := by
        have hh : (2 : K) = 1 + 1 := by norm_num
        rw [hh] at h
        exact add_left_cancel (by rw [h, add_zero])
      exact one_ne_zero h1
  have h11 : (1 : K) + 1 = 0 := by
    rw [← show (2 : K) = 1 + 1 by norm_num]; exact h2
  have hc : c = 1 := by
    rcases w183EqZeroOrOne hK c with hc0 | hc1
    · exfalso
      have h := hirr 0
      rw [hc0] at h
      have hzero : (0 : K) ^ 2 + b * 0 + 0 = 0 := by ring
      exact h hzero
    · exact hc1
  have hb : b = 1 := by
    rcases w183EqZeroOrOne hK b with hb0 | hb1
    · exfalso
      have h := hirr 1
      rw [hb0, hc] at h
      simp only [one_pow, zero_mul, mul_one, add_zero] at h
      exact h h11
    · exact hb1
  subst hc
  subst hb
  have hirr' : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := hirr
  have hK01 : ∀ x : K, x = 0 ∨ x = 1 := w183EqZeroOrOne hK
  let e : K ≃+* ZMod 2 := CFSG.Quasithin.G64.ringEquivZModTwo K hK
  obtain ⟨S₀, hS₀card, hS₀q, hS₀gen⟩ := s16nt_gen_base_minus
  have hirrZ : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hgenZ : w183Gen (StatedQuadMinus 2 (ZMod 2) 1 1) (quadMinusPolar 2 (ZMod 2) 1 1) S₀ :=
    (w183S16ntNormOneGen_iffM hirrZ S₀).mp hS₀gen
  have hgenK : w183Gen (StatedQuadMinus 2 K 1 1) (quadMinusPolar 2 K 1 1)
      ((w183PiEquiv e (Fin (2 - 1) ⊕ (Fin (2 - 1) ⊕ Fin 2))).symm '' S₀) := by
    have h := w183GenMapRingEquiv e (StatedQuadMinus 2 K 1 1) (StatedQuadMinus 2 (ZMod 2) 1 1)
      (quadMinusPolar 2 K 1 1) (quadMinusPolar 2 (ZMod 2) 1 1)
      (fun v => by simpa using w183MapStatedQuadMinus e 2 (1 : K) (1 : K) v)
      (fun v w => by simpa using w183MapQuadMinusPolar e 2 (1 : K) (1 : K) v w) hgenZ
    rwa [← Equiv.image_symm_eq_preimage (w183PiEquiv e _) S₀] at h
  let C : ℕ → Prop := fun k => ∃ S : Set (Fin (k + 1) ⊕ (Fin (k + 1) ⊕ Fin 2) → K),
      S.Nonempty ∧ S.ncard ≤ 2 * (k + 2) ∧
        (∀ v ∈ S, StatedQuadMinus (k + 2) K 1 1 v = 1) ∧
        w183Gen (StatedQuadMinus (k + 2) K 1 1) (quadMinusPolar (k + 2) K 1 1) S
  have hbase : C 0 := by
    refine ⟨(w183PiEquiv e (Fin 1 ⊕ (Fin 1 ⊕ Fin 2))).symm '' S₀, ?_, ?_, ?_, hgenK⟩
    · exact w183NonemptyOfGenM hgenK ⟨_, w183MinusNormOneVec (m := 0) (1 : K) (1 : K)⟩
    · rw [Set.ncard_image_of_injective S₀ (w183PiEquiv e _).symm.injective]
      omega
    · rintro v ⟨s, hs, rfl⟩
      have h1 : e (StatedQuadMinus 2 K 1 1
          ((w183PiEquiv e (Fin 1 ⊕ (Fin 1 ⊕ Fin 2))).symm s)) = 1 := by
        rw [w183MapStatedQuadMinus e 2 (1 : K) (1 : K), Equiv.apply_symm_apply]
        simpa using hS₀q s hs
      exact e.injective (by rw [h1, map_one])
  have hstep : ∀ k, C k → C (k + 1) := by
    intro k hCk
    obtain ⟨S, hSne, hScard, hSq, hSgen⟩ := hCk
    have hconn : ∀ u v : Fin (k + 1) ⊕ (Fin (k + 1) ⊕ Fin 2) → K,
        StatedQuadMinus (k + 2) K 1 1 u = 1 → StatedQuadMinus (k + 2) K 1 1 v = 1 → u ≠ v →
        quadMinusPolar (k + 2) K 1 1 u v = 1 ∨ ∃ w, StatedQuadMinus (k + 2) K 1 1 w = 1 ∧
          quadMinusPolar (k + 2) K 1 1 u w = 1 ∧ quadMinusPolar (k + 2) K 1 1 v w = 1 := by
      by_cases hk0 : k = 0
      · subst hk0
        exact w183MinusConnFour hK
      · have hk1 : 1 ≤ k := by omega
        have hfin : 5 ≤ Module.finrank K (Fin (k + 1) ⊕ (Fin (k + 1) ⊕ Fin 2) → K) := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum]
          simp only [Fintype.card_fin]
          omega
        have h := w183ConnQuadForm hK01 (quadMinusForm (k + 2) K 1 1 hirr') hfin
        intro u v hu hv huv
        rcases h u v hu hv huv with h1 | ⟨w, hw, h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨w, hw, h1, h2⟩
    obtain ⟨S', hS'card, hS'q, hS'gen⟩ :=
      w183MinusStep hK01 hirr' k hconn
        (w183MinusNormOneVec (m := k) (1 : K) (1 : K)) hSq hSgen
    refine ⟨S', ?_, ?_, ?_, hS'gen⟩
    · exact w183NonemptyOfGenM hS'gen ⟨_, w183MinusNormOneVec (m := k + 1) (1 : K) (1 : K)⟩
    · omega
    · exact hS'q
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  have hmain : ∀ k, C k := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih => exact hstep k ih
  obtain ⟨S, _, hScard, hSq, hSgen⟩ := hmain k
  exact ⟨S, hScard, hSq, (w183S16ntNormOneGen_iffM (n := k + 2) hirr' S).mpr hSgen⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
