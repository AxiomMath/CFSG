module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Gu2
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.QuasithinUnique
  CFSG.Quasithin.B6

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem not_isIrrIn_of_fixes_line {p : ℕ} [Fact p.Prime] {Y : Subgroup (SU3F p F)}
    (hY : ∀ y ∈ Y, matU y 0 2 = 0 ∧ matU y 1 2 = 0) :
    ¬ IsIrrIn (StatedSU 3 (p ^ 1) F) Y := by
  intro hirr
  let W : Submodule F (Fin 3 → F) := Submodule.span F {![0, 0, 1]}
  have hW : ∀ g : ↥(Y.map (StatedSU 3 (p ^ 1) F).subtype), ∀ v ∈ W,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
    rintro ⟨_, g, hg, rfl⟩ v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨h0, h1⟩ := hY g hg
    refine Submodule.mem_span_singleton.mpr ⟨c * matU g 2 2, ?_⟩
    funext j
    have h0' : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := h0
    have h1' : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := h1
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0', h1', matU]
    exact mul_comm _ _
  rcases hirr W hW with hbot | htop
  · have : (![0, 0, 1] : Fin 3 → F) ∈ W := Submodule.mem_span_singleton_self _
    rw [hbot] at this
    have h2 := congrFun (Submodule.mem_bot _ |>.mp this) 2
    simp at h2
  · have : (![1, 0, 0] : Fin 3 → F) ∈ W := by rw [htop]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have h0 := congrFun hc 0
    simp at h0

theorem normal_two_le_leviU (hF : Nat.card F = 3 ^ 2) {Y N : Subgroup (SU3F 3 F)}
    (hB : leviU hF ≤ Y) (hNY : N ≤ Y) (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N)
    (hexp : ∀ a ∈ N, a ^ 2 = 1) : N ≤ leviU hF := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrel : Odd ((leviU hF).relIndex Y) := by
    have h1 := Subgroup.relIndex_mul_index hB
    have h2 : Odd ((leviU hF).relIndex Y * Y.index) := by
      rw [h1]
      exact odd_index_leviU hp2 hF
    exact (Nat.odd_mul.mp h2).1
  obtain ⟨S, hS, -⟩ := exists_isSylowTwoOf_ge (J := leviU hF) (X := ⊥)
    (IsPGroup.of_card (n := 0) (by simp)) bot_le
  have hSodd : Odd (S.relIndex (leviU hF)) :=
    Nat.not_even_iff_odd.mp fun he => hS.2.2 (even_iff_two_dvd.mp he)
  have hSY : IsSylowTwoOf S Y := by
    refine ⟨hS.1.trans hB, hS.2.1, fun hd => ?_⟩
    have h3 := Subgroup.relIndex_mul_relIndex S (leviU hF) Y hS.1 hB
    have hodd3 : Odd (S.relIndex Y) := by
      rw [← h3]
      exact hSodd.mul hrel
    exact (Nat.not_even_iff_odd.mpr hodd3) (even_iff_two_dvd.mpr hd)
  have hN2 : IsPGroup 2 ↥(N.subgroupOf Y) := fun g => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hexp (g.1 : SU3F 3 F) g.2⟩
  have : (N.subgroupOf Y).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g.1 g.2 n.1 hn⟩
  have hle := hN2.le_sylow_of_normal (toSylow2 hSY)
  intro a ha
  have h1 : (⟨a, hNY ha⟩ : ↥Y) ∈ N.subgroupOf Y := ha
  have h2 := hle h1
  rw [toSylow2_coe] at h2
  exact hS.1 (Subgroup.mem_subgroupOf.mp h2)

theorem matU_eq_of_normal_two (hF : Nat.card F = 3 ^ 2) {Y N : Subgroup (SU3F 3 F)}
    (hB : leviU hF ≤ Y) (hNY : N ≤ Y) (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hexp : ∀ a ∈ N, a ^ 2 = 1) {a : SU3F 3 F}
    (ha : a ∈ N) (ha1 : a ≠ 1) : matU a = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_u3 hF
  have h3 := three_eq_zero_u3 hF
  obtain ⟨A, rfl⟩ := normal_two_le_leviU hF hB hNY hnorm hexp ha
  have hA2 : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h1 : Lemma41aU3.blkU (uniData hF) (A * A) = Lemma41aU3.blkU (uniData hF) 1 := by
      rw [map_mul, map_one, ← pow_two]
      exact hexp _ ha
    have h2 := Lemma41aU3.blkU_injective (uniData hF) h1
    have h3' := congrArg (fun x : ↥(GU2Stated (3 ^ 1) F) =>
      ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h2
    simpa using h3'
  have c1 := gu2_conj_commute hB hnorm hcomm (g := gE1 hF) (ginv := gAlg1) ha gAlg1_mul
  have c2 := gu2_conj_commute hB hnorm hcomm (g := gE2 hF hi) (ginv := gAlg2' i) ha
    (gAlg2'_mul hi)
  have c3 := gu2_conj_commute hB hnorm hcomm (g := gE3 hF hi) (ginv := gAlg3' i) ha
    (gAlg3'_mul h3 hi)
  rcases involution_gu2_eq h3 hi hA2 c1 c2 c3 with h1 | h1
  · exfalso
    apply ha1
    have : A = 1 := Subtype.ext (Units.ext (by simpa using h1))
    rw [this, map_one]
  · rw [matU_blkU hF, h1]
    have hdet : (-1 : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    rw [hdet, inv_one]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Lemma41aL3.blkMat]

theorem false_of_normal_two_u3 (hF : Nat.card F = 3 ^ 2) {Y N : Subgroup (SU3F 3 F)}
    (hB : leviU hF ≤ Y) (hirr : IsIrrIn (StatedSU 3 (3 ^ 1) F) Y) (hNY : N ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hexp : ∀ a ∈ N, a ^ 2 = 1) (hne : N ≠ ⊥) : False := by
  have h2 : (2 : F) ≠ 0 := fun h => one_ne_zero (show (1 : F) = 0 by
    linear_combination three_eq_zero_u3 hF - h)
  obtain ⟨a, haN, ha1⟩ : ∃ a ∈ N, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hcon a ha))
  have hD := matU_eq_of_normal_two hF hB hNY hnorm hcomm hexp haN ha1
  refine not_isIrrIn_of_fixes_line (p := 3) (Y := Y) (fun y hy => ?_) hirr
  have h1 : y * a * y⁻¹ ∈ N := hnorm y hy a haN
  have h1ne : y * a * y⁻¹ ≠ 1 := fun h => ha1 (by
    have := congrArg (fun x => y⁻¹ * x * y) h
    simpa [mul_assoc] using this)
  have hD' := matU_eq_of_normal_two hF hB hNY hnorm hcomm hexp h1 h1ne
  have heq : y * a * y⁻¹ = a := ext_matU (by rw [hD, hD'])
  have hcomm' : y * a = a * y := mul_inv_eq_iff_eq_mul.mp heq
  have hm := congrArg matU hcomm'
  rw [matU_mul, matU_mul, hD] at hm
  have e02 := congrFun (congrFun hm 0) 2
  have e12 := congrFun (congrFun hm 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02 e12
  refine ⟨?_, ?_⟩
  · have : 2 * matU y 0 2 = 0 := by linear_combination e02
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : 2 * matU y 1 2 = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_left h2

end CFSG.Quasithin.E2P.Asc80
