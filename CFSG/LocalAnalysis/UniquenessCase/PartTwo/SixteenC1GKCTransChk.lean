module

public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCLev
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Vec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

@[expose] def s16c1cOdd : List ℕ :=
  ((sylowWords true).filter fun w => w.length % 2 == 1).map wordC

@[expose] def s16c1cTransB (c w : ℕ) : Bool :=
  (w != 0) && (List.range 64).all (fun n => act c n ^^^ n == 0 || act c n ^^^ n == w) &&
    (List.range 64).any (fun n => act c n ^^^ n == w)

@[expose] def s16c1cIsTrans (c : ℕ) : Bool := (List.range 64).any (s16c1cTransB c)

@[expose] def s16c1cSpans (c₁ c₂ : ℕ) : Bool :=
  (List.range 64).all fun n => (List.range 64).any fun m =>
    act c₁ m == m && act c₂ (n ^^^ m) == (n ^^^ m)

@[expose] def s16c1cTransOK (H : List ℕ) : Bool :=
  !(H.any fun c => s16c1cOdd.contains c) ||
    H.any fun c₁ => H.any fun c₂ => s16c1cIsTrans c₁ && s16c1cIsTrans c₂ && s16c1cSpans c₁ c₂

theorem s16c1c_transCheck : (s16c1cLev 4).all s16c1cTransOK = true := by
  decide +kernel

theorem s16c1c_vec_inj {n m : ℕ} (hn : n < 64) (hm : m < 64) (h : vec n = vec m) : n = m := by
  have hall : ∀ a b : Fin 64, vec (a : ℕ) = vec (b : ℕ) → a = b := by decide +kernel
  have := hall ⟨n, hn⟩ ⟨m, hm⟩ h
  simpa using congrArg Fin.val this

theorem s16c1c_vec_zero : vec 0 = (0 : V₀) := by
  decide +kernel

theorem s16c1c_isTrans_sound {y : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hy : Coded y c)
    (h : s16c1cIsTrans c = true) :
    ∃ w₀ : V₀, w₀ ≠ 0 ∧ (∀ u, y u - u = 0 ∨ y u - u = w₀) ∧ ∃ u, y u - u = w₀ := by
  rw [s16c1cIsTrans, List.any_eq_true] at h
  obtain ⟨w, hwmem, hw⟩ := h
  simp only [s16c1cTransB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true,
    List.any_eq_true, List.mem_range] at hw
  obtain ⟨⟨hwne, hwall⟩, n, hnlt, hnw⟩ := hw
  have hwlt : w < 64 := List.mem_range.mp hwmem
  have hstep : ∀ k, y (vec k) - vec k = vec (act c k ^^^ k) := by
    intro k
    rw [s16c1c_coded_apply hy k, CFSG.LargeExtraspecial.OrthoF2.vec_sub, ← s16c1G_vec_xor]
  refine ⟨vec w, ?_, ?_, ?_⟩
  · intro hz
    exact hwne (s16c1c_vec_inj hwlt (by norm_num) (hz.trans s16c1c_vec_zero.symm))
  · intro u
    obtain ⟨k, hk, hku⟩ := s16c1G_exists_vec u
    rw [← hku, hstep k]
    have hk' := hwall k hk
    simp only [Bool.or_eq_true, beq_iff_eq] at hk'
    rcases hk' with h0 | hw'
    · left; rw [h0, s16c1c_vec_zero]
    · right; rw [hw']
  · exact ⟨vec n, by rw [hstep n, beq_iff_eq.mp hnw]⟩

theorem s16c1c_spans_sound {y₁ y₂ : V₀ ≃ₗ[ZMod 2] V₀} {c₁ c₂ : ℕ} (h₁ : Coded y₁ c₁)
    (h₂ : Coded y₂ c₂) (h : s16c1cSpans c₁ c₂ = true) :
    ∀ u, ∃ u₁, y₁ u₁ = u₁ ∧ y₂ (u - u₁) = u - u₁ := by
  intro u
  obtain ⟨n, hn, hnu⟩ := s16c1G_exists_vec u
  rw [s16c1cSpans, List.all_eq_true] at h
  have hm := h n (List.mem_range.mpr hn)
  rw [List.any_eq_true] at hm
  obtain ⟨m, hmmem, hm⟩ := hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨hm1, hm2⟩ := hm
  refine ⟨vec m, ?_, ?_⟩
  · rw [s16c1c_coded_apply h₁ m, hm1]
  · rw [← hnu]
    have hsub : vec n - vec m = vec (n ^^^ m) := by
      rw [CFSG.LargeExtraspecial.OrthoF2.vec_sub, ← s16c1G_vec_xor]
    rw [hsub, s16c1c_coded_apply h₂ (n ^^^ m), hm2]

theorem s16c1c_exists_trans_pair {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1)
    (hT : ∀ x ∈ P, x ∈ s16c1c_T) (hcard : Nat.card P = 16) (hnot : ¬ P ≤ Ω₀ true) :
    ∃ y₁ ∈ P, ∃ y₂ ∈ P,
      (∃ w₀ : V₀, w₀ ≠ 0 ∧ (∀ u, y₁ u - u = 0 ∨ y₁ u - u = w₀) ∧ ∃ u, y₁ u - u = w₀) ∧
      (∃ w₀ : V₀, w₀ ≠ 0 ∧ (∀ u, y₂ u - u = 0 ∨ y₂ u - u = w₀) ∧ ∃ u, y₂ u - u = w₀) ∧
      ∀ u, ∃ u₁, y₁ u₁ = u₁ ∧ y₂ (u - u₁) = u - u₁ := by
  have hcode : ∀ x ∈ P, ∃ c ∈ (sylowWords true).map wordC, Coded x c :=
    fun x hx => s16c1c_exists_coded_of_mem_T (hT x hx)
  obtain ⟨H, hH, hcodeP, hcodeH⟩ := s16c1c_describe hab h2 hcode hcard
  obtain ⟨y, hyP, hyΩ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨w, hw, hyw⟩ := s16c1c_mem_T.mp (hT y hyP)
  have hodd : w.length % 2 = 1 := by
    have hwq : ∀ k ∈ w, qB true k = true := s16c1c_spec.1 w hw
    refine Nat.not_even_iff.mp fun he => hyΩ ?_
    rw [← hyw]
    exact (wordProd_mem_omegaGroup_iff hwq).mpr he
  obtain ⟨c, hcH, hyc⟩ := hcodeP y hyP
  have hyw' : Coded y (wordC w) := hyw ▸ coded_wordProd w
  have hcw : c = wordC w := (Coded.eq_iff hyc hyw').mp rfl
  have hcwH : wordC w ∈ H := hcw ▸ hcH
  have hcwOdd : wordC w ∈ s16c1cOdd := by
    rw [s16c1cOdd]
    exact List.mem_map.mpr ⟨w, List.mem_filter.mpr ⟨hw, by simpa using hodd⟩, rfl⟩
  have hOK : s16c1cTransOK H = true := (List.all_eq_true.mp s16c1c_transCheck) H hH
  rw [s16c1cTransOK, Bool.or_eq_true] at hOK
  rcases hOK with hno | hsome
  · have hfalse : (H.any fun c => s16c1cOdd.contains c) = false := by simpa using hno
    have htrue : (H.any fun c => s16c1cOdd.contains c) = true :=
      List.any_eq_true.mpr ⟨wordC w, hcwH, by simpa [List.contains_iff_mem] using hcwOdd⟩
    rw [hfalse] at htrue
    exact (Bool.false_ne_true htrue).elim
  · rw [List.any_eq_true] at hsome
    obtain ⟨c₁, hc₁H, hsome⟩ := hsome
    rw [List.any_eq_true] at hsome
    obtain ⟨c₂, hc₂H, hsome⟩ := hsome
    simp only [Bool.and_eq_true] at hsome
    obtain ⟨⟨ht₁, ht₂⟩, hsp⟩ := hsome
    obtain ⟨y₁, hy₁P, hy₁c⟩ := hcodeH c₁ hc₁H
    obtain ⟨y₂, hy₂P, hy₂c⟩ := hcodeH c₂ hc₂H
    exact ⟨y₁, hy₁P, y₂, hy₂P, s16c1c_isTrans_sound hy₁c ht₁,
      s16c1c_isTrans_sound hy₂c ht₂, s16c1c_spans_sound hy₁c hy₂c hsp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
