module

public import CFSG.RankThree.SubgroupLists.OrthogonalForms
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists

variable {p : ℕ} [Fact p.Prime]

@[expose] def rot (a b α β : ZMod p) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![α, -b * β; a * β, α]

theorem rot_mul (a b α β α' β' : ZMod p) :
    rot a b α β * rot a b α' β' = rot a b (α * α' - a * b * β * β') (α * β' + β * α') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_rot (a b α β : ZMod p) : (rot a b α β).det = α ^ 2 + a * b * β ^ 2 := by
  simp [rot, Matrix.det_fin_two]
  ring

theorem rot_zero_zero (a b : ZMod p) : rot a b 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem entries_of_isometry {a b : ZMod p} (ha : a ≠ 0) {x y z w : ZMod p}
    (e0 : a * x ^ 2 + b * z ^ 2 = a) (e1 : a * x * y + b * z * w = 0)
    (e2 : a * y ^ 2 + b * w ^ 2 = b) (e3 : x * w - y * z = 1) : w = x ∧ y = -b * (z / a) := by
  have hwx : a * (w - x) = 0 := by
    linear_combination (-w) * (e0) + (a * x) * (e3) + z * (e1)
  have hyz : a * y + b * z = 0 := by
    linear_combination w * (e1) - (a * y) * (e3) - z * (e2)
  refine ⟨?_, ?_⟩
  · have := (mul_eq_zero.mp hwx).resolve_left ha
    linear_combination this
  · field_simp
    linear_combination hyz

theorem mem_soGL_two_iff {a b : ZMod p} (ha : a ≠ 0) (g : GL (Fin 2) (ZMod p)) :
    g ∈ soGL (Matrix.diagonal ![a, b]) ↔ ∃ α β : ZMod p, α ^ 2 + a * b * β ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = rot a b α β := by
  rw [mem_soGL]
  constructor
  · rintro ⟨h1, h2⟩
    have e00 := congrFun (congrFun h1 0) 0
    have e01 := congrFun (congrFun h1 0) 1
    have e11 := congrFun (congrFun h1 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.transpose_apply]
      at e00 e01 e11
    rw [Matrix.det_fin_two] at h2
    obtain ⟨hwx, hyz⟩ := entries_of_isometry (b := b) ha (x := (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0)
      (y := (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) (z := (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0)
      (w := (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1) (by linear_combination e00)
      (by linear_combination e01) (by linear_combination e11) h2
    have hz : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 =
        a * ((g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 / a) := by field_simp
    refine ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0, (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 / a,
      ?_, ?_⟩
    · apply mul_left_cancel₀ ha
      rw [hz] at e00
      linear_combination e00
    · ext i j
      fin_cases i <;> fin_cases j
      · simp [rot]
      · simp only [rot, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        exact hyz
      · simp only [rot, Fin.mk_one, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        exact hz
      · simp only [rot, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        exact hwx
  · rintro ⟨α, β, h, hg⟩
    rw [hg]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
          Matrix.transpose_apply]
      · linear_combination a * h
      · ring
      · ring
      · linear_combination b * h
    · rw [det_rot]
      exact h

@[expose] def conic (a b : ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun q => q.1 ^ 2 + a * b * q.2 ^ 2 = 1

theorem mem_conic {a b : ZMod p} {q : ZMod p × ZMod p} :
    q ∈ conic a b ↔ q.1 ^ 2 + a * b * q.2 ^ 2 = 1 := by
  simp [conic]

@[expose] noncomputable def rotGL (a b : ZMod p) (q : ↥(conic a b)) : GL (Fin 2) (ZMod p) :=
  GeneralLinearGroup.mkOfDetNeZero (rot a b q.1.1 q.1.2) (by
    rw [det_rot, mem_conic.mp q.2]
    exact one_ne_zero)

theorem coe_rotGL (a b : ZMod p) (q : ↥(conic a b)) :
    ((rotGL a b q : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = rot a b q.1.1 q.1.2 :=
  rfl

theorem rotGL_mem {a b : ZMod p} (ha : a ≠ 0) (q : ↥(conic a b)) :
    rotGL a b q ∈ soGL (Matrix.diagonal ![a, b]) :=
  (mem_soGL_two_iff ha _).mpr ⟨q.1.1, q.1.2, mem_conic.mp q.2, rfl⟩

theorem rotGL_injective {a b : ZMod p} (ha : a ≠ 0) :
    Function.Injective fun q : ↥(conic a b) =>
      (⟨rotGL a b q, rotGL_mem ha q⟩ : ↥(soGL (Matrix.diagonal ![a, b]))) := by
  intro q q' h
  have h1 := congrArg (fun g : ↥(soGL (Matrix.diagonal ![a, b])) =>
    ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))) h
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  simp only [coe_rotGL, rot] at e00 e10
  simp at e00 e10
  apply Subtype.ext
  exact Prod.ext e00 (e10.resolve_right ha)

theorem rotGL_surjective {a b : ZMod p} (ha : a ≠ 0) :
    Function.Surjective fun q : ↥(conic a b) =>
      (⟨rotGL a b q, rotGL_mem ha q⟩ : ↥(soGL (Matrix.diagonal ![a, b]))) := by
  rintro ⟨g, hg⟩
  obtain ⟨α, β, h, hgrot⟩ := (mem_soGL_two_iff ha g).mp hg
  refine ⟨⟨(α, β), mem_conic.mpr h⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hgrot.symm

theorem natCard_soGL_two_eq {a b : ZMod p} (ha : a ≠ 0) :
    Nat.card (soGL (Matrix.diagonal ![a, b])) = (conic a b).card := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨rotGL_injective ha, rotGL_surjective ha⟩),
    Nat.card_eq_fintype_card, Fintype.card_coe]

theorem ringChar_zmod_ne_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem card_filter_one_add_mul_sq_eq_zero {N : ZMod p} (hN : N ≠ 0) (hp2 : p ≠ 2) :
    (Finset.univ.filter fun m : ZMod p => 1 + N * m ^ 2 = 0).card =
      if IsSquare (-N) then 2 else 0 := by
  have hset : (Finset.univ.filter fun m : ZMod p => 1 + N * m ^ 2 = 0) =
      {x : ZMod p | x ^ 2 = -N⁻¹}.toFinset := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      rw [h]
      field_simp
      ring
  have hcard := quadraticChar_card_sqrts (ringChar_zmod_ne_two hp2) (-N⁻¹)
  have hsq : IsSquare (-N⁻¹) ↔ IsSquare (-N) := by
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r * N, by
        have : -N = (-N⁻¹) * N ^ 2 := by field_simp
        rw [this, hr]
        ring⟩
    · rintro ⟨r, hr⟩
      exact ⟨r * N⁻¹, by
        have : -N⁻¹ = (-N) * (N⁻¹) ^ 2 := by field_simp
        rw [this, hr]
        ring⟩
  have hne : -N⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hN)
  rw [hset]
  by_cases h : IsSquare (-N)
  · have h1 : quadraticChar (ZMod p) (-N⁻¹) = 1 := (quadraticChar_one_iff_isSquare hne).mpr (hsq.mpr h)
    rw [h1] at hcard
    simp only [h, ↓reduceIte]
    exact_mod_cast hcard
  · have h1 : quadraticChar (ZMod p) (-N⁻¹) = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr (fun h' => h (hsq.mp h'))
    rw [h1] at hcard
    simp only [h, ↓reduceIte]
    have : (({x : ZMod p | x ^ 2 = -N⁻¹}.toFinset.card : ℕ) : ℤ) = 0 := by
      rw [hcard]; norm_num
    exact_mod_cast this

theorem card_conic {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    (conic a b).card = if IsSquare (-(a * b)) then p - 1 else p + 1 := by
  have hN : a * b ≠ 0 := mul_ne_zero ha hb
  set N := a * b with hNdef
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hmem : ((-1 : ZMod p), (0 : ZMod p)) ∈ conic a b := by
    rw [mem_conic]
    simp
  have h1 : ((conic a b).erase (-1, 0)).card + 1 = (conic a b).card :=
    Finset.card_erase_add_one hmem
  have hbij : ((conic a b).erase (-1, 0)).card =
      (Finset.univ.filter fun m : ZMod p => ¬ (1 + N * m ^ 2 = 0)).card := by
    refine Finset.card_bij' (fun q _ => q.2 / (q.1 + 1))
      (fun m _ => ((1 - N * m ^ 2) / (1 + N * m ^ 2), 2 * m / (1 + N * m ^ 2))) ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_erase, mem_conic] at hq
      obtain ⟨hne, hq⟩ := hq
      have hq1 : q.1 + 1 ≠ 0 := by
        intro h0
        have hq1 : q.1 = -1 := by linear_combination h0
        have hq2 : N * q.2 ^ 2 = 0 := by
          rw [hq1] at hq
          linear_combination hq
        have : q.2 = 0 := by
          rcases mul_eq_zero.mp hq2 with h | h
          · exact absurd h hN
          · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
        exact hne (Prod.ext hq1 this)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h0
      field_simp at h0
      apply hq1
      have : 2 * (q.1 + 1) = 0 := by linear_combination h0 - hq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · exact h
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_erase, mem_conic]
      refine ⟨?_, ?_⟩
      · intro h
        have h1 := congrArg Prod.fst h
        simp only at h1
        field_simp at h1
        apply h2
        linear_combination h1
      · simp only
        field_simp
        ring
    · intro q hq
      rw [Finset.mem_erase, mem_conic] at hq
      obtain ⟨hne, hq⟩ := hq
      have hq1 : q.1 + 1 ≠ 0 := by
        intro h0
        have hq1 : q.1 = -1 := by linear_combination h0
        have hq2 : N * q.2 ^ 2 = 0 := by
          rw [hq1] at hq
          linear_combination hq
        have : q.2 = 0 := by
          rcases mul_eq_zero.mp hq2 with h | h
          · exact absurd h hN
          · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
        exact hne (Prod.ext hq1 this)
      have hden : 1 + N * (q.2 / (q.1 + 1)) ^ 2 = 2 / (q.1 + 1) := by
        field_simp
        linear_combination hq
      have hden0 : 1 + N * (q.2 / (q.1 + 1)) ^ 2 ≠ 0 := by
        rw [hden]
        exact div_ne_zero h2 hq1
      ext
      · simp only
        rw [hden]
        field_simp
        linear_combination -hq
      · simp only
        rw [hden]
        field_simp
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only
      have hden : (1 - N * m ^ 2) / (1 + N * m ^ 2) + 1 = 2 / (1 + N * m ^ 2) := by
        field_simp
        ring
      rw [hden]
      have hm' : (1 + m ^ 2 * N) ≠ 0 := by rwa [mul_comm (m ^ 2) N]
      field_simp
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
    (fun m : ZMod p => 1 + N * m ^ 2 = 0)
  rw [Finset.card_univ, ZMod.card] at h3
  have h4 := card_filter_one_add_mul_sq_eq_zero hN hp2
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  by_cases hsq : IsSquare (-N)
  · simp only [hsq, ↓reduceIte] at h4 ⊢
    omega
  · simp only [hsq, ↓reduceIte] at h4 ⊢
    omega

theorem natCard_soGL_two {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    Nat.card (soGL (Matrix.diagonal ![a, b])) = if IsSquare (-(a * b)) then p - 1 else p + 1 := by
  rw [natCard_soGL_two_eq ha, card_conic ha hb hp2]

theorem rot_pow_six (a b α β : ZMod p) :
    rot a b α β ^ 6 = rot a b
      ((α ^ 3 - 3 * α * (a * b) * β ^ 2) ^ 2 - a * b * (3 * α ^ 2 * β - a * b * β ^ 3) ^ 2)
      (2 * (α ^ 3 - 3 * α * (a * b) * β ^ 2) * (3 * α ^ 2 * β - a * b * β ^ 3)) := by
  have h2 : rot a b α β ^ 2 = rot a b (α ^ 2 - a * b * β ^ 2) (2 * α * β) := by
    rw [sq, rot_mul]
    congr 1 <;> ring
  have h3 : rot a b α β ^ 3 = rot a b (α ^ 3 - 3 * α * (a * b) * β ^ 2)
      (3 * α ^ 2 * β - a * b * β ^ 3) := by
    rw [pow_succ, h2, rot_mul]
    congr 1 <;> ring
  have h6 : rot a b α β ^ 6 = rot a b α β ^ 3 * rot a b α β ^ 3 := by
    rw [← pow_add]
  rw [h6, h3, rot_mul]
  congr 1 <;> ring

theorem conic_of_pow_six {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) {α β : ZMod p}
    (h : α ^ 2 + a * b * β ^ 2 = 1) (h6 : rot a b α β ^ 6 = 1) :
    (β = 0 ∧ α ^ 2 = 1) ∨ (4 * α ^ 2 = 1 ∧ 4 * (a * b) * β ^ 2 = 3) := by
  have hN : a * b ≠ 0 := mul_ne_zero ha hb
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  rw [rot_pow_six, ← rot_zero_zero a b] at h6
  have e00 := congrFun (congrFun h6 0) 0
  have e10 := congrFun (congrFun h6 1) 0
  simp [rot] at e00 e10
  have hb6 : 2 * (α ^ 3 - 3 * α * (a * b) * β ^ 2) * (3 * α ^ 2 * β - a * b * β ^ 3) = 0 := by
    rcases e10 with e | (e | e) | e
    · exact absurd e ha
    · exact absurd e h2
    · rw [e]; ring
    · rw [e]; ring
  by_cases hβ : β = 0
  · left
    refine ⟨hβ, ?_⟩
    rw [hβ] at h
    linear_combination h
  · right
    have hNβ : a * b * β ^ 2 ≠ 0 := mul_ne_zero hN (pow_ne_zero 2 hβ)
    have hα2 : α ^ 2 - 1 ≠ 0 := by
      intro h0
      apply hNβ
      linear_combination h - h0
    have hkey : (α ^ 2 - 1) * (4 * α ^ 2 - 1) ^ 2 = 0 := by
      have hN' : a * b * β ^ 2 = 1 - α ^ 2 := by linear_combination h
      have : (α ^ 3 - 3 * α * (a * b) * β ^ 2) ^ 2 - a * b * (3 * α ^ 2 * β - a * b * β ^ 3) ^ 2 = 1 := by
        linear_combination e00
      have e1 : (α ^ 3 - 3 * α * (a * b) * β ^ 2) = α * (4 * α ^ 2 - 3) := by
        linear_combination (-3 * α) * hN'
      have e2 : a * b * (3 * α ^ 2 * β - a * b * β ^ 3) ^ 2 =
          (1 - α ^ 2) * (4 * α ^ 2 - 1) ^ 2 := by
        have : (3 * α ^ 2 * β - a * b * β ^ 3) ^ 2 = β ^ 2 * (3 * α ^ 2 - a * b * β ^ 2) ^ 2 := by ring
        rw [this]
        have h3 : 3 * α ^ 2 - a * b * β ^ 2 = 4 * α ^ 2 - 1 := by linear_combination -hN'
        rw [h3]
        linear_combination (4 * α ^ 2 - 1) ^ 2 * hN'
      rw [e1, e2] at this
      have h2' : 2 * ((α ^ 2 - 1) * (4 * α ^ 2 - 1) ^ 2) = 0 := by linear_combination this
      exact (mul_eq_zero.mp h2').resolve_left h2
    have h4 : (4 * α ^ 2 - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hα2
      · exact h
    have h5 : 4 * α ^ 2 = 1 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h4
      linear_combination this
    refine ⟨h5, ?_⟩
    linear_combination 4 * h - h5

theorem natCard_soGL_two_le_six {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2)
    (h6 : ∀ y ∈ soGL (Matrix.diagonal ![a, b]), y ^ 6 = 1) :
    Nat.card (soGL (Matrix.diagonal ![a, b])) ≤ 6 := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hN : a * b ≠ 0 := mul_ne_zero ha hb
  rw [natCard_soGL_two_eq ha]
  set A : Finset (ZMod p) := Finset.univ.filter fun α => 4 * α ^ 2 = 1 with hA
  set B : Finset (ZMod p) := Finset.univ.filter fun β => 4 * (a * b) * β ^ 2 = 3 with hB
  have hAcard : A.card ≤ 2 := by
    have hsub : A ⊆ {2⁻¹, -2⁻¹} := by
      intro α hα
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hα
      have h1 : (2 * α) * (2 * α) = 1 := by linear_combination hα
      rcases mul_self_eq_one_iff.mp h1 with h | h
      · have : α = 2⁻¹ := by
          field_simp
          linear_combination h
        simp [this]
      · have : α = -2⁻¹ := by
          field_simp
          linear_combination h
        simp [this]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have hBcard : B.card ≤ 2 := by
    by_cases hne : B.Nonempty
    · obtain ⟨β₀, hβ₀⟩ := hne
      have hsub : B ⊆ {β₀, -β₀} := by
        intro β hβ
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hβ hβ₀
        have h4N : 4 * (a * b) ≠ 0 := mul_ne_zero (by
          intro h
          have : (2 : ZMod p) * 2 = 0 := by linear_combination h
          rcases mul_eq_zero.mp this with h' | h' <;> exact h2 h') hN
        have h1 : β ^ 2 = β₀ ^ 2 := mul_left_cancel₀ h4N (by rw [hβ, hβ₀])
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
        · simp [h]
        · simp [h]
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hsub : conic a b ⊆ ({((1 : ZMod p), (0 : ZMod p)), (-1, 0)} : Finset _) ∪ (A ×ˢ B) := by
    intro q hq
    have hq' := mem_conic.mp hq
    have hg6 := h6 (rotGL a b ⟨q, hq⟩) (rotGL_mem ha _)
    have hm6 : rot a b q.1 q.2 ^ 6 = 1 := by
      have := congrArg (fun g : GL (Fin 2) (ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p))) hg6
      simpa [coe_rotGL] using this
    rcases conic_of_pow_six ha hb hp2 hq' hm6 with ⟨hβ, hα⟩ | ⟨hα, hβ⟩
    · apply Finset.mem_union_left
      have h1 : q.1 * q.1 = 1 := by linear_combination hα
      rcases mul_self_eq_one_iff.mp h1 with h | h
      · simp [Prod.ext_iff, h, hβ]
      · simp [Prod.ext_iff, h, hβ]
    · apply Finset.mem_union_right
      simp [hA, hB, hα, hβ]
  calc (conic a b).card ≤ (({((1 : ZMod p), (0 : ZMod p)), (-1, 0)} : Finset _) ∪ (A ×ˢ B)).card :=
        Finset.card_le_card hsub
    _ ≤ ({((1 : ZMod p), (0 : ZMod p)), (-1, 0)} : Finset (ZMod p × ZMod p)).card +
          (A ×ˢ B).card := Finset.card_union_le _ _
    _ ≤ 2 + 2 * 2 := by
        rw [Finset.card_product]
        exact add_le_add Finset.card_le_two (Nat.mul_le_mul hAcard hBcard)
    _ = 6 := by norm_num

@[expose] def dmat : Matrix (Fin 2) (Fin 2) (ZMod p) := !![-1, 0; 0, 1]

theorem dmat_mul_rot_mul_dmat (a b α β : ZMod p) :
    dmat * rot a b α β * dmat = rot a b α (-β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat, rot, Matrix.mul_apply, Fin.sum_univ_two]

end CFSG.RankThree.PartOne.KF1322
