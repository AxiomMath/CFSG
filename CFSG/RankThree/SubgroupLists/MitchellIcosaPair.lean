module

public import CFSG.RankThree.SubgroupLists.MitchellIcosaPairFrame
import CFSG.RankThree.SubgroupLists.MitchellFourFrame
import CFSG.RankThree.SubgroupLists.MitchellFourSquares
import CFSG.RankThree.SubgroupLists.MitchellIcosa
import CFSG.RankThree.SubgroupLists.MitchellIcosaSecond
import CFSG.RankThree.SubgroupLists.MitchellNondegenerate
import CFSG.RankThree.SubgroupLists.MitchellQOne

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem exists_orth_in_span_pair {u w v : Matrix V₄ V₄ K} {x y : K} (hv : v = x • u + y • w)
    (huw : cliffB u w = 0) (hQu : cliffB u u ≠ 0) (hQw : cliffB w w ≠ 0) (hQv : cliffB v v ≠ 0) :
    ∃ α β : K, cliffB v (α • u + β • w) = 0 ∧
      cliffB (α • u + β • w) (α • u + β • w) ≠ 0 := by
  have hwu : cliffB w u = 0 := by rw [cliffB_comm, huw]
  subst hv
  refine ⟨-y * cliffB w w, x * cliffB u u, ?_, ?_⟩
  · simp only [cliffB_add_left, cliffB_add_right, cliffB_smul_left, cliffB_smul_right, huw, hwu]
    ring
  · have : cliffB ((-y * cliffB w w) • u + (x * cliffB u u) • w)
        ((-y * cliffB w w) • u + (x * cliffB u u) • w) =
        cliffB u u * cliffB w w * cliffB (x • u + y • w) (x • u + y • w) := by
      simp only [cliffB_add_left, cliffB_add_right, cliffB_smul_left, cliffB_smul_right, huw, hwu]
      ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hQu hQw) hQv

theorem cliffB_eq_zero_of_mul_comm (h2 : (2 : K) ≠ 0) {a b w : Matrix V₄ V₄ K}
    (haM : a ∈ (cliffSpace : Submodule K _)) (hbM : b ∈ (cliffSpace : Submodule K _))
    (hwM : w ∈ (cliffSpace : Submodule K _)) (haa : a * a = 1) (hbb : b * b = 1)
    (hab : cliffB a b ≠ 0) (hwa : cliffB w a = 0) (hw0 : w ≠ 0)
    (hc : a * b * w = w * (a * b) ∨ a * b * w = -(w * (a * b))) : cliffB w b = 0 := by
  have hsq := mul_sq_of_involutions h2 haM hbM haa hbb
  rcases hc with hc | hc
  · have haw : a * w = -(w * a) :=
      (mul_eq_neg_mul_iff h2 haM hwM).mpr (by rw [cliffB_comm]; exact hwa)
    have hbw : b * w + w * b = (2 * cliffB b w) • 1 := mul_add_mul_of_mem h2 hbM hwM
    have e : b * w = (2 * cliffB b w) • 1 - w * b := eq_sub_of_add_eq hbw
    have h1 : a * b * w = (2 * cliffB b w) • a + w * (a * b) := by
      calc a * b * w = a * (b * w) := Matrix.mul_assoc _ _ _
        _ = a * ((2 * cliffB b w) • 1 - w * b) := by rw [e]
        _ = (2 * cliffB b w) • a - (a * w) * b := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc]
        _ = (2 * cliffB b w) • a + w * (a * b) := by
          rw [haw, Matrix.neg_mul, sub_neg_eq_add, Matrix.mul_assoc]
    have h4 : (2 * cliffB b w) • a = 0 := by
      rw [hc] at h1
      have h3 := congrArg (fun X => X - w * (a * b)) h1
      simpa using h3.symm
    have h5 : (2 * cliffB b w) • (1 : Matrix V₄ V₄ K) = 0 := by
      have := congrArg (fun X => a * X) h4
      simpa [Matrix.mul_smul, haa] using this
    have h6 : 2 * cliffB b w = 0 := (smul_eq_zero.mp h5).resolve_right one_ne_zero
    rw [cliffB_comm]
    exact (mul_eq_zero.mp h6).resolve_left h2
  · exfalso
    have hy : a * b * (a * b) * w = w * (a * b * (a * b)) := by
      calc a * b * (a * b) * w = a * b * (a * b * w) := Matrix.mul_assoc _ _ _
        _ = a * b * (-(w * (a * b))) := by rw [hc]
        _ = -(a * b * w * (a * b)) := by rw [Matrix.mul_neg, ← Matrix.mul_assoc]
        _ = -(-(w * (a * b)) * (a * b)) := by rw [hc]
        _ = w * (a * b * (a * b)) := by rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [hsq] at hy
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one] at hy
    have h7 := sub_left_injective hy
    rw [hc, smul_neg] at h7
    have h8 := eq_neg_iff_add_eq_zero.mp h7.symm
    rw [← two_smul K, smul_smul] at h8
    have h9 : (2 * (2 * cliffB a b)) • (w * (a * b)) = 0 := h8
    have hne : 2 * (2 * cliffB a b) ≠ 0 := mul_ne_zero h2 (mul_ne_zero h2 hab)
    have h10 : w * (a * b) = 0 := (smul_eq_zero.mp h9).resolve_left hne
    apply hw0
    have e : a * b * (b * a) = 1 := by
      calc a * b * (b * a) = a * (b * b) * a := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hbb, Matrix.mul_one, haa]
    calc w = w * (a * b * (b * a)) := by rw [e, Matrix.mul_one]
      _ = w * (a * b) * (b * a) := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [h10, Matrix.zero_mul]

section Main

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "⟪" x "⟫" => (((x : _) : GL V₄ K) : Matrix V₄ V₄ K)

theorem false_of_icosa_pair_aux (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {d e f f₂ : GL V₄ K}
    (hdG : d ∈ G) (heG : e ∈ G) (hfG : f ∈ G) (hf₂G : f₂ ∈ G) (hd : IsNCInv d) (he : IsNCInv e)
    (hf : IsNCInv f) (hf₂ : IsNCInv f₂)
    (hθ : 16 * cliffB ⟪d⟫ ⟪e⟫ ^ 4 - 12 * cliffB ⟪d⟫ ⟪e⟫ ^ 2 + 1 = 0)
    (hβ1 : cliffB ⟪d⟫ ⟪e⟫ ^ 2 ≠ 1) (hfP : ∀ a b : K, ⟪f⟫ ≠ a • ⟪d⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪d⟫ ⟪f⟫ ≠ 0) (hf₂S : ∀ a b c : K, ⟪f₂⟫ ≠ a • ⟪d⟫ + b • ⟪e⟫ + c • ⟪f⟫)
    (hγ₂ : cliffB ⟪d⟫ ⟪f₂⟫ ≠ 0 ∨ cliffB ⟪e⟫ ⟪f₂⟫ ≠ 0) {v : Matrix V₄ V₄ K}
    (hvM : v ∈ (cliffSpace : Submodule K _)) (hvd : cliffB v ⟪d⟫ = 0) (hve : cliffB v ⟪e⟫ = 0)
    (hvf : cliffB v ⟪f⟫ = 0) (hvf₂ : cliffB v ⟪f₂⟫ = 0) (hQv : cliffB v v ≠ 0) : False := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  have hM : ∀ x : GL V₄ K, IsNCInv x → ⟪x⟫ ∈ (cliffSpace : Submodule K _) := fun x hx =>
    (mem_cliffSpace_of_involution h2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2).1
  have hsq : ∀ x : GL V₄ K, IsNCInv x → ⟪x⟫ * ⟪x⟫ = 1 := fun x hx => by
    rw [← Units.val_mul, hx.2.1, Units.val_one]
  have hβ : cliffB ⟪d⟫ ⟪e⟫ * cliffB ⟪d⟫ ⟪e⟫ ≠ 1 := by rwa [← sq]
  have hind := lin_indep_of_not_mem_span h2 (cliffB_eq_one_of_mul_self h2 (hsq d hd))
    (cliffB_eq_one_of_mul_self h2 (hsq e he)) hβ hfP
  obtain ⟨u₀, w₀, hu₀M, hw₀M, hu₀d, hu₀e, hu₀f, hw₀d, hw₀e, hw₀f, huw₀, hQu₀, hQw₀⟩ :=
    exists_orth_pair_of_three hp2 hGS hU0 hneg hdG heG hfG hd he hf hβ hfP
  obtain ⟨x, y, hxy⟩ := mem_span_pair_of_orth_three h2 (hM d hd) (hM e he) (hM f hf) hu₀M hw₀M
    hvM hind ⟨hu₀d, hu₀e, hu₀f⟩ ⟨hw₀d, hw₀e, hw₀f⟩ huw₀ hQu₀ hQw₀ ⟨hvd, hve, hvf⟩
  obtain ⟨α, β, hvw, hQw⟩ := exists_orth_in_span_pair hxy huw₀ hQu₀ hQw₀ hQv
  have hwM : α • u₀ + β • w₀ ∈ (cliffSpace : Submodule K _) :=
    add_mem (Submodule.smul_mem _ _ hu₀M) (Submodule.smul_mem _ _ hw₀M)
  have hworth : ∀ a : Matrix V₄ V₄ K, cliffB u₀ a = 0 → cliffB w₀ a = 0 →
      cliffB (α • u₀ + β • w₀) a = 0 := fun a h1 h2' => by
    rw [cliffB_add_left, cliffB_smul_left, cliffB_smul_left, h1, h2', mul_zero, mul_zero, add_zero]
  generalize α • u₀ + β • w₀ = w at hwM hvw hQw hworth
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hQw (cliffB_zero_left 0)
  have hwd : cliffB w ⟪d⟫ = 0 := hworth _ hu₀d hw₀d
  have hwe : cliffB w ⟪e⟫ = 0 := hworth _ hu₀e hw₀e
  have hwf : cliffB w ⟪f⟫ = 0 := hworth _ hu₀f hw₀f
  have hvw' : v * w = -(w * v) := (mul_eq_neg_mul_iff h2 hvM hwM).mpr hvw
  have hcomm : ∀ (a b : GL V₄ K) (c : Matrix V₄ V₄ K), IsNCInv a → IsNCInv b →
      c ∈ (cliffSpace : Submodule K _) → cliffB c ⟪a⟫ = 0 → cliffB c ⟪b⟫ = 0 →
      ((a * b : GL V₄ K) : Matrix V₄ V₄ K) * c = c * ((a * b : GL V₄ K) : Matrix V₄ V₄ K) := by
    intro a b c ha hb hcM hca hcb
    rw [Units.val_mul]
    exact (commute_mul_of_cliffB_eq_zero h2 (hM a ha) (hM b hb) hcM
      ((cliffB_comm _ _).trans hca) ((cliffB_comm _ _).trans hcb)).eq
  obtain ⟨d₂, hd₂, hd₂G, hγ₂'⟩ : ∃ d₂ : GL V₄ K, (d₂ = d ∨ d₂ = e) ∧ d₂ ∈ G ∧
      cliffB ⟪d₂⟫ ⟪f₂⟫ ≠ 0 := by
    rcases hγ₂ with h | h
    · exact ⟨d, Or.inl rfl, hdG, h⟩
    · exact ⟨e, Or.inr rfl, heG, h⟩
  have hd₂N : IsNCInv d₂ := by rcases hd₂ with rfl | rfl <;> assumption
  have hvd₂ : cliffB v ⟪d₂⟫ = 0 := by rcases hd₂ with rfl | rfl <;> assumption
  have hwd₂ : cliffB w ⟪d₂⟫ = 0 := by rcases hd₂ with rfl | rfl <;> assumption
  obtain ⟨K', iF, iFin, iCh, φ, k, s, hk, hs, hv⟩ := exists_frame hp2 hvM hQv
  have hP1 := plusImage_of_icosa_triple hp5 hGS hU0 hneg hdG heG hfG hd he hf hθ hβ1 hfP hγ hvM
    hwM hvd hve hvf hwd hwe hwf hvw hQw φ hk hs hv
  have hP2 := plusImage_of_icosa_triple hp5 hGS hU0 hneg hdG heG hfG hd he hf hθ hβ1 hfP hγ hvM
    hwM hvd hve hvf hwd hwe hwf hvw hQw φ (mul_mem hk swapGL_mem) (neg_ne_zero.mpr hs)
    (frameMat_swap_of φ k hv)
  have hc := mul_comm_or_neg_of_graph hp5 hGS hq hZ hneg hU0 φ hk hs hv hvw' hP2.1
    (G.mul_mem hdG heG) (G.mul_mem hdG hfG) (hcomm d e v hd he hvM hvd hve)
    (hcomm d f v hd hf hvM hvd hvf) (hcomm d e w hd he hwM hwd hwe) (hcomm d f w hd hf hwM hwd hwf)
    hP1.2 (G.mul_mem hd₂G hf₂G) (hcomm d₂ f₂ v hd₂N hf₂ hvM hvd₂ hvf₂)
  rw [Units.val_mul] at hc
  have hwf₂ := cliffB_eq_zero_of_mul_comm h2 (hM d₂ hd₂N) (hM f₂ hf₂) hwM (hsq d₂ hd₂N)
    (hsq f₂ hf₂) hγ₂' hwd₂ hw0 hc
  obtain ⟨a, b, c, hf₂'⟩ := mem_span_three_of_orth_pair h2 (hM d hd) (hM e he) (hM f hf) hvM hwM
    (hM f₂ hf₂) hind ⟨hvd, hve, hvf⟩ ⟨hwd, hwe, hwf⟩ hvw hQv hQw
    ⟨by rw [cliffB_comm]; exact hvf₂, by rw [cliffB_comm]; exact hwf₂⟩
  exact hf₂S a b c hf₂'

theorem false_of_icosa_pair_nonisotropic (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {t : G}
    (ht : IsNCInv (t : GL V₄ K)) {e f f₂ : G} (heD : ∃ g : G, e = g * t * g⁻¹)
    (hfD : ∃ g : G, f = g * t * g⁻¹) (hf₂D : ∃ g : G, f₂ = g * t * g⁻¹)
    (hθ : 16 * cliffB ⟪t⟫ ⟪e⟫ ^ 4 - 12 * cliffB ⟪t⟫ ⟪e⟫ ^ 2 + 1 = 0)
    (hβ1 : cliffB ⟪t⟫ ⟪e⟫ ^ 2 ≠ 1) (hfP : ∀ a b : K, ⟪f⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪t⟫ ⟪f⟫ ≠ 0 ∨ cliffB ⟪e⟫ ⟪f⟫ ≠ 0)
    (hf₂S : ∀ a b c : K, ⟪f₂⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫)
    (hγ₂ : cliffB ⟪t⟫ ⟪f₂⟫ ≠ 0 ∨ cliffB ⟪e⟫ ⟪f₂⟫ ≠ 0) {v : Matrix V₄ V₄ K}
    (hvM : v ∈ (cliffSpace : Submodule K _)) (hvt : cliffB v ⟪t⟫ = 0) (hve : cliffB v ⟪e⟫ = 0)
    (hvf : cliffB v ⟪f⟫ = 0) (hvf₂ : cliffB v ⟪f₂⟫ = 0) (hQv : cliffB v v ≠ 0) : False := by
  have hN : ∀ g : G, IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := conj_isNCInv hGS ht
  have heN : IsNCInv (e : GL V₄ K) := by obtain ⟨g, hg⟩ := heD; rw [hg]; exact hN g
  have hfN : IsNCInv (f : GL V₄ K) := by obtain ⟨g, hg⟩ := hfD; rw [hg]; exact hN g
  have hf₂N : IsNCInv (f₂ : GL V₄ K) := by obtain ⟨g, hg⟩ := hf₂D; rw [hg]; exact hN g
  rcases hγ with hγ | hγ
  · exact false_of_icosa_pair_aux hp5 hGS hq hZ hneg hU0 t.2 e.2 f.2 f₂.2 ht heN hfN hf₂N hθ hβ1
      hfP hγ hf₂S hγ₂ hvM hvt hve hvf hvf₂ hQv
  · refine false_of_icosa_pair_aux hp5 hGS hq hZ hneg hU0 e.2 t.2 f.2 f₂.2 heN ht hfN hf₂N ?_ ?_
      ?_ hγ ?_ hγ₂.symm hvM hve hvt hvf hvf₂ hQv
    · rw [cliffB_comm]
      exact hθ
    · rw [cliffB_comm]
      exact hβ1
    · intro a b h
      exact hfP b a (by rw [h, add_comm])
    · intro a b c h
      exact hf₂S b a c (by rw [h]; abel)

end Main

end CFSG.RankThree.SubgroupLists
