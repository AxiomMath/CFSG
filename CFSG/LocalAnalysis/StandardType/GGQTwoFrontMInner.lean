module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMData
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwoFrontM_inner_class {B Bs L : Subgroup G} {x : G} (hT : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 4)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) {y : G}
    (hy : y ∈ Bs) (hy3 : y ^ 3 = 1) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ a : ↥L, (∀ l : ↥L, y * (l : G) * y⁻¹ = ((a * l * a⁻¹ : ↥L) : G)) ∧
      e (QuotientGroup.mk a) ≠ 1 ∧ e (QuotientGroup.mk a) ^ 3 = 1 := by
  have hL : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 1 := qTwoFrontM_lieModel hK e
  obtain ⟨c, hcL, hc⟩ :=
    qTwoLMPrimeC_inner (m := 4) hT hBs hN (by norm_num) hL y hy
  refine ⟨⟨c, hcL⟩, ?_, ?_, ?_⟩
  ·
    intro l
    simpa using hc (l : G) l.2
  ·
    set a : ↥L := ⟨c, hcL⟩ with ha
    have hconj : ∀ l : ↥L, y * (l : G) * y⁻¹ = ((a * l * a⁻¹ : ↥L) : G) := by
      intro l
      simpa [ha] using hc (l : G) l.2
    intro heq
    have hmk1 : QuotientGroup.mk a = 1 := (MulEquiv.map_eq_one_iff e).mp heq
    have hcen : a ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff a).mp hmk1
    have hcommL : ∀ l : ↥L, (l : G) * y = y * (l : G) := by
      intro l
      have h1 : y * (l : G) * y⁻¹ = (l : G) := by
        rw [hconj l]
        have hcomm : l * a = a * l := (Subgroup.mem_center_iff.mp hcen) l
        have hfix : a * l * a⁻¹ = l := by
          rw [← hcomm]
          simp
        rw [hfix]
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hcent : y ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => hcommL ⟨l, hl⟩
    have hymem : y ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hy, hcent⟩
    rw [qTwoLMPrimeC_ker hT hBs] at hymem
    exact hyx hymem
  ·
    set a : ↥L := ⟨c, hcL⟩ with ha
    have hconj : ∀ l : ↥L, y * (l : G) * y⁻¹ = ((a * l * a⁻¹ : ↥L) : G) := by
      intro l
      simpa [ha] using hc (l : G) l.2
    have hpow : ∀ k : ℕ, ∀ l : ↥L,
        ((a ^ k * l * (a ^ k)⁻¹ : ↥L) : G) = y ^ k * (l : G) * (y ^ k)⁻¹ := by
      intro k
      induction k with
      | zero =>
        intro l
        simp
      | succ k ih =>
        intro l
        have hstep : a ^ (k + 1) * l * (a ^ (k + 1))⁻¹
            = a ^ k * (a * l * a⁻¹) * (a ^ k)⁻¹ := by
          simp only [pow_succ]
          group
        calc ((a ^ (k + 1) * l * (a ^ (k + 1))⁻¹ : ↥L) : G)
            = ((a ^ k * (a * l * a⁻¹) * (a ^ k)⁻¹ : ↥L) : G) := by rw [hstep]
          _ = y ^ k * (y * (l : G) * y⁻¹) * (y ^ k)⁻¹ := by
              rw [ih (a * l * a⁻¹), hconj l]
          _ = y ^ (k + 1) * (l : G) * (y ^ (k + 1))⁻¹ := by
              rw [pow_succ]
              group
    have hfix : ∀ l : ↥L, a ^ 3 * l * (a ^ 3)⁻¹ = l := by
      intro l
      apply Subtype.ext
      have h := hpow 3 l
      rw [hy3] at h
      simpa using h
    have hmem : a ^ 3 ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact (mul_inv_eq_iff_eq_mul.mp (hfix l)).symm
    have hmk3 : QuotientGroup.mk (a ^ 3) = 1 := (QuotientGroup.eq_one_iff (a ^ 3)).mpr hmem
    rw [← map_pow, ← QuotientGroup.mk_pow, hmk3, map_one]

end CFSG.StandardType.QTwo

end
