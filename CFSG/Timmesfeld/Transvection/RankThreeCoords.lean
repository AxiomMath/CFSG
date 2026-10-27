module

public import CFSG.Timmesfeld.Transvection.TriangleCoordsG

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G]

theorem weylElt_mul_lowerElt_mul_weylElt' {K : Type*} [Field K] [CharP K 2] (t : K) :
    weylElt K * lowerElt K t * weylElt K = upperElt K t := by
  rw [← weylElt_mul_upperElt_mul_weylElt]
  calc weylElt K * (weylElt K * upperElt K t * weylElt K) * weylElt K =
      (weylElt K * weylElt K) * upperElt K t * (weylElt K * weylElt K) := by group
    _ = upperElt K t := by rw [weylElt_mul_self, one_mul, mul_one]

theorem weylElt_mul_weylElt_conj {K : Type*} [Field K] [CharP K 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    weylElt K * (weylElt K * g * weylElt K) * weylElt K = g := by
  calc weylElt K * (weylElt K * g * weylElt K) * weylElt K =
      (weylElt K * weylElt K) * g * (weylElt K * weylElt K) := by group
    _ = g := by rw [weylElt_mul_self, one_mul, mul_one]

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

@[expose] noncomputable def swap (hcard : Nat.card E = Nat.card A) : SL2Coords E A k where
  card_eq := hcard.trans φ.card_eq
  mat x := weylElt _ * φ.mat x * weylElt _
  mat_mul {x y} hx hy := by
    rw [sup_comm] at hx hy
    rw [φ.mat_mul hx hy]
    calc weylElt (GaloisField 2 k) * (φ.mat x * φ.mat y) * weylElt (GaloisField 2 k) =
        weylElt (GaloisField 2 k) * φ.mat x * (weylElt (GaloisField 2 k) *
          weylElt (GaloisField 2 k)) * φ.mat y * weylElt (GaloisField 2 k) := by
          rw [weylElt_mul_self, mul_one]
          group
      _ = weylElt (GaloisField 2 k) * φ.mat x * weylElt (GaloisField 2 k) *
          (weylElt (GaloisField 2 k) * φ.mat y * weylElt (GaloisField 2 k)) := by group
  mat_surj g := by
    obtain ⟨x, hx, hxg⟩ := φ.mat_surj (weylElt _ * g * weylElt _)
    refine ⟨x, by rwa [sup_comm], ?_⟩
    rw [hxg, weylElt_mul_weylElt_conj]
  mat_inj {x} hx h1 := by
    rw [sup_comm] at hx
    refine φ.mat_inj hx ?_
    have := congrArg (fun g => weylElt (GaloisField 2 k) * g * weylElt (GaloisField 2 k)) h1
    rw [weylElt_mul_weylElt_conj, mul_one, weylElt_mul_self] at this
    exact this
  mem_A_iff {x} hx := by
    rw [sup_comm] at hx
    rw [φ.mem_E_iff hx, mem_upperUnipotent_iff, mem_lowerUnipotent_iff]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [ht, weylElt_mul_upperElt_mul_weylElt]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← weylElt_mul_weylElt_conj (φ.mat x), ht, weylElt_mul_lowerElt_mul_weylElt']
  mem_E_iff {x} hx := by
    rw [sup_comm] at hx
    rw [φ.mem_A_iff hx, mem_upperUnipotent_iff, mem_lowerUnipotent_iff]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [ht, weylElt_mul_lowerElt_mul_weylElt']⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← weylElt_mul_weylElt_conj (φ.mat x), ht, weylElt_mul_upperElt_mul_weylElt]

theorem swap_mat (hcard : Nat.card E = Nat.card A) (x : G) :
    (φ.swap hcard).mat x = weylElt _ * φ.mat x * weylElt _ := rfl

theorem swap_mat_of_mat_eq_diagElt (hcard : Nat.card E = Nat.card A) {h : G}
    {μ : (GaloisField 2 k)ˣ} (hh : φ.mat h = diagElt μ) :
    (φ.swap hcard).mat h = diagElt μ⁻¹ := by
  rw [swap_mat, hh, weylElt_mul_diagElt, mul_assoc, weylElt_mul_self, mul_one]

end SL2Coords

end CFSG.Timmesfeld.Transvection
