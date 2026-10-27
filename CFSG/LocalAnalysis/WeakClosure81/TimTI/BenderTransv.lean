module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Open

private theorem timti_sub_one_mul_self {F : Type} [Field F] [CharP F 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] {t : Matrix ι ι F} (ht : t * t = 1) :
    (t - 1) * (t - 1) = 0 := by
  have hadd : ∀ M : Matrix ι ι F, M + M = 0 := by
    intro M
    ext a b
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h : (t - 1) * (t - 1) = t * t + 1 - (t + t) := by
    rw [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [h, ht, hadd t, sub_zero, hadd 1]

private theorem timti_rank_eq_zero_imp {F : Type} [Field F] {ι : Type}
    [Fintype ι] [DecidableEq ι] {N : Matrix ι ι F} (h : N.rank = 0) : N = 0 := by
  have h1 : LinearMap.range N.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
  ext i j
  have h2 : N.mulVec (Pi.single j 1) ∈ LinearMap.range N.mulVecLin := ⟨Pi.single j 1, rfl⟩
  rw [h1, Submodule.mem_bot] at h2
  have := congrFun h2 i
  simpa [Matrix.mulVec_single_one] using this

private theorem timti_rank_sub_one_eq_one {F : Type} [Field F] [CharP F 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι ≤ 3)
    {t : Matrix ι ι F} (ht : t * t = 1) (ht1 : t ≠ 1) : (t - 1).rank = 1 := by
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero
    (A := t - 1) (B := t - 1) (timti_sub_one_mul_self ht)
  have hpos : 0 < (t - 1).rank := by
    by_contra h0
    have h0' : (t - 1).rank = 0 := Nat.eq_zero_of_not_pos h0
    exact ht1 (sub_eq_zero.mp (timti_rank_eq_zero_imp h0'))
  omega

theorem isSymplecticTransvectionIn_one_of_mul_self {F : Type} [Field F] [CharP F 2]
    {g : ↥(StatedSp 1 F)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    SevenK.IsSymplecticTransvectionIn 1 g := by
  have hGL2 : (g : GL (Fin 1 ⊕ Fin 1) F) * (g : GL (Fin 1 ⊕ Fin 1) F) = 1 := by
    have := congrArg (fun u : ↥(StatedSp 1 F) => (u : GL (Fin 1 ⊕ Fin 1) F)) hg2
    simpa using this
  have hmat2 : ((g : GL (Fin 1 ⊕ Fin 1) F) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) *
      ((g : GL (Fin 1 ⊕ Fin 1) F) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) = 1 := by
    have := congrArg (fun u : GL (Fin 1 ⊕ Fin 1) F =>
      (u : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)) hGL2
    simpa using this
  have hmat1 : ((g : GL (Fin 1 ⊕ Fin 1) F) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) ≠ 1 := by
    intro hgt
    exact hg1 (Subtype.ext (Units.ext hgt))
  exact timti_rank_sub_one_eq_one (ι := Fin 1 ⊕ Fin 1) (by simp) hmat2 hmat1

theorem isUnitaryTransvectionIn_three_of_mul_self {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) {x : StatedProj (StatedSU 3 (2 ^ n) F)}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : SevenK.IsUnitaryTransvectionIn 3 n x := by
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective x
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite F
  have hcharF : Fintype.card F = 2 ^ (2 * n) := by
    rw [Fintype.card_eq_nat_card, hF, ← pow_mul, Nat.mul_comm n 2]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * n) hcharF
  have hmem : (g₀ * g₀ : ↥(StatedSU 3 (2 ^ n) F)) ∈
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) := by
    have hq : (QuotientGroup.mk (g₀ * g₀) :
        StatedProj (StatedSU 3 (2 ^ n) F)) = 1 := by
      rw [QuotientGroup.mk_mul, hg₀, hx2]
    exact (QuotientGroup.eq_one_iff (g₀ * g₀)).mp hq
  have hGLmem : (g₀ : GL (Fin 3) F) * (g₀ : GL (Fin 3) F) ∈
      StatedScalars (Fin 3) F := by
    simpa using Subgroup.mem_subgroupOf.mp hmem
  rw [StatedScalars] at hGLmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hGLmem
  have hdet : Matrix.GeneralLinearGroup.det (g₀ : GL (Fin 3) F) = 1 := by
    apply Units.ext
    simpa using CFSG.Open.StatedAPI.det_of_mem_statedSU (n := 3) (q := 2 ^ n) g₀.2
  have hlambda : c ^ 3 = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
      rw [hc, map_mul, hdet, mul_one]
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    exact h1
  have hgsq : (g₀ : GL (Fin 3) F) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [pow_two, ← hc]
  have hg6 : (g₀ : GL (Fin 3) F) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hgsq, ← map_pow, hlambda, map_one]
  let g : ↥(StatedSU 3 (2 ^ n) F) := g₀ ^ 3
  have hmg : (QuotientGroup.mk g : StatedProj (StatedSU 3 (2 ^ n) F)) = x := by
    show (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf
      (StatedSU 3 (2 ^ n) F))) g = x
    rw [show g = g₀ ^ 3 from rfl, map_pow]
    change (QuotientGroup.mk g₀ : StatedProj (StatedSU 3 (2 ^ n) F)) ^ 3 = x
    rw [hg₀]
    show x ^ (2 + 1) = x
    rw [pow_succ, pow_two, hx2, one_mul]
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    show ((g * g : ↥(StatedSU 3 (2 ^ n) F)) : GL (Fin 3) F) = 1
    rw [Subgroup.coe_mul]
    have hgcoe : (g : GL (Fin 3) F) = (g₀ : GL (Fin 3) F) ^ 3 := by
      rw [show g = g₀ ^ 3 from rfl, Subgroup.coe_pow]
    rw [hgcoe, ← pow_two, ← pow_mul, show 3 * 2 = 6 from rfl, hg6]
  have hg1 : (g : GL (Fin 3) F) ≠ 1 := by
    intro hgg
    have hgsub : g = 1 := Subtype.ext hgg
    apply hx1
    rw [← hmg, hgsub, QuotientGroup.mk_one]
  have hGL2 : (g : GL (Fin 3) F) * (g : GL (Fin 3) F) = 1 := by
    have := congrArg (fun u : ↥(StatedSU 3 (2 ^ n) F) => (u : GL (Fin 3) F)) hg2
    simpa using this
  have hmat2 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hGL2
    simpa using this
  have hmat1 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
    fun hgt => hg1 (Units.ext hgt)
  exact ⟨g, hmg, timti_rank_sub_one_eq_one (ι := Fin 3) (by simp) hmat2 hmat1⟩

end CFSG.LocalAnalysis.WeakClosure81.TimTI
