module

public import CFSG.RankThree.PartOne.CTP.StrongPLinear

public section

namespace CFSG.RankThree.PartOne.StrongP

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem pow_apply_ne_zero_imp (r : ι → ℕ) (N : Matrix ι ι K) (hN : ∀ i j, N i j ≠ 0 → r i < r j) :
    ∀ k : ℕ, ∀ i j, (N ^ k) i j ≠ 0 → r i + k ≤ r j := by
  intro k
  induction k with
  | zero =>
    intro i j h
    simp only [pow_zero] at h
    by_cases hij : i = j
    · subst hij; simp
    · exact absurd (one_apply_ne hij) h
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (N ^ k) i l ≠ 0 := left_ne_zero_of_mul hl
    have h2 : N l j ≠ 0 := right_ne_zero_of_mul hl
    have := ih i l h1
    have := hN l j h2
    omega

theorem pow_eq_zero_of_lt (r : ι → ℕ) (m : ℕ) (hr : ∀ i, r i < m) (N : Matrix ι ι K)
    (hN : ∀ i j, N i j ≠ 0 → r i < r j) : N ^ m = 0 := by
  ext i j
  by_contra h
  have := pow_apply_ne_zero_imp r N hN m i j h
  have := hr j
  omega

@[expose] def IsUnitri (r : ι → ℕ) (u : GL ι K) : Prop :=
  ∀ i j, ((u : Matrix ι ι K) - 1) i j ≠ 0 → r i < r j

theorem IsUnitri.pow_eq_one [Nonempty ι] {p : ℕ} [Fact p.Prime] [CharP K p] {r : ι → ℕ} {m : ℕ}
    (hr : ∀ i, r i < m) {u : GL ι K} (hu : IsUnitri r u) (k : ℕ) (hk : m ≤ p ^ k) :
    u ^ (p ^ k) = 1 := by
  have hN : ((u : Matrix ι ι K) - 1) ^ m = 0 := pow_eq_zero_of_lt r m hr _ hu
  have hNp : ((u : Matrix ι ι K) - 1) ^ (p ^ k) = 0 := by
    have : p ^ k = m + (p ^ k - m) := by omega
    rw [this, pow_add, hN, zero_mul]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : (u : Matrix ι ι K) = 1 + ((u : Matrix ι ι K) - 1) := by abel
  rw [h1, add_pow_char_pow_of_commute p k (Commute.one_left _), one_pow]
  have h2 : (1 + ((u : Matrix ι ι K) - 1) - 1) ^ (p ^ k) = 0 := by
    rw [add_sub_cancel_left]; exact hNp
  rw [add_sub_cancel_left] at h2
  rw [h2, add_zero]

theorem IsUnitri.mul {r : ι → ℕ} {u v : GL ι K} (hu : IsUnitri r u) (hv : IsUnitri r v) :
    IsUnitri r (u * v) := by
  intro i j h
  have e : ((u * v : GL ι K) : Matrix ι ι K) - 1 =
      ((u : Matrix ι ι K) - 1) * ((v : Matrix ι ι K) - 1) + ((u : Matrix ι ι K) - 1) +
        ((v : Matrix ι ι K) - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e] at h
  by_contra hij
  apply h
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
  have h1 : ((u : Matrix ι ι K) - 1) i j = 0 := by_contra fun h' => hij (hu i j h')
  have h2 : ((v : Matrix ι ι K) - 1) i j = 0 := by_contra fun h' => hij (hv i j h')
  have h3 : ∑ l, ((u : Matrix ι ι K) - 1) i l * ((v : Matrix ι ι K) - 1) l j = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : ((u : Matrix ι ι K) - 1) i l = 0
    · rw [hl, zero_mul]
    · by_cases hl' : ((v : Matrix ι ι K) - 1) l j = 0
      · rw [hl', mul_zero]
      · exact absurd (lt_trans (hu i l hl) (hv l j hl')) hij
  rw [h1, h2, h3]; simp

theorem IsUnitri.one (r : ι → ℕ) : IsUnitri r (1 : GL ι K) := by
  intro i j h
  simp at h

theorem IsUnitri.pow {r : ι → ℕ} {u : GL ι K} (hu : IsUnitri r u) (n : ℕ) :
    IsUnitri r (u ^ n) := by
  induction n with
  | zero => simpa using IsUnitri.one r
  | succ n ih => rw [pow_succ]; exact ih.mul hu

theorem IsUnitri.diag {r : ι → ℕ} {u : GL ι K} (hu : IsUnitri r u) (i : ι) :
    (u : Matrix ι ι K) i i = 1 := by
  by_contra h
  have h' : ((u : Matrix ι ι K) - 1) i i ≠ 0 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    exact sub_ne_zero.mpr h
  exact lt_irrefl _ (hu i i h')

@[expose] def unitriSubgroup [Nonempty ι] (p : ℕ) [Fact p.Prime] [CharP K p] (r : ι → ℕ)
    (m : ℕ) (hr : ∀ i, r i < m) : Subgroup (GL ι K) where
  carrier := {u | IsUnitri r u}
  mul_mem' := IsUnitri.mul
  one_mem' := IsUnitri.one r
  inv_mem' {u} hu := by
    have hpow : u ^ (p ^ m) = 1 :=
      hu.pow_eq_one hr m (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    have hpos : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
    have : u⁻¹ = u ^ (p ^ m - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, hpow]
    rw [this]
    exact hu.pow _

theorem closure_pair_pow_eq_one [Nonempty ι] (p : ℕ) [Fact p.Prime] [CharP K p] {r : ι → ℕ}
    {m : ℕ} (hr : ∀ i, r i < m) {x y : GL ι K} (hx : IsUnitri r x) (hy : IsUnitri r y)
    (g : GL ι K) (hg : g ∈ Subgroup.closure ({x, y} : Set (GL ι K))) : g ^ (p ^ m) = 1 := by
  have hle : Subgroup.closure ({x, y} : Set (GL ι K)) ≤ unitriSubgroup p r m hr := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  exact (hle hg : IsUnitri r g).pow_eq_one hr m (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le

@[expose] def NoncentralPair (p : ℕ) (H : Subgroup (GL ι K)) : Prop :=
  ∃ x y : GL ι K, x ∈ H ∧ y ∈ H ∧ x ^ p = 1 ∧ y ^ p = 1 ∧
    IsPGroup p (Subgroup.closure ({x, y} : Set (GL ι K))) ∧
    (x * y)⁻¹ * (y * x) ∉ StatedScalars ι K

theorem NoncentralPair.hasNoncommPair {p : ℕ} {H : Subgroup (GL ι K)} (h : NoncentralPair p H) :
    HasNoncommPair p (StatedProj H) := by
  obtain ⟨x, y, hx, hy, hxp, hyp, hP, hnc⟩ := h
  refine ⟨QuotientGroup.mk ⟨x, hx⟩, QuotientGroup.mk ⟨y, hy⟩, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : H) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [this, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow]
    have : (⟨y, hy⟩ : H) ^ p = 1 := Subtype.ext (by simpa using hyp)
    rw [this, QuotientGroup.mk_one]
  · intro h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    exact hnc (Subgroup.mem_subgroupOf.mp h)
  · have hinj : Function.Injective (H.subtype) := H.subtype_injective
    have hmap1 : (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set H)).map H.subtype =
        Subgroup.closure ({x, y} : Set (GL ι K)) := by
      rw [MonoidHom.map_closure, Set.image_pair]; rfl
    have hP' : IsPGroup p (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set H)) := by
      intro g
      obtain ⟨k, hk⟩ := hP ⟨(g : H), by
        rw [← hmap1]; exact ⟨g, g.2, rfl⟩⟩
      refine ⟨k, Subtype.ext (hinj ?_)⟩
      have := congrArg (fun z : Subgroup.closure ({x, y} : Set (GL ι K)) => (z : GL ι K)) hk
      simpa using this
    have hmap2 : (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set H)).map
        (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)) =
        Subgroup.closure ({(QuotientGroup.mk ⟨x, hx⟩ : StatedProj H), QuotientGroup.mk ⟨y, hy⟩} :
          Set (StatedProj H)) := by
      rw [MonoidHom.map_closure, Set.image_pair]; rfl
    rintro ⟨w, hw⟩
    rw [← hmap2] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    obtain ⟨k, hk⟩ := hP' ⟨g, hg⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set H) =>
      (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) (z : H))) hk
    simpa [← map_pow] using this

theorem NoncentralPair.conj {p : ℕ} {H H' : Subgroup (GL ι K)} (P : GL ι K)
    (hH : ∀ g ∈ H, P * g * P⁻¹ ∈ H') (h : NoncentralPair p H) : NoncentralPair p H' := by
  obtain ⟨x, y, hx, hy, hxp, hyp, hP, hnc⟩ := h
  refine ⟨P * x * P⁻¹, P * y * P⁻¹, hH x hx, hH y hy, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, hxp]; simp
  · rw [conj_pow, hyp]; simp
  · have hmap : Subgroup.closure ({P * x * P⁻¹, P * y * P⁻¹} : Set (GL ι K)) =
        (Subgroup.closure ({x, y} : Set (GL ι K))).map (MulAut.conj P).toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]; rfl
    rw [hmap]
    exact hP.map _
  · intro hs
    apply hnc
    have e : (P * x * P⁻¹ * (P * y * P⁻¹))⁻¹ * (P * y * P⁻¹ * (P * x * P⁻¹)) =
        P * ((x * y)⁻¹ * (y * x)) * P⁻¹ := by group
    rw [e] at hs
    have := (inferInstance : (StatedScalars ι K).Normal).conj_mem _ hs P⁻¹
    simpa [mul_assoc] using this

theorem noncentralPair_of_unitri [Nonempty ι] {p : ℕ} [Fact p.Prime] [CharP K p]
    {H : Subgroup (GL ι K)} {r : ι → ℕ} {m : ℕ} (hr : ∀ i, r i < m) (hmp : m ≤ p)
    {x y : GL ι K} (hx : x ∈ H) (hy : y ∈ H) (hxu : IsUnitri r x) (hyu : IsUnitri r y)
    (hxy : x * y ≠ y * x) : NoncentralPair p H := by
  have hmp' : m ≤ p ^ 1 := by simpa using hmp
  refine ⟨x, y, hx, hy, by simpa using hxu.pow_eq_one hr 1 hmp',
    by simpa using hyu.pow_eq_one hr 1 hmp', ?_, ?_⟩
  · intro g
    obtain ⟨k, hk⟩ : ∃ k : ℕ, g.1 ^ (p ^ k) = 1 := by
      refine ⟨m, ?_⟩
      exact closure_pair_pow_eq_one p hr hxu hyu g.1 g.2
    exact ⟨k, Subtype.ext hk⟩
  · intro hs
    obtain ⟨c, hc⟩ := hs
    have hxy_u : IsUnitri r (x * y) := hxu.mul hyu
    have hyx_u : IsUnitri r (y * x) := hyu.mul hxu
    have hscal : (y * x : GL ι K) = (x * y) * Matrix.GeneralLinearGroup.scalar ι c := by
      rw [hc]; group
    have hmat : ((y * x : GL ι K) : Matrix ι ι K) =
        (c : K) • ((x * y : GL ι K) : Matrix ι ι K) := by
      rw [hscal, Units.val_mul]
      ext i j
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_diagonal, mul_comm]
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hd := congrFun (congrFun hmat i) i
    rw [hyx_u.diag i, Matrix.smul_apply, hxy_u.diag i, smul_eq_mul, mul_one] at hd
    have hc1 : (c : K) = 1 := hd.symm
    apply hxy
    have hc1' : c = 1 := Units.ext hc1
    rw [hc1'] at hscal
    have h2 : y * x = x * y := by simpa using hscal
    exact h2.symm

end CFSG.RankThree.PartOne.StrongP
