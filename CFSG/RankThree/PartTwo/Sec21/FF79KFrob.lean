module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

private lemma prod_range_seven_perm {M : Type*} [CommMonoid M] (f : ℕ → M)
    (hf : ∀ n, f (n + 7) = f n) {c : ℕ} (hc : c % 7 ≠ 0) :
    ∏ i ∈ Finset.range 7, f (c * i) = ∏ i ∈ Finset.range 7, f i := by
  have hper : ∀ q r, f (r + 7 * q) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show r + 7 * (q + 1) = (r + 7 * q) + 7 by omega, hf, ih]
  have hf' : ∀ n, f n = f (n % 7) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n 7]
    exact hper _ _
  have hinj : ∀ r < 7, r ≠ 0 → ∀ a < 7, ∀ a' < 7, r * a % 7 = r * a' % 7 → a = a' := by decide
  have hsurj : ∀ r < 7, r ≠ 0 → ∀ b < 7, ∃ a < 7, r * a % 7 = b := by decide
  have hmod : ∀ a < 7, c * a % 7 = (c % 7) * a % 7 := fun a ha => by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt ha]
  calc ∏ i ∈ Finset.range 7, f (c * i)
      = ∏ i ∈ Finset.range 7, f (c * i % 7) := Finset.prod_congr rfl fun i _ => hf' _
    _ = ∏ i ∈ Finset.range 7, f i := by
      refine Finset.prod_nbij (fun i => c * i % 7) ?_ ?_ ?_ fun _ _ => rfl
      · intro a _
        exact Finset.mem_range.2 (Nat.mod_lt _ (by omega))
      · intro a ha a' ha' h
        simp only [Finset.coe_range, Set.mem_Iio] at ha ha'
        simp only at h
        rw [hmod a ha, hmod a' ha'] at h
        exact hinj (c % 7) (Nat.mod_lt _ (by omega)) hc a ha a' ha' h
      · intro b hb
        simp only [Finset.coe_range, Set.mem_Iio] at hb
        obtain ⟨a, ha, hab⟩ := hsurj (c % 7) (Nat.mod_lt _ (by omega)) hc b hb
        refine ⟨a, by simpa using ha, ?_⟩
        simp only
        rw [hmod a ha, hab]

section Abstract

variable {Q N : Type*} [CommGroup Q] [Group N] [MulDistribMulAction N Q]

private def trace7 (d : N) (q : Q) : Q := ∏ i ∈ Finset.range 7, (d ^ i) • q

private lemma trace7_mul (d : N) (a b : Q) : trace7 d (a * b) = trace7 d a * trace7 d b := by
  simp [trace7, smul_mul', Finset.prod_mul_distrib]

private lemma trace7_one (d : N) : trace7 d (1 : Q) = 1 := by
  simp [trace7, smul_one]

private def triple (β : N) (y : Q) : Q := y * (β • y) * ((β ^ 2) • y)

private lemma trace_aux (hsq : ∀ q : Q, q * q = 1) {d β : N} {k : ℕ} (hk : k = 2 ∨ k = 4)
    (hd : d ^ 7 = 1) (hβ : β ^ 3 = 1) (hrel : β * d * β⁻¹ = d ^ k)
    (hfix : ∀ q : Q, β • q = q → q = 1) (q : Q) : d • q = q := by
  have hG1 : ∀ n : ℕ, β * d ^ n = d ^ (k * n) * β := by
    intro n
    have h1 : (β * d * β⁻¹) ^ n = β * d ^ n * β⁻¹ := conj_pow
    rw [hrel, ← pow_mul] at h1
    exact (eq_mul_inv_iff_mul_eq.1 h1).symm
  have hC0 : ∀ i : ℕ, d ^ i * d ^ (6 * i) = 1 := by
    intro i
    rw [← pow_add, show i + 6 * i = 7 * i by ring, pow_mul, hd, one_pow]
  have hC1 : ∀ i : ℕ, d ^ i * (β * d ^ (6 * i)) = d ^ ((1 + 6 * k) * i) * β := by
    intro i
    rw [hG1, ← mul_assoc, ← pow_add]
    congr 2
    ring
  have hC2 : ∀ i : ℕ, d ^ i * (β ^ 2 * d ^ (6 * i)) = d ^ ((1 + 6 * k * k) * i) * β ^ 2 := by
    intro i
    have : β ^ 2 * d ^ (6 * i) = d ^ (k * (k * (6 * i))) * β ^ 2 := by
      rw [sq, mul_assoc, hG1, ← mul_assoc, hG1, mul_assoc, ← sq]
    rw [this, ← mul_assoc, ← pow_add]
    congr 2
    ring
  have hS : ∀ y : Q, triple β y = 1 := by
    intro y
    apply hfix
    have h3 : β * β ^ 2 = 1 := by rw [← pow_succ']; exact hβ
    have h2 : β • (β ^ 2 • y) = y := by rw [smul_smul, h3, one_smul]
    have h22 : β • (β • y) = β ^ 2 • y := by rw [smul_smul, sq]
    simp only [triple]
    rw [smul_mul', smul_mul', h2, h22]
    ac_rfl
  have h2 : trace7 d q * trace7 d (β • q) * trace7 d ((β ^ 2) • q) = 1 := by
    rw [← trace7_mul, ← trace7_mul]
    have := hS q
    simp only [triple] at this
    rw [this, trace7_one]
  have hterm : ∀ i : ℕ, (d ^ i) • triple β ((d ^ (6 * i)) • q) =
      q * ((d ^ ((1 + 6 * k) * i) * β) • q) * ((d ^ ((1 + 6 * k * k) * i) * β ^ 2) • q) := by
    intro i
    simp only [triple, smul_mul', smul_smul, hC0, hC1, hC2, one_smul]
  have hper : ∀ y : Q, ∀ n : ℕ, (d ^ (n + 7)) • y = (d ^ n) • y := by
    intro y n
    rw [pow_add, hd, mul_one]
  have hk1 : (1 + 6 * k) % 7 ≠ 0 := by rcases hk with rfl | rfl <;> decide
  have hk2 : (1 + 6 * k * k) % 7 ≠ 0 := by rcases hk with rfl | rfl <;> decide
  have h3 : ∏ i ∈ Finset.range 7, (d ^ i) • triple β ((d ^ (6 * i)) • q) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [hS, smul_one]
  have hq7 : q ^ 7 = q := by
    have h2 : q ^ 2 = 1 := by rw [sq]; exact hsq q
    rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul, h2, one_pow, one_mul]
  have e1 : ∏ i ∈ Finset.range 7, (d ^ ((1 + 6 * k) * i) * β) • q = trace7 d (β • q) := by
    simp only [mul_smul]
    exact prod_range_seven_perm (fun n => (d ^ n) • (β • q)) (fun n => hper _ n) hk1
  have e2 : ∏ i ∈ Finset.range 7, (d ^ ((1 + 6 * k * k) * i) * β ^ 2) • q =
      trace7 d ((β ^ 2) • q) := by
    simp only [mul_smul]
    exact prod_range_seven_perm (fun n => (d ^ n) • ((β ^ 2) • q)) (fun n => hper _ n) hk2
  have h3' : q * (trace7 d (β • q) * trace7 d ((β ^ 2) • q)) = 1 := by
    simp only [hterm] at h3
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      hq7, e1, e2] at h3
    rw [← mul_assoc]
    exact h3
  have h4 : q = trace7 d q := by
    refine mul_right_cancel (b := trace7 d (β • q) * trace7 d ((β ^ 2) • q)) ?_
    rw [h3', ← mul_assoc, h2]
  have h5 : d • trace7 d q = trace7 d q := by
    unfold trace7
    rw [Finset.smul_prod']
    simp only [smul_smul, ← pow_succ']
    have e1 := Finset.prod_range_succ' (fun i => (d ^ i) • q) 7
    have e2 := Finset.prod_range_succ (fun i => (d ^ i) • q) 7
    simp only [hd, pow_zero, one_smul] at e1 e2
    exact mul_right_cancel (b := q) (e1.symm.trans e2)
  calc d • q = d • trace7 d q := congrArg (d • ·) h4
    _ = trace7 d q := h5
    _ = q := h4.symm

end Abstract

section Geometric

variable {G : Type*} [Group G]

private abbrev NN (T₀ E : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (T₀ : Set G)

private def conjE (T₀ E : Subgroup G) (g : NN T₀ E) : E →* E where
  toFun x := ⟨g.1 * x * g.1⁻¹, (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 g.2).1 x).1 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp] private lemma conjE_coe (T₀ E : Subgroup G) (g : NN T₀ E) (x : E) :
    ((conjE T₀ E g x : E) : G) = g.1 * x * g.1⁻¹ := rfl

variable {T₀ E : Subgroup G} [(T₀.subgroupOf E).Normal]

private def conjQ (g : NN T₀ E) : ↥E ⧸ T₀.subgroupOf E →* ↥E ⧸ T₀.subgroupOf E :=
  QuotientGroup.map (T₀.subgroupOf E) (T₀.subgroupOf E) (conjE T₀ E g) (fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 g.2).2 x).1
      (Subgroup.mem_subgroupOf.1 hx))

private instance instActQ : MulDistribMulAction (NN T₀ E) (↥E ⧸ T₀.subgroupOf E) where
  smul g q := conjQ g q
  one_smul q := by
    refine QuotientGroup.induction_on q fun x => ?_
    show (QuotientGroup.mk (conjE T₀ E 1 x) : ↥E ⧸ T₀.subgroupOf E) = QuotientGroup.mk x
    exact congrArg QuotientGroup.mk (Subtype.ext (by simp))
  mul_smul g h q := by
    refine QuotientGroup.induction_on q fun x => ?_
    show (QuotientGroup.mk (conjE T₀ E (g * h) x) : ↥E ⧸ T₀.subgroupOf E) =
      QuotientGroup.mk (conjE T₀ E g (conjE T₀ E h x))
    exact congrArg QuotientGroup.mk (Subtype.ext (by simp [mul_assoc]))
  smul_one g := map_one (conjQ g)
  smul_mul g a b := map_mul (conjQ g) a b

private lemma smul_mk_eq_iff (g : NN T₀ E) (x : E) :
    g • (QuotientGroup.mk x : ↥E ⧸ T₀.subgroupOf E) = QuotientGroup.mk x ↔
      (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ ∈ T₀ := by
  change (QuotientGroup.mk (conjE T₀ E g x) : ↥E ⧸ T₀.subgroupOf E) = QuotientGroup.mk x ↔ _
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simp [div_eq_mul_inv]

end Geometric

theorem frob73_mod {G : Type*} [Group G] {T₀ E : Subgroup G} (hTE : T₀ ≤ E)
    (hEN : E ≤ Subgroup.normalizer (T₀ : Set G))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ T₀) (hsq : ∀ x ∈ E, x * x ∈ T₀)
    {d β : G} (hdE : d ∈ Subgroup.normalizer (E : Set G))
    (hdT : d ∈ Subgroup.normalizer (T₀ : Set G))
    (hβE : β ∈ Subgroup.normalizer (E : Set G)) (hβT : β ∈ Subgroup.normalizer (T₀ : Set G))
    (hd : d ^ 7 = 1) (hβ : β ^ 3 = 1) {k : ℕ} (hk : k = 2 ∨ k = 4)
    (hrel : β * d * β⁻¹ = d ^ k)
    (hfix : ∀ x ∈ E, β * x * β⁻¹ * x⁻¹ ∈ T₀ → x ∈ T₀) :
    ∀ x ∈ E, d * x * d⁻¹ * x⁻¹ ∈ T₀ := by
  haveI : (T₀.subgroupOf E).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTE).2 hEN
  have hc : ∀ a b : ↥E ⧸ T₀.subgroupOf E, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
      Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv, mul_assoc] using hcomm x x.2 y y.2
  letI : CommGroup (↥E ⧸ T₀.subgroupOf E) :=
    { (inferInstance : Group (↥E ⧸ T₀.subgroupOf E)) with mul_comm := hc }
  have hsq' : ∀ q : ↥E ⧸ T₀.subgroupOf E, q * q = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq x x.2
  let dd : NN T₀ E := ⟨d, Subgroup.mem_inf.2 ⟨hdE, hdT⟩⟩
  let bb : NN T₀ E := ⟨β, Subgroup.mem_inf.2 ⟨hβE, hβT⟩⟩
  have hd' : dd ^ 7 = 1 := Subtype.ext (by simpa using hd)
  have hβ' : bb ^ 3 = 1 := Subtype.ext (by simpa using hβ)
  have hrel' : bb * dd * bb⁻¹ = dd ^ k := Subtype.ext (by simpa using hrel)
  have hfix' : ∀ q : ↥E ⧸ T₀.subgroupOf E, bb • q = q → q = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    intro h
    rw [smul_mk_eq_iff] at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hfix x x.2 h
  intro x hx
  exact (smul_mk_eq_iff dd ⟨x, hx⟩).1
    (trace_aux hsq' hk hd' hβ' hrel' hfix' (QuotientGroup.mk ⟨x, hx⟩))

end CFSG.RankThree.PartTwo.Sec21.FF79
