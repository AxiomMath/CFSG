module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAutOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldMatrix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSL2
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.CGT.Stroth77.L4Sylow.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedProj StatedSL StatedSU StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank

private theorem fieldAut_pow_three_pow_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (hφpow : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    φ ^ (3 ^ (f.factorization 3)) = 1 := by
  let q₀ := p ^ (f / 3 ^ (f.factorization 3))
  have hpow : ∀ m : ℕ, ∀ x : K, (φ ^ m) x = x ^ (q₀ ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ']
        change φ ((φ ^ m) x) = x ^ (q₀ ^ (m + 1))
        rw [ih, hφpow, ← pow_mul, pow_succ]
  have hq0pow : q₀ ^ (3 ^ (f.factorization 3)) = p ^ f := by
    dsimp only [q₀]
    rw [← pow_mul, Nat.div_mul_cancel]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hpowcard : ∀ x : K, x ^ Nat.card K = x := by
    intro x
    have hF : Fintype K := Fintype.ofFinite K
    simp [Nat.card_eq_fintype_card]
  apply RingEquiv.ext
  intro x
  rw [hpow, hq0pow, ← hK]
  exact hpowcard x

private theorem pairMat_map {ι : Type*} [DecidableEq ι] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : ι) (g : Matrix (Fin 2) (Fin 2) R) :
    (pairMat a b g).map f = pairMat a b (g.map f) := by
  ext x y
  rw [Matrix.map_apply]
  simp only [pairMat, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [Matrix.one_apply]

private noncomputable def slMap {K : Type} [Field K] (φ : K →+* K) (g : SpecialLinearGroup (Fin 2) K) :
    SpecialLinearGroup (Fin 2) K :=
  ⟨(g : Matrix (Fin 2) (Fin 2) K).map φ, by
    change (φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) K)).det = 1
    rw [← φ.map_det, g.prop, map_one]⟩

private theorem map_lam {K : Type} [Field K] (φ : K →+* K) (i : Fin 2) (g : SpecialLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup.map (n := Fin 2 ⊕ Fin 2) φ
        ((lam i g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      lam i (slMap φ g) := by
  ext x y
  rw [Matrix.GeneralLinearGroup.map_apply, coe_lam, coe_lam]
  exact congrFun (congrFun (pairMat_map φ (Sum.inl i) (Sum.inr i)
    (g : Matrix (Fin 2) (Fin 2) K)) x) y

private theorem not_three_dvd_sq_add_one {q : ℕ} (hq : ¬ 3 ∣ q) : ¬ 3 ∣ q ^ 2 + 1 := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rintro h
  rcases hmod with hm | hm <;>
    simp [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod, Nat.add_mod, hm] at h

private theorem factorization_card_statedSp_two_eq {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) :
    (Nat.card (StatedSp 2 K)).factorization 3 =
      2 * (Nat.card (StatedSL 2 K)).factorization 3 := by
  set q := Nat.card K with hqdef
  have hq : 2 ≤ q := by rw [hqdef]; exact Finite.one_lt_card
  have h3q1 : q.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
  have h3q : ∀ n : ℕ, (q ^ n).factorization 3 = 0 := fun n =>
    Nat.factorization_eq_zero_of_not_dvd (fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h))
  have h3q2 : (q ^ 2 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_three_dvd_sq_add_one h3)
  have hq2 : 1 < q ^ 2 := by
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hne1 : q ^ 2 - 1 ≠ 0 := by omega
  have hne2 : q ^ 2 + 1 ≠ 0 := by positivity
  have hne3 : q ≠ 0 := by omega
  have hne4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hne3
  have hq4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), Nat.one_le_pow 4 q (by omega)]
    ring
  have e : Nat.card (StatedSp 2 K) = q ^ 4 * ((q ^ 2 - 1) * ((q ^ 2 - 1) * (q ^ 2 + 1))) := by
    rw [card_statedSp_two, ← hqdef, hq4]
  have e2 : Nat.card (StatedSL 2 K) = q * (q ^ 2 - 1) := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two, ← hqdef]
  rw [e, e2, Nat.factorization_mul hne4 (mul_ne_zero hne1 (mul_ne_zero hne1 hne2)),
    Nat.factorization_mul hne1 (mul_ne_zero hne1 hne2), Nat.factorization_mul hne1 hne2,
    Nat.factorization_mul hne3 hne1]
  simp only [Finsupp.add_apply, h3q, h3q2, h3q1]
  omega

private theorem disjoint_pair {i j : Fin 2} (hij : i ≠ j) :
    Disjoint ({Sum.inl i, Sum.inr i} : Set (Fin 2 ⊕ Fin 2)) {Sum.inl j, Sum.inr j} := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxi hxj
  rcases hxi with rfl | rfl <;> rcases hxj with h | h <;> simp_all

private noncomputable def blocksHom {K : Type} [Field K] :
    SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →* StatedSp 2 K where
  toFun p := lam (0 : Fin 2) p.1 * lam (1 : Fin 2) p.2
  map_one' := by simp
  map_mul' p q := by
    show lam (0 : Fin 2) (p.1 * q.1) * lam (1 : Fin 2) (p.2 * q.2) =
      (lam (0 : Fin 2) p.1 * lam (1 : Fin 2) p.2) *
        (lam (0 : Fin 2) q.1 * lam (1 : Fin 2) q.2)
    rw [map_mul, map_mul]
    exact (commute_lam_lam (i := 0) (j := 1) (by decide) q.1 p.2).mul_mul_mul_comm
      (lam (0 : Fin 2) p.1) (lam (1 : Fin 2) q.2)

private theorem lam_mul_eq_one_left {K : Type} [Field K] {i j : Fin 2} (hij : i ≠ j)
    {u v : SpecialLinearGroup (Fin 2) K} (h : lam i u * lam j v = 1) : lam i u = 1 := by
  apply statedSp_ext
  ext x y
  by_cases hx : x ∈ ({Sum.inl i, Sum.inr i} : Set (Fin 2 ⊕ Fin 2))
  · by_cases hy : y ∈ ({Sum.inl i, Sum.inr i} : Set (Fin 2 ⊕ Fin 2))
    · have hmat : (((lam i u * lam j v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y =
          (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y := by
        rw [h]; rfl
      rw [← IsSupp.mul_apply_of_mem (isSupp_lam i u) (isSupp_lam j v)
        (disjoint_pair hij) hx y]
      exact hmat
    · exact (isSupp_lam i u) x y (Or.inr hy)
  · exact (isSupp_lam i u) x y (Or.inl hx)

private theorem blocksHom_eq_one {K : Type} [Field K] {p : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hp : blocksHom p = 1) : p = 1 := by
  have h1 : lam (0 : Fin 2) p.1 = 1 := by
    apply lam_mul_eq_one_left (i := 0) (j := 1) (by decide)
    simpa only [blocksHom, MonoidHom.coe_mk, OneHom.coe_mk, map_one, mul_one] using hp
  have h2 : lam (1 : Fin 2) p.2 = 1 := by
    have h : lam (0 : Fin 2) p.1 * lam (1 : Fin 2) p.2 = 1 := by
      simpa only [blocksHom, MonoidHom.coe_mk, OneHom.coe_mk] using hp
    rw [h1, one_mul] at h
    exact h
  refine Prod.ext ?_ ?_
  · exact lam_injective (0 : Fin 2) (by simpa using h1)
  · exact lam_injective (1 : Fin 2) (by simpa using h2)

private theorem blocksHom_injective {K : Type} [Field K] : Function.Injective (blocksHom (K := K)) := by
  intro p q hpq
  have h : blocksHom (p * q⁻¹) = 1 := by
    rw [map_mul, hpq, map_inv, mul_inv_cancel]
  have h1 := blocksHom_eq_one h
  have h2 := congrArg (fun x : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K =>
    x * q) h1
  simpa using h2

private noncomputable def toSLOf {K : Type} [Field K] {C : Subgroup (GL (Fin 2) K)} (hC : C ≤ StatedSL 2 K) :
    C →* SpecialLinearGroup (Fin 2) K :=
  (specialLinearGroupEquivStatedSL 2 K).symm.toMonoidHom.comp (Subgroup.inclusion hC)

private theorem toSLOf_injective {K : Type} [Field K] {C : Subgroup (GL (Fin 2) K)} (hC : C ≤ StatedSL 2 K) :
    Function.Injective (toSLOf hC) :=
  (specialLinearGroupEquivStatedSL 2 K).symm.injective.comp (Subgroup.inclusion_injective hC)

private theorem slMap_toSLOf {K : Type} [Field K] (φ : K →+* K) {C : Subgroup (GL (Fin 2) K)}
    (hC : C ≤ StatedSL 2 K)
    {s : ℕ} (hCmap : ∀ g ∈ C, Matrix.GeneralLinearGroup.map φ g = g ^ s) (g : C) :
    slMap φ (toSLOf hC g) = (toSLOf hC g) ^ s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  have hcoe : (toSLOf hC g).val = ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h := specialLinearGroupEquivStatedSL_coe 2 K (toSLOf hC g)
    have h2 : (specialLinearGroupEquivStatedSL 2 K) (toSLOf hC g) =
        ⟨(g : GL (Fin 2) K), hC g.2⟩ :=
      (specialLinearGroupEquivStatedSL 2 K).apply_symm_apply _
    rw [h2] at h
    exact h.symm
  change ((toSLOf hC g).val).map φ = (toSLOf hC g).val ^ s
  rw [hcoe]
  have hg := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) (hCmap g g.2)
  rw [Units.val_pow_eq_pow_val] at hg
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map] at hg
  exact hg

private noncomputable def bHom {K : Type} [Field K] {C : Subgroup (GL (Fin 2) K)} (hC : C ≤ StatedSL 2 K) :
    C × C →* StatedSp 2 K :=
  blocksHom.comp (((toSLOf hC).comp (MonoidHom.fst C C)).prod
    ((toSLOf hC).comp (MonoidHom.snd C C)))

private theorem map_bHom {K : Type} [Field K] (φ : K →+* K) {C : Subgroup (GL (Fin 2) K)}
    (hC : C ≤ StatedSL 2 K)
    {s : ℕ} (hCmap : ∀ g ∈ C, Matrix.GeneralLinearGroup.map φ g = g ^ s) (p : C × C) :
    Matrix.GeneralLinearGroup.map (n := Fin 2 ⊕ Fin 2) φ
        ((bHom hC p : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (((bHom hC p : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) ^ s := by
  have h1 : slMap φ (toSLOf hC p.1) = (toSLOf hC p.1) ^ s := slMap_toSLOf φ hC hCmap p.1
  have h2 : slMap φ (toSLOf hC p.2) = (toSLOf hC p.2) ^ s := slMap_toSLOf φ hC hCmap p.2
  have hcomm : Commute (((lam (0 : Fin 2) (toSLOf hC p.1) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K)) (((lam (1 : Fin 2) (toSLOf hC p.2) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K)) :=
    (commute_lam_lam (i := 0) (j := 1) (by decide : (0 : Fin 2) ≠ 1)
      (toSLOf hC p.1) (toSLOf hC p.2)).map (Subgroup.subtype (StatedSp 2 K))
  change Matrix.GeneralLinearGroup.map φ
      (((lam (0 : Fin 2) (toSLOf hC p.1) * lam (1 : Fin 2) (toSLOf hC p.2) : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K)) = _
  rw [Subgroup.coe_mul, map_mul, map_lam, map_lam, h1, h2,
    map_pow (lam (0 : Fin 2)) (toSLOf hC p.1) s,
    map_pow (lam (1 : Fin 2)) (toSLOf hC p.2) s, Subgroup.coe_pow, Subgroup.coe_pow]
  exact (hcomm.mul_pow s).symm

theorem exists_abelian_sylow_power_map_statedSp {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : 3 ≤ p ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (φ : RingAut K) (hφ : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSp 2 K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSp 2 K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSp 2 K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSp 2 K)), IsFieldMapQuot (StatedSp 2 K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSp 2 K))), τ x = x ^ s := by
  have hq' : 3 ≤ p ^ f := hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, s, hCsyl, hCcyc, hs, hCmap⟩ :=
    exists_stable_cyclic_sylow_three_statedSL_two hp hp3 hf hK φ hφ
  have : IsMulCommutative C := hCcyc.isMulCommutative
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h
    have h3eq : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p
    exact hp3 h3eq.symm
  have hCcard : Nat.card C = 3 ^ (Nat.card (StatedSL 2 K)).factorization 3 := hCsyl.card_eq
  have hcard : Nat.card (C × C) = 3 ^ (Nat.card (StatedSp 2 K)).factorization 3 := by
    rw [Nat.card_prod, hCcard, ← pow_add, factorization_card_statedSp_two_eq h3]
    congr 1
    ring
  have hbHinj : Function.Injective (bHom hCsyl.le) := by
    intro x y hxy
    have h1 : (toSLOf hCsyl.le x.1, toSLOf hCsyl.le x.2) =
        (toSLOf hCsyl.le y.1, toSLOf hCsyl.le y.2) := blocksHom_injective hxy
    exact Prod.ext (toSLOf_injective hCsyl.le (Prod.ext_iff.mp h1).1)
      (toSLOf_injective hCsyl.le (Prod.ext_iff.mp h1).2)
  let N : Subgroup (StatedSp 2 K) := (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)
  have : N.Normal := inferInstance
  obtain ⟨Q, hQ⟩ :=
    CFSG.CGT.Stroth77.L4Sylow.exists_sylow_quotient_eq_range N (bHom hCsyl.le) hbHinj hcard
  refine ⟨Q, s, ?_, hs, ?_⟩
  · intro x hx y hy
    rw [hQ] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    show (QuotientGroup.mk' N) (bHom hCsyl.le a) * (QuotientGroup.mk' N) (bHom hCsyl.le b) =
      (QuotientGroup.mk' N) (bHom hCsyl.le b) * (QuotientGroup.mk' N) (bHom hCsyl.le a)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    have : IsMulCommutative (C × C) := inferInstance
    have hab : a * b = b * a := mul_comm' a b
    exact congrArg (bHom hCsyl.le) hab
  · intro τ hτ x hx
    rw [hQ] at hx
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨h, hh, hτh⟩ := hτ (bHom hCsyl.le a)
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hτh]
    have hhpow : h = (bHom hCsyl.le a) ^ s := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      apply Units.ext
      rw [hh, Units.val_pow_eq_pow_val]
      exact congrArg (fun z : GL (Fin 2 ⊕ Fin 2) K =>
        (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        (map_bHom φ hCsyl.le hCmap a)
    rw [hhpow]
    exact map_pow (QuotientGroup.mk' N) (bHom hCsyl.le a) s

theorem exists_test_element_statedSp {K : Type} [Field K] [Finite K] :
    ∃ a : K, (∀ σ : RingAut K, σ a = a → σ = 1) ∧
      ∃ A₀ : StatedSp 2 K,
        Matrix.trace (((A₀ : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          a + a⁻¹ + ((2 : ℕ) : K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  let a : K := (g : K)
  have ha : a ≠ 0 := Units.ne_zero g
  have hfix : ∀ σ : RingAut K, σ a = a → σ = 1 := by
    intro σ hσ
    let σu : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom
    have hσu : σu g = g := by
      apply Units.ext
      exact hσ
    ext x
    by_cases hx : x = 0
    · subst hx; simp
    · let u : Kˣ := Units.mk0 x hx
      have hu : (u : K) = x := rfl
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hσuu : σu u = u := by
        rw [← hk, map_zpow, hσu]
      have h1 : σ x = (σu u : K) := by
        rw [← hu, ← hk]
        simp [σu]
      rw [h1, hσuu]
      exact hu
  refine ⟨a, hfix, ?_⟩
  refine ⟨torusHom (r := 2) (k := K) (Pi.mulSingle (0 : Fin 2) g), ?_⟩
  rw [coe_torusHom, Matrix.trace_diagonal, Fintype.sum_sum_type]
  simp only [Pi.mulSingle_apply, Fin.isValue, Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num
  ring

theorem three_pow_dvd_of_pow_mem_inner_statedSp {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : 3 ≤ p ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (φ : RingAut K) (hφ : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3))))
    (τ : MulAut (StatedProj (StatedSp 2 K))) (hτ : IsFieldMapQuot (StatedSp 2 K) φ τ)
    (j : ℕ) (hj : τ ^ j ∈ inner (StatedProj (StatedSp 2 K))) :
    3 ^ (f.factorization 3) ∣ j := by
  obtain ⟨a, ha, A₀, hA₀⟩ := exists_test_element_statedSp (K := K)
  have hperf : Group.IsPerfect (StatedSp 2 K) := by
    have hcard : 3 ≤ Nat.card K := by rw [hK]; exact hq
    refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 K ?_
    rcases lt_or_eq_of_le hcard with h4 | h3
    · left
      have : Fintype K := Fintype.ofFinite K
      have hcarduniv : (Finset.univ : Finset K).card = Nat.card K := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
        (n := 4) (by rw [hcarduniv]; omega)
      exact ⟨t, ht⟩
    · right; left
      exact ⟨h3.symm, le_rfl⟩
  let q₀ := p ^ (f / 3 ^ (f.factorization 3))
  have hpow : ∀ m : ℕ, ∀ x : K, (φ ^ m) x = x ^ (q₀ ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ']
        change φ ((φ ^ m) x) = x ^ (q₀ ^ (m + 1))
        rw [ih, hφ, ← pow_mul, pow_succ]
  have hφb : φ ^ (3 ^ (f.factorization 3)) = 1 :=
    fieldAut_pow_three_pow_eq_one hf hK φ hφ
  have h3odd : Odd (3 ^ (f.factorization 3)) := (show Odd (3 : ℕ) by decide).pow
  have hodd : Odd (orderOf φ) :=
    Odd.of_dvd_nat h3odd (orderOf_dvd_iff_pow_eq_one.mpr hφb)
  have hφj : φ ^ j = 1 :=
    pow_eq_one_of_pow_mem_inner (StatedSp 2 K) hperf φ hodd a ha 2 A₀ hA₀ τ hτ j hj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hpowcard : ∀ x : K, x ^ Nat.card K = x := by
    intro x
    have hF : Fintype K := Fintype.ofFinite K
    simp [Nat.card_eq_fintype_card]
  have hgu : g ^ (q₀ ^ j) = g := by
    have h1 : (g : K) ^ (q₀ ^ j) = (g : K) := by
      have := hpow j (g : K)
      rw [hφj] at this
      simpa using this.symm
    apply Units.ext
    simpa using h1
  have hdvdorder : orderOf g ∣ q₀ ^ j - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hq1 : 1 ≤ q₀ ^ j := one_le_pow₀ (one_le_pow₀ hp.one_le : 1 ≤ q₀)
    have h2 : g ^ (q₀ ^ j - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, hgu, one_mul]
    exact mul_right_cancel h2
  have hq0pow : q₀ ^ (3 ^ (f.factorization 3)) = p ^ f := by
    dsimp only [q₀]
    rw [← pow_mul, Nat.div_mul_cancel]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hordg : orderOf g = q₀ ^ (3 ^ (f.factorization 3)) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK, ← hq0pow]
  have hbig : q₀ ^ (3 ^ (f.factorization 3)) - 1 ∣ q₀ ^ j - 1 := by
    rw [← hordg]; exact hdvdorder
  have h3bdvd : 3 ^ (f.factorization 3) ∣ f :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hq0ge : 2 ≤ q₀ := by
    have hle : 3 ^ (f.factorization 3) ≤ f := Nat.le_of_dvd (by omega) h3bdvd
    have hk : f / 3 ^ (f.factorization 3) ≠ 0 := by
      have hpos : 0 < f / 3 ^ (f.factorization 3) :=
        Nat.div_pos hle (pow_pos (by norm_num) _)
      omega
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ (f / 3 ^ (f.factorization 3)) := le_self_pow hp.one_le hk
      _ = q₀ := rfl
  exact dvd_of_pow_sub_one_dvd_pow_sub_one hq0ge (pow_pos (by norm_num) _) hbig

theorem fieldSylowData_statedSp {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : 3 ≤ p ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) :
    FieldSylowData (StatedProj (StatedSp 2 K)) (f.factorization 3) := by
  obtain ⟨φ, hφpow⟩ := by
    have : Fact p.Prime := ⟨hp⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K p :=
      charP_of_card_eq_prime_pow (R := K) (by simpa [Nat.card_eq_fintype_card] using hK)
    exact exists_ringAut_pow_of_charP (K := K) (p := p) (f / 3 ^ (f.factorization 3))
  obtain ⟨Q, s, hQab, hs, hQmap⟩ :=
    exists_abelian_sylow_power_map_statedSp hp hp3 hf hq hK φ hφpow
  have hH : ∀ g ∈ StatedSp 2 K, Matrix.GeneralLinearGroup.map (φ : K →+* K) g ∈ StatedSp 2 K :=
    fun g hg => CFSG.Open.StatedAPI.map_mem_statedSp (φ : K →+* K) hg
  obtain ⟨τ, hτ⟩ := exists_isFieldMapQuot (StatedSp 2 K) φ hH
  have hφb : φ ^ (3 ^ (f.factorization 3)) = 1 :=
    fieldAut_pow_three_pow_eq_one hf hK φ hφpow
  refine ⟨Q, τ, s, hQab, hs, ?_, ?_, ?_⟩
  · intro x hx
    exact hQmap τ hτ x hx
  · have hτα : IsFieldMapQuot (StatedSp 2 K) (φ ^ (3 ^ (f.factorization 3)))
        (τ ^ (3 ^ (f.factorization 3))) := isFieldMapQuot_pow hτ _
    rw [hφb] at hτα
    exact eq_one_of_isFieldMapQuot_one hτα
  · intro j hj
    exact three_pow_dvd_of_pow_mem_inner_statedSp hp hf hq hK φ hφpow τ hτ j hj

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
