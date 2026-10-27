module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux4

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan Matrix
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private lemma p9uUOdd_conjTr_diagonal {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (d : Fin n → K) :
    conjTr (unitaryInvolution K 2 1) (Matrix.diagonal d) =
      Matrix.diagonal (fun i => unitaryInvolution K 2 1 (d i)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
  · simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), map_zero]

private lemma p9uUOdd_diag_pow_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {g : GL (Fin n) K} (hU : ggIsUnitaryMat (p := 2) (f := 1) g)
    {d : Fin n → K} (hgd : (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d) (i : Fin n) :
    d i ^ 3 = 1 := by
  unfold ggIsUnitaryMat at hU
  rw [hgd, p9uUOdd_conjTr_diagonal, Matrix.diagonal_mul_diagonal] at hU
  have hii := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hU
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hii
  rw [unitaryInvolution_apply] at hii
  norm_num at hii
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
  exact hii

private lemma p9uUOdd_ne_zero_of_pow_three {K : Type} [Field K] {x : K} (hx : x ^ 3 = 1) :
    x ≠ 0 := by
  intro h
  rw [h] at hx
  norm_num at hx

private def p9uUOdd_actBy {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {G : Type}
    [Group G] (ψ : Su K 2 1 n →* G) (b : G) (M : GL (Fin n) K) : Prop :=
  ∀ x : Su K 2 1 n, ∃ y : Su K 2 1 n,
    (y : GL (Fin n) K) = M * (x : GL (Fin n) K) * M⁻¹ ∧ b * ψ x * b⁻¹ = ψ y

private lemma p9uUOdd_actBy_of_induces {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {G : Type} [Group G] {ψ : Su K 2 1 n →* G} {b : G} {M : GL (Fin n) K}
    (h : GGInducesUnitary (p := 2) (f := 1) ψ b M) : p9uUOdd_actBy ψ b M :=
  fun x => h.2 x

private lemma p9uUOdd_actBy_mul {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {G : Type}
    [Group G] {ψ : Su K 2 1 n →* G} {b c : G} {M N : GL (Fin n) K}
    (hb : p9uUOdd_actBy ψ b M) (hc : p9uUOdd_actBy ψ c N) :
    p9uUOdd_actBy ψ (b * c) (M * N) := by
  intro x
  obtain ⟨y, hy, hcy⟩ := hc x
  obtain ⟨z, hz, hbz⟩ := hb y
  refine ⟨z, ?_, ?_⟩
  · rw [hz, hy]; group
  · rw [show b * c * ψ x * (b * c)⁻¹ = b * (c * ψ x * c⁻¹) * b⁻¹ by group, hcy, hbz]

private lemma p9uUOdd_actBy_self {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {G : Type}
    [Group G] {ψ : Su K 2 1 n →* G} (t : Su K 2 1 n) :
    p9uUOdd_actBy ψ (ψ t) (t : GL (Fin n) K) := by
  intro x
  refine ⟨t * x * t⁻¹, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  · rw [map_mul, map_mul, map_inv]

private lemma p9uUOdd_actBy_inv_self {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {G : Type} [Group G] {ψ : Su K 2 1 n →* G} (t : Su K 2 1 n) :
    p9uUOdd_actBy ψ (ψ t)⁻¹ ((t : GL (Fin n) K)⁻¹) := by
  intro x
  refine ⟨t⁻¹ * x * t, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  · rw [map_mul, map_mul, map_inv, inv_inv]

private lemma p9uUOdd_conj_eq_of_actBy {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {G : Type} [Group G] {ψ : Su K 2 1 n →* G} {b c : G} {M : GL (Fin n) K}
    (hb : p9uUOdd_actBy ψ b M) (hc : p9uUOdd_actBy ψ c M) :
    ∀ x : Su K 2 1 n, c * ψ x * c⁻¹ = b * ψ x * b⁻¹ := by
  intro x
  obtain ⟨y1, hy1, hb1⟩ := hb x
  obtain ⟨y2, hy2, hc1⟩ := hc x
  have hy : y1 = y2 := Subtype.ext (by rw [hy1, hy2])
  rw [hc1, hb1, hy]

private lemma p9uUOdd_centralizer_of_conj_eq {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {G : Type} [Group G] {ψ : Su K 2 1 n →* G} {u b : G}
    (hbN : b ∈ Subgroup.normalizer (ψ.range : Set G))
    (h : ∀ x : Su K 2 1 n, u * ψ x * u⁻¹ = b * ψ x * b⁻¹) :
    u * b⁻¹ ∈ Subgroup.centralizer (ψ.range : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := hw
  have hbN' : b⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.inv_mem _ hbN
  have hwb : b⁻¹ * ψ x * b ∈ ψ.range := by
    simpa using (Subgroup.mem_normalizer_iff.mp hbN' (ψ x)).mp ⟨x, rfl⟩
  obtain ⟨x', hx'⟩ := hwb
  have hconj : (u * b⁻¹) * ψ x * (u * b⁻¹)⁻¹ = ψ x := by
    have h1 : (u * b⁻¹) * ψ x * (u * b⁻¹)⁻¹ = u * (b⁻¹ * ψ x * b) * u⁻¹ := by group
    rw [h1, ← hx', h x']
    rw [hx']
    group
  have hgoal : (u * b⁻¹) * ψ x = ψ x * (u * b⁻¹) := by
    calc (u * b⁻¹) * ψ x
        = ((u * b⁻¹) * ψ x * (u * b⁻¹)⁻¹) * (u * b⁻¹) := by group
      _ = ψ x * (u * b⁻¹) := by rw [hconj]
  exact hgoal.symm

private lemma p9uUOdd_mem_normalizer_range_of_acts {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {G : Type} [Group G] {ψ : Su K 2 1 n →* G} {Bs : Subgroup G}
    (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ Bs) {b : G} (hb : b ∈ Bs) :
    b ∈ Subgroup.normalizer (ψ.range : Set G) := by
  have key : ∀ c ∈ Bs, ∀ z ∈ ψ.range, c * z * c⁻¹ ∈ ψ.range := by
    intro c hc z hz
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨g, -, hind⟩ := hdiag c hc
    obtain ⟨y, -, hby⟩ := hind.2 s
    exact ⟨y, hby.symm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key b hb z hz, fun hz => ?_⟩
  have h := key b⁻¹ (Bs.inv_mem hb) _ hz
  convert h using 1
  group

private def p9uUOdd_correct {n : ℕ} {K : Type} [Field K] (a b c l₀ : Fin n) (d : Fin n → K) :
    Fin n → K :=
  fun i => if i = a then d a else if i = b then d b else if i = c then d c
    else if i = l₀ then (d a * d b * d c)⁻¹ else 1

private lemma p9uUOdd_correct_a {n : ℕ} {K : Type} [Field K] (a b c l₀ : Fin n)
    (d : Fin n → K) : p9uUOdd_correct a b c l₀ d a = d a := by
  unfold p9uUOdd_correct
  rw [if_pos rfl]

private lemma p9uUOdd_correct_b {n : ℕ} {K : Type} [Field K] (a b c l₀ : Fin n)
    (d : Fin n → K) (hab : a ≠ b) : p9uUOdd_correct a b c l₀ d b = d b := by
  unfold p9uUOdd_correct
  rw [if_neg (Ne.symm hab), if_pos rfl]

private lemma p9uUOdd_correct_c {n : ℕ} {K : Type} [Field K] (a b c l₀ : Fin n)
    (d : Fin n → K) (hac : a ≠ c) (hbc : b ≠ c) : p9uUOdd_correct a b c l₀ d c = d c := by
  unfold p9uUOdd_correct
  rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos rfl]

private lemma p9uUOdd_correct_l {n : ℕ} {K : Type} [Field K] (a b c l₀ : Fin n)
    (d : Fin n → K) (hal : a ≠ l₀) (hbl : b ≠ l₀) (hcl : c ≠ l₀) :
    p9uUOdd_correct a b c l₀ d l₀ = (d a * d b * d c)⁻¹ := by
  unfold p9uUOdd_correct
  rw [if_neg (Ne.symm hal), if_neg (Ne.symm hbl), if_neg (Ne.symm hcl), if_pos rfl]

private lemma p9uUOdd_correct_prod {n : ℕ} {K : Type} [Field K] (a b c l₀ : Fin n)
    (d : Fin n → K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hal : a ≠ l₀)
    (hbl : b ≠ l₀) (hcl : c ≠ l₀) (hda : d a ≠ 0) (hdb : d b ≠ 0) (hdc : d c ≠ 0) :
    ∏ i, p9uUOdd_correct a b c l₀ d i = 1 := by
  rw [(Finset.prod_subset (s₁ := ({a, b, c, l₀} : Finset (Fin n))) (s₂ := Finset.univ)
    (Finset.subset_univ _) ?_).symm]
  · rw [show ({a, b, c, l₀} : Finset (Fin n)) = insert a (insert b (insert c (insert l₀ ∅)))
        from rfl,
      Finset.prod_insert (by simp [hab, hac, hal]), Finset.prod_insert (by simp [hbc, hbl]),
      Finset.prod_insert (by simp [hcl]), Finset.prod_insert (by simp), Finset.prod_empty,
      mul_one]
    rw [p9uUOdd_correct_a, p9uUOdd_correct_b a b c l₀ d hab,
      p9uUOdd_correct_c a b c l₀ d hac hbc, p9uUOdd_correct_l a b c l₀ d hal hbl hcl]
    rw [show d a * (d b * (d c * (d a * d b * d c)⁻¹)) = (d a * d b * d c) *
        (d a * d b * d c)⁻¹ by ring]
    exact mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero hda hdb) hdc)
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hxa, hxb, hxc, hxl⟩ := hx
    simp only [p9uUOdd_correct, if_neg hxa, if_neg hxb, if_neg hxc, if_neg hxl]

theorem qtwoDL1_baseU_oddC {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = L)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {r r' : MulAut ↥Bs}
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    (hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹) :
    Odd (Nat.card ↥(Subgroup.centralizer
      ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (L : Set G))) := by
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp (by simpa using h.dvd)
  have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) :=
    fun b hb => p9uUOdd_mem_normalizer_range_of_acts hd hb
  refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le ?_)
  intro c0 hc0
  rw [Subgroup.mem_inf] at hc0
  obtain ⟨hcA, hcL⟩ := hc0
  rw [Subgroup.mem_centralizer_iff]
  intro b0 hb0
  have hcard : ({a, b, c} : Finset (Fin n)).card ≤ 3 := by
    rw [show ({a, b, c} : Finset (Fin n)) = insert a (insert b ({c} : Finset (Fin n)))
        from rfl]
    calc (insert a (insert b ({c} : Finset (Fin n))) : Finset (Fin n)).card
        ≤ (insert b ({c} : Finset (Fin n))).card + 1 := Finset.card_insert_le a _
      _ ≤ ({c} : Finset (Fin n)).card + 1 + 1 := by
          have := Finset.card_insert_le b ({c} : Finset (Fin n))
          omega
      _ = 3 := by simp
  obtain ⟨l₀, hl₀⟩ := ggNSPosPB2_exists_notMem h.four_le ({a, b, c} : Finset (Fin n)) hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl₀
  obtain ⟨hl₀a, hl₀b, hl₀c⟩ := hl₀
  let β : ↥Bs := ⟨b0, hb0⟩
  obtain ⟨g, hgdiag, hindg⟩ := hd b0 hb0
  obtain ⟨d, hgd⟩ := hgdiag
  have hd3 : ∀ i, d i ^ 3 = 1 := fun i => p9uUOdd_diag_pow_three hindg.1 hgd i
  let e : Fin n → K := p9uUOdd_correct a b c l₀ d
  have hea : e a = d a := p9uUOdd_correct_a a b c l₀ d
  have heb : e b = d b := p9uUOdd_correct_b a b c l₀ d hab
  have hec : e c = d c := p9uUOdd_correct_c a b c l₀ d hac hbc
  have hel : e l₀ = (d a * d b * d c)⁻¹ :=
    p9uUOdd_correct_l a b c l₀ d (Ne.symm hl₀a) (Ne.symm hl₀b) (Ne.symm hl₀c)
  have he3 : ∀ i, e i ^ 3 = 1 := by
    intro i
    by_cases hia : i = a
    · rw [hia, hea]; exact hd3 a
    by_cases hib : i = b
    · rw [hib, heb]; exact hd3 b
    by_cases hic : i = c
    · rw [hic, hec]; exact hd3 c
    by_cases hil : i = l₀
    · rw [hil, hel, inv_pow,
        show (d a * d b * d c) ^ 3 = 1 by
          rw [mul_pow, mul_pow, hd3 a, hd3 b, hd3 c, mul_one, one_mul],
        inv_one]
    · simp only [e, p9uUOdd_correct, if_neg hia, if_neg hib, if_neg hic, if_neg hil, one_pow]
  have hedet : ∏ i, e i = 1 := by
    rw [show e = p9uUOdd_correct a b c l₀ d from rfl]
    exact p9uUOdd_correct_prod a b c l₀ d hab hac hbc (Ne.symm hl₀a) (Ne.symm hl₀b)
      (Ne.symm hl₀c) (p9uUOdd_ne_zero_of_pow_three (hd3 a))
      (p9uUOdd_ne_zero_of_pow_three (hd3 b)) (p9uUOdd_ne_zero_of_pow_three (hd3 c))
  have heunit : ∀ i, unitaryInvolution K 2 1 (e i) * e i = 1 := by
    intro i
    have h := he3 i
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ] at h
    rw [unitaryInvolution_apply]
    norm_num
    exact h
  let t : Su K 2 1 n := ggNSPosPB2_diagSU e hedet heunit
  have htcoemat : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal e :=
    ggNSPosPB2_diagSU_coe e hedet heunit
  have htBs : ψ t ∈ Bs :=
    ggNSDiag_torus_le h hd t ⟨e, htcoemat, fun i => by rw [hp3]; exact he3 i⟩
  let β' : G := (β : G) * (ψ t)⁻¹
  have hβ'Bs : β' ∈ Bs := by
    show (β : G) * (ψ t)⁻¹ ∈ Bs
    exact Bs.mul_mem β.2 (Bs.inv_mem htBs)
  let B' : ↥Bs := ⟨β', hβ'Bs⟩
  have hB'coe : (B' : G) = β' := rfl
  let δf : Fin n → K := fun i => d i * (e i)⁻¹
  let M : GL (Fin n) K := g * (t : GL (Fin n) K)⁻¹
  have hdiag_inv : (Matrix.diagonal e)⁻¹ = Matrix.diagonal (fun i => (e i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => e i * (e i)⁻¹) = (fun _ => 1) from
      funext (fun i => mul_inv_cancel₀ (p9uUOdd_ne_zero_of_pow_three (he3 i))),
      Matrix.diagonal_one]
  have hMmat : (M : Matrix (Fin n) (Fin n) K) = Matrix.diagonal δf := by
    have h1 : (M : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) *
          (((t : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹ := by
      rw [show M = g * (t : GL (Fin n) K)⁻¹ from rfl]
      norm_cast
    rw [h1, hgd, htcoemat, hdiag_inv, show δf = (fun i => d i * (e i)⁻¹) from rfl,
      Matrix.diagonal_mul_diagonal]
  have hδa : δf a = 1 := by
    show d a * (e a)⁻¹ = 1
    rw [hea]
    exact mul_inv_cancel₀ (p9uUOdd_ne_zero_of_pow_three (hd3 a))
  have hδb : δf b = 1 := by
    show d b * (e b)⁻¹ = 1
    rw [heb]
    exact mul_inv_cancel₀ (p9uUOdd_ne_zero_of_pow_three (hd3 b))
  have hδc : δf c = 1 := by
    show d c * (e c)⁻¹ = 1
    rw [hec]
    exact mul_inv_cancel₀ (p9uUOdd_ne_zero_of_pow_three (hd3 c))
  have hactβ : p9uUOdd_actBy ψ (β : G) g := p9uUOdd_actBy_of_induces hindg
  have hactti : p9uUOdd_actBy ψ (ψ t)⁻¹ ((t : GL (Fin n) K)⁻¹) := p9uUOdd_actBy_inv_self t
  have hactβ' : p9uUOdd_actBy ψ β' M := p9uUOdd_actBy_mul hactβ hactti
  have key : ∀ {x y : Fin n} (hxy : x ≠ y)
      (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c) {r : MulAut ↥Bs}
      (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
        ψ (ggPermSU (Equiv.swap x y)) * (s : G) * (ψ (ggPermSU (Equiv.swap x y)))⁻¹),
      r B' = B' := by
    intro x y hxy hx hy r hr
    have hδxy : δf x = δf y := by
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        simp_all [hδa, hδb, hδc]
    let P : Su K 2 1 n := ggPermSU (Equiv.swap x y)
    have hPval : (((P : Su K 2 1 n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (Equiv.swap x y).permMatrix K := rfl
    have hτ : (Equiv.swap x y) * (Equiv.swap x y) = 1 := Equiv.swap_mul_self x y
    have hP2 : P * P = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      apply Units.ext
      rw [Units.val_mul, hPval, ← Matrix.permMatrix_mul, hτ, Matrix.permMatrix_one,
        Units.val_one]
    have hψP2 : ψ P * ψ P = 1 := by rw [← map_mul, hP2, map_one]
    have hr2 : r ^ 2 = 1 := by
      apply MulEquiv.ext
      intro s
      apply Subtype.ext
      change ((r (r s) : ↥Bs) : G) = (s : G)
      have hψPi : (ψ P)⁻¹ = ψ P := by
        calc (ψ P)⁻¹ = (ψ P)⁻¹ * 1 := by rw [mul_one]
          _ = (ψ P)⁻¹ * (ψ P * ψ P) := by rw [hψP2]
          _ = ψ P := by group
      calc ((r (r s) : ↥Bs) : G)
          = ψ P * ((r s : ↥Bs) : G) * (ψ P)⁻¹ := hr (r s)
        _ = ψ P * (ψ P * (s : G) * (ψ P)⁻¹) * (ψ P)⁻¹ := by rw [hr s]
        _ = (ψ P * ψ P) * (s : G) * ((ψ P)⁻¹ * (ψ P)⁻¹) := by group
        _ = 1 * (s : G) * (ψ P * ψ P) := by rw [hψP2, hψPi, hψP2]
        _ = (s : G) := by rw [hψP2]; group
    have hPM : (P : GL (Fin n) K) * M = M * (P : GL (Fin n) K) := by
      apply Units.ext
      show ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K) =
        (M : Matrix (Fin n) (Fin n) K) * ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hPval, hMmat]
      exact (ggNSPosPB2_diag_comm_perm (K := K) (f := 1) x y δf hδxy).symm
    have hPMinv : (P : GL (Fin n) K) * M * (P : GL (Fin n) K)⁻¹ = M := by
      rw [hPM]; group
    have h1 : ((r B' : ↥Bs) : G) = ψ P * (B' : G) * (ψ P)⁻¹ := hr B'
    have hactr : p9uUOdd_actBy ψ ((r B' : ↥Bs) : G) M := by
      rw [h1]
      have hPP : p9uUOdd_actBy ψ (ψ P) ((P : GL (Fin n) K)) := p9uUOdd_actBy_self P
      have hPPi : p9uUOdd_actBy ψ (ψ P)⁻¹ ((P : GL (Fin n) K)⁻¹) :=
        p9uUOdd_actBy_inv_self P
      have h := p9uUOdd_actBy_mul (p9uUOdd_actBy_mul hPP hactβ') hPPi
      rwa [hPMinv] at h
    have hconj := p9uUOdd_conj_eq_of_actBy hactβ' hactr
    let z : ↥Bs := r B' * B'⁻¹
    have hzmem : (z : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
      show ((r B' * B'⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (ψ.range : Set G)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (p9uUOdd_centralizer_of_conj_eq (hBsN B'.2) hconj)
    have hrz : r z = z := by
      apply Subtype.ext
      change ((r z : ↥Bs) : G) = (z : G)
      rw [hr z]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzmem)
        (ψ (ggPermSU (Equiv.swap x y))) ⟨P, rfl⟩
      rw [hcomm]; group
    have hrB : r (r B') = B' := by
      have h := congrArg (fun f : MulAut ↥Bs => f B') hr2
      simpa [pow_two, MulAut.coe_mul] using h
    have hrzz : r z = z⁻¹ := by
      show r (r B' * B'⁻¹) = (r B' * B'⁻¹)⁻¹
      rw [map_mul, map_inv, hrB]
      group
    have hz2 : z ^ 2 = 1 := by
      have hzz : z = z⁻¹ := hrz.symm.trans hrzz
      rw [pow_two]
      nth_rewrite 2 [hzz]
      exact mul_inv_cancel z
    have hzp : z ^ p = 1 := by
      have h := h.bstar.2.1.2 z z.2
      rw [← Subgroup.coe_pow] at h
      exact Subtype.ext h
    have hz1 : z = 1 := by
      have hcop : Nat.gcd 2 p = 1 := Nat.coprime_two_left.mpr (h.prime.odd_of_ne_two h.odd)
      have h3 : z ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨hz2, hzp⟩
      rwa [hcop, pow_one] at h3
    have hzr : r B' * B'⁻¹ = 1 := by
      rw [← show z = r B' * B'⁻¹ from rfl]
      exact hz1
    exact mul_inv_eq_one.mp hzr
  have hB'A : β' ∈ (ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨B', ?_, hB'coe⟩
      show r B' = (MonoidHom.id ↥Bs) B'
      simpa using key hab (Or.inl rfl) (Or.inr (Or.inl rfl)) hr
    · refine Subgroup.mem_map.mpr ⟨B', ?_, hB'coe⟩
      show r' B' = (MonoidHom.id ↥Bs) B'
      simpa using key hbc (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hr'
  have hcβ' : β' * c0 = c0 * β' := (Subgroup.mem_centralizer_iff.mp hcA) β' hB'A
  have hψtL : ψ t ∈ L := by rw [← hrange]; exact ⟨t, rfl⟩
  have hcψt : ψ t * c0 = c0 * ψ t := (Subgroup.mem_centralizer_iff.mp hcL) (ψ t) hψtL
  calc b0 * c0 = (β' * ψ t) * c0 := by
        show (β : G) * c0 = (β' * ψ t) * c0
        rw [show β' = (β : G) * (ψ t)⁻¹ from rfl]; group
    _ = β' * (ψ t * c0) := by group
    _ = β' * (c0 * ψ t) := by rw [hcψt]
    _ = (β' * c0) * ψ t := by group
    _ = (c0 * β') * ψ t := by rw [hcβ']
    _ = c0 * (β' * ψ t) := by group
    _ = c0 * b0 := by
        show c0 * (β' * ψ t) = c0 * (β : G)
        rw [show β' = (β : G) * (ψ t)⁻¹ from rfl]; group

end CFSG.StandardType.QTwo

end
