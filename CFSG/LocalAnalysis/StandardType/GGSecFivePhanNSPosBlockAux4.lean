module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPB2_map_mem_hyperplane {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {p : ℕ} {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) (hab : a ≠ b)
    (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    {t : Su K 2 f n} {d : Fin n → K}
    (htd : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hdp : ∀ k, d k ^ p = 1) (hda : d a = d b) :
    ψ t ∈ ggHyperplane Bs r := by
  have hBs : ψ t ∈ Bs := ggNSDiag_torus_le h hd t ⟨d, htd, hdp⟩
  rw [ggHyperplane]
  refine Subgroup.mem_map.mpr ⟨⟨ψ t, hBs⟩, ?_, rfl⟩
  show r ⟨ψ t, hBs⟩ = (MonoidHom.id ↥Bs) ⟨ψ t, hBs⟩
  apply Subtype.ext
  rw [hr ⟨ψ t, hBs⟩]
  have hcomm := ggNSPosPB2_diag_comm_perm_GL (K := K) (f := f) a b htd hda
  have hconj : ggPermSU (Equiv.swap a b) * t * (ggPermSU (Equiv.swap a b))⁻¹ = t := by
    rw [hcomm]; group
  have h2 : ψ (ggPermSU (Equiv.swap a b) * t * (ggPermSU (Equiv.swap a b))⁻¹) = ψ t := by
    rw [hconj]
  rw [map_mul, map_mul, map_inv] at h2
  simpa using h2

theorem ggNSPosPB2_comm_of_centralizer {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {G : Type} [Group G] [Finite G] {ψ : Su K 2 f n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {p : ℕ}
    {t x : Su K 2 f n} (htp : t ^ p = 1) (hyt : ψ x * ψ t = ψ t * ψ x) {k : ℕ}
    (hcop : Nat.Coprime p (2 ^ k)) (hx2 : x ^ (2 ^ k) ∈ Subgroup.center (Su K 2 f n)) :
    x * t = t * x := by
  set z : Su K 2 f n := x * t * x⁻¹ * t⁻¹ with hz
  have hzker : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hz]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyt]
    group
  have hzcen : z ∈ Subgroup.center (Su K 2 f n) := hker hzker
  have hxt : x * t * x⁻¹ = z * t := by rw [hz]; group
  have hzct : Commute z t := (Subgroup.mem_center_iff.mp hzcen t).symm
  have hzp : z ^ p = 1 := by
    have h1 : (x * t * x⁻¹) ^ p = 1 := by
      rw [conj_pow, htp, mul_one, mul_inv_cancel]
    rw [hxt, hzct.mul_pow, htp, mul_one] at h1
    exact h1
  have hpow : ∀ m : ℕ, x ^ m * t * (x ^ m)⁻¹ = z ^ m * t := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      have hstep : x ^ (m + 1) * t * (x ^ (m + 1))⁻¹ =
          x * (x ^ m * t * (x ^ m)⁻¹) * x⁻¹ := by
        rw [pow_succ']; group
      rw [hstep, ih]
      have hzc : z ^ m ∈ Subgroup.center (Su K 2 f n) :=
        (Subgroup.center (Su K 2 f n)).pow_mem hzcen m
      have hc := Subgroup.mem_center_iff.mp hzc x
      calc x * (z ^ m * t) * x⁻¹ = (x * z ^ m) * t * x⁻¹ := by group
        _ = (z ^ m * x) * t * x⁻¹ := by rw [hc]
        _ = z ^ m * (x * t * x⁻¹) := by group
        _ = z ^ m * (z * t) := by rw [hxt]
        _ = z ^ (m + 1) * t := by rw [pow_succ]; group
  have hz2k : z ^ (2 ^ k) = 1 := by
    have hcomm2 : x ^ (2 ^ k) * t = t * x ^ (2 ^ k) :=
      (Subgroup.mem_center_iff.mp hx2 t).symm
    have h1 : x ^ (2 ^ k) * t * (x ^ (2 ^ k))⁻¹ = t := by rw [hcomm2]; group
    have h2 := hpow (2 ^ k)
    rw [h1] at h2
    exact mul_right_cancel (h2.symm.trans (one_mul t).symm)
  have hz1 : z = 1 := by
    have h3 := pow_gcd_eq_one.mpr ⟨hzp, hz2k⟩
    rwa [hcop.gcd_eq_one, pow_one] at h3
  have hxt2 : x * t * x⁻¹ = t := by
    have := congrArg (fun w => w * t) hz1
    simpa [hz, mul_assoc] using this
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [hxt2]

theorem ggNSPosPB2_entry_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {t x : Su K 2 f n} {d : Fin n → K} {i j : Fin n}
    (htd : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hdij : d i ≠ d j) (hxt : x * t = t * x) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
  have h1 : (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j =
      (((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j := by
    have := congrArg (fun w : Su K 2 f n => (((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
      hxt
    simpa only [Subgroup.coe_mul, Units.val_mul] using congrFun (congrFun this i) j
  rw [htd, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (d i)] at h1
  have h2 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * (d j - d i) = 0 := by
    rw [mul_sub, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr (Ne.symm hdij))

theorem ggNSPosPB2_pow_apply {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {a b : Fin n}
    {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, i ≠ j → ¬ (i = a ∧ j = b) → ¬ (i = b ∧ j = a) → M i j = 0) :
    ∀ m : ℕ,
      (∀ i j, i ≠ j → ¬ (i = a ∧ j = b) → ¬ (i = b ∧ j = a) → (M ^ m) i j = 0) ∧
      (∀ i, i ≠ a → i ≠ b → (M ^ m) i i = (M i i) ^ m) := by
  intro m; induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro i j hij _ _; simpa [Matrix.one_apply] using hij
    · intro i _ _; simp
  | succ m ih =>
    obtain ⟨ihoff, ihdiag⟩ := ih
    refine ⟨?_, ?_⟩
    · intro i j hij h1 h2
      rw [pow_succ, Matrix.mul_apply]
      by_cases hi : i = a ∨ i = b
      · have hj : j ≠ a ∧ j ≠ b := by
          constructor
          · intro h; rcases hi with hi | hi
            · exact hij (hi.trans h.symm)
            · exact h2 ⟨hi, h⟩
          · intro h; rcases hi with hi | hi
            · exact h1 ⟨hi, h⟩
            · exact hij (hi.trans h.symm)
        have hzero : ∀ k, k ≠ j → M k j = 0 := by
          intro k hk
          refine hM k j hk ?_ ?_
          · intro hh; exact hj.2 hh.2
          · intro hh; exact hj.1 hh.2
        rw [Finset.sum_eq_single j]
        · rw [ihoff i j hij h1 h2, zero_mul]
        · intro k _ hk; rw [hzero k hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      · push Not at hi
        have hzero : ∀ k, k ≠ i → (M ^ m) i k = 0 := by
          intro k hk
          refine ihoff i k (Ne.symm hk) ?_ ?_
          · intro hh; exact hi.1 hh.1
          · intro hh; exact hi.2 hh.1
        rw [Finset.sum_eq_single i]
        · rw [ihdiag i hi.1 hi.2, hM i j hij h1 h2, mul_zero]
        · intro k _ hk; rw [hzero k hk, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
    · intro i hia hib
      rw [pow_succ, Matrix.mul_apply]
      have hzero : ∀ k, k ≠ i → (M ^ m) i k = 0 := by
        intro k hk
        refine ihoff i k (Ne.symm hk) ?_ ?_
        · intro hh; exact hia hh.1
        · intro hh; exact hib hh.1
      rw [Finset.sum_eq_single i]
      · rw [ihdiag i hia hib, pow_succ]
      · intro k _ hk; rw [hzero k hk, zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h

theorem ggNSPosPB2_pow_mem_block {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {a b : Fin n} {x : Su K 2 f n}
    (hoff : ∀ i j, i ≠ j → ¬ (i = a ∧ j = b) → ¬ (i = b ∧ j = a) →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0)
    (hdiag : ∀ c, c ≠ a → c ≠ b →
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c) ^ (2 ^ f + 1) = 1) :
    x ^ (2 ^ f + 1) ∈ ggSuPairBlock K 2 f n a b := by
  intro i j hij
  obtain ⟨hp_off, hp_diag⟩ := ggNSPosPB2_pow_apply (K := K) (a := a) (b := b)
    (M := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hoff (2 ^ f + 1)
  have hcoe : (((x ^ (2 ^ f + 1) : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ (2 ^ f + 1)) := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  rw [hcoe, Matrix.one_apply]
  have h1 : ¬ (i = a ∧ j = b) := by
    rintro ⟨hia, hjb⟩
    rcases hij with ⟨hi, _⟩ | ⟨_, hj⟩
    · exact hi hia
    · exact hj hjb
  have h2 : ¬ (i = b ∧ j = a) := by
    rintro ⟨hib, hja⟩
    rcases hij with ⟨_, hib'⟩ | ⟨hja', _⟩
    · exact hib' hib
    · exact hja' hja
  by_cases hij' : i = j
  · subst hij'
    rw [if_pos rfl]
    have hiab : i ≠ a ∧ i ≠ b := by
      rcases hij with h | h
      · exact h
      · exact h
    rw [hp_diag i hiab.1 hiab.2, hdiag i hiab.1 hiab.2]
  · rw [if_neg hij', hp_off i j hij' h1 h2]

theorem ggNSPosPB2_pow_eq_one_of_diag {K : Type} [Field K] [Finite K] [CharP K 2] {f n p : ℕ}
    {t : Su K 2 f n} {d : Fin n → K}
    (htd : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hdp : ∀ k, d k ^ p = 1) : t ^ p = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, htd, Matrix.diagonal_pow,
    show (d ^ p) = fun _ => 1 from funext hdp, Matrix.diagonal_one]
  rfl

theorem ggNSPosPB2_twoElt_mem_map {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {p : ℕ} {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (a b : Fin n) (hab : a ≠ b) (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    {y : G} (hy : y ∈ ψ.range ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))
    {k : ℕ} (hyk : y ^ (2 ^ k) = 1) :
    y ∈ (ggSuPairBlock K 2 f n a b).map ψ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hyR
  have hx2 : x ^ (2 ^ k) ∈ Subgroup.center (Su K 2 f n) :=
    h.ker (by rw [MonoidHom.mem_ker, map_pow, hyk])
  have hcop : Nat.Coprime p (2 ^ k) :=
    (h.prime.coprime_iff_not_dvd).mpr fun hdvd =>
      h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
        (h.prime.dvd_of_dvd_pow hdvd))
  have hoff : ∀ i j, i ≠ j → ¬ (i = a ∧ j = b) → ¬ (i = b ∧ j = a) →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij h1 h2
    obtain ⟨t, d, htd, hdp, hda, hdij⟩ :=
      ggNSPosPB2_exists_sep (K := K) (f := f) (n := n) h.odd h.dvd h.card h.four_le
        hab hij ⟨h1, h2⟩
    have htHyp : ψ t ∈ ggHyperplane Bs r :=
      ggNSPosPB2_map_mem_hyperplane h hd a b hab r hr htd hdp hda
    have hyt : ψ x * ψ t = ψ t * ψ x :=
      (Subgroup.mem_centralizer_iff.mp hyC (ψ t) htHyp).symm
    have htp : t ^ p = 1 := ggNSPosPB2_pow_eq_one_of_diag htd hdp
    have hxt := ggNSPosPB2_comm_of_centralizer (k := k) h.ker htp hyt hcop hx2
    exact ggNSPosPB2_entry_eq_zero htd hdij hxt
  have hdiag : ∀ c, c ≠ a → c ≠ b →
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c) ^ (2 ^ f + 1) = 1 := by
    intro c hca hcb
    have hconj := ((mem_SUid (σ := unitaryInvolution K 2 f)).mp x.2).2
    have h := congrFun (congrFun hconj c) c
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single c] at h
    · rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, unitaryInvolution_apply] at h
      rw [pow_succ]
      exact h
    · intro m _ hm
      rw [hoff m c hm (fun hh => hcb hh.2) (fun hh => hca hh.2), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ c) h'
  have hyq : (ψ x) ^ (2 ^ f + 1) ∈ (ggSuPairBlock K 2 f n a b).map ψ :=
    ⟨x ^ (2 ^ f + 1), ggNSPosPB2_pow_mem_block hoff hdiag, map_pow ψ x (2 ^ f + 1)⟩
  have hf1 : 1 ≤ f := by
    by_contra hf
    push Not at hf
    have hf0 : f = 0 := by omega
    subst hf0
    have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (by simpa using h.dvd)
    exact h.odd hp2'
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop2 : Nat.Coprime (2 ^ f + 1) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd).pow_right k
  have hbez : ((2 ^ f + 1 : ℕ) : ℤ) * Nat.gcdA (2 ^ f + 1) (2 ^ k) +
      ((2 ^ k : ℕ) : ℤ) * Nat.gcdB (2 ^ f + 1) (2 ^ k) = 1 := by
    have hh := Nat.gcd_eq_gcd_ab (2 ^ f + 1) (2 ^ k)
    rw [hcop2.gcd_eq_one] at hh
    exact_mod_cast hh.symm
  have hy' : (ψ x ^ (2 ^ f + 1)) ^ (Nat.gcdA (2 ^ f + 1) (2 ^ k)) *
        (ψ x ^ (2 ^ k)) ^ (Nat.gcdB (2 ^ f + 1) (2 ^ k)) = ψ x := by
    rw [← zpow_natCast (ψ x) (2 ^ f + 1), ← zpow_natCast (ψ x) (2 ^ k), ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_add, hbez, zpow_one]
  rw [← hy']
  exact mul_mem (zpow_mem hyq _) (by rw [hyk, _root_.one_zpow]; exact one_mem _)

end CFSG.StandardType

end
