module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_pow_mul_mem {K : Subgroup G} {k u : G} (hk : k ∈ K)
    (hu : ∀ j : ℕ, u ^ j * k * (u ^ j)⁻¹ ∈ K) (hu' : ∀ j : ℕ, ∀ y ∈ K, u ^ j * y * (u ^ j)⁻¹ ∈ K) (n : ℕ) :
    ∃ κ ∈ K, (k * u) ^ n = κ * u ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨κ, hκ, hn⟩ := ih
    refine ⟨κ * (u ^ n * k * (u ^ n)⁻¹), K.mul_mem hκ (hu n), ?_⟩
    rw [pow_succ, hn, pow_succ]
    group

theorem uc22p22r_mem_of_two_power {K X : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hXK : X ≤ normalizer (K : Set G)) (hXq : ∀ u ∈ X, u ^ q = 1) {k u t : G} (hk : k ∈ K) (hu : u ∈ X)
    (htku : t = k * u) (ht : ∃ a : ℕ, t ^ 2 ^ a = 1) : t ∈ K := by
  obtain ⟨a, ha⟩ := ht
  have hnorm : ∀ j : ℕ, ∀ y ∈ K, u ^ j * y * (u ^ j)⁻¹ ∈ K := by
    intro j y hy
    have hj : u ^ j ∈ normalizer (K : Set G) := Subgroup.pow_mem _ (hXK hu) j
    exact (Subgroup.mem_normalizer_iff.1 hj y).1 hy
  obtain ⟨κ, hκ, hpow⟩ := uc22p22r_pow_mul_mem (K := K) (k := k) (u := u) hk (fun j => hnorm j k hk) hnorm (2 ^ a)
  have hu2 : u ^ 2 ^ a ∈ K := by
    have h1 : κ * u ^ 2 ^ a = 1 := by rw [← hpow, ← htku, ha]
    have h2 : u ^ 2 ^ a = κ⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact K.inv_mem hκ
  have hcop : Nat.Coprime q (2 ^ a) := by
    refine Nat.Coprime.pow_right a ?_
    exact (Nat.coprime_primes hq Nat.prime_two).2 hq2
  obtain ⟨r, s, hrs⟩ : ∃ r s : ℤ, (q : ℤ) * r + (2 ^ a : ℕ) * s = 1 := by
    have := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨r, s, h⟩ := this
    exact ⟨r, s, by simpa [mul_comm] using h⟩
  have hu1 : u = (u ^ 2 ^ a) ^ s := by
    have hq1 : u ^ (q : ℤ) = 1 := by simpa using hXq u hu
    calc u = u ^ ((q : ℤ) * r + (2 ^ a : ℕ) * s) := by rw [hrs, zpow_one]
      _ = (u ^ (q : ℤ)) ^ r * (u ^ ((2 ^ a : ℕ) : ℤ)) ^ s := by
        rw [zpow_add, zpow_mul, zpow_mul]
      _ = (u ^ 2 ^ a) ^ s := by rw [hq1, one_zpow, one_mul, zpow_natCast]
  have huK : u ∈ K := by
    rw [hu1]
    exact K.zpow_mem hu2 s
  rw [htku]
  exact K.mul_mem hk huK

theorem uc22p22r_permutes_inf {K X T : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hXq : ∀ u ∈ X, u ^ q = 1) (hXK : X ≤ normalizer (K : Set G)) (hT : IsPGroup 2 T)
    (hXT : Permutes X T) : Permutes X (T ⊓ K) := by
  unfold Permutes at hXT ⊢
  have h2 : ∀ t ∈ T, ∃ a : ℕ, t ^ 2 ^ a = 1 := by
    intro t ht
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  ext z
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    have hmem : x * t ∈ (T : Set G) * (X : Set G) := by
      rw [← hXT]
      exact ⟨x, hx, t, ht.1, rfl⟩
    obtain ⟨t', ht', x', hx', hxt⟩ := hmem
    have hk : x * t * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hXK hx) t).1 ht.2
    have hu : x * x'⁻¹ ∈ X := X.mul_mem hx (X.inv_mem hx')
    have htku : t' = (x * t * x⁻¹) * (x * x'⁻¹) := by
      have : t' = x * t * x'⁻¹ := by rw [← hxt]; group
      rw [this]
      group
    have ht'K := uc22p22r_mem_of_two_power hq hq2 hXK hXq hk hu htku (h2 t' ht')
    exact ⟨t', ⟨ht', ht'K⟩, x', hx', hxt⟩
  · rintro ⟨t, ht, x, hx, rfl⟩
    have hmem : t * x ∈ (X : Set G) * (T : Set G) := by
      rw [hXT]
      exact ⟨t, ht.1, x, hx, rfl⟩
    obtain ⟨x', hx', t', ht', hxt⟩ := hmem
    have hk : x'⁻¹ * t * x' ∈ K := by
      have h := (Subgroup.mem_normalizer_iff.1 (hXK (X.inv_mem hx')) t).1 ht.2
      simpa using h
    have hu : x'⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hx') hx
    have htku : t' = (x'⁻¹ * t * x') * (x'⁻¹ * x) := by
      have : t' = x'⁻¹ * (t * x) := by rw [← hxt]; group
      rw [this]
      group
    have ht'K := uc22p22r_mem_of_two_power hq hq2 hXK hXq hk hu htku (h2 t' ht')
    exact ⟨x', hx', t', ⟨ht', ht'K⟩, hxt⟩

theorem uc22p22r_exists_fixed_rcoset {x g : G} {O : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hx : x ^ q = 1) (hO : IsPGroup 2 O) (hxO : ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    (hg : x * g * x⁻¹ * g⁻¹ ∈ O) : ∃ o ∈ O, x * (o * g) * x⁻¹ = o * g := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let S : Set G := {s | s * g⁻¹ ∈ O}
  have hSx : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro s hs
    show x * s * x⁻¹ * g⁻¹ ∈ O
    have h1 : x * (s * g⁻¹) * x⁻¹ ∈ O := hxO _ hs
    have : x * s * x⁻¹ * g⁻¹ = (x * (s * g⁻¹) * x⁻¹) * (x * g * x⁻¹ * g⁻¹) := by group
    rw [this]
    exact O.mul_mem h1 hg
  have hSpow : ∀ n : ℕ, ∀ s ∈ S, x ^ n * s * (x ^ n)⁻¹ ∈ S := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      have h := hSx _ (ih s hs)
      have e : x ^ (n + 1) * s * (x ^ (n + 1))⁻¹ = x * (x ^ n * s * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact h
  have hxinv : x⁻¹ = x ^ (q - 1) := by
    have hq1 : 1 ≤ q := hq.one_lt.le
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hq1, hx]
  have hSinv : ∀ s ∈ S, x⁻¹ * s * x ∈ S := by
    intro s hs
    have h := hSpow (q - 1) s hs
    rw [← hxinv, inv_inv] at h
    exact h
  let σ : Equiv.Perm ↥S :=
    { toFun := fun s => ⟨x * (s : G) * x⁻¹, hSx s s.2⟩
      invFun := fun s => ⟨x⁻¹ * (s : G) * x, hSinv s s.2⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc]) }
  have hσpow : ∀ n : ℕ, ∀ s : ↥S, ((σ ^ n) s : G) = x ^ n * (s : G) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [pow_succ, Equiv.Perm.mul_apply]
      have h := ih (σ s)
      show (((σ ^ n) (σ s) : ↥S) : G) = _
      rw [h]
      show x ^ n * (x * (s : G) * x⁻¹) * (x ^ n)⁻¹ = _
      rw [pow_succ']
      group
  have hσ : σ ^ q ^ 1 = 1 := by
    rw [pow_one]
    ext s
    rw [hσpow, hx]
    simp
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hcard : Fintype.card ↥S = Nat.card ↥O := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun s => ⟨(s : G) * g⁻¹, s.2⟩
        invFun := fun o => ⟨(o : G) * g, by
          show (o : G) * g * g⁻¹ ∈ O
          simp⟩
        left_inv := fun s => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hndvd : ¬ q ∣ Fintype.card ↥S := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hO.exists_card_eq
    rw [hk]
    intro hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := q) (n := 1) hndvd hσ
  have hs' : x * (s : G) * x⁻¹ = (s : G) := congrArg Subtype.val hs
  refine ⟨(s : G) * g⁻¹, s.2, ?_⟩
  have e : (s : G) * g⁻¹ * g = (s : G) := by group
  rw [e]
  exact hs'

theorem uc22p22r_le_of_trivial_action {K M : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hx : x ^ q = 1) (hxK : x ∈ normalizer (K : Set G))
    (htriv : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    (hC : ∀ k ∈ K, x * k * x⁻¹ = k → k ∈ M) (hO : pCoreOf 2 K ≤ M) : K ≤ M := by
  intro g hg
  have hxK' : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.1 hxK k).1 hk
  have hxK'' : ∀ k ∈ K, x⁻¹ * k * x ∈ K := by
    intro k hk
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxK) k).1 hk
    simpa using h
  have hxO : ∀ o ∈ pCoreOf 2 K, x * o * x⁻¹ ∈ pCoreOf 2 K := by
    have hn := uc22p22f_mem_normalizer_pCoreOf (K := K) (n := x) hxK' hxK''
    intro o ho
    exact (Subgroup.mem_normalizer_iff.1 hn o).1 ho
  obtain ⟨o, ho, hfix⟩ := uc22p22r_exists_fixed_rcoset hq hq2 hx (uc22p22f_isPGroup_pCoreOf K) hxO
    (htriv g hg)
  have hoK : o ∈ K := Subgroup.map_subtype_le _ ho
  have hog : o * g ∈ M := hC (o * g) (K.mul_mem hoK hg) hfix
  have e : g = o⁻¹ * (o * g) := by group
  rw [e]
  exact M.mul_mem (M.inv_mem (hO ho)) hog

end CFSG.LocalAnalysis.UniquenessCase.UC22
