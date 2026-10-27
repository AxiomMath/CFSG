module

public import CFSG.Quasithin.Vol2.Ch11SecA15S5
public import CFSG.Quasithin.Vol2.Ch11SecBK4K

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open CFSG.Quasithin.Vol2.KGNat (spJ)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem iterate_eq_of_pow [IsMulCommutative ↥V] {D : FFModel} {M : Type} [AddCommGroup M]
    [Module K M] {LM : KGNat.LinModel D K M} {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V}
    {π : D.Gam →* ↥H} {f : ↥V → M} (hf : KGNat.IsCoord LM H Z π f) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) {T : M →+ M}
    (hT : ∀ w, f (SecA.conjV V x hxV w) = T (f w)) {p : ℕ}
    (hxp : x ^ p ∈ Subgroup.centralizer (V : Set G)) : ∀ y, T^[p] y = y := by
  have hk : ∀ (k : ℕ) (w : ↥V), f ((SecA.conjV V x hxV ^ k) w) = T^[k] (f w) := by
    intro k
    induction k with
    | zero => intro w; rfl
    | succ k ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, hT, ih, Function.iterate_succ_apply']
  intro y
  obtain ⟨w, rfl⟩ := hf.surj y
  rw [← hk, ← SecA.conjV_pow, conjV_eq_one_of_mem _ hxp, MulAut.one_apply]

theorem card_fix_cube_of_odd {M : Type} [AddCommGroup M] [Module K M] [Finite M]
    (T : M →+ M) (σ : K →+* K) (hσ : ∀ (c : K) (y : M), T (c • y) = σ c • T y) {p : ℕ}
    (hp2 : Odd p) (hTp : ∀ y, T^[p] y = y) {y₀ : M} (hy₀ : y₀ ≠ 0) (hσ1 : ∃ θ, σ θ ≠ θ) :
    Nat.card {z : M // T z = z} ^ 3 ≤ Nat.card M := by
  obtain ⟨θ, h1, h2⟩ := exists_sigma_sq_ne T σ hσ hp2 hTp hy₀ hσ1
  exact card_fix_cube_le T σ hσ h1 h2

theorem det_eq_one_add (A : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K)
    (ℓ : (Fin 3 → K) →ₗ[K] K) (hA : ∀ y, A *ᵥ y - y = ℓ (A *ᵥ y - y) • v) :
    A.det = 1 + ℓ (A *ᵥ v - v) := by
  set φ : Fin 3 → K := fun j => ℓ (A *ᵥ Pi.single j 1 - Pi.single j 1) with hφ
  have hAeq : A = 1 + replicateCol (Fin 1) v * replicateRow (Fin 1) φ := by
    ext i j
    have h1 := congrFun (hA (Pi.single j 1)) i
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at h1
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, hφ,
      Matrix.mulVec_single_one]
    have h2 : (1 : Matrix (Fin 3) (Fin 3) K) i j = (Pi.single j (1 : K) : Fin 3 → K) i := by
      rw [Matrix.one_apply, Pi.single_apply]
    rw [h2, mul_comm (v i)]
    have h3 : A.col j i = A i j := rfl
    rw [h3] at h1
    linear_combination h1
  have hlin : φ ⬝ᵥ v = ℓ (A *ᵥ v - v) := by
    have hv : v = ∑ j, v j • Pi.single j 1 := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    conv_rhs => rw [hv]
    rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib, map_sum, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, ← smul_sub, map_smul, smul_eq_mul, mul_comm]
  calc A.det = (1 + replicateCol (Fin 1) v * replicateRow (Fin 1) φ).det := by rw [← hAeq]
    _ = 1 + φ ⬝ᵥ v := Matrix.det_one_add_replicateCol_mul_replicateRow v φ
    _ = 1 + ℓ (A *ᵥ v - v) := by rw [hlin]

omit [Field K] in
theorem dvd_card_sub_one {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) {μ : K}
    (hμ1 : μ ≠ 1) (hμp : μ ^ p = 1) : p ∣ Nat.card K - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hμp
    exact zero_ne_one hμp
  set u : Kˣ := Units.mk0 μ hμ0 with hu
  have hu1 : u ≠ 1 := fun h => hμ1 (by simpa [hu] using congrArg Units.val h)
  have hup : u ^ p = 1 := Units.ext (by simpa [hu] using hμp)
  rw [← Nat.card_units, ← orderOf_eq_prime hup hu1]
  exact orderOf_dvd_natCard u

theorem oddCodim_sl3 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2]
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSL 3 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hxp : x ^ p ∈ Subgroup.centralizer (V : Set G))
    (hdiag : p ∣ 2 ^ n - 1 → x ∈ L ⊔ Subgroup.centralizer (V : Set G)) :
    2 * n ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨T, σ, hσ, hT⟩ := exists_semilinear_conjV hf
    (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT) (x₀ := ![1, 0, 0])
    (fun h => one_ne_zero (congrFun h 0)) hxV hxL
  have hTp := iterate_eq_of_pow hf hxV hT hxp
  obtain ⟨y₀, hy₀⟩ : ∃ y, T y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx1 (mem_centralizer_of_sl3 hLV hVL hf hxV hxL fun v => by rw [hT, h])
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (map_zero T)
  have hM := card_fun_three hK
  have hbound : Nat.card {z : Fin 3 → K // T z = z} ≤ 2 ^ n := by
    by_cases hσ1 : ∃ θ, σ θ ≠ θ
    · have h1 := card_fix_cube_of_odd T σ hσ hpodd hTp hy₀0 hσ1
      rw [hM, show 3 * n = n * 3 by ring, pow_mul] at h1
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
    simp only [not_exists, ne_eq, not_not] at hσ1
    by_contra hgt
    rw [not_le] at hgt
    let TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
      { toFun := T
        map_add' := map_add T
        map_smul' := fun c z => by rw [hσ, hσ1]; rfl }
    have hTL : ∀ z, TL z = T z := fun z => rfl
    have hker : ∀ z, z ∈ LinearMap.ker (TL - LinearMap.id) ↔ T z = z := fun z => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hTL]
    have hcardk : Nat.card {z : Fin 3 → K // T z = z} =
        Nat.card (LinearMap.ker (TL - LinearMap.id)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun z => (hker z).symm)
    have hq2 : Nat.card K ^ 2 ≤ Nat.card (LinearMap.ker (TL - LinearMap.id)) := by
      have hq : 1 < Nat.card K := Finite.one_lt_card
      have hfin : Nat.card (LinearMap.ker (TL - LinearMap.id)) =
          Nat.card K ^ Module.finrank K (LinearMap.ker (TL - LinearMap.id)) :=
        Module.natCard_eq_pow_finrank
      rw [hcardk, hfin, ← hK] at hgt
      rw [hfin]
      have : 1 < Module.finrank K (LinearMap.ker (TL - LinearMap.id)) := by
        by_contra hle
        rw [not_lt] at hle
        have := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq) hle
        rw [pow_one] at this
        omega
      exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq) this
    obtain ⟨v, hv0, hrange⟩ := KGNat.exists_span_eq_range_sub TL ⟨y₀, hy₀⟩ hq2
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hv0 (funext h)
    set ℓ : (Fin 3 → K) →ₗ[K] K := (v i)⁻¹ • LinearMap.proj i with hℓ
    have hℓv : ℓ v = 1 := by
      simp [hℓ, inv_mul_cancel₀ hi]
    have hdecomp : ∀ z, T z - z = ℓ (T z - z) • v := by
      intro z
      have hmem : T z - z ∈ LinearMap.range (TL - LinearMap.id) := ⟨z, by
        rw [LinearMap.sub_apply, LinearMap.id_apply, hTL]⟩
      rw [hrange, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      rw [← hc, map_smul, hℓv, smul_eq_mul, mul_one]
    set μ := 1 + ℓ (T v - v) with hμ
    have hTv : T v = μ • v := by
      have := hdecomp v
      rw [hμ, add_smul, one_smul, ← this]
      abel
    by_cases hμ1 : μ = 1
    ·
      have hTT : ∀ z, T (T z) = z := by
        intro z
        have e1 := hdecomp z
        set c := ℓ (T z - z) with hc
        have e2 : T z = z + c • v := by rw [← e1]; abel
        rw [e2, map_add, hσ, hσ1, hTv, hμ1, one_smul, e2, add_assoc, ← add_smul,
          CharTwo.add_self_eq_zero, zero_smul, add_zero]
      exact hy₀ (eq_id_of_iterate_two T hpodd hTp hTT y₀)
    ·
      have hiter : ∀ k : ℕ, T^[k] v = μ ^ k • v := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Function.iterate_succ_apply', ih, hσ, hσ1, hTv, smul_smul, pow_succ,
            mul_comm]
      have hμp : μ ^ p = 1 := by
        have h1 := hiter p
        rw [hTp] at h1
        have h3 : (μ ^ p - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)
      have hpq := dvd_card_sub_one hp hμ1 hμp
      rw [hK] at hpq
      obtain ⟨A, hA⟩ := (KGNat.rho3_bijective hf).2
        ⟨SecA.conjV V x hxV, conjV_mem_autOn_of_mem_sup hLV (hdiag hpq) hxV⟩
      have hTA : ∀ z, T z = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ z := by
        intro z
        obtain ⟨w, rfl⟩ := hf.surj z
        rw [← hT, ← hf.act3, hA]
      have hdet := det_eq_one_add (A : Matrix (Fin 3) (Fin 3) K) v ℓ (fun z => by
        rw [← hTA]
        exact hdecomp z)
      rw [A.2, ← hTA, ← hμ] at hdet
      exact hμ1 hdet.symm
  have hC : ∀ w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)), T (f w) = f w :=
    fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]
  have h3 := le_rkIdx_add hV hf hC hM hbound
  omega

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
