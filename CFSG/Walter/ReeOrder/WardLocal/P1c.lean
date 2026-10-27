module

public import CFSG.Walter.ReeOrder.WardLocal.P1b

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {q : ℕ} (S : WardSetup G PSL(2, K) q (-1))

@[expose] noncomputable def wgen : G := S.J * S.κ (dgen K)

@[expose] noncomputable def WW : Subgroup G := Subgroup.zpowers (wgen S)

variable {S}

theorem wgen_pow (i : ℕ) : wgen S ^ i = S.J ^ i * S.κ (dgen K) ^ i :=
  (Commute.mul_pow (S.κ_comm (dgen K)).symm i)

variable {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
include hq hK

theorem orderOf_κ_dgen : 2 * orderOf (S.κ (dgen K)) + 1 = q := by
  obtain ⟨k', hk', -⟩ := Block.q_half hq
  rw [S.orderOf_κ, orderOf_dgen (hK.trans hk'), hk']

theorem orderOf_wgen : orderOf (wgen S) = q - 1 := by
  have h := orderOf_κ_dgen hq hK (S := S)
  obtain ⟨k', hk', hodd⟩ := Block.q_half hq
  have hk'' : orderOf (S.κ (dgen K)) = k' := by omega
  have hcop : Nat.Coprime (orderOf S.J) (orderOf (S.κ (dgen K))) := by
    rw [S.orderOf_J, hk'']; exact Nat.coprime_two_left.mpr hodd
  have hc : Commute S.J (S.κ (dgen K)) := (S.κ_comm _).symm
  rw [wgen, hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop, S.orderOf_J, hk'']
  omega

theorem card_WW : Nat.card (WW S) = q - 1 := by
  rw [WW, Nat.card_zpowers, orderOf_wgen hq hK]

theorem WW_sq_eq_one {w : G} (hw : w ∈ WW S) (h2 : w ^ 2 = 1) : w = 1 ∨ w = S.J := by
  obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hw)
  simp only at h2 ⊢
  obtain ⟨k', hk', hodd⟩ := Block.q_half hq
  have hord : orderOf (S.κ (dgen K)) = k' := by
    have := orderOf_κ_dgen hq hK (S := S); omega
  rw [← pow_mul, wgen_pow] at h2
  have hJ : S.J ^ (i * 2) = 1 := by rw [pow_mul', sq, S.J_mul, one_pow]
  rw [hJ, one_mul] at h2
  have hk'i : k' ∣ i := by
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_right.mpr hodd) this)
  have hdi : S.κ (dgen K) ^ i = 1 := by
    obtain ⟨t, rfl⟩ := hk'i; rw [pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
  rw [wgen_pow, hdi, mul_one]
  rcases Nat.even_or_odd i with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left; rw [← two_mul, pow_mul, sq, S.J_mul, one_pow]
  · right; rw [pow_succ, pow_mul, sq, S.J_mul, one_pow, one_mul]

variable [CharP K 3] (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))

omit hK [CharP K 3] in
include hcT in
theorem J_mem_normalizer_PP1 : S.J ∈ Subgroup.normalizer (PP1 S : Set G) := by
  have hconj : ∀ x ∈ PP1 S, S.J * x * S.J⁻¹ ∈ PP1 S := by
    intro x hx
    refine mem_PP1 hq hcT (Subgroup.mul_mem _ (Subgroup.mul_mem _ J_mem_CF (PP1_le_CF hx))
      (Subgroup.inv_mem _ J_mem_CF)) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp isPGroup_PP1) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj x, fun h => ?_⟩
  have := hconj _ h
  rw [S.J_inv] at this
  have e : S.J * (S.J * x * S.J) * S.J = x := by
    calc S.J * (S.J * x * S.J) * S.J = (S.J * S.J) * x * (S.J * S.J) := by group
      _ = x := by rw [S.J_mul, one_mul, mul_one]
  rwa [e] at this

omit hK [CharP K 3] in
include hcT in
theorem WW_le_normalizer_PP1 : WW S ≤ Subgroup.normalizer (PP1 S : Set G) := by
  rw [WW, Subgroup.zpowers_le, wgen]
  exact Subgroup.mul_mem _ (J_mem_normalizer_PP1 hq hcT)
    (RR_le_normalizer_PP1 hq hcT (mem_RR.mpr ⟨1, by rw [pow_one]⟩))

omit [CharP K 3] hq hK in
theorem conj_mem_AA {g x : G} (hg : g ∈ Subgroup.normalizer (PP1 S : Set G)) (hx : x ∈ AA S) :
    g * x * g⁻¹ ∈ AA S := by
  obtain ⟨hxP, hx1, hinv, hc⟩ := mem_AA.mp hx
  refine mem_AA.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxP, ?_, ?_, ?_⟩
  · intro h; apply hx1
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  · intro t ht htx
    apply hinv (g⁻¹ * t * g) (by rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by group,
      ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht])
    calc x * (g⁻¹ * t * g) = g⁻¹ * ((g * x * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [htx]
      _ = g⁻¹ * t * g * x := by group
  · rwa [← card_centralizer_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)]

include hcT hG in
theorem AA_free {w x : G} (hw : w ∈ WW S) (hw1 : w ≠ 1) (hx : x ∈ AA S)
    (hwx : w * x * w⁻¹ = x) : False := by
  obtain ⟨hxP, hx1, hinv, -⟩ := mem_AA.mp hx
  obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hw)
  simp only at hw1 hwx
  have hcomm : wgen S ^ i * x = x * wgen S ^ i := by
    calc wgen S ^ i * x = wgen S ^ i * x * (wgen S ^ i)⁻¹ * wgen S ^ i := by group
      _ = x * wgen S ^ i := by rw [hwx]
  by_cases hd : S.κ (dgen K) ^ (2 * i) = 1
  ·
    have hw2 : (wgen S ^ i) ^ 2 = 1 := by
      rw [← pow_mul, wgen_pow, mul_comm i 2, pow_mul S.J 2 i, sq S.J, S.J_mul, one_pow, one_mul,
        hd]
    rcases WW_sq_eq_one hq hK (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i) hw2 with h | h
    · exact hw1 h
    · rw [h] at hcomm
      exact hinv S.J S.orderOf_J hcomm.symm
  ·
    have hw2 : (wgen S ^ i) ^ 2 = S.κ (dgen K) ^ (2 * i) := by
      rw [← pow_mul, wgen_pow, mul_comm i 2, pow_mul S.J 2 i, sq S.J, S.J_mul, one_pow, one_mul]
    have hmem : S.κ (dgen K) ^ (2 * i) ∈ RR S :=
      mem_RR.mpr ⟨2 * i, by rw [map_pow]⟩
    have hc2 : x * S.κ (dgen K) ^ (2 * i) = S.κ (dgen K) ^ (2 * i) * x := by
      rw [← hw2, sq, ← mul_assoc, ← hcomm, mul_assoc, ← hcomm, mul_assoc]
    have hx3 : orderOf x = 3 :=
      orderOf_eq_prime (PP1_pow_three hq hK hcT hG hxP) hx1
    exact not_three_dvd_of_commute_RR hK hq hmem hd hc2 (by rw [hx3])

omit hq hK [CharP K 3] in
theorem inv_mem_AA {x : G} (hx : x ∈ AA S) : x⁻¹ ∈ AA S := by
  obtain ⟨hxP, hx1, hinv, hc⟩ := mem_AA.mp hx
  refine mem_AA.mpr ⟨Subgroup.inv_mem _ hxP, inv_ne_one.mpr hx1, fun t ht h => ?_, ?_⟩
  · apply hinv t ht
    calc x * t = x * (t * x⁻¹) * x := by group
      _ = x * (x⁻¹ * t) * x := by rw [h]
      _ = t * x := by group
  · rwa [centralizer_inv]

omit [CharP K 3] in
theorem card_WW_finset : (WW S : Set G).toFinset.card = q - 1 := by
  have := card_WW hq hK (S := S)
  rw [Set.toFinset_card, ← this, Nat.card_eq_fintype_card]
  rfl

include hcT hG in
theorem AA_transitive (hA : (AA S).card = q - 1) {x : G} (hx : x ∈ AA S) {y : G}
    (hy : y ∈ AA S) : ∃ w ∈ WW S, w * x * w⁻¹ = y := by
  set img := (WW S : Set G).toFinset.image fun w => w * x * w⁻¹ with himg
  have hsub : img ⊆ AA S := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    rw [Set.mem_toFinset] at hw
    exact conj_mem_AA (WW_le_normalizer_PP1 hq hcT hw) hx
  have hinj : Set.InjOn (fun w => w * x * w⁻¹) ((WW S : Set G).toFinset : Set G) := by
    intro w hw w' hw' h
    simp only [Set.coe_toFinset, SetLike.mem_coe] at hw hw'
    by_contra hne
    apply AA_free hq hK hcT hG (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw') hw)
      (fun h1 => hne (by
        have := congrArg (fun t => w' * t) h1
        simpa using this)) hx
    calc w'⁻¹ * w * x * (w'⁻¹ * w)⁻¹ = w'⁻¹ * (w * x * w⁻¹) * w' := by group
      _ = w'⁻¹ * (w' * x * w'⁻¹) * w' := by rw [show w * x * w⁻¹ = w' * x * w'⁻¹ from h]
      _ = x := by group
  have hcard : img.card = (AA S).card := by
    rw [Finset.card_image_of_injOn hinj, card_WW_finset hq hK, hA]
  have heq : img = AA S := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  rw [← heq] at hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨w, Set.mem_toFinset.mp hw, rfl⟩

include hcT hG in
theorem J_inv_AA (hA : (AA S).card = q - 1) {x : G} (hx : x ∈ AA S) :
    S.J * x * S.J⁻¹ = x⁻¹ := by
  obtain ⟨w, hw, hwx⟩ := AA_transitive hq hK hcT hG hA hx (inv_mem_AA hx)
  have hw2 : (w ^ 2) * x * (w ^ 2)⁻¹ = x := by
    calc w ^ 2 * x * (w ^ 2)⁻¹ = w * (w * x * w⁻¹) * w⁻¹ := by rw [sq]; group
      _ = w * x⁻¹ * w⁻¹ := by rw [hwx]
      _ = (w * x * w⁻¹)⁻¹ := by group
      _ = x := by rw [hwx, inv_inv]
  have hsq : w ^ 2 = 1 := by
    by_contra h
    exact AA_free hq hK hcT hG (Subgroup.pow_mem _ hw 2) h hx hw2
  obtain ⟨hxP, hx1, -, -⟩ := mem_AA.mp hx
  rcases WW_sq_eq_one hq hK hw hsq with rfl | rfl
  · exfalso
    simp only [one_mul, inv_one, mul_one] at hwx
    have hx3 : orderOf x = 3 := orderOf_eq_prime (PP1_pow_three hq hK hcT hG hxP) hx1
    have h2 : x ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hwx]; exact mul_inv_cancel x
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx3] at this; omega
  · exact hwx

namespace Block

variable {D : S.EtaData} {m : ℕ} (B : Block S D m)

omit hcT in
include B hq hK hG in
theorem card_AA : (AA S).card = q - 1 := by
  have hcT := B.hcT hq hK hG
  obtain ⟨n₀, hn₀⟩ := B.count_AA hq hK hG
  have hdvd : Nat.card (WW S) ∣ (AA S).card :=
    card_dvd_card_of_free (WW S) (AA S)
      (fun w hw x hx => conj_mem_AA (WW_le_normalizer_PP1 hq hcT hw) hx)
      (fun w hw hw1 x hx hwx => AA_free hq hK hcT hG hw hw1 hx hwx)
  rw [card_WW hq hK] at hdvd
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  rcases Nat.lt_or_ge n₀ 2 with h | h
  · interval_cases n₀
    · exfalso
      have h1 : (AA S).card = 2 * q - 1 := by omega
      rw [h1] at hdvd
      have h2 : q - 1 ∣ 2 * q - 1 - 2 * (q - 1) := Nat.dvd_sub hdvd (dvd_mul_left _ _)
      rw [show 2 * q - 1 - 2 * (q - 1) = 1 by omega] at h2
      have := Nat.le_of_dvd one_pos h2
      omega
    · omega
  · exfalso
    have : q * 2 ≤ q * n₀ := Nat.mul_le_mul_left q h
    omega

end Block

end CFSG.Walter.WardLocal
