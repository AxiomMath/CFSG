module

public import CFSG.RankThree.PartOne.N143.JAct

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL tSep tNon permSL permSL_inv ent ent_ext
  ent_mul_diagSL ent_diagSL_mul nonreg diagSL_mem_Tor mem_Tor_iff prod_nonreg nonreg_pow)
open scoped commutatorElement

section Matrices

variable {K : Type} [Field K] {p : ℕ} {ζ : Kˣ}

theorem Zc_mul_diagSL_comm (hζ : IsZeta p ζ) {x : SL3 K} (hx : x ∈ Zc (K := K) ζ)
    {v : Fin 3 → Kˣ} (hv : ∏ i, v i = 1) (h01 : v 0 = v 1) :
    x * diagSL v hv = diagSL v hv * x := by
  obtain ⟨h02, h12, h20, h21⟩ := (mem_Zc_iff hζ).1 hx
  apply ent_ext
  intro a b
  rw [ent_mul_diagSL, ent_diagSL_mul]
  fin_cases a <;> fin_cases b <;> simp [h02, h12, h20, h21, h01, mul_comm]

theorem diagSL_mem_Zc (hζ : IsZeta p ζ) (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) :
    diagSL v hv ∈ Zc (K := K) ζ := by
  rw [mem_Zc_iff hζ]
  simp [KFOUT3.diagSL_apply]

theorem ent_diagSL_two_two (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) :
    ent (diagSL v hv) 2 2 = (v 2 : K) := by
  simp [KFOUT3.diagSL_apply]

theorem commutator_diag_mem_blk (hζ : IsZeta p ζ) {m : SL3 K}
    (hσ : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv))
    {v : Fin 3 → Kˣ} (hv : ∏ i, v i = 1) (hv1 : ∀ i, v i ^ p = 1) :
    m * diagSL v hv * m⁻¹ * (diagSL v hv)⁻¹ ∈
      (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range := by
  rw [hσ v hv hv1]
  obtain ⟨D', hD'⟩ : ∃ D' : SL3 K,
      D' = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv) := ⟨_, rfl⟩
  rw [← hD']
  have hD'Zc : D' ∈ Zc (K := K) ζ := by
    rw [hD']
    exact diagSL_mem_Zc hζ _ _
  have hdZc : diagSL v hv ∈ Zc (K := K) ζ := diagSL_mem_Zc hζ v hv
  have hz : D' * (diagSL v hv)⁻¹ ∈ Zc (K := K) ζ :=
    Subgroup.mul_mem _ hD'Zc (Subgroup.inv_mem _ hdZc)
  refine mem_range_blkSL_of_mem_Zc hζ hz ?_
  have h2 : ent (D' * (diagSL v hv)⁻¹ * diagSL v hv) 2 2 = ent D' 2 2 := by
    rw [inv_mul_cancel_right]
  have hD22 : ent D' 2 2 = (v 2 : K) := by
    rw [hD', ent_diagSL_two_two]
    have e : permVec (Equiv.swap (0 : Fin 3) 1) v 2 = v 2 := by simp [permVec, swap01_two]
    rw [e]
  rw [ent_mul_two_two hζ hz, hD22, ent_diagSL_two_two] at h2
  have hne : (v 2 : K) ≠ 0 := (v 2).ne_zero
  exact mul_right_cancel₀ hne (h2.trans (one_mul _).symm)

end Matrices

section Core

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {ρ : SL3 K →* G}

omit [Finite G] [CharP K 2] [Finite K] in
theorem swap_fixed_iff (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {m : SL3 K}
    (hσ : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv))
    {v : Fin 3 → Kˣ} (hv : ∏ i, v i = 1) (hv1 : ∀ i, v i ^ p = 1) :
    ρ (m * diagSL v hv * m⁻¹) = ρ (diagSL v hv) ↔ v 0 = v 1 := by
  constructor
  · intro h
    have hd : diagSL v hv ∈ Tor p K := diagSL_mem_Tor v hv1 hv
    have h1 : m * diagSL v hv * m⁻¹ = diagSL v hv :=
      hρ.eq_of_map_eq hp (by rw [conj_pow, Tor_pow_eq_one hd, mul_one, mul_inv_cancel])
        (Tor_pow_eq_one hd) h
    rw [hσ v hv hv1] at h1
    have h2 : ((permVec (Equiv.swap (0 : Fin 3) 1) v 0 : Kˣ) : K) = (v 0 : K) := by
      have := congrArg (fun y : SL3 K => ent y 0 0) h1
      simpa [KFOUT3.diagSL_apply] using this
    have e : permVec (Equiv.swap (0 : Fin 3) 1) v 0 = v 1 := by simp [permVec]
    rw [e] at h2
    exact (Units.ext h2).symm
  · intro h01
    have hv' : permVec (Equiv.swap (0 : Fin 3) 1) v = v := by
      funext k
      fin_cases k
      · simp [permVec, h01]
      · simp [permVec, h01]
      · simp [permVec, swap01_two]
    rw [hσ v hv hv1]
    exact congrArg ρ (diagSL_congr hv' _ _)

omit [CharP K 2] [Finite K] in
theorem Nt_eq_swap (h : JGood p A c J) (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) {x : G} (hxN : x ∈ Subgroup.normalizer (A : Set G)) {m : SL3 K}
    (hxm : ρ m = x)
    (hσ : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv)) :
    Nt A J (A.normalizerMonoidHom ⟨x, hxN⟩) =
      J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G) := by
  have hpow : (tNon ζ 2 : SL3 K) ^ p = 1 := Tor_pow_eq_one (KFOUT3.tNon_mem hζ 2)
  unfold Nt
  apply le_antisymm
  · apply inf_le_inf_left
    apply Subgroup.centralizer_le
    rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_autFixedInG_normalizerMonoidHom]
    refine ⟨hρ.map_mem_A (KFOUT3.tNon_mem hζ 2), ?_⟩
    rw [← hxm]
    have h01 : nonreg ζ 2 0 = nonreg ζ 2 1 := by rw [nonreg_two_zero, nonreg_two_one]
    have key : ρ (m * tNon ζ 2 * m⁻¹) = ρ (tNon ζ 2) :=
      (swap_fixed_iff hp hρ hσ (prod_nonreg ζ 2) (nonreg_pow hζ.pow 2)).2 h01
    rw [map_mul, map_mul, map_inv] at key
    exact key
  · intro y hy
    refine Subgroup.mem_inf.2 ⟨hy.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [SetLike.mem_coe, mem_autFixedInG_normalizerMonoidHom] at ha
    obtain ⟨haA, hfix⟩ := ha
    obtain ⟨m', hm', rfl⟩ := (hρ.mem_inf_centralizer_single hp hpow).1 hy
    have hm'J : ρ m' ∈ J := hρ.range_eq ▸ ⟨m', rfl⟩
    obtain ⟨i, d, hd, rfl⟩ := hρ.exists_decomp h haA
    rw [← hxm, hρ.conj_decomp h m i d] at hfix
    have hfix' : ρ (m * d * m⁻¹) = ρ d := mul_left_cancel hfix
    obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
    have h01 : v 0 = v 1 := (swap_fixed_iff hp hρ hσ hv hv1).1 hfix'
    have hcomm : m' * diagSL v hv = diagSL v hv * m' :=
      Zc_mul_diagSL_comm hζ hm' hv h01
    have hc : c * ρ m' = ρ m' * c := Sec12Three.comm_c_L h.hyp (ρ m') hm'J
    have hci : c ^ i * ρ m' = ρ m' * c ^ i := (Commute.zpow_left (hc : Commute c (ρ m')) i).eq
    calc c ^ i * ρ (diagSL v hv) * ρ m' = c ^ i * (ρ (diagSL v hv) * ρ m') := by
          simp only [mul_assoc]
      _ = c ^ i * (ρ m' * ρ (diagSL v hv)) := by rw [← map_mul, ← map_mul, ← hcomm]
      _ = (c ^ i * ρ m') * ρ (diagSL v hv) := by simp only [mul_assoc]
      _ = (ρ m' * c ^ i) * ρ (diagSL v hv) := by rw [hci]
      _ = ρ m' * (c ^ i * ρ (diagSL v hv)) := by simp only [mul_assoc]

end Core

section Moved

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {ρ : SL3 K →* G}

omit [Finite K] in
theorem Kof_eq_swap (h : JGood p A c J) (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) (h4 : 4 ≤ Nat.card K) {x : G} (hxN : x ∈ Subgroup.normalizer (A : Set G))
    {m : SL3 K} (hxm : ρ m = x)
    (hσ : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv)) :
    Kof A J (A.normalizerMonoidHom ⟨x, hxN⟩) = (blkφ ρ).range := by
  unfold Kof
  rw [Nt_eq_swap h hp hρ hζ hxN hxm hσ, hρ.commutator_inf_centralizer_tNon hp hζ h4,
    map_blkSL_range_eq]

omit [CharP K 2] [Finite K] in
theorem autMoved_le_swap (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) {x : G} (hxN : x ∈ Subgroup.normalizer (A : Set G)) {m : SL3 K}
    (hxm : ρ m = x) (hmN : m ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)))
    (hσ : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv)) :
    autMovedInG A (A.normalizerMonoidHom ⟨x, hxN⟩) ≤ (blkφ ρ).range := by
  unfold autMovedInG autMoved
  rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨e, rfl⟩
  show x * (e : G) * x⁻¹ * (e : G)⁻¹ ∈ (blkφ ρ).range
  obtain ⟨i, d, hd, he⟩ := hρ.exists_decomp h e.2
  have hP : ρ (m * d * m⁻¹) ∈ A :=
    hρ.map_mem_A ((Subgroup.mem_normalizer_iff.1 hmN d).1 hd)
  have hQ : ρ d ∈ A := hρ.map_mem_A hd
  have hu : c ^ i ∈ A := h.zpow_c_mem i
  have hcomm : c ^ i * (ρ (m * d * m⁻¹) * (ρ d)⁻¹) = (ρ (m * d * m⁻¹) * (ρ d)⁻¹) * c ^ i :=
    h.comm_A hu (A.mul_mem hP (A.inv_mem hQ))
  have e1 : c ^ i * ρ (m * d * m⁻¹) * (c ^ i * ρ d)⁻¹ = ρ (m * d * m⁻¹ * d⁻¹) := by
    rw [map_mul ρ (m * d * m⁻¹) d⁻¹, map_inv]
    calc c ^ i * ρ (m * d * m⁻¹) * (c ^ i * ρ d)⁻¹
        = c ^ i * (ρ (m * d * m⁻¹) * (ρ d)⁻¹) * (c ^ i)⁻¹ := by group
      _ = (ρ (m * d * m⁻¹) * (ρ d)⁻¹) * c ^ i * (c ^ i)⁻¹ := by rw [hcomm]
      _ = ρ (m * d * m⁻¹) * (ρ d)⁻¹ := by rw [mul_inv_cancel_right]
  rw [← hxm, he, hρ.conj_decomp h m i d, e1]
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
  obtain ⟨M, hM⟩ := commutator_diag_mem_blk hζ hσ hv hv1
  exact ⟨M, by rw [blkφ_apply, hM]⟩

end Moved

theorem exists_conj_swap (σ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h3 : σ ^ 3 ≠ 1) :
    ∃ τ : Equiv.Perm (Fin 3), τ⁻¹ * (σ * τ) = Equiv.swap 0 1 := by
  revert σ
  decide

theorem sl2_card (K : Type) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem exists_kt_data (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G}
    (h : JGood p A c J) {t : MulAut A} (ht : t ∈ reflectionSet p A) (htJ : t ∈ torusImage A J)
    {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (ρ' : SL3 K →* G) (ζ : Kˣ) (x : G)
      (hxN : x ∈ Subgroup.normalizer (A : Set G)) (m' : SL3 K),
      Nat.card K = 2 ^ f ∧ IsPSL3Cover p A J ρ' ∧ IsZeta p ζ ∧ ρ' m' = x ∧
      A.normalizerMonoidHom ⟨x, hxN⟩ = t ∧
      m' ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) ∧
      (∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
        m' * diagSL v hv * m'⁻¹ = diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv)) ∧
      Function.Injective (blkφ ρ') ∧ Kof A J t = (blkφ ρ').range ∧
      autMovedInG A t ≤ (blkφ ρ').range := by
  classical
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA h hf hm
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hchar : CharP K 2 := charP_two_of_card hK
  have hf1 : 1 ≤ f := hm.1.2.1
  have hf3 := three_le_of_dvd_pred h5 hf1 hf
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hf)
  obtain ⟨x, hxJ, hxN, rfl⟩ := Sec12Three.mem_torusImage_iff.1 htJ
  obtain ⟨m, hmN, hxm⟩ := (hρ.mem_inf_normalizer_iff hp h).1 ⟨hxJ, hxN⟩
  subst hxm
  obtain ⟨σ, hσ⟩ := exists_perm_conj_Tor hζ hmN
  have hord : orderOf (A.normalizerMonoidHom ⟨ρ m, hxN⟩) = 2 := ht.1.1
  have h2 : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (A.normalizerMonoidHom ⟨ρ m, hxN⟩)
    rwa [hord] at this
  have ht1 : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have ht3 : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ^ 3 ≠ 1 := by
    intro h3
    apply ht1
    have : A.normalizerMonoidHom ⟨ρ m, hxN⟩ ^ 3 = A.normalizerMonoidHom ⟨ρ m, hxN⟩ := by
      rw [pow_succ, h2, one_mul]
    rw [← this]
    exact h3
  have hact : ∀ n : ℕ, σ ^ n = 1 → ∀ a ∈ A, (ρ m) ^ n * a * ((ρ m) ^ n)⁻¹ = a := by
    intro n hn a ha
    obtain ⟨i, d, hd, rfl⟩ := hρ.exists_decomp h ha
    rw [← map_pow, hρ.conj_decomp h (m ^ n) i d]
    obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
    rw [conj_pow_diagSL hσ n v hv hv1]
    have : diagSL (permVec (σ ^ n) v) (prod_permVec (σ ^ n) hv) = diagSL v hv :=
      diagSL_congr (by rw [hn, permVec_one]) _ _
    rw [this]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply ht1
    have := normalizerMonoidHom_pow_eq_one hxN 1 (hact 1 (by rw [pow_one]; exact h1))
    simpa using this
  have hσ3 : σ ^ 3 ≠ 1 := fun h3 => ht3 (normalizerMonoidHom_pow_eq_one hxN 3 (hact 3 h3))
  obtain ⟨τ, hτ⟩ := exists_conj_swap σ hσ1 hσ3
  have hρ' := hρ.conjPerm τ
  have hP : permSL τ ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) := permSL_mem_normalizer_Tor τ
  have hmN' : (permSL τ)⁻¹ * m * permSL τ ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) hmN) hP
  have hxm' : (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom) ((permSL τ)⁻¹ * m * permSL τ) = ρ m := by
    show ρ (permSL τ * ((permSL τ)⁻¹ * m * permSL τ) * (permSL τ)⁻¹) = ρ m
    congr 1
    group
  have hσ' : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      ((permSL τ)⁻¹ * m * permSL τ) * diagSL v hv * ((permSL τ)⁻¹ * m * permSL τ)⁻¹ =
        diagSL (permVec (Equiv.swap 0 1) v) (prod_permVec _ hv) := by
    intro v hv hv1
    have e1 : (permSL τ)⁻¹ * m * permSL τ * diagSL v hv * ((permSL τ)⁻¹ * m * permSL τ)⁻¹ =
        (permSL τ)⁻¹ * (m * (permSL τ * diagSL v hv * (permSL τ)⁻¹) * m⁻¹) * ((permSL τ)⁻¹)⁻¹ := by
      group
    rw [e1, permSL_conj_diagSL τ v hv, hσ (permVec τ v) (prod_permVec τ hv) (fun i => hv1 _),
      permSL_inv]
    rw [permSL_conj_diagSL τ⁻¹]
    exact diagSL_congr (by rw [permVec_permVec, permVec_permVec, mul_assoc, hτ]) _ _
  have hrange := Kof_eq_swap h hp hρ' hζ h4 hxN hxm' hσ'
  have hle := autMoved_le_swap h hρ' hζ hxN hxm' hmN' hσ'
  exact ⟨K, hKf, hKfin, hchar, ρ.comp (MulAut.conj (permSL τ)).toMonoidHom, ζ, ρ m, hxN,
    (permSL τ)⁻¹ * m * permSL τ, hK, hρ', hζ, hxm', rfl, hmN', hσ', blkφ_injective hρ', hrange, hle⟩

theorem jLemmaKt1_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    JLemmaKt1 := by
  intro G _ _ p A c J h t ht htJ f hf hm
  classical
  obtain ⟨K, hKf, hKfin, hchar, ρ', ζ, x, hxN, m', hK, hρ', hζ, hxm', hxt, hmN', hσ', hinj, hrange,
    hle⟩ := exists_kt_data hGA h ht htJ hf hm
  have h5 := Sec12Three.five_le h.hyp
  have hf1 : 1 ≤ f := hm.1.2.1
  have hf3 := three_le_of_dvd_pred h5 hf1 hf
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    KCRootAxis.sl2_isSimpleGroup h4
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* (blkφ ρ').range :=
    MonoidHom.ofInjective hinj
  refine ⟨?_, ?_, ?_⟩
  · rw [hrange]
    exact e.symm.isSimpleGroup
  · rw [hrange, ← Nat.card_congr e.toEquiv, sl2_card, hK, ← pow_mul, mul_comm f 2]
  · rw [hrange]
    exact hle

end CFSG.RankThree.PartOne.N143
