module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Gen

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)

theorem cycleType_of_orderOf_eq_three {σ : alternatingGroup (Fin 7)} (h : orderOf σ = 3) :
    (σ : Equiv.Perm (Fin 7)).cycleType = {3} ∨ (σ : Equiv.Perm (Fin 7)).cycleType = {3, 3} := by
  have h' : orderOf (σ : Equiv.Perm (Fin 7)) = 3 := by rw [Subgroup.orderOf_coe, h]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (h'.symm ▸ Nat.prime_three)
  rw [h'] at hn
  have hsum := Equiv.Perm.sum_cycleType_le (σ : Equiv.Perm (Fin 7))
  rw [hn] at hsum
  simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hn1 : n ≤ 1 := by omega
  interval_cases n
  · left
    rw [hn]
    rfl
  · right
    rw [hn]
    rfl

@[expose] def dthree : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 1 * Equiv.swap 0 2) * (Equiv.swap 3 4 * Equiv.swap 3 5)

theorem cycleType_dthree : dthree.cycleType = {3, 3} := by
  have h1 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2).cycleType = {3} :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h2 : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 3 5).cycleType = {3} :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2)
      (Equiv.swap 3 4 * Equiv.swap 3 5) := by
    intro x
    fin_cases x <;> decide
  rw [dthree, hd.cycleType_mul, h1, h2]
  decide

theorem exists_odd_commute_dthree :
    ∃ τ : Equiv.Perm (Fin 7), Equiv.Perm.sign τ = -1 ∧ τ * dthree * τ⁻¹ = dthree :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5, by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide, by decide⟩

theorem isConj_of_cycleType_eq_A7 {σ τ : alternatingGroup (Fin 7)} (hσ : orderOf σ = 3)
    (hστ : (σ : Equiv.Perm (Fin 7)).cycleType = (τ : Equiv.Perm (Fin 7)).cycleType) :
    IsConj σ τ := by
  rcases cycleType_of_orderOf_eq_three hσ with h3 | h33
  · refine alternatingGroup.isConj_of (Equiv.Perm.isConj_iff_cycleType_eq.mpr hστ) ?_
    rw [← Equiv.Perm.sum_cycleType, h3]
    simp
  ·
    have key : ∀ ρ : alternatingGroup (Fin 7), (ρ : Equiv.Perm (Fin 7)).cycleType = {3, 3} →
        ∃ c : alternatingGroup (Fin 7),
          (c : Equiv.Perm (Fin 7)) * dthree * (c : Equiv.Perm (Fin 7))⁻¹ = ρ := by
      intro ρ hρ
      obtain ⟨p, hp⟩ := isConj_iff.mp
        (Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_dthree.trans hρ.symm))
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs
      · exact ⟨⟨p, Equiv.Perm.mem_alternatingGroup.mpr hs⟩, hp⟩
      · obtain ⟨t, ht, htd⟩ := exists_odd_commute_dthree
        refine ⟨⟨p * t, ?_⟩, ?_⟩
        · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs, ht]
          decide
        · change p * t * dthree * (p * t)⁻¹ = ρ
          rw [← hp]
          calc p * t * dthree * (p * t)⁻¹ = p * (t * dthree * t⁻¹) * p⁻¹ := by group
            _ = p * dthree * p⁻¹ := by rw [htd]
    obtain ⟨a, ha⟩ := key σ h33
    obtain ⟨b, hb⟩ := key τ (hστ ▸ h33)
    refine isConj_iff.mpr ⟨b * a⁻¹, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← ha, ← hb]
    group

theorem mulVec_eq_zero_of_pow_three {F : Type} [Field F] (h2 : (2 : F) = 0)
    {A : Matrix (Fin 2) (Fin 2) F} (hdet : A.det = 1) (h3 : A ^ 3 = 1) (h1 : A ≠ 1)
    {v : Fin 2 → F} (hv : A.mulVec v = v) : v = 0 := by
  have hCH : A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
        ring
  have hAAv : (A * A).mulVec v = v := by rw [← Matrix.mulVec_mulVec, hv, hv]
  rw [hCH, hdet, one_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv] at hAAv
  have htv : A.trace • v = 0 := by
    have e : A.trace • v = v + v := by rw [sub_eq_iff_eq_add] at hAAv; exact hAAv
    rw [e, ← two_smul F v, h2, zero_smul]
  by_contra hv0
  have ht : A.trace = 0 := (smul_eq_zero.mp htv).resolve_right hv0
  rw [ht, zero_smul, hdet, one_smul, zero_sub] at hCH
  have hneg : (-1 : F) = 1 := by rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  have hm1 : (-1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    ext i j
    rw [Matrix.neg_apply]
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, hneg]
    · rw [Matrix.one_apply_ne hij, neg_zero]
  have hAA : A * A = 1 := by rw [hCH, hm1]
  apply h1
  calc A = A * (A * A) := by rw [hAA, mul_one]
    _ = A ^ 3 := by rw [pow_three]
    _ = 1 := h3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_map_eq_three {M2 U : Subgroup G} {A : Type} [Group A] {φ : ↥M2 →* A}
    (hker : φ.ker = U.subgroupOf M2) (hU2 : IsPGroup 2 U) {x : G} (hx : x ∈ M2)
    (hx3 : orderOf x = 3) : orderOf (φ ⟨x, hx⟩) = 3 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨x, hx⟩ : ↥M2) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hx3, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [this, map_one]
  · intro h1
    have hk : (⟨x, hx⟩ : ↥M2) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at hk
    obtain ⟨k, hk'⟩ := hU2 ⟨x, hk⟩
    have : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk'
      simpa using this
    rw [hx3] at this
    have h3k := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    norm_num at h3k

theorem exists_conj_mem_sup_of_map_eq_three {M2 U : Subgroup G}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hker : π.ker = U.subgroupOf M2) (hU2 : IsPGroup 2 U)
    (hUM2 : U ≤ M2) {x y : G} (hx : x ∈ M2) (hy : y ∈ M2) (hx3 : orderOf x = 3)
    (hy3 : orderOf y = 3) (hxy : π ⟨x, hx⟩ = π ⟨y, hy⟩) :
    ∃ g ∈ U ⊔ Subgroup.zpowers x, g * x * g⁻¹ = y := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := U ⊔ Subgroup.zpowers x with hX
  have hXM2 : X ≤ M2 := sup_le hUM2 (Subgroup.zpowers_le.mpr hx)
  have hxX : x ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hyX : y ∈ X := by
    have hk : (⟨x, hx⟩ : ↥M2)⁻¹ * ⟨y, hy⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have e : y = x * (x⁻¹ * y) := by group
    rw [e]
    exact X.mul_mem hxX (Subgroup.mem_sup_left (by simpa using hk))
  have hπX : ∀ (g : G) (hg : g ∈ M2), g ∈ X → π ⟨g, hg⟩ ∈ Subgroup.zpowers (π ⟨x, hx⟩) := by
    intro g hg hgX
    have hle : X ≤ ((Subgroup.zpowers (π ⟨x, hx⟩)).comap π).map M2.subtype := by
      refine sup_le ?_ ?_
      · intro u hu
        refine ⟨⟨u, hUM2 hu⟩, ?_, rfl⟩
        have : (⟨u, hUM2 hu⟩ : ↥M2) ∈ π.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          exact hu
        rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_ker.mp this]
        exact Subgroup.one_mem _
      · rw [Subgroup.zpowers_le]
        exact ⟨⟨x, hx⟩, Subgroup.mem_zpowers _, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hle hgX
    have : g' = ⟨g, hg⟩ := Subtype.ext hgg'
    rw [← this]
    exact hg'
  have hπx3 : orderOf (π ⟨x, hx⟩) = 3 := orderOf_map_eq_three hker hU2 hx hx3
  have hcardX : Nat.card X = 3 * Nat.card U := by
    have h1 := card_map_mul_card_inf hker hXM2
    have hmap : (X.subgroupOf M2).map π = Subgroup.zpowers (π ⟨x, hx⟩) := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        exact hπX g g.2 (Subgroup.mem_subgroupOf.mp hg)
      · rw [Subgroup.zpowers_le]
        exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩
    rw [hmap, Nat.card_zpowers, hπx3, inf_of_le_right (le_sup_left : U ≤ X)] at h1
    exact h1.symm
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hU2
  have hsyl : ∀ w : G, w ∈ X → orderOf w = 3 →
      CFSG.Quasithin.IsSylowIn 3 (Subgroup.zpowers w) X := by
    intro w hwX hw3
    refine ⟨Subgroup.zpowers_le.mpr hwX,
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw3, pow_one]), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers w) (K := X)
    rw [inf_of_le_left (Subgroup.zpowers_le.mpr hwX), Nat.card_zpowers, hw3, hcardX, he,
      mul_comm] at h1
    have h2 : (Subgroup.zpowers w).relIndex X = 2 ^ e := Nat.eq_of_mul_eq_mul_left (by norm_num) h1
    rw [h2]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  have hPx := hsyl x hxX hx3
  have hPy := hsyl y hyX hy3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X hPx.toSylow hPy.toSylow
  have hmem : g * (⟨x, hxX⟩ : ↥X) * g⁻¹ ∈ (hPy.toSylow : Subgroup ↥X) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨⟨x, hxX⟩, ?_, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [CFSG.Quasithin.IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers x
  rw [CFSG.Quasithin.IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hmem
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hgM2 : (g : G) ∈ M2 := hXM2 g.2
  have hπg : π ⟨g, hgM2⟩ ∈ Subgroup.zpowers (π ⟨x, hx⟩) := hπX g hgM2 g.2
  have hcomm : π ⟨g, hgM2⟩ * π ⟨x, hx⟩ = π ⟨x, hx⟩ * π ⟨g, hgM2⟩ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hπg
    rw [← hk]
    exact (Commute.zpow_left (Commute.refl _) k)
  have hπi : π ⟨y, hy⟩ ^ i = π ⟨x, hx⟩ := by
    have e1 : (⟨y, hy⟩ : ↥M2) ^ i = ⟨g, hgM2⟩ * ⟨x, hx⟩ * ⟨g, hgM2⟩⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hi)
    rw [← map_zpow, e1, map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right]
  rw [← hxy] at hπi
  have hi1 : i % 3 = 1 := by
    have h1 : π ⟨x, hx⟩ ^ (i - 1) = 1 := by
      rw [zpow_sub, hπi, zpow_one, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hπx3] at h1
    omega
  refine ⟨g, g.2, ?_⟩
  have e2 : y ^ i = y := by
    rw [← zpow_mod_orderOf, hy3]
    have : i % ((3 : ℕ) : ℤ) = 1 := by exact_mod_cast hi1
    rw [this, zpow_one]
  rw [← hi, e2]

theorem exists_conj_of_map_eq_three {M2 U : Subgroup G} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hker : π.ker = U.subgroupOf M2) (hU2 : IsPGroup 2 U) (hUM2 : U ≤ M2) {x y : G}
    (hx : x ∈ M2) (hy : y ∈ M2) (hx3 : orderOf x = 3) (hy3 : orderOf y = 3)
    (hxy : π ⟨x, hx⟩ = π ⟨y, hy⟩) : ∃ g ∈ M2, g * x * g⁻¹ = y := by
  obtain ⟨g, hg, h⟩ := exists_conj_mem_sup_of_map_eq_three hker hU2 hUM2 hx hy hx3 hy3 hxy
  exact ⟨g, sup_le hUM2 (Subgroup.zpowers_le.mpr hx) hg, h⟩

theorem exists_fpf_three_of_setting (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∃ k ∈ oTwoUpper H, orderOf k = 3 ∧ ∀ u ∈ pCoreOf 2 M2, k * u * k⁻¹ = u → u = 1 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hLin, hQeq, hUK, -⟩ := setting_K_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hcardK := card_eq_of_isLin2Type hLin
  rw [hQeq, hU16] at hcardK
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥(oTwoUpper H)) 3
    (by rw [hcardK]; norm_num)
  have hk3 : orderOf (k : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hk
  refine ⟨k, k.2, hk3, ?_⟩
  intro u hu hku
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβ⟩ := hLin
  have hβi : Function.Injective β := by
    have hc : Nat.card ↥(blockU (oTwoUpper H)) ≤ Nat.card (Multiplicative (Fin 2 → F)) := by
      rw [hUK, hU16, Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)),
        Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, hF]
      norm_num
    exact (hβs.bijective_of_nat_card_le hc).1
  have h2 : (2 : F) = 0 := by
    have h4 := FiniteField.cast_card_eq_zero F
    rw [hF] at h4
    have h4' : (2 : F) ^ 2 = 0 := by exact_mod_cast h4
    exact pow_eq_zero_iff (by norm_num) |>.mp h4'
  have hα3 : (α k : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    rfl
  have hα1 : (α k : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h1
    have h1' : α k = 1 := Subtype.ext h1
    have h3' : k ∈ CFSG.pCore 2 ↥(oTwoUpper H) := by
      rw [← hαk]
      exact h1'
    have h4 : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := by
      exact ⟨_, h3', rfl⟩
    rw [hQeq] at h4
    obtain ⟨e, he⟩ := hU2 ⟨k, h4⟩
    have : orderOf (k : G) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val he
      simpa using this
    rw [hk3] at this
    have h3k := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    norm_num at h3k
  have huK : u ∈ blockU (oTwoUpper H) := by rw [hUK]; exact hu
  have hfix := hβ k ⟨u, huK⟩ ⟨u, huK⟩ hku.symm
  have h0 := mulVec_eq_zero_of_pow_three h2 (α k).2 hα3 hα1 hfix.symm
  have h5 : β ⟨u, huK⟩ = 1 := h0
  have h6 : (⟨u, huK⟩ : ↥(blockU (oTwoUpper H))) = 1 := hβi (h5.trans (map_one β).symm)
  exact congrArg Subtype.val h6

theorem stmt5_2_14_one_of
    (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four) (h526 : Stmt5_2_6) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {x y : G} (hx3 : orderOf x = 3) (hy3 : orderOf y = 3)
    (hxi : ∃ i : G, orderOf i = 2 ∧ i * x = x * i)
    (hyj : ∃ j : G, orderOf j = 2 ∧ j * y = y * j) : ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨z, hz2, hzT, hzU⟩ := stmt5_2_12_center_of hQ hyp hM23 hS
  have hC := centralizer_le_of_setting hQ h5211 hyp hM23 hS hz2 hzT hzU
  obtain ⟨k, hkK, hk3, hkfix⟩ := exists_fpf_three_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hkM2 : k ∈ M2 := hS.K_lt.le hkK
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2', hT8, hUT, hπ'⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hUN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have red : ∀ w : G, orderOf w = 3 → (∃ i : G, orderOf i = 2 ∧ i * w = w * i) →
      ∃ a : G, a * w * a⁻¹ ∈ M2 ∧ (a * w * a⁻¹) * z = z * (a * w * a⁻¹) := by
    rintro w hw3 ⟨i, hi2, hiw⟩
    obtain ⟨a, ha⟩ :=
      exists_conj_eq_of_orderOf_two h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hz2 hzT hzU hi2
    have hcomm : (a * w * a⁻¹) * z = z * (a * w * a⁻¹) := by
      rw [← ha]
      calc a * w * a⁻¹ * (a * i * a⁻¹) = a * (w * i) * a⁻¹ := by group
        _ = a * (i * w) * a⁻¹ := by rw [hiw]
        _ = a * i * a⁻¹ * (a * w * a⁻¹) := by group
    refine ⟨a, hC ?_, hcomm⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm.symm
  have hk3' : orderOf (π' ⟨k, hkM2⟩) = 3 := orderOf_map_eq_three hker hU2 hkM2 hk3
  have notct : ∀ (w : G) (hw : w ∈ M2), orderOf w = 3 → w * z = z * w →
      ((π' ⟨w, hw⟩ : A7) : Equiv.Perm (Fin 7)).cycleType ≠
        ((π' ⟨k, hkM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType := by
    intro w hw hw3 hwz hct
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hk3' hct.symm)
    obtain ⟨m, rfl⟩ := hsurj c
    have hmk : (m : G) * k * (m : G)⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem m.2 hkM2) (M2.inv_mem m.2)
    have hmk3 : orderOf ((m : G) * k * (m : G)⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk3
    have hπeq : π ⟨(m : G) * k * (m : G)⁻¹, hmk⟩ = π ⟨w, hw⟩ := by
      rw [← hπ', ← hπ']
      congr 1
      rw [← hc]
      have : (⟨(m : G) * k * (m : G)⁻¹, hmk⟩ : ↥M2) = m * ⟨k, hkM2⟩ * m⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    obtain ⟨g, hg, hgw⟩ := exists_conj_of_map_eq_three hS.ker_eq hU2 hUM2 hmk hw hmk3 hw3 hπeq
    set gm : G := g * m with hgm
    have hgmM2 : gm ∈ M2 := M2.mul_mem hg m.2
    have hu : gm⁻¹ * z * gm ∈ pCoreOf 2 M2 := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (M2.inv_mem hgmM2)) z).mp hzU
      simpa using this
    have hwz' : w * z * w⁻¹ = z := by rw [hwz, mul_inv_cancel_right]
    have hku : k * (gm⁻¹ * z * gm) * k⁻¹ = gm⁻¹ * z * gm := by
      have e : w = gm * k * gm⁻¹ := by rw [← hgw, hgm]; group
      rw [e] at hwz'
      calc k * (gm⁻¹ * z * gm) * k⁻¹ = gm⁻¹ * (gm * k * gm⁻¹ * z * (gm * k * gm⁻¹)⁻¹) * gm := by
            group
        _ = gm⁻¹ * z * gm := by rw [hwz']
    have h1 := hkfix _ hu hku
    apply hz1
    calc z = gm * (gm⁻¹ * z * gm) * gm⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨a, haM2, haz⟩ := red x hx3 hxi
  obtain ⟨b, hbM2, hbz⟩ := red y hy3 hyj
  have hx3' : orderOf (a * x * a⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hy3' : orderOf (b * y * b⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy3
  have hcx := notct _ haM2 hx3' haz
  have hcy := notct _ hbM2 hy3' hbz
  have hxo := orderOf_map_eq_three hker hU2 haM2 hx3'
  have hyo := orderOf_map_eq_three hker hU2 hbM2 hy3'
  have hcxy : ((π' ⟨_, haM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType =
      ((π' ⟨_, hbM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType := by
    rcases cycleType_of_orderOf_eq_three hk3' with hk | hk <;>
    rcases cycleType_of_orderOf_eq_three hxo with hx | hx <;>
    rcases cycleType_of_orderOf_eq_three hyo with hy | hy <;>
    first
      | exact hx.trans hy.symm
      | exact absurd (hx.trans hk.symm) hcx
      | exact absurd (hy.trans hk.symm) hcy
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hxo hcxy)
  obtain ⟨m, rfl⟩ := hsurj c
  have hmx : (m : G) * (a * x * a⁻¹) * (m : G)⁻¹ ∈ M2 :=
    M2.mul_mem (M2.mul_mem m.2 haM2) (M2.inv_mem m.2)
  have hmx3 : orderOf ((m : G) * (a * x * a⁻¹) * (m : G)⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3'
  have hπeq : π ⟨(m : G) * (a * x * a⁻¹) * (m : G)⁻¹, hmx⟩ = π ⟨b * y * b⁻¹, hbM2⟩ := by
    rw [← hπ', ← hπ']
    congr 1
    rw [← hc]
    have : (⟨(m : G) * (a * x * a⁻¹) * (m : G)⁻¹, hmx⟩ : ↥M2) = m * ⟨_, haM2⟩ * m⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  obtain ⟨g, -, hg⟩ := exists_conj_of_map_eq_three hS.ker_eq hU2 hUM2 hmx hbM2 hmx3 hy3' hπeq
  refine ⟨b⁻¹ * g * m * a, ?_⟩
  calc b⁻¹ * g * m * a * x * (b⁻¹ * g * m * a)⁻¹ =
        b⁻¹ * (g * ((m : G) * (a * x * a⁻¹) * (m : G)⁻¹) * g⁻¹) * b := by group
    _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [hg]
    _ = y := by group

end CFSG.Quasithin.H13
