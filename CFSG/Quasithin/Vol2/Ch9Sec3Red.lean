module

public import CFSG.Quasithin.Vol2.Ch9Sec3Diag

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

section Model

variable {K : Type} [Field K]

@[expose] noncomputable def diagHom (K : Type) [Field K] : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun := diagOf
  map_one' := by
    apply Subtype.ext
    rw [coe_diagOf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagOf, coe_diagOf, coe_diagOf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagHom_apply (a : Kˣ) : diagHom K a = diagOf a := rfl

theorem exists_eq_diagOf {g : SpecialLinearGroup (Fin 2) K} (hg : g ∈ diagT K) :
    ∃ a : Kˣ, g = diagOf a ∧ (a : K) = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  refine ⟨(diagEquiv K).symm ⟨g, hg⟩, ?_, rfl⟩
  have := congrArg Subtype.val ((diagEquiv K).apply_symm_apply ⟨g, hg⟩)
  exact this.symm

theorem rho_diag_smul_e11 (a b : Kˣ) (c : K) :
    Om4.rho (diagOf a, diagOf b) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd (((a : K) * b * c) • !![(1 : K), 0; 0, 0]) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
  ext i j
  rw [mul_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [coe_diagOf]
  ring

theorem pow_three_eq_one_of_card_four [Fintype K] (hK : Fintype.card K = 4) (x : Kˣ) :
    x ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h := FiniteField.pow_card_sub_one_eq_one (x : K) x.ne_zero
  rwa [hK] at h

end Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem mem_centralizer_V1_iff_diag (k : ↥(fsuL0 T L)) (a b : Kˣ)
    (hk : ψ k = (diagOf a, diagOf b)) :
    (k : G) ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ↔ a * b = 1 := by
  constructor
  · intro hkV
    have hw := hc.symm_mem (e := e) 1
    set w := e.symm (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) with hwdef
    have h1 : (k : G) * w * (k : G)⁻¹ = w := by
      rw [← Subgroup.mem_centralizer_iff.mp hkV _ hw, mul_inv_cancel_right]
    have h2 : bar e (Subgroup.inclusion S.L0_le_normalizer_V k) (e w) = e w := by
      rw [bar_apply]
      congr 1
      exact Subtype.ext h1
    rw [hc.bar_L0, hk, hwdef, MulEquiv.apply_symm_apply, rho_diag_smul_e11] at h2
    have h3 := congrArg (fun X : Om4.VM K =>
      (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) 0 0) h2
    simp only [toAdd_ofAdd, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
      mul_one] at h3
    exact Units.ext (by rw [Units.val_mul, h3, Units.val_one])
  · intro hab
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hev := hc.toAdd_e_eq hv
    set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hcdef
    have hev' : e ⟨v, hv.1⟩ = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      exact hev
    have hab' : (a : K) * b = 1 := by rw [← Units.val_mul, hab, Units.val_one]
    have hfix : bar e (Subgroup.inclusion S.L0_le_normalizer_V k) (e ⟨v, hv.1⟩) =
        e ⟨v, hv.1⟩ := by
      rw [hc.bar_L0, hk, hev', rho_diag_smul_e11, hab', one_mul]
    rw [bar_apply] at hfix
    have h3 : (k : G) * v * (k : G)⁻¹ = v := congrArg Subtype.val (e.injective hfix)
    calc v * (k : G) = ((k : G) * v * (k : G)⁻¹) * k := by rw [h3]
      _ = k * v := by group

variable {D : Subgroup G}

omit [Finite G] [Fintype K] [CharP K 2] hc in
theorem exists_diag_of_mem (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    {x : G} (hx : x ∈ D) (hxL : x ∈ fsuL0 T L) :
    ∃ a b : Kˣ, ψ ⟨x, hxL⟩ = (diagOf a, diagOf b) := by
  have hmem : ψ ⟨x, hxL⟩ ∈ (diagT K).prod (diagT K) := by
    rw [← hdiag]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨a, ha, -⟩ := exists_eq_diagOf hmem.1
  obtain ⟨b, hb, -⟩ := exists_eq_diagOf hmem.2
  exact ⟨a, b, Prod.ext ha hb⟩

omit [Finite G] [Fintype K] [CharP K 2] hc in
theorem exists_mem_of_diag
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) (a b : Kˣ) :
    ∃ x ∈ D, ∃ hxL : x ∈ fsuL0 T L, ψ ⟨x, hxL⟩ = (diagOf a, diagOf b) := by
  have hmem : ((diagOf a, diagOf b) : SpecialLinearGroup (Fin 2) K × _) ∈
      (diagT K).prod (diagT K) := ⟨diagOf_mem a, diagOf_mem b⟩
  rw [← hdiag] at hmem
  obtain ⟨y, hy, hψy⟩ := hmem
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, y.2, hψy⟩

theorem exists_mul_sym (h2 : n = 2)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    (hDL : D ≤ fsuL0 T L) {x : G} (hx : x ∈ D) :
    ∃ b ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G),
      ∃ d ∈ D, ∃ hdL : d ∈ fsuL0 T L, (ψ ⟨d, hdL⟩).1 = (ψ ⟨d, hdL⟩).2 ∧ x = b * d := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  obtain ⟨a, b, hab⟩ := exists_diag_of_mem hdiag hx (hDL hx)
  set f := (a * b) ^ 2 with hf
  obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag f f
  refine ⟨x * d⁻¹, ⟨D.mul_mem hx (D.inv_mem hdD), ?_⟩, d, hdD, hdL,
    by rw [hψd], by rw [inv_mul_cancel_right]⟩
  have hxd : ψ ⟨x * d⁻¹, (fsuL0 T L).mul_mem (hDL hx) ((fsuL0 T L).inv_mem hdL)⟩ =
      (diagOf (a * f⁻¹), diagOf (b * f⁻¹)) := by
    have : (⟨x * d⁻¹, (fsuL0 T L).mul_mem (hDL hx) ((fsuL0 T L).inv_mem hdL)⟩ :
        ↥(fsuL0 T L)) = ⟨x, hDL hx⟩ * ⟨d, hdL⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hab, hψd]
    simp only [Prod.mk_mul_mk, Prod.inv_mk, ← diagHom_apply, ← map_inv, ← map_mul]
  refine (hc.mem_centralizer_V1_iff_diag _ _ _ hxd).mpr ?_
  have h3 := pow_three_eq_one_of_card_four hK4 (a * b)
  calc a * f⁻¹ * (b * f⁻¹) = (a * b) * (f * f)⁻¹ := by rw [mul_mul_mul_comm, mul_inv]
    _ = (a * b) * (a * b)⁻¹ := by
      rw [hf, ← pow_add, show (2 + 2 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]
    _ = 1 := mul_inv_cancel _

theorem first_red (h2 : n = 2) (h1 : zQ T I = fsuV T I)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    (hDL : D ≤ fsuL0 T L) {X : Subgroup G}
    (hXZ : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hB : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (X : Set G))
    (hsym : ∀ d ∈ D, ∀ hdL : d ∈ fsuL0 T L, (ψ ⟨d, hdL⟩).1 = (ψ ⟨d, hdL⟩).2 →
      d ∈ Subgroup.normalizer (X : Set G)) :
    D ≤ Subgroup.normalizer (X : Set G) ∧
      X ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨b, hb, d, hdD, hdL, hsd, rfl⟩ := hc.exists_mul_sym h2 hdiag hDL hx
    exact Subgroup.mul_mem _ (hB hb) (hsym d hdD hdL hsd)
  · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hev := hc.toAdd_e_eq hv
    set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hcdef
    have hev' : e ⟨v, hv.1⟩ = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      exact hev
    by_cases hc0 : c = 0
    · have hv1 : v = 1 := by
        have h3 : e ⟨v, hv.1⟩ = 1 := by rw [hev', hc0, zero_smul]; rfl
        exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h3)
      rw [hv1, one_mul, mul_one]
    obtain ⟨z, hzV, hzZ, c₀, hc₀, hze⟩ := hc.exists_z h1
    set q := Units.mk0 (c / c₀) (div_ne_zero hc0 hc₀) with hq
    obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag (q ^ 2) (q ^ 2)
    have hq4 : ((q ^ 2 : Kˣ) : K) * ((q ^ 2 : Kˣ) : K) = c / c₀ := by
      have h3 := pow_three_eq_one_of_card_four hK4 q
      have : (q ^ 2) * (q ^ 2) = q := by
        calc q ^ 2 * q ^ 2 = q ^ 3 * q := by group
          _ = q := by rw [h3, one_mul]
      rw [← Units.val_mul, this, hq, Units.val_mk0]
    have hdz : (d : G) * z * d⁻¹ = v := by
      have h3 : bar e (Subgroup.inclusion S.L0_le_normalizer_V ⟨d, hdL⟩) (e ⟨z, hzV⟩) =
          e ⟨v, hv.1⟩ := by
        rw [hc.bar_L0, hψd, hze, rho_diag_smul_e11, hev', hq4, div_mul_cancel₀ c hc₀]
      rw [bar_apply] at h3
      exact congrArg Subtype.val (e.injective h3)
    have hdN := hsym d hdD hdL (by rw [hψd])
    have hy' : d⁻¹ * y * d ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) y).mp hy
      simpa using this
    have hcz := Subgroup.mem_centralizer_iff.mp (hXZ hy') z hzZ
    rw [← hdz]
    calc (d : G) * z * d⁻¹ * y = d * (z * (d⁻¹ * y * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * y * d) * z) * d⁻¹ := by rw [hcz]
      _ = y * (d * z * d⁻¹) := by group

theorem act_V1 {t : G} (ht : t ∈ T) {A B : GL (Fin 2) K} {τ : K ≃+* K}
    (h : bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM τ ∨
      bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ c : K,
      bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
        Multiplicative.ofAdd ((μ * τ c) • !![(1 : K), 0; 0, 0]) := by
  have htM : t ∈ fsuM T L := Setup.T_le_fsuM ht
  set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨t, S.hMN htM⟩ with hy
  have hV1 : ∀ w ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G),
      t * w * t⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
    rintro w ⟨hwV, hwC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (S.hMN htM) w).mp hwV,
      Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : t⁻¹ * s * t ∈ T ⊓ fsuL0 T L := by
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hs.1) ht, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (T_le_normalizer_L0 ht))
        s).mp hs.2
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hwC _ hs'
    calc s * (t * w * t⁻¹) = t * ((t⁻¹ * s * t) * w) * t⁻¹ := by group
      _ = t * (w * (t⁻¹ * s * t)) * t⁻¹ := by rw [h2]
      _ = t * w * t⁻¹ * s := by group
  rcases h with h | h
  all_goals
    have hE : ∀ c : K, bar e y (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
        (Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) := by
      intro c
      rw [hy, h]
      try rw [MulAut.mul_apply, Om4.trM_smul_e11]
    have hw := hc.symm_mem (e := e) 1
    have h2 := hc.toAdd_e_eq (hV1 _ hw)
    have h3 : e ⟨t * (e.symm (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) : G) *
        t⁻¹, (hV1 _ hw).1⟩ = bar e y (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) := by
      rw [← bar_apply e y, MulEquiv.apply_symm_apply]
    rw [h3, hE, Om4.toAdd_apply_smul_e11, map_one, one_smul] at h2
    obtain ⟨hA, hB⟩ := Om4.isUT_of_mul_e11 h2
    obtain ⟨hA0, -⟩ := hA.apply_ne_zero
    obtain ⟨hB0, -⟩ := hB.apply_ne_zero
    exact ⟨_, mul_ne_zero hA0 hB0, fun c => by rw [hE, Om4.apply_smul_e11 hA hB]⟩

theorem mem_centralizer_V1_of_one {t : G} (ht : t ∈ T) {A B : GL (Fin 2) K}
    (h : bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM 1 ∨
      bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM 1 * Om4.trM) :
    t ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨μ, hμ, hact⟩ := hc.act_V1 ht h
  simp only [RingAut.one_apply] at hact
  set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ with hy
  have hiter : ∀ j : ℕ, ∀ c : K, (bar e y ^ j) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd ((μ ^ j * c) • !![(1 : K), 0; 0, 0]) := by
    intro j
    induction j with
    | zero => intro c; simp
    | succ j ih =>
      intro c
      rw [pow_succ', MulAut.mul_apply, ih, hact, pow_succ']
      congr 2
      ring
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.hyp.fsu.sylow.1) ⟨t, ht⟩
  have hk' : orderOf t = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hy1 : bar e y ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk', pow_orderOf_eq_one]
      rfl
    rw [this, map_one]
  have hμk : μ ^ 2 ^ k = 1 := by
    have := hiter (2 ^ k) 1
    rw [hy1, MulAut.one_apply] at this
    have h2 := congrArg
      (fun X : Om4.VM K => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) 0 0) this
    simpa using h2.symm
  have hμ1 : μ = 1 := by
    have h3 : μ ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ
    have h4 : orderOf μ ∣ Nat.gcd (2 ^ k) (Fintype.card K - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hμk) (orderOf_dvd_of_pow_eq_one h3)
    have h5 : Nat.gcd (2 ^ k) (Fintype.card K - 1) = 1 := by
      rw [hc.card]
      refine Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ?_)
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by
        have := S.two_le; omega⟩) odd_one
    rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have hv2 := hc.toAdd_e_eq hv
  set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hcdef
  have hev : e ⟨v, hv.1⟩ = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hv2
  have hfix : bar e y (e ⟨v, hv.1⟩) = e ⟨v, hv.1⟩ := by
    rw [hev, hact, hμ1, one_mul]
  rw [bar_apply] at hfix
  have h5 : t * v * t⁻¹ = v := congrArg Subtype.val (e.injective hfix)
  calc v * t = (t * v * t⁻¹) * t := by rw [h5]
    _ = t * v := by group

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
