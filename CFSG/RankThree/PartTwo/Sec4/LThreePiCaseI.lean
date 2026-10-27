module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section Eigen

variable {K : Type} [Field K]

theorem pow_mulVec_of_eigen {y : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} {d : K}
    (h : y *ᵥ v = d • v) (n : ℕ) : (y ^ n) *ᵥ v = d ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ, mul_comm]

theorem commute_of_eigen {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    {y y' : Matrix (Fin 3) (Fin 3) K} {d d' : Fin 3 → K} (hy : ∀ i, y *ᵥ b i = d i • b i)
    (hy' : ∀ i, y' *ᵥ b i = d' i • b i) : y * y' = y' * y := by
  apply eq_of_mulVec_eq_of_linearIndependent hb
  intro i
  rw [← Matrix.mulVec_mulVec, hy', Matrix.mulVec_smul, hy, ← Matrix.mulVec_mulVec, hy,
    Matrix.mulVec_smul, hy', smul_smul, smul_smul, mul_comm]

theorem det_eq_prod_of_eigen {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    {y : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} (hy : ∀ i, y *ᵥ b i = d i • b i) :
    y.det = d 0 * d 1 * d 2 := by
  have hu := isUnit_colMat hb
  have hmul := mul_colMat_eq hy
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three] at h
  have h0 : (colMat b).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  rw [mul_comm] at h
  exact mul_left_cancel₀ h0 h

theorem trace_eq_sum_of_eigen {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    {y : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} (hy : ∀ i, y *ᵥ b i = d i • b i) :
    y.trace = d 0 + d 1 + d 2 := by
  have hu := isUnit_colMat hb
  have hmul := mul_colMat_eq hy
  have h : y = colMat b * diagonal d * (colMat b)⁻¹ := by
    rw [← hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hu), Matrix.mul_one]
  rw [h, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hu), Matrix.one_mul, Matrix.trace_diagonal, Fin.sum_univ_three]

theorem sum_eq_zero_of_injective_of_cube {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {d : Fin 3 → K} (hd : Function.Injective d) {ℓ : K} (hd3 : ∀ i, d i ^ 3 = ℓ) :
    d 0 + d 1 + d 2 = 0 := by
  have hs := one_add_tau_add_sq hτ hτ1
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have h1 : d 1 ^ 3 = 0 := by rw [hd3, ← hd3 0, h0]; ring
    have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h1
    exact absurd (hd (h0.trans this.symm)) (by decide)
  have hr : ∀ i, (d i / d 0) ^ 3 = 1 := fun i => by
    rw [div_pow, hd3, hd3, div_self (by rw [← hd3 0]; exact pow_ne_zero 3 hd0)]
  have hne : ∀ i j, i ≠ j → d i / d 0 ≠ d j / d 0 := fun i j hij h =>
    hij (hd (by rwa [div_left_inj' hd0] at h))
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h12 := hne 1 2 (by decide)
  rw [div_self hd0] at h01 h02
  have hsum : 1 + d 1 / d 0 + d 2 / d 0 = 0 := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 (hr 1) with h1 | h1 | h1
    · exact absurd h1.symm h01
    · rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 (hr 2) with h2 | h2 | h2
      · exact absurd h2.symm h02
      · exact absurd (h1.trans h2.symm) h12
      · rw [h1, h2]; exact hs
    · rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 (hr 2) with h2 | h2 | h2
      · exact absurd h2.symm h02
      · rw [h1, h2]; linear_combination hs
      · exact absurd (h1.trans h2.symm) h12
  have : d 0 * (1 + d 1 / d 0 + d 2 / d 0) = d 0 + d 1 + d 2 := by field_simp
  rw [← this, hsum, mul_zero]

theorem prod_eq_of_injective_of_cube {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {d : Fin 3 → K} (hd : Function.Injective d) {ℓ : K} (hd3 : ∀ i, d i ^ 3 = ℓ) :
    d 0 * d 1 * d 2 = ℓ := by
  have hs := one_add_tau_add_sq hτ hτ1
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have h1 : d 1 ^ 3 = 0 := by rw [hd3, ← hd3 0, h0]; ring
    have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h1
    exact absurd (hd (h0.trans this.symm)) (by decide)
  have hr : ∀ i, (d i / d 0) ^ 3 = 1 := fun i => by
    rw [div_pow, hd3, hd3, div_self (by rw [← hd3 0]; exact pow_ne_zero 3 hd0)]
  have hne : ∀ i j, i ≠ j → d i / d 0 ≠ d j / d 0 := fun i j hij h =>
    hij (hd (by rwa [div_left_inj' hd0] at h))
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h12 := hne 1 2 (by decide)
  rw [div_self hd0] at h01 h02
  have hprod : d 1 / d 0 * (d 2 / d 0) = 1 := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 (hr 1) with h1 | h1 | h1
    · exact absurd h1.symm h01
    · rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 (hr 2) with h2 | h2 | h2
      · exact absurd h2.symm h02
      · exact absurd (h1.trans h2.symm) h12
      · rw [h1, h2, ← pow_succ', hτ]
    · rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 (hr 2) with h2 | h2 | h2
      · exact absurd h2.symm h02
      · rw [h1, h2, ← pow_succ, hτ]
      · exact absurd (h1.trans h2.symm) h12
  have : d 0 * d 1 * d 2 = d 0 ^ 3 * (d 1 / d 0 * (d 2 / d 0)) := by field_simp
  rw [this, hprod, mul_one, hd3]

end Eigen

section Types

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_inner_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (h1 : Type123 π (p ^ f) K y 1) :
    ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹ := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ := h1
  have hyZ : y ∉ zPi π 3 (p ^ f) K := by
    intro hy
    have hcz : y * z ∈ zPi π 3 (p ^ f) K := mul_mem hy hz
    have hs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hcz
    have hgc := commute_of_mem_statedScalars hs g
    have hconj : g⁻¹ * (y * z) * g = y * z := by rw [mul_assoc, ← hgc, inv_mul_cancel_left]
    rw [hconj] at hD
    obtain ⟨c, hc⟩ := hs
    have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hD
    have h22 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hD
    simp only [← hc, coe_scalar_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, coe_diagTau_eq_diagonal, Matrix.diagonal_apply_eq] at h00 h22
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at h00 h22
    exact hτ1 (h00.symm.trans h22)
  have hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    have h1 : (y * z) ^ 3 = 1 := by
      have := diagTau_pow_three hτ
      rw [← hD] at this
      have e : (g⁻¹ * (y * z) * g) ^ 3 = g⁻¹ * (y * z) ^ 3 * g := by
        have := conj_pow (a := g⁻¹) (b := y * z) (i := 3)
        rwa [inv_inv] at this
      rw [e] at this
      calc (y * z) ^ 3 = g * (g⁻¹ * (y * z) ^ 3 * g) * g⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hcz : Commute y z := (commute_of_mem_statedScalars
      (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz) y)
    rw [hcz.mul_pow] at h1
    have : y ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem (pow_mem hz 3)
  exact (rank3II_4_10_two hK hq hτ hτ1 hyH hyZ hy3).mpr (Or.inl ⟨y * z, ⟨z, hz, rfl⟩, g, hg, hD⟩)

theorem not_inner_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (h3 : Type123 π (p ^ f) K y 3) :
    ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹ := by
  intro hin
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hyZ, hy3, -⟩ := id h3
  rcases (rank3II_4_10_two hK hq hτ hτ1 hyH hyZ hy3).mp hin with
    ⟨_, ⟨z, hz, rfl⟩, g, hg, hD⟩ | ⟨⟨_, ⟨z, hz, rfl⟩, g, hg, e, he, hD⟩, -⟩
  · exact not_type123_three_of_one hK hq ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ h3
  · have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        have hτ0 : τ ≠ 0 := by
          rintro rfl
          simp at hτ
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    exact not_type123_three_of_two hK hq ⟨e, he3, he1, z, hz, g, hg, hD⟩ h3

theorem type1_of_regular (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {y : GL (Fin 3) K}
    (hyH : y ∈ glPi π 3 (p ^ f) K) (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b) {d : Fin 3 → K}
    (hd : Function.Injective d) (hyb : ∀ i, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i) :
    Type123 π (p ^ f) K y 1 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hyZ : y ∉ zPi π 3 (p ^ f) K := by
    intro hy
    obtain ⟨c, hc⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy
    have h0 := hyb 0
    have h1 := hyb 1
    rw [← hc, coe_scalar_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at h0 h1
    have e0 : d 0 = c := (smul_left_injective K (hb.ne_zero 0) h0).symm
    have e1 : d 1 = c := (smul_left_injective K (hb.ne_zero 1) h1).symm
    exact absurd (hd (e0.trans e1.symm)) (by decide)
  rcases type123_exhaust hK hq hyH hyZ hy3 with h1 | h2 | h3
  · exact h1
  · exfalso
    apply trace_ne_zero_of_type2 hK hq h2
    obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy3
    have hd3 : ∀ i, d i ^ 3 = ℓ := by
      intro i
      have h := pow_mulVec_of_eigen (hyb i) 3
      rw [← Units.val_pow_eq_pow_val, ← hℓ, coe_scalar_eq_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec] at h
      exact (smul_left_injective K (hb.ne_zero i) h).symm
    rw [trace_eq_sum_of_eigen hb hyb]
    exact sum_eq_zero_of_injective_of_cube hτ hτ1 hd hd3
  · exfalso
    obtain ⟨-, -, hirr⟩ := h3
    rcases hirr (Submodule.span K {b 0}) (fun v hv => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [Matrix.mulVec_smul, hyb, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) with h | h
    · exact hb.ne_zero 0 (by
        have : b 0 ∈ Submodule.span K {b 0} := Submodule.mem_span_singleton_self _
        rwa [h, Submodule.mem_bot] at this)
    · have h1 : b 1 ∈ Submodule.span K {b 0} := h ▸ Submodule.mem_top
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
      have h0 : ∑ i, (![a, -1, 0] : Fin 3 → K) i • b i = 0 := by
        rw [Fin.sum_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, ha, zero_smul, add_zero, neg_one_smul, add_neg_cancel]
      have := Fintype.linearIndependent_iff.mp hb _ h0 1
      simp at this

end Types

section Pairs

variable {G : Type*} [Group G] [Finite G]

theorem card_zpowers_sup_zpowers {b c : G} (hb3 : b ^ 3 = 1) (hc3 : orderOf c = 3)
    (hbc : b ∉ Subgroup.zpowers c) (hcomm : b * c = c * b) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := fun h => hbc (h ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hc : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((Commute.zpow_zpow (show Commute c b from hcomm.symm) i j)).eq
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers b = ⊥ := by
    by_contra hne
    obtain ⟨⟨x, hxc, hxb⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxo : orderOf x = 3 := by
      have hxb3 : x ^ 3 = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxb
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hb3,
          _root_.one_zpow]
      exact orderOf_eq_prime hxb3 hx1'
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hxb
    have heq : Subgroup.zpowers x = Subgroup.zpowers b := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hbo]
    apply hbc
    have hxc' : Subgroup.zpowers x ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hxc
    rw [heq] at hxc'
    exact hxc' (Subgroup.mem_zpowers b)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hc3, hbo] at h
  exact h

end Pairs

section CaseI

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite G] in
theorem card_eq_of_pgl (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) :
    Nat.card A = 27 ∧ Nat.card (pglHom hK hq A hpgl).range = 9 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcard := card_eq_card_inf_mul_card_range (L := L) (e := e) (hK := hK) (hq := hq) (A' := A)
    (hA' := hpgl)
  rw [hAc, Nat.card_zpowers, hc3] at hcard
  have hE := card_le_nine_of_comm h3 hτ hτ1 (pglHom hK hq A hpgl).range
    (range_pglHom_comm hAcomm) (range_pglHom_pow hA.1.2)
  omega

omit [Finite G] in
theorem isPGLAt_commute_of_mem {e : L ≃* slPi π 3 (p ^ f) K} {a b : G} (hbL : b ∈ L)
    (hab : a * b = b * a) {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    y * (e ⟨b, hbL⟩ : GL (Fin 3) K) = (e ⟨b, hbL⟩ : GL (Fin 3) K) * y := by
  have h1 := hy.2 (e ⟨b, hbL⟩)
  rw [coe_slAct_eq] at h1
  simp only [MulEquiv.symm_apply_apply] at h1
  have h2 : (⟨a * b * a⁻¹, hLn.conj_mem _ hbL a⟩ : L) = ⟨b, hbL⟩ :=
    Subtype.ext (by change a * b * a⁻¹ = b; rw [hab, mul_inv_cancel_right])
  rw [h2] at h1
  calc y * (e ⟨b, hbL⟩ : GL (Fin 3) K) = y * (e ⟨b, hbL⟩ : GL (Fin 3) K) * y⁻¹ * y := by group
    _ = _ := by rw [← h1]

omit [Finite G] hLn in
theorem mem_centralizer_of_scalar {e : L ≃* slPi π 3 (p ^ f) K} {b : G} (hbL : b ∈ L)
    (hs : (e ⟨b, hbL⟩ : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    b ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : (e ⟨l, hl⟩ : GL (Fin 3) K) * e ⟨b, hbL⟩ = e ⟨b, hbL⟩ * e ⟨l, hl⟩ :=
    commute_of_mem_statedScalars hs _
  have h2 : e (⟨l, hl⟩ * ⟨b, hbL⟩) = e (⟨b, hbL⟩ * ⟨l, hl⟩) := by
    rw [map_mul, map_mul]
    exact Subtype.ext h1
  exact congrArg Subtype.val (e.injective h2)

theorem linearIndependent_cols_of_GL (g : GL (Fin 3) K) :
    LinearIndependent K (fun i : Fin 3 => fun r : Fin 3 => (g : Matrix (Fin 3) (Fin 3) K) r i) := by
  have := (Matrix.linearIndependent_cols_iff_isUnit (A := (g : Matrix (Fin 3) (Fin 3) K))).mpr
    g.isUnit
  convert this using 1
  funext i r
  rfl

theorem mulVec_col_of_conj {g x : GL (Fin 3) K} {d : Fin 3 → K}
    (h : (x : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal d) (i : Fin 3) :
    (x : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun r => (g : Matrix (Fin 3) (Fin 3) K) r i) =
      d i • fun r => (g : Matrix (Fin 3) (Fin 3) K) r i := by
  ext r
  have := congrFun (congrFun h r) i
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [this, mul_comm]

theorem alt411_one_of_pgl (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) {b : G} (hbA : b ∈ A) (hbL : b ∈ L)
    (hbc : b ∉ Subgroup.zpowers c) :
    Nat.card A = 27 ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ IsTypeCOnSL A L := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hA27', hE9⟩ := card_eq_of_pgl hK hq hA hA27 hc3 hAc hpgl
  set E := (pglHom hK hq A hpgl).range with hEdef
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  set eb : GL (Fin 3) K := (e ⟨b, hbL⟩ : GL (Fin 3) K) with heb
  have hebZ : eb ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply hbc
    rw [← hLC]
    exact ⟨hbL, mem_centralizer_of_scalar hbL (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)⟩
  have heb3 : orderOf eb = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : eb ^ 3 = 1 := by
      rw [heb, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨b, hbL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb3]; rfl)
      rw [this, map_one, Subgroup.coe_one]
    refine orderOf_eq_prime h3 fun h1 => hebZ ?_
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨g, hg, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 (e ⟨b, hbL⟩).2 hebZ heb3
  set fr : Fin 3 → (Fin 3 → K) := fun i r => (g : Matrix (Fin 3) (Fin 3) K) r i with hfr
  have hfrli : LinearIndependent K fr := linearIndependent_cols_of_GL g
  have hegD : (eb : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal ![τ, τ ^ 2, 1] := by
    have h1 : (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
        ((g * (g⁻¹ * eb * g) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hgD, Units.val_mul, coe_diagTau_eq_diagonal]
    rw [h1, ← Units.val_mul]
    congr 1
    group
  have hebfr : ∀ i, (eb : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = ![τ, τ ^ 2, 1] i • fr i :=
    mulVec_col_of_conj hegD
  have hdinj : Function.Injective (![τ, τ ^ 2, 1] : Fin 3 → K) := by
    have hv : (![τ, τ ^ 2, 1] : Fin 3 → K) = fun i => τ ^ ((i + 1 : Fin 3) : ℕ) := by
      funext i
      fin_cases i <;> simp
    rw [hv]
    exact (tau_pow_injective hτ hτ1).comp (add_left_injective 1)
  have hframe : ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∀ i, ∃ c : K,
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = c • fr i := by
    intro a ha y hy i
    have hc := isPGLAt_commute_of_mem hbL (hAcomm a ha b hbA) hy
    refine exists_smul_of_commute_regular hfrli hdinj hebfr ?_ i
    rw [← Units.val_mul, ← Units.val_mul, hc]
  refine ⟨hA27', ?_, ?_⟩
  ·
    have hcb : Subgroup.zpowers c ⊔ Subgroup.zpowers b ≤ A ⊓ L := by
      refine sup_le (Subgroup.zpowers_le.mpr ⟨?_, hcL⟩) (Subgroup.zpowers_le.mpr ⟨hbA, hbL⟩)
      have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
      exact this.1
    have h9 := card_zpowers_sup_zpowers hb3 hc3 hbc
      (hAcomm b hbA c (by have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
        hAc ▸ Subgroup.mem_zpowers c; exact this.1))
    have hge : 9 ≤ Nat.card (A ⊓ L : Subgroup G) := h9 ▸ Subgroup.card_le_of_le hcb
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 27 := hA27' ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card (A ⊓ L : Subgroup G) ≠ 27 := by
      intro h27
      have hAL : A ≤ L := by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ L ≤ A) (by rw [h27, hA27'])
        rw [← this]
        exact inf_le_right
      have hev : ∀ a : A, ∃ d : Fin 3 → K, ∀ i,
          ((e ⟨a, hAL a.2⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = d i • fr i := by
        intro a
        have hy := isPGLAt_of_mem e hπ (hAL a.2)
        choose d hd using hframe a a.2 _ hy
        exact ⟨d, hd⟩
      choose d hd using hev
      have hd3 : ∀ a i, d a i ^ 3 = 1 := by
        intro a i
        have h1 := pow_mulVec_of_eigen (hd a i) 3
        have h2 : ((e ⟨a, hAL a.2⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← map_pow]
          have : (⟨a, hAL a.2⟩ : L) ^ 3 = 1 :=
            Subtype.ext (by rw [Subgroup.coe_pow, hA.1.2 a a.2]; rfl)
          rw [this, map_one, Subgroup.coe_one, Units.val_one]
        rw [h2, Matrix.one_mulVec] at h1
        have := smul_left_injective K (hfrli.ne_zero i)
          (show (1 : K) • fr i = d a i ^ 3 • fr i by rw [one_smul]; exact h1)
        exact this.symm
      have hdet : ∀ a, d a 0 * d a 1 * d a 2 = 1 := by
        intro a
        rw [← det_eq_prod_of_eigen hfrli (hd a)]
        exact ((mem_slPi_iff hπ).mp (e ⟨a, hAL a.2⟩).2).2
      have hd0 : ∀ a i, d a i ≠ 0 := fun a i h0 => by
        have := hd3 a i
        rw [h0] at this
        norm_num at this
      let F : A → rootsOfUnity 3 K × rootsOfUnity 3 K := fun a =>
        (⟨Units.mk0 (d a 0) (hd0 a 0), (mem_rootsOfUnity 3 _).mpr (Units.ext (by
          rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd3, Units.val_one]))⟩,
        ⟨Units.mk0 (d a 1) (hd0 a 1), (mem_rootsOfUnity 3 _).mpr (Units.ext (by
          rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd3, Units.val_one]))⟩)
      have hFinj : Function.Injective F := by
        intro a a' haa'
        simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at haa'
        obtain ⟨h0, h1⟩ := haa'
        have e0 : d a 0 = d a' 0 := congrArg Units.val h0
        have e1 : d a 1 = d a' 1 := congrArg Units.val h1
        have e2 : d a 2 = d a' 2 := by
          have h01 : d a 0 * d a 1 ≠ 0 := mul_ne_zero (hd0 a 0) (hd0 a 1)
          have h' := hdet a'
          rw [← e0, ← e1] at h'
          exact mul_left_cancel₀ h01 ((hdet a).trans h'.symm)
        have hall : ∀ i, d a i = d a' i := by
          intro i
          fin_cases i
          · exact e0
          · exact e1
          · exact e2
        have heq := eq_of_mulVec_eq_of_linearIndependent hfrli (M := ((e ⟨a, hAL a.2⟩ :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (N := ((e ⟨a', hAL a'.2⟩ :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) fun i => by rw [hd, hd, hall i]
        have h3 : e ⟨a, hAL a.2⟩ = e ⟨a', hAL a'.2⟩ := Subtype.ext (Units.ext heq)
        have h4 : (a : G) = a' := congrArg (fun x : L => (x : G)) (e.injective h3)
        exact Subtype.ext h4
      have hle := Nat.card_le_card_of_injective F hFinj
      rw [Nat.card_prod, hA27'] at hle
      have h3 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
      have : Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) ≤ 9 :=
        (Nat.mul_le_mul h3 h3).trans (by norm_num)
      omega
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card
      (A ⊓ L : Subgroup G) ∣ 3 ^ 3 by rwa [show (3 : ℕ) ^ 3 = 27 by norm_num])
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [hk'] at hge; norm_num at hge
    · rw [hk'] at hge; norm_num at hge
    · rw [hk']; norm_num
    · rw [hk'] at hne; norm_num at hne
  ·
    set D : Subgroup (GL (Fin 3) K) :=
      E.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hD
    have hDmap : D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = E := by
      apply le_antisymm
      · rintro _ ⟨d, hd, rfl⟩
        exact hd.1
      · rintro _ ⟨a, rfl⟩
        obtain ⟨y, hy⟩ := hpgl a a.2
        refine ⟨y, ⟨?_, hy.1⟩, ?_⟩
        · change (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E
          exact mk_mem_range_pglHom a.2 hy
        · rw [QuotientGroup.mk'_apply, pglHom_apply a hy]
    have hTC : IsTypeC π (p ^ f) K D := by
      refine ⟨inf_le_right, fun d hd => pow_three_mem_of_mk (range_pglHom_pow hA.1.2 _ hd.1), ?_,
        fr, hfrli, fun d hd i => ?_⟩
      · rw [hDmap]
        exact hE9
      · obtain ⟨a, ha, hy⟩ := exists_isPGLAt_of_mk_mem hd.2 hd.1
        exact hframe a ha d hy i
    refine ⟨fun x _ => mem_normalizer_of_normal x, π, p, f, K, inferInstance, hK, hq, e, D, hTC,
      fun x => ?_, fun y hy => ?_⟩
    · obtain ⟨y, hy⟩ := hpgl x x.2
      refine ⟨y, ⟨mk_mem_range_pglHom x.2 hy, hy.1⟩, fun z => ?_⟩
      have := hy.2 (e z)
      rw [slAct_apply, MulEquiv.symm_apply_apply] at this
      exact this
    · obtain ⟨a, ha, hya⟩ := exists_isPGLAt_of_mk_mem hy.2 hy.1
      refine ⟨⟨a, ha⟩, fun z => ?_⟩
      have := hya.2 (e z)
      rw [slAct_apply, MulEquiv.symm_apply_apply] at this
      exact this

omit [Finite G] in
theorem isPGLAt_pow {e : L ≃* slPi π 3 (p ^ f) K} {g : G} {y : GL (Fin 3) K}
    (hy : IsPGLAt e g y) (n : ℕ) : IsPGLAt e (g ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact isPGLAt_of_mem_centralizer e (Subgroup.one_mem _)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact isPGLAt_mul e ih hy

omit [Finite G] in
theorem mem_zPi_of_isPGLAt (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {g : G} (hg : g ∈ Subgroup.centralizer (L : Set G))
    {y : GL (Fin 3) K} (hy : IsPGLAt e g y) : y ∈ zPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h1 := isPGLAt_inv_mul_mem hK hq (isPGLAt_of_mem_centralizer e hg) hy
  rw [inv_one, one_mul] at h1
  rw [zPi_eq hπ hq' hτ hτ1]
  exact ⟨hy.1, h1⟩

omit [Finite G] in
theorem pow_three_mem_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {g : G} (hg : g ^ 3 = 1) {y : GL (Fin 3) K}
    (hy : IsPGLAt e g y) : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
  have h := isPGLAt_pow hy 3
  rw [hg] at h
  exact mem_zPi_of_isPGLAt hK hq (Subgroup.one_mem _) h

omit [Finite G] in
theorem exists_regular_lift (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {A : Subgroup G} {hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y}
    {b : Fin 3 → (Fin 3 → K)} {z : GL (Fin 3) K}
    (hz : (z : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {d : Fin 3 → K} (hd : Function.Injective d)
    (hzb : ∀ i, (z : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i) :
    ∃ a ∈ A, ∃ y, IsPGLAt e a y ∧ ∃ d' : Fin 3 → K, Function.Injective d' ∧
      ∀ i, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d' i • b i := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨y, hy⟩ := hpgl a a.2
  rw [pglHom_apply a hy, QuotientGroup.eq] at ha
  obtain ⟨μ, hμ⟩ := ha
  have hyz : y = z * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ := by
    rw [map_inv, hμ]
    group
  refine ⟨a, a.2, y, hy, fun i => (μ⁻¹ : Kˣ) * d i, ?_, fun i => ?_⟩
  · intro i j hij
    exact hd (mul_left_cancel₀ (Units.ne_zero _) hij)
  · rw [hyz, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, hzb, smul_smul]

omit [Finite G] in
theorem false_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {c : G}
    (hc3 : orderOf c = 3) (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) (hAL : A ⊓ L ≤ Subgroup.zpowers c)
    {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    (hframe : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHom hK hq A hpgl).range → ∀ i, ∃ c' : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c' • b i)
    {z : GL (Fin 3) K}
    (hz : (z : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {d : Fin 3 → K} (hd : Function.Injective d)
    (hzb : ∀ i, (z : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  obtain ⟨a, ha, y, hy, d', hd', hyb⟩ := exists_regular_lift hK hq hz hd hzb
  have hy3 := pow_three_mem_zPi hK hq (hA.1.2 a ha) hy
  have h1 := type1_of_regular hK hq hy.1 hy3 hb hd' hyb
  obtain ⟨l, hl, hyl⟩ := exists_inner_of_type1 hK hq hy.1 h1
  obtain ⟨μ, -, hylμ, -⟩ := exists_det_eq_cube_of_inner hK hq hy.1 hl hyl
  have hlb : ∀ i, (l : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = ((μ⁻¹ : Kˣ) * d' i) • b i := by
    intro i
    have : l = y * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ := by rw [map_inv, hylμ]; group
    rw [this, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, hyb, smul_smul]
  have hdl : Function.Injective fun i => ((μ⁻¹ : Kˣ) : K) * d' i := fun i j hij =>
    hd' (mul_left_cancel₀ (Units.ne_zero _) hij)
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy3
  have hl3 : (l : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have hcube : ∀ i, (((μ⁻¹ : Kˣ) : K) * d' i) ^ 3 = (μ⁻¹ : Kˣ) ^ 3 * ℓ := by
      intro i
      have h := pow_mulVec_of_eigen (hyb i) 3
      rw [← Units.val_pow_eq_pow_val, ← hℓ, coe_scalar_eq_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec] at h
      rw [mul_pow, ← (smul_left_injective K (hb.ne_zero i) h)]
    have hprod := prod_eq_of_injective_of_cube hτ hτ1 hdl hcube
    have hdet : (l : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hl).2
    rw [det_eq_prod_of_eigen hb hlb] at hdet
    rw [hdet] at hprod
    apply eq_of_mulVec_eq_of_linearIndependent hb
    intro i
    rw [pow_mulVec_of_eigen (hlb i), hcube, ← hprod, one_smul, Matrix.one_mulVec]
  set v : G := (e.symm ⟨l, hl⟩ : G) with hv
  have hvL : v ∈ L := (e.symm ⟨l, hl⟩).2
  have hvA : ∀ a' ∈ A, a' * v = v * a' := by
    intro a' ha'
    obtain ⟨y', hy'⟩ := hpgl a' ha'
    have hy'b : ∀ i, ∃ c' : K, (y' : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c' • b i :=
      hframe y' (mk_mem_range_pglHom ha' hy')
    choose c' hc' using hy'b
    have hcomm := commute_of_eigen hb hc' hlb
    have h2 := hy'.2 ⟨l, hl⟩
    have h3 : y' * l * y'⁻¹ = l := by
      rw [← Units.val_mul, ← Units.val_mul] at hcomm
      rw [Units.ext hcomm, mul_inv_cancel_right]
    rw [h3] at h2
    have h4 : slAct e ⟨a', mem_normalizer_of_normal a'⟩ ⟨l, hl⟩ = ⟨l, hl⟩ := Subtype.ext h2
    rw [slAct_apply] at h4
    have h5 := congrArg (fun s => (e.symm s : G)) h4
    simp only [MulEquiv.symm_apply_apply] at h5
    change a' * v * a'⁻¹ = v at h5
    calc a' * v = a' * v * a'⁻¹ * a' := by group
      _ = v * a' := by rw [h5]
  have hv3 : v ^ 3 = 1 := by
    rw [hv, ← Subgroup.coe_pow, ← map_pow]
    have : (⟨l, hl⟩ : slPi π 3 (p ^ f) K) ^ 3 = 1 := Subtype.ext (Units.ext (by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hl3, Subgroup.coe_one, Units.val_one]))
    rw [this, map_one, Subgroup.coe_one]
  have hvAm : v ∈ A := mem_of_maximal_of_commute hA hv3 fun a' ha' => hvA a' ha'
  have hvc : v ∈ Subgroup.zpowers c := hAL ⟨hvAm, hvL⟩
  have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
    rw [← hLC] at hvc
    exact hvc.2
  have hls : (l : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    have hπ' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
    refine mem_statedScalars_of_commute hπ hπ' hτ hτ1 fun x hx => ?_
    obtain ⟨m, hm⟩ := e.surjective ⟨x, hx⟩
    have h1 : (⟨v, hvL⟩ : L) * m = m * ⟨v, hvL⟩ :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hvC _ m.2).symm)
    have h2 := congrArg (fun s : L => ((e s : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) h1
    have hev : e ⟨v, hvL⟩ = ⟨l, hl⟩ := by
      rw [show (⟨v, hvL⟩ : L) = e.symm ⟨l, hl⟩ from Subtype.ext rfl, MulEquiv.apply_symm_apply]
    simp only [map_mul, Subgroup.coe_mul, hm, hev] at h2
    exact h2
  obtain ⟨κ, hκ⟩ := hls
  have h0 := hlb 0
  have h1 := hlb 1
  rw [← hκ, coe_scalar_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at h0 h1
  have e0 := smul_left_injective K (hb.ne_zero 0) h0
  have e1 := smul_left_injective K (hb.ne_zero 1) h1
  exact absurd (hdl (e0.symm.trans e1)) (by decide)

end CaseI

end CFSG.RankThree.PartTwo.Sec4
