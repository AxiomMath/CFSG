module

public import CFSG.RankThree.GF2n.Smith81.S81UGen
public import CFSG.RankThree.GF2n.Smith81.S81NModel2
public import CFSG.RankThree.GF2n.Smith81.S81UPureComb

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

private theorem h86_tInv2_matrix : ((tInv2 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
    Matrix.transvection (0 : Fin 6) 1 1 * Matrix.transvection (2 : Fin 6) 3 1 := by
  simp only [tInv2, tInv1, Units.val_mul, transvGL_val]

private theorem h86_tv_unitary (hσ : ∀ c, σ (σ c) = c) {a b : Fin 6} (hb : b = partner a)
    {c : F} (hc : σ c = c) :
    conjTr σ (Matrix.transvection a b c) * hypGram F * Matrix.transvection a b c = hypGram F := by
  subst hb
  exact transvection_long_unitary hσ a hc

private theorem h86_unitary_mul {A B : Matrix (Fin 6) (Fin 6) F}
    (hA : conjTr σ A * hypGram F * A = hypGram F) (hB : conjTr σ B * hypGram F * B = hypGram F) :
    conjTr σ (A * B) * hypGram F * (A * B) = hypGram F := by
  rw [conjTr_mul]
  calc conjTr σ B * conjTr σ A * hypGram F * (A * B)
      = conjTr σ B * (conjTr σ A * hypGram F * A) * B := by simp only [Matrix.mul_assoc]
    _ = conjTr σ B * hypGram F * B := by rw [hA]
    _ = hypGram F := hB

theorem tInv2_unitary (hσ : ∀ c, σ (σ c) = c) :
    conjTr σ ((tInv2 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * hypGram F *
      ((tInv2 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = hypGram F := by
  rw [h86_tInv2_matrix]
  exact h86_unitary_mul
    (h86_tv_unitary hσ (a := (0 : Fin 6)) (b := 1) (by decide) (map_one σ))
    (h86_tv_unitary hσ (a := (2 : Fin 6)) (b := 3) (by decide) (map_one σ))

theorem tInv2_det : ((tInv2 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  rw [h86_tInv2_matrix, Matrix.det_mul, Matrix.det_transvection_of_ne (0 : Fin 6) 1 (by decide) 1,
    Matrix.det_transvection_of_ne (2 : Fin 6) 3 (by decide) 1, mul_one]

private theorem h86_sq_pair {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * (x * y) * y := by rw [← hxy]
    _ = x * x * (y * y) := by simp only [mul_assoc]
    _ = 1 := by rw [hx, hy, one_mul]

theorem tInv2_mul_self : tInv2 F * tInv2 F = 1 := by
  have h2 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, CharTwo.two_eq_zero]
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), transvGL F i j hij 0 = 1 := by
    intro i j hij
    apply Units.ext
    simp only [transvGL_val, Matrix.transvection_zero, Units.val_one]
  have hsq : ∀ (i j : Fin 6) (hij : i ≠ j), transvGL F i j hij 1 * transvGL F i j hij 1 = 1 := by
    intro i j hij
    rw [transvGL_mul_same, h2, hz]
  unfold tInv2 tInv1
  exact h86_sq_pair (hsq 0 1 (by decide)) (hsq 2 3 (by decide))
    (transvGL_commute 0 1 2 3 (by decide) (by decide) (by decide) (by decide) 1 1)

@[expose] noncomputable def tSU2 (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) : SUid σ 6 :=
  ⟨frameGL σ ω hω * tInv2 F * (frameGL σ ω hω)⁻¹,
    frame_conj_mem_SUid hσ.invol hω tInv2_det (tInv2_unitary hσ.invol)⟩

@[expose] def adm2 (a b : Fin 6) : Prop := a ≠ 1 ∧ a ≠ 3 ∧ b ≠ 0 ∧ b ≠ 2

instance (a b : Fin 6) : Decidable (adm2 a b) :=
  inferInstanceAs (Decidable (a ≠ 1 ∧ a ≠ 3 ∧ b ≠ 0 ∧ b ≠ 2))

private theorem h86_comm_of {X x y : GL (Fin 6) F} (hx : X * x = x * X) (hy : X * y = y * X) :
    X * (x * y) = x * y * X := by
  calc X * (x * y) = (X * x) * y := (mul_assoc _ _ _).symm
    _ = (x * X) * y := by rw [hx]
    _ = x * (X * y) := mul_assoc _ _ _
    _ = x * (y * X) := by rw [hy]
    _ = x * y * X := (mul_assoc _ _ _).symm

theorem adm2_comm (a b : Fin 6) (hab : a ≠ b) (h : adm2 a b) (c : F) :
    transvGL F a b hab c * tInv2 F = tInv2 F * transvGL F a b hab c := by
  have h' : a ≠ 1 ∧ a ≠ 3 ∧ b ≠ 0 ∧ b ≠ 2 := h
  obtain ⟨h1, h3, h0, h2⟩ := h'
  have hx := transvGL_commute a b 0 1 hab (by decide) h0 (Ne.symm h1) c 1
  have hy := transvGL_commute a b 2 3 hab (by decide) h2 (Ne.symm h3) c 1
  unfold tInv2 tInv1
  exact h86_comm_of hx hy

theorem adm2_pair (a b : Fin 6) (h : adm2 a b) : adm2 (partner b) (partner a) := by
  revert a b
  decide

private theorem h86_cover_key : ∀ J : Finset (Fin 6), J.card = 3 →
    ∃ a ∈ J, ∃ b, b ∉ J ∧ (a ≠ 1 ∧ a ≠ 3 ∧ b ≠ 0 ∧ b ≠ 2) := by
  decide

theorem adm2_cover (I : Set.powersetCard (Fin 6) 3) : ∃ a ∈ I.val, ∃ b, b ∉ I.val ∧ adm2 a b := by
  obtain ⟨a, ha, b, hb, h⟩ := h86_cover_key I.val (Set.powersetCard.mem_iff.mp I.property)
  exact ⟨a, ha, b, hb, h⟩

private theorem h87_Nop_ub {a b : Fin 6} (hab : a ≠ b) (i j k i' j' k' : Fin 6)
    (hij : i < j) (hjk : j < k) (hij' : i' < j') (hjk' : j' < k')
    (hc : b ∈ ({i, j, k} : Finset (Fin 6))) (ha : a ∉ ({i, j, k} : Finset (Fin 6)))
    (he : insert a (({i, j, k} : Finset (Fin 6)).erase b) = {i', j', k'}) :
    Nop F a b hab (ub F i j k hij hjk) = ub F i' j' k' hij' hjk' := by
  unfold ub
  rw [Nop_cubeBasis]
  split_ifs with h
  · congr 1
    exact Subtype.ext he
  · exact (h ⟨hc, ha⟩).elim

private theorem h87_mem_ker (j : Fin 12) : kerG2 F j ∈ LinearMap.ker (rho F (tInv2 F) - 1) := by
  rw [(ker_range_eq2 (K := F)).1]
  exact Submodule.subset_span (Set.mem_range_self j)

private theorem h87_mem_range (j : Fin 8) :
    ranG2 F j ∈ LinearMap.range (rho F (tInv2 F) - 1) := by
  rw [(ker_range_eq2 (K := F)).2]
  exact Submodule.subset_span (Set.mem_range_self j)

theorem covC2_gens : ∀ u ∈ Set.range (kerG2 F), u ∈ LinearMap.range (rho F (tInv2 F) - 1) ∨
    ∃ (a b : Fin 6) (hab : a ≠ b), adm2 a b ∧ ∃ v ∈ LinearMap.ker (rho F (tInv2 F) - 1),
      Nop F a b hab v = u := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Or.inl (h87_mem_range 0)
  · exact Or.inr ⟨4, 5, by decide, by decide, kerG2 F 2, h87_mem_ker 2,
      h87_Nop_ub (a := 4) (b := 5) (by decide) 0 1 5 0 1 4 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨5, 4, by decide, by decide, kerG2 F 1, h87_mem_ker 1,
      h87_Nop_ub (a := 5) (b := 4) (by decide) 0 1 4 0 1 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inl (h87_mem_range 1)
  · exact Or.inl (h87_mem_range 2)
  · exact Or.inl (h87_mem_range 3)
  · exact Or.inl (h87_mem_range 4)
  · exact Or.inr ⟨4, 5, by decide, by decide, kerG2 F 8, h87_mem_ker 8,
      h87_Nop_ub (a := 4) (b := 5) (by decide) 2 3 5 2 3 4 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨5, 4, by decide, by decide, kerG2 F 7, h87_mem_ker 7,
      h87_Nop_ub (a := 5) (b := 4) (by decide) 2 3 4 2 3 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inl (h87_mem_range 5)
  · exact Or.inl (h87_mem_range 6)
  · exact Or.inl (h87_mem_range 7)

theorem pos2_pair (a b : Fin 6) (h : pos2 a b) : pos2 (partner b) (partner a) := by
  have key : ∀ x y : Fin 6, pos2 x y → pos2 (partner y) (partner x) := by decide
  exact key a b h

theorem pos2_adm (a b : Fin 6) (h : pos2 a b) : adm2 a b := by
  have key : ∀ x y : Fin 6, pos2 x y → adm2 x y := by decide
  exact key a b h

theorem hUC2 (a b : Fin 6) (hab : a ≠ b) (c : F) (h : pos2 a b) :
    ∀ ξ ∈ LinearMap.ker (rho F (tInv2 F) - 1),
      rho F (transvGL F a b hab c) ξ - ξ ∈ LinearMap.range (rho F (tInv2 F) - 1) := by
  have hp : lev2 a < lev2 b := by
    have key : ∀ x y : Fin 6, pos2 x y → lev2 x < lev2 y := by decide
    exact key a b h
  intro ξ hξ
  exact model2_hUC (K := F) (u := transvGL F a b hab c) ⟨a, b, hab, c, hp, rfl⟩ ξ hξ

theorem hUfix2 : ∀ ξ ∈ LinearMap.ker (rho F (tInv2 F) - 1),
    (∀ (a b : Fin 6) (hab : a ≠ b) (c : F), pos2 a b → rho F (transvGL F a b hab c) ξ = ξ) →
      ξ ∈ LinearMap.range (rho F (tInv2 F) - 1) := by
  intro ξ hξ hfix
  refine model2_hUfix (K := F) ξ hξ ?_
  rintro u ⟨a, b, hab, c, hpos, rfl⟩
  have hp : pos2 a b := by
    have key : ∀ x y : Fin 6, lev2 x < lev2 y → pos2 x y := by decide
    exact key a b hpos
  exact hfix a b hab c hp

@[expose] def posP2 (a b : Fin 6) : Prop := lev2 a < lev2 b ∧ b ≠ partner a

instance (a b : Fin 6) : Decidable (posP2 a b) :=
  inferInstanceAs (Decidable (lev2 a < lev2 b ∧ b ≠ partner a))

theorem lev2_le (i : Fin 6) : lev2 i ≤ 3 := by
  revert i
  decide

theorem posP2_lev (a b : Fin 6) (h : posP2 a b) :
    lev2 a < lev2 b ∧ lev2 (partner b) < lev2 (partner a) := by
  have key : ∀ a b : Fin 6, posP2 a b →
      lev2 a < lev2 b ∧ lev2 (partner b) < lev2 (partner a) := by
    decide
  exact key a b h

theorem posP2_ne (a b : Fin 6) (h : posP2 a b) : b ≠ partner a := h.2

theorem exists_norm_one_ne_one (hσ : IsUnitaryInvolution σ) : ∃ μ : F, σ μ * μ = 1 ∧ μ ≠ 1 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (map_zero σ)
  have hsc0 : σ c ≠ 0 := by
    intro h
    apply hc0
    have h2 := congrArg σ h
    rw [hσ.invol, map_zero σ] at h2
    exact h2
  refine ⟨c / σ c, ?_, ?_⟩
  · rw [map_div₀ σ, hσ.invol, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hc0 hsc0)]
    ring
  · intro h
    apply hc
    exact ((div_eq_one_iff_eq hsc0).mp h).symm

private theorem h89_ne_zero {μ : F} (hμ : σ μ * μ = 1) : μ ≠ 0 := by
  rintro rfl
  simp at hμ

private theorem h89_ne_inv {μ : F} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) : μ ≠ μ⁻¹ := by
  intro h
  apply hμ1
  have h1 : μ * μ = 1 := by
    calc μ * μ = μ * μ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hμ0
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (μ - 1) * (μ - 1) = 0 := by linear_combination h1 - (μ - 1) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)

private theorem h89_one_ne_inv {ν : F} (hν1 : ν ≠ 1) : (1 : F) ≠ ν⁻¹ :=
  fun h => hν1 (inv_eq_one.mp h.symm)

private theorem h89_inv_ne_one {ν : F} (hν1 : ν ≠ 1) : ν⁻¹ ≠ 1 :=
  fun h => hν1 (inv_eq_one.mp h)

private theorem h89_posP2_adm (a b : Fin 6) (h : posP2 a b) : adm2 a b := by
  have key : ∀ a b : Fin 6, posP2 a b → adm2 a b := by
    decide
  exact key a b h

private theorem h89_posP2_list (a b : Fin 6) (h : posP2 a b) :
    (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 0 ∧ b = 5) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 4) ∨
      (a = 2 ∧ b = 5) ∨ (a = 4 ∧ b = 1) ∨ (a = 4 ∧ b = 3) ∨ (a = 5 ∧ b = 1) ∨ (a = 5 ∧ b = 3) := by
  have key : ∀ a b : Fin 6, posP2 a b →
      (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 0 ∧ b = 5) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 4) ∨
      (a = 2 ∧ b = 5) ∨ (a = 4 ∧ b = 1) ∨ (a = 4 ∧ b = 3) ∨ (a = 5 ∧ b = 1) ∨ (a = 5 ∧ b = 3) := by
    decide
  exact key a b h

private theorem h89_A_ne {μ : F} (hμ0 : μ ≠ 0) :
    ∀ i : Fin 6, (![μ, μ, μ⁻¹, μ⁻¹, 1, 1] : Fin 6 → F) i ≠ 0 := by
  intro i
  fin_cases i
  · exact hμ0
  · exact hμ0
  · exact inv_ne_zero hμ0
  · exact inv_ne_zero hμ0
  · exact one_ne_zero
  · exact one_ne_zero

private theorem h89_A_hu {μ : F} (hμ : σ μ * μ = 1) :
    ∀ i : Fin 6, σ ((![μ, μ, μ⁻¹, μ⁻¹, 1, 1] : Fin 6 → F) i) *
      (![μ, μ, μ⁻¹, μ⁻¹, 1, 1] : Fin 6 → F) (partner i) = 1 := by
  have hinv : σ (μ⁻¹) * μ⁻¹ = 1 := by
    rw [map_inv₀ σ, ← mul_inv, hμ, inv_one]
  intro i
  fin_cases i
  · exact hμ
  · exact hμ
  · exact hinv
  · exact hinv
  · show σ 1 * 1 = 1
    rw [map_one σ, mul_one]
  · show σ 1 * 1 = 1
    rw [map_one σ, mul_one]

private theorem h89_A_det {μ : F} (hμ0 : μ ≠ 0) :
    ∏ i, (![μ, μ, μ⁻¹, μ⁻¹, 1, 1] : Fin 6 → F) i = 1 := by
  have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
  rw [Fin.prod_univ_six]
  show μ * μ * μ⁻¹ * μ⁻¹ * 1 * 1 = 1
  linear_combination (μ * μ⁻¹ + 1) * hinv

private theorem h89_B_ne {ν : F} (hν0 : ν ≠ 0) :
    ∀ i : Fin 6, (![1, 1, 1, 1, ν, ν⁻¹] : Fin 6 → F) i ≠ 0 := by
  intro i
  fin_cases i
  · exact one_ne_zero
  · exact one_ne_zero
  · exact one_ne_zero
  · exact one_ne_zero
  · exact hν0
  · exact inv_ne_zero hν0

private theorem h89_B_hu {ν : F} (hν : σ ν = ν) (hν0 : ν ≠ 0) :
    ∀ i : Fin 6, σ ((![1, 1, 1, 1, ν, ν⁻¹] : Fin 6 → F) i) *
      (![1, 1, 1, 1, ν, ν⁻¹] : Fin 6 → F) (partner i) = 1 := by
  intro i
  fin_cases i
  · show σ 1 * 1 = 1
    rw [map_one σ, mul_one]
  · show σ 1 * 1 = 1
    rw [map_one σ, mul_one]
  · show σ 1 * 1 = 1
    rw [map_one σ, mul_one]
  · show σ 1 * 1 = 1
    rw [map_one σ, mul_one]
  · show σ ν * ν⁻¹ = 1
    rw [hν, mul_inv_cancel₀ hν0]
  · show σ (ν⁻¹) * ν = 1
    rw [map_inv₀ σ, hν, inv_mul_cancel₀ hν0]

private theorem h89_B_det {ν : F} (hν0 : ν ≠ 0) :
    ∏ i, (![1, 1, 1, 1, ν, ν⁻¹] : Fin 6 → F) i = 1 := by
  have hinv : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν0
  rw [Fin.prod_univ_six]
  show 1 * 1 * 1 * 1 * ν * ν⁻¹ = 1
  linear_combination hinv

private theorem h89_comm_mul {G : Type*} [Group G] {D x y : G} (hx : D * x = x * D)
    (hy : D * y = y * D) : D * (x * y) = x * y * D := by
  rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

private theorem h89_gen (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * tInv2 F * (frameGL σ ω hω)⁻¹)
    {a b : Fin 6} (hab : a ≠ b) (hb : b ≠ partner a) (hadm : adm2 a b)
    (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, σ (d i) * d (partner i) = 1)
    (hdet : ∏ i, d i = 1) (h01 : d 0 = d 1) (h23 : d 2 = d 3) (hne : d a ≠ d b) (c : F) :
    ∃ A ∈ Gcent σ t, ∃ B ∈ Gcent σ t, gShort hσ hω hab hb c = ⁅A, B⁆ := by
  have hx : ∀ e : F, transvGL F a b hab e * tInv2 F = tInv2 F * transvGL F a b hab e :=
    fun e => adm2_comm a b hab hadm e
  have hx' : ∀ e : F, transvGL F (partner b) (partner a) (partner_ne_partner hab) e * tInv2 F =
      tInv2 F * transvGL F (partner b) (partner a) (partner_ne_partner hab) e :=
    fun e => adm2_comm (partner b) (partner a) (partner_ne_partner hab) (adm2_pair a b hadm) e
  have hdx : (diagGL d hd : GL (Fin 6) F) * tInv2 F = tInv2 F * (diagGL d hd : GL (Fin 6) F) := by
    unfold tInv2 tInv1
    exact h89_comm_mul (diagGL_commute_transvGL d hd 0 1 (by decide) 1 h01)
      (diagGL_commute_transvGL d hd 2 3 (by decide) 1 h23)
  exact gShort_eq_comm hσ hω t (tInv2 F) ht hab hb hx hx' d hd hu hdet hdx hne c

theorem posP2_comm (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * tInv2 F * (frameGL σ ω hω)⁻¹)
    {μ : F} (hμ : σ μ * μ = 1) (hμ1 : μ ≠ 1) {ν : F} (hν : σ ν = ν) (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) :
    ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a), posP2 a b → ∀ c : F,
      ∃ A ∈ Gcent σ t, ∃ B ∈ Gcent σ t, gShort hσ hω hab hb c = ⁅A, B⁆ := by
  intro a b hab hb hpos c
  have hadm : adm2 a b := h89_posP2_adm a b hpos
  have hμ0 : μ ≠ 0 := h89_ne_zero hμ
  rcases h89_posP2_list a b hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h89_gen hσ hω t ht hab hb hadm (![μ, μ, μ⁻¹, μ⁻¹, 1, 1]) (h89_A_ne hμ0) (h89_A_hu hμ)
      (h89_A_det hμ0) rfl rfl (h89_ne_inv hμ0 hμ1) c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl (Ne.symm hν1) c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl (h89_one_ne_inv hν1) c
  · exact h89_gen hσ hω t ht hab hb hadm (![μ, μ, μ⁻¹, μ⁻¹, 1, 1]) (h89_A_ne hμ0) (h89_A_hu hμ)
      (h89_A_det hμ0) rfl rfl (h89_ne_inv hμ0 hμ1).symm c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl (Ne.symm hν1) c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl (h89_one_ne_inv hν1) c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl hν1 c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl hν1 c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl (h89_inv_ne_one hν1) c
  · exact h89_gen hσ hω t ht hab hb hadm (![1, 1, 1, 1, ν, ν⁻¹]) (h89_B_ne hν0) (h89_B_hu hν hν0)
      (h89_B_det hν0) rfl rfl (h89_inv_ne_one hν1) c

theorem hpure2 : ∀ ξ ∈ LinearMap.range (rho F (tInv2 F) - 1),
    (∀ (a b : Fin 6) (hab : a ≠ b), posP2 a b → rho F (transvGL F a b hab 1) ξ = ξ) → IsPure F ξ := by
  intro ξ hξR hfix
  rw [(ker_range_eq2 (K := F)).2] at hξR
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hξR
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), posP2 i j → rho F (transvGL F i j hij 1) ξ = ξ :=
    fun i j hij hp => hfix i j hij hp
  have hs_eq : ξ = cfm F ξ 21 • ub F 0 2 4 + cfm F ξ 37 • ub F 0 2 5 := by
    apply cfm_ext3
    intro m hm hc'
    rcases exists_mask3 hm hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (simp (config := {decide := true}) [cfm_add, cfm_smul, cfm_ub_mask]; done)
    | (rw [cfm_zero_of_fixed posP2 hz _ hm (by decide)]
       simp (config := {decide := true}) [cfm_add, cfm_smul, cfm_ub_mask]; done)
    | (rw [← hc]
       simp (config := {decide := true}) [ranG2, vA, vB, cfm_add, cfm_smul, cfm_ub_mask,
         Fin.sum_univ_succ, cfm_zero]; done)
  rw [hs_eq]
  exact isPure_comb_024_025 _ _

theorem involModel12_tSU2 [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (h4 : 4 ≤ 2 ^ f)
    {ω : F} (hω : ω + unitaryInvolution F 2 f ω = 1) :
    UInvolModel12 (unitaryInvolution F 2 f)
      (tSU2 (isUnitaryInvolution_unitaryInvolution hF) hω) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨ν, hν, hν0, hν1⟩ := exists_fixed_ne_zero_one hF h4
  obtain ⟨μ, hμ, hμ1⟩ := exists_norm_one_ne_one hσ
  have ht : ((tSU2 hσ hω : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) =
      frameGL (unitaryInvolution F 2 f) ω hω * tInv2 F *
        (frameGL (unitaryInvolution F 2 f) ω hω)⁻¹ := rfl
  have H1 : ∀ (a b : Fin 6) (hab : a ≠ b), adm2 a b → ∀ c : F,
      transvGL F a b hab c * tInv2 F = tInv2 F * transvGL F a b hab c :=
    fun a b hab h c => adm2_comm a b hab h c
  have H2 : ∀ a b : Fin 6, adm2 a b → adm2 (partner b) (partner a) := fun a b h => adm2_pair a b h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact covW_of_F hσ _ (covW_F_of_adm hσ hω _ (tInv2 F) ht adm2 H1 H2 adm2_cover)
  · exact covC_of_F hσ _ (covC_F_of_gens hσ hω _ (tInv2 F) ht adm2 H1 H2
      (Set.range (kerG2 F)) (ker_range_eq2 (K := F)).1.le covC2_gens)
  · obtain ⟨hU, h1, h2⟩ := P3_F_of_pos hσ hω _ (tInv2 F) ht tInv2_mul_self pos2 pos2_pair
      (fun a b hab h c => adm2_comm a b hab (pos2_adm a b h) c)
      (fun a b hab c h => hUC2 a b hab c h) hUfix2
    exact ⟨rootFam hσ hω pos2, P3_of_F hσ _ _ hU h1 h2⟩
  · exact P2_of_roots hσ hω _ (tInv2 F) ht posP2 lev2 lev2_le posP2_lev posP2_ne
      (posP2_comm hσ hω _ ht hμ hμ1 hν hν0 hν1) hpure2

end CFSG.RankThree.GF2n.Smith81.U6Cube
