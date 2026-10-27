module

public import CFSG.Quasithin.H13.VolII16SLNat
public import CFSG.Quasithin.H13.VolII16Central
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13.VolI CFSG.Assembly.LowTwoRank Matrix Subgroup
open scoped commutatorElement

variable {K : Type} [Field K]

theorem diagSL_mul_transvection_comm {n : ℕ} {d : Fin n → K} (hd : ∏ i, d i = 1)
    {i j : Fin n} (hij : i ≠ j) (hdij : d i = d j) (c : K) :
    GL83.I713.diagSL d hd * SpecialLinearGroup.transvection hij c =
      SpecialLinearGroup.transvection hij c * GL83.I713.diagSL d hd := by
  have hne : ∀ a, d a ≠ 0 := by
    intro a ha
    have h0 : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ a) ha
    rw [hd] at h0
    exact one_ne_zero h0
  have hvinv : Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hne a)
  have h := TauCeti.diagonal_mul_transvection_mul_diagonal (i := i) (j := j) (v := d)
    (w := fun i => (d i)⁻¹) (fun a => mul_inv_cancel₀ (hne a)) c
  have hdiag : d i * c * (d j)⁻¹ = c := by
    rw [hdij, mul_comm (d j) c, mul_assoc, mul_inv_cancel₀ (hne j), mul_one]
  rw [hdiag] at h
  apply Subtype.ext
  show (GL83.I713.diagSL d hd : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hij c : Matrix (Fin n) (Fin n) K) =
    (SpecialLinearGroup.transvection hij c : Matrix (Fin n) (Fin n) K) *
      (GL83.I713.diagSL d hd : Matrix (Fin n) (Fin n) K)
  rw [SpecialLinearGroup.transvection_coe]
  change Matrix.diagonal d * Matrix.transvection i j c =
    Matrix.transvection i j c * Matrix.diagonal d
  calc Matrix.diagonal d * Matrix.transvection i j c
      = (Matrix.diagonal d * Matrix.transvection i j c) * 1 := (mul_one _).symm
    _ = (Matrix.diagonal d * Matrix.transvection i j c) *
          (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) := by rw [hvinv]
    _ = ((Matrix.diagonal d * Matrix.transvection i j c) *
          Matrix.diagonal (fun i => (d i)⁻¹)) * Matrix.diagonal d :=
        (mul_assoc _ _ _).symm
    _ = Matrix.transvection i j c * Matrix.diagonal d := by rw [h]

theorem diagSL_mul_comm {n : ℕ} {d e : Fin n → K} (hd : ∏ i, d i = 1)
    (he : ∏ i, e i = 1) :
    GL83.I713.diagSL d hd * GL83.I713.diagSL e he =
      GL83.I713.diagSL e he * GL83.I713.diagSL d hd := by
  apply Subtype.ext
  change Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem closure_centralizers_sl_four {d e : Fin 4 → K} (hd : ∏ i, d i = 1)
    (he : ∏ i, e i = 1) (hd01 : d 0 = d 1) (hd12 : d 1 = d 2) (he12 : e 1 = e 2)
    (he23 : e 2 = e 3) :
    Subgroup.closure {g : SpecialLinearGroup (Fin 4) K |
      g * GL83.I713.diagSL d hd = GL83.I713.diagSL d hd * g ∨
        g * GL83.I713.diagSL e he = GL83.I713.diagSL e he * g} = ⊤ := by
  classical
  set S := {g : SpecialLinearGroup (Fin 4) K |
    g * GL83.I713.diagSL d hd = GL83.I713.diagSL d hd * g ∨
      g * GL83.I713.diagSL e he = GL83.I713.diagSL e he * g} with hS
  have mem1 : ∀ {i j : Fin 4} (hij : i ≠ j), d i = d j → ∀ c : K,
      SpecialLinearGroup.transvection hij c ∈ Subgroup.closure S :=
    fun hij hdij c => Subgroup.subset_closure
      (Or.inl (diagSL_mul_transvection_comm hd hij hdij c).symm)
  have mem2 : ∀ {i j : Fin 4} (hij : i ≠ j), e i = e j → ∀ c : K,
      SpecialLinearGroup.transvection hij c ∈ Subgroup.closure S :=
    fun hij heij c => Subgroup.subset_closure
      (Or.inr (diagSL_mul_transvection_comm he hij heij c).symm)
  have h01 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 1) c ∈ Subgroup.closure S :=
    mem1 (by decide) hd01
  have h10 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 0) c ∈ Subgroup.closure S :=
    mem1 (by decide) hd01.symm
  have h02 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 2) c ∈ Subgroup.closure S :=
    mem1 (by decide) (hd01.trans hd12)
  have h20 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 0) c ∈ Subgroup.closure S :=
    mem1 (by decide) (hd01.trans hd12).symm
  have h12 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 2) c ∈ Subgroup.closure S :=
    mem1 (by decide) hd12
  have h21 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) c ∈ Subgroup.closure S :=
    mem1 (by decide) hd12.symm
  have h13 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 3) c ∈ Subgroup.closure S :=
    mem2 (by decide) (he12.trans he23)
  have h31 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 1) c ∈ Subgroup.closure S :=
    mem2 (by decide) (he12.trans he23).symm
  have h23 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 3) c ∈ Subgroup.closure S :=
    mem2 (by decide) he23
  have h32 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 2) c ∈ Subgroup.closure S :=
    mem2 (by decide) he23.symm
  have hcomm : ∀ {x y : SpecialLinearGroup (Fin 4) K}, x ∈ Subgroup.closure S →
      y ∈ Subgroup.closure S → ⁅x, y⁆ ∈ Subgroup.closure S := fun hx hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have h03 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) c ∈ Subgroup.closure S := by
    intro c
    have h := SpecialLinearGroup.commutatorElement_transvection (i := (0 : Fin 4))
      (j := (1 : Fin 4)) (l := (3 : Fin 4)) (by decide) (by decide) (by decide) c 1
    rw [mul_one] at h
    rw [← h]
    exact hcomm (h01 c) (h13 1)
  have h30 : ∀ c : K,
      SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 0) c ∈ Subgroup.closure S := by
    intro c
    have h := SpecialLinearGroup.commutatorElement_transvection (i := (3 : Fin 4))
      (j := (1 : Fin 4)) (l := (0 : Fin 4)) (by decide) (by decide) (by decide) c 1
    rw [mul_one] at h
    rw [← h]
    exact hcomm (h31 c) (h10 1)
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 c
    | exact h10 c
    | exact h02 c
    | exact h20 c
    | exact h12 c
    | exact h21 c
    | exact h13 c
    | exact h31 c
    | exact h23 c
    | exact h32 c
    | exact h03 c
    | exact h30 c

theorem s16_sl_four_cover_of_order_seven {l : K} (hl : orderOf l = 7)
    {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hR : (FFModel.nat (StatedSL 4 K)).Realizes H ⊤ Z) : Z = ⊥ := by
  classical
  have hl7 : l ^ 7 = 1 := by
    have h := pow_orderOf_eq_one l
    rwa [hl] at h
  have hl1 : l ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hl
    norm_num at hl
  have hl0 : l ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 7 ≠ 0)] at hl7
    exact zero_ne_one hl7
  have hl4 : l ^ 4 ≠ 1 := by
    intro h
    have hdvd : orderOf l ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hl] at hdvd
    norm_num at hdvd
  have hl3 : l ^ 3 ≠ 1 := by
    intro h
    have hdvd : orderOf l ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hl] at hdvd
    norm_num at hdvd
  have hl4ne : l ^ 4 ≠ l := by
    intro h
    have h' : l ^ 3 * l = 1 * l := by
      calc l ^ 3 * l = l ^ 4 := (pow_succ l 3).symm
        _ = l := h
        _ = 1 * l := (one_mul l).symm
    exact hl3 (mul_right_cancel₀ hl0 h')
  obtain ⟨π₀, b₀, hπs, -, hbk, hbe⟩ :=
    topBot_data (D := FFModel.nat (StatedSL 4 K)) rfl rfl hR
  let π : ↥(StatedSL 4 K) →* ↥H := π₀
  let b : W →* Multiplicative (Fin 4 → K) := b₀
  set ψ := specialLinearGroupEquivStatedSL 4 K
  let ρ : SpecialLinearGroup (Fin 4) K →* MulAut W := H.subtype.comp (π.comp ψ.toMonoidHom)
  have hbk' : ∀ w, b w = 1 ↔ w ∈ Z := hbk
  have hρ : ∀ (g : SpecialLinearGroup (Fin 4) K) (w : W),
      Multiplicative.toAdd (b (ρ g w)) =
        (g : Matrix (Fin 4) (Fin 4) K) *ᵥ Multiplicative.toAdd (b w) := fun g w =>
    congrArg Multiplicative.toAdd (hbe (ψ g) w)
  let d : Fin 4 → K := ![l, l, l, l ^ 4]
  let e : Fin 4 → K := ![l ^ 4, l, l, l]
  have hd : ∏ i, d i = 1 := by
    rw [Fin.prod_univ_four]
    show l * l * l * l ^ 4 = 1
    calc l * l * l * l ^ 4 = l ^ 7 := by ring
      _ = 1 := hl7
  have he : ∏ i, e i = 1 := by
    rw [Fin.prod_univ_four]
    show l ^ 4 * l * l * l = 1
    calc l ^ 4 * l * l * l = l ^ 7 := by ring
      _ = 1 := hl7
  have hd1 : ∀ i, d i ≠ 1 := by
    intro i
    fin_cases i
    · simpa [d] using hl1
    · simpa [d] using hl1
    · simpa [d] using hl1
    · simpa [d] using hl4
  have he1 : ∀ i, e i ≠ 1 := by
    intro i
    fin_cases i
    · simpa [e] using hl4
    · simpa [e] using hl1
    · simpa [e] using hl1
    · simpa [e] using hl1
  have hd7 : ∀ i, d i ^ 7 = 1 := by
    have hl47 : (l ^ 4) ^ 7 = 1 := by
      rw [← pow_mul, show 4 * 7 = 7 * 4 by norm_num, pow_mul, hl7, one_pow]
    intro i
    fin_cases i
    · simpa [d] using hl7
    · simpa [d] using hl7
    · simpa [d] using hl7
    · simpa [d] using hl47
  have he7 : ∀ i, e i ^ 7 = 1 := by
    have hl47 : (l ^ 4) ^ 7 = 1 := by
      rw [← pow_mul, show 4 * 7 = 7 * 4 by norm_num, pow_mul, hl7, one_pow]
    intro i
    fin_cases i
    · simpa [e] using hl47
    · simpa [e] using hl7
    · simpa [e] using hl7
    · simpa [e] using hl7
  have hpow : ∀ (v : Fin 4 → K) (hv : ∏ i, v i = 1), (∀ i, v i ^ 7 = 1) →
      ρ (GL83.I713.diagSL v hv) ^ 7 = 1 := by
    intro v hv hv7
    rw [← map_pow]
    have h1 : GL83.I713.diagSL v hv ^ 7 = 1 := by
      apply Subtype.ext
      change (Matrix.diagonal v) ^ 7 = 1
      rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact hv7 i
    rw [h1, map_one]
  have hfpf : ∀ (v : Fin 4 → K) (hv : ∏ i, v i = 1), (∀ i, v i ≠ 1) →
      ∀ w, ρ (GL83.I713.diagSL v hv) w = w → w ∈ Z := by
    intro v hv hv1 w hw
    have h1 := hρ (GL83.I713.diagSL v hv) w
    rw [hw] at h1
    change Multiplicative.toAdd (b w) =
      Matrix.diagonal v *ᵥ Multiplicative.toAdd (b w) at h1
    have h2 : Multiplicative.toAdd (b w) = 0 := funext fun i => by
      have h3 := congrFun h1 i
      rw [Matrix.mulVec_diagonal] at h3
      have h4 : (v i - 1) * Multiplicative.toAdd (b w) i = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (hv1 i))
    exact (hbk' w).1 (Multiplicative.toAdd.injective (by rw [h2, toAdd_one]))
  have hgen : H ≤ Subgroup.closure {x | x * ρ (GL83.I713.diagSL d hd) =
      ρ (GL83.I713.diagSL d hd) * x ∨ x * ρ (GL83.I713.diagSL e he) =
        ρ (GL83.I713.diagSL e he) * x} := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := ψ.surjective γ
    have hx' : ρ g = x := congrArg Subtype.val hγ
    rw [← hx']
    have hle : Subgroup.closure {g : SpecialLinearGroup (Fin 4) K |
        g * GL83.I713.diagSL d hd = GL83.I713.diagSL d hd * g ∨
          g * GL83.I713.diagSL e he = GL83.I713.diagSL e he * g} ≤
        (Subgroup.closure {x | x * ρ (GL83.I713.diagSL d hd) =
          ρ (GL83.I713.diagSL d hd) * x ∨ x * ρ (GL83.I713.diagSL e he) =
            ρ (GL83.I713.diagSL e he) * x}).comap ρ := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact Subgroup.subset_closure (by
        rcases hg with hg | hg
        · left
          rw [← map_mul, hg, map_mul]
        · right
          rw [← map_mul, hg, map_mul])
    exact hle (by
      rw [closure_centralizers_sl_four hd he rfl rfl rfl rfl]
      exact Subgroup.mem_top g)
  exact eq_bot_of_two_fpf (t₁ := ρ (GL83.I713.diagSL d hd))
    (t₂ := ρ (GL83.I713.diagSL e he)) hW2 hZ hcomm
    (π (ψ (GL83.I713.diagSL d hd))).2 (π (ψ (GL83.I713.diagSL e he))).2
    (by rw [← map_mul, ← map_mul, diagSL_mul_comm hd he]) ⟨3, by norm_num⟩
    ⟨3, by norm_num⟩ (hpow d hd hd7) (hpow e he he7)
    (hfpf d hd hd1) (hfpf e he he1) hgen

theorem s16_sl_four_eight_cover [Finite K] (hK : Nat.card K = 8)
    {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (hR : (FFModel.nat (StatedSL 4 K)).Realizes H ⊤ Z) : Z = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ ({0, 1} : Finset K) := by
      intro x _
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hx1 : x = 1 := h x hx0
        simp [hx1]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at hle
    have h2 : ({0, 1} : Finset K).card ≤ 2 := by
      rw [Finset.card_insert_of_notMem (by simp)]
      simp
    omega
  have hl7 : l ^ 7 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one l hl0
    rw [hcard] at h
    norm_num at h
    exact h
  have hl : orderOf l = 7 := by
    have hfact : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact @orderOf_eq_prime K _ l 7 hfact hl7 hl1
  exact s16_sl_four_cover_of_order_seven hl hW2 hZ hcomm hR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
