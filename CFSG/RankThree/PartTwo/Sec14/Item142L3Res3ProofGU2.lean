module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofDickson
public import CFSG.LieType.SeitzGeneration.UnitaryHeisGU2

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open scoped MatrixGroups

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem card_map_eq_card_quotient_ker {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (Y : Subgroup G) : Nat.card (Y.map φ) = Nat.card (Y ⧸ (φ.comp Y.subtype).ker) := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ.comp Y.subtype)).toEquiv,
    MonoidHom.range_comp, Subgroup.range_subtype]

theorem card_map_eq_of_ker_eq {G H₁ H₂ : Type*} [Group G] [Group H₁] [Group H₂]
    (φ₁ : G →* H₁) (φ₂ : G →* H₂) (hk : φ₁.ker = φ₂.ker) (Y : Subgroup G) :
    Nat.card (Y.map φ₁) = Nat.card (Y.map φ₂) := by
  rw [card_map_eq_card_quotient_ker φ₁, card_map_eq_card_quotient_ker φ₂, ← MonoidHom.comap_ker,
    ← MonoidHom.comap_ker, hk]

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def gu2ProjE (h : UnitaryFieldData ℓ f K) : gu2 h →* PGL(Fin 2, K) :=
  ProjGenLinGroup.mk.comp (gu2 h).subtype

theorem ker_gu2ProjE (h : UnitaryFieldData ℓ f K) : (gu2ProjE h).ker = (gu2Proj h).ker := by
  ext g
  rw [mem_ker_gu2Proj, MonoidHom.mem_ker]
  exact ProjGenLinGroup.mk_eq_one

theorem card_map_gu2ProjE (h : UnitaryFieldData ℓ f K) (Y : Subgroup (gu2 h)) :
    Nat.card (Y.map (gu2ProjE h)) = Nat.card (Y.map (gu2Proj h)) :=
  card_map_eq_of_ker_eq _ _ (ker_gu2ProjE h) Y

theorem range_gu2ProjE_le (h : UnitaryFieldData ℓ f K) :
    (gu2ProjE h).range ≤
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  rintro _ ⟨g, rfl⟩
  exact mk_mem_range_toPGL _ (isSquare_of_norm_one h (norm_det_of_mem_gu2 h g.2))

theorem card_image_ge_prim (h : UnitaryFieldData ℓ f K)
    (Y : Subgroup (gu2 h))
    {μ₁ μ₂ ν₁ ν₂ α β : K} (hμ₁ : h.bar μ₁ * μ₁ = 1) (hμ₂ : h.bar μ₂ * μ₂ = 1)
    (hν₁ : h.bar ν₁ * ν₁ = 1) (hν₂ : h.bar ν₂ * ν₂ = 1) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hμ6 : 6 ≤ orderOf (μ₁ / μ₂))
    (hsf : SubfieldFree ℓ f (orderOf (μ₁ / μ₂))) (hν3 : 3 ≤ orderOf (ν₁ / ν₂))
    {A B : gu2 h}
    (hAm : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)])
    (hA : A ∈ Y) (hB : B ∈ Y) :
    ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) ≤ 2 * Nat.card (Y.map (gu2ProjE h)) := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hne : ∀ x : K, h.bar x * x = 1 → x ≠ 0 := fun x hx h0 => by
    rw [h0, mul_zero] at hx
    exact zero_ne_one hx
  have hμ₁0 := hne _ hμ₁
  have hμ₂0 := hne _ hμ₂
  have hν₁0 := hne _ hν₁
  have hν₂0 := hne _ hν₂
  have hbα : h.bar α ≠ 0 := by simpa using hα
  have hbβ : h.bar β ≠ 0 := by simpa using hβ
  have hρ : μ₁ / μ₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hμ6
    omega
  have hρν : ν₁ / ν₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hν3
    omega
  have hμ12 : μ₁ ≠ μ₂ := fun h1 => hρ (by rw [h1, div_self hμ₂0])
  have hν12 : ν₁ ≠ ν₂ := fun h1 => hρν (by rw [h1, div_self hν₂0])
  have hnorm : ∀ x y : K, h.bar x * x = 1 → h.bar y * y = 1 → h.bar ((x * y)⁻¹) * (x * y)⁻¹ = 1 :=
    fun x y hx hy => by
      rw [map_inv₀, map_mul, ← mul_inv]
      have : h.bar x * h.bar y * (x * y) = 1 := by
        linear_combination (h.bar y * y) * hx + hy
      rw [this, inv_one]
  obtain ⟨s, hs⟩ := isSquare_of_norm_one h (hnorm μ₁ μ₂ hμ₁ hμ₂)
  obtain ⟨s', hs'⟩ := isSquare_of_norm_one h (hnorm ν₁ ν₂ hν₁ hν₂)
  have hss : s * s * (μ₁ * μ₂) = 1 := by
    rw [← hs]
    exact inv_mul_cancel₀ (mul_ne_zero hμ₁0 hμ₂0)
  have hss' : s' * s' * (ν₁ * ν₂) = 1 := by
    rw [← hs']
    exact inv_mul_cancel₀ (mul_ne_zero hν₁0 hν₂0)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hss
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    simp at hss'
  set Bmat : Matrix (Fin 2) (Fin 2) K :=
    !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
      (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)] with hBmat
  have hdetB : Bmat.det = ν₁ * ν₂ := by
    rw [hBmat, Matrix.det_fin_two_of]
    linear_combination (ν₂ * (ν₁ - ν₂)) * hαβ
  let A' : SpecialLinearGroup (Fin 2) K := ⟨s • diagonal ![μ₁, μ₂], by
    rw [Matrix.det_smul, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hss⟩
  let B' : SpecialLinearGroup (Fin 2) K := ⟨s' • Bmat, by
    rw [Matrix.det_smul, hdetB]
    simp only [Fintype.card_fin]
    linear_combination hss'⟩
  have hinvA : (s * μ₁)⁻¹ = s * μ₂ :=
    (eq_inv_of_mul_eq_one_right (by linear_combination hss : s * μ₁ * (s * μ₂) = 1)).symm
  have hinvB : (s' * ν₁)⁻¹ = s' * ν₂ :=
    (eq_inv_of_mul_eq_one_right (by linear_combination hss' : s' * ν₁ * (s' * ν₂) = 1)).symm
  have hAP : ((A' : Matrix (Fin 2) (Fin 2) K)) * (1 : Matrix (Fin 2) (Fin 2) K) =
      1 * diagonal ![s * μ₁, (s * μ₁)⁻¹] := by
    rw [hinvA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A']
  have hμsq : (s * μ₁) ^ 2 = μ₁ / μ₂ := by
    rw [eq_div_iff hμ₂0]
    linear_combination μ₁ * hss
  have hνsq : (s' * ν₁) ^ 2 = ν₁ / ν₂ := by
    rw [eq_div_iff hν₂0]
    linear_combination ν₁ * hss'
  have hpowne : ∀ x : K, h.bar x * x = 1 → x ^ (ℓ ^ f + 1) = 1 := fun x hx => by
    rw [← bar_mul_self_eq_pow]
    exact hx
  have hμq : ((s * μ₁) ^ 2) ^ (ℓ ^ f + 1) = 1 := by
    rw [hμsq, div_pow, hpowne _ hμ₁, hpowne _ hμ₂, div_one]
  let PB : Matrix (Fin 2) (Fin 2) K := !![α, -h.bar β; β, h.bar α]
  have hPB : PB.det ≠ 0 := by
    have : PB.det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hαβ
    rw [this]
    exact one_ne_zero
  have hBP : ((B' : Matrix (Fin 2) (Fin 2) K)) * PB = PB * diagonal ![s' * ν₁, (s' * ν₁)⁻¹] := by
    rw [hinvB]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B', Bmat, PB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;>
      first | ring1 | linear_combination (s' * α * (ν₁ - ν₂)) * hαβ |
        linear_combination (s' * β * (ν₁ - ν₂)) * hαβ
  have hB3 : 2 < orderOf (B' : PSL2MatrixGroup K) := by
    rw [orderOf_mk_eq hPB hBP, hνsq]
    omega
  have hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A' : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B' : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False := by
    rintro x hx0 ⟨c, hc⟩ ⟨c', hc'⟩
    have hA0 := congrFun hc 0
    have hA1 := congrFun hc 1
    have hB0 := congrFun hc' 0
    have hB1 := congrFun hc' 1
    simp [A', B', Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hA0 hA1 hB0 hB1
    by_cases hx0' : x 0 = 0
    · have hx1' : x 1 ≠ 0 := fun h1 => hx0 (by
        ext i
        fin_cases i <;> simp [hx0', h1])
      rw [hx0'] at hB0
      have : s' * ((ν₁ - ν₂) * (α * h.bar β)) * x 1 = 0 := by simpa using hB0
      exact (mul_ne_zero (mul_ne_zero hs'0 (mul_ne_zero (sub_ne_zero.2 hν12)
        (mul_ne_zero hα hbβ))) hx1') this
    · by_cases hx1' : x 1 = 0
      · rw [hx1'] at hB1
        have : s' * ((ν₁ - ν₂) * (β * h.bar α)) * x 0 = 0 := by simpa using hB1
        exact (mul_ne_zero (mul_ne_zero hs'0 (mul_ne_zero (sub_ne_zero.2 hν12)
          (mul_ne_zero hβ hbα))) hx0') this
      · have h1 : s * μ₁ = c := hA0.resolve_right hx0'
        have h2 : s * μ₂ = c := hA1.resolve_right hx1'
        exact hμ12 (mul_left_cancel₀ hs0 (h1.trans h2.symm))
  have hmk : ∀ (g : gu2 h) (u : K) (hu : u ≠ 0) (T : SpecialLinearGroup (Fin 2) K),
      ((T : Matrix (Fin 2) (Fin 2) K) = u • ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) →
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL T) = gu2ProjE h g := by
    intro g u hu T hT
    show _ = ProjGenLinGroup.mk (g : GL (Fin 2) K)
    symm
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 u hu, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hT]
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hAJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A') ∈ Y.map (gu2ProjE h) := by
    rw [hmk A s hs0 A' (by rw [hAm])]
    exact Subgroup.mem_map_of_mem _ hA
  have hBJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B') ∈ Y.map (gu2ProjE h) := by
    rw [hmk B s' hs'0 B' (by rw [hBm])]
    exact Subgroup.mem_map_of_mem _ hB
  exact card_ge_of_pgl_pair_prim h.card (Y.map (gu2ProjE h))
    ((Y.map_le_range (gu2ProjE h)).trans (range_gu2ProjE_le h)) hAJ hBJ
    (P := (1 : Matrix (Fin 2) (Fin 2) K)) (Matrix.det_one.trans_ne one_ne_zero) hAP
    (by rw [hμsq]; exact hμ6) (by rw [hμsq]; exact hsf) hμq hB3 hno

theorem su2_le_of_pair_prim (h : UnitaryFieldData ℓ f K)
    (hq4 : 4 ≤ ℓ ^ f) (Y : Subgroup (GL (Fin 2) K))
    {μ₁ μ₂ ν₁ ν₂ α β : K} (hμ₁ : h.bar μ₁ * μ₁ = 1) (hμ₂ : h.bar μ₂ * μ₂ = 1)
    (hν₁ : h.bar ν₁ * ν₁ = 1) (hν₂ : h.bar ν₂ * ν₂ = 1) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hμ6 : 6 ≤ orderOf (μ₁ / μ₂))
    (hsf : SubfieldFree ℓ f (orderOf (μ₁ / μ₂))) (hν3 : 3 ≤ orderOf (ν₁ / ν₂))
    {A B : GL (Fin 2) K}
    (hAm : (A : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)])
    (hA : A ∈ Y) (hB : B ∈ Y) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → g ∈ Y := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hAu : A ∈ gu2 h := by
    rw [mem_gu2, hAm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hμ₁, hμ₂]
  have hBu : B ∈ gu2 h := by
    rw [mem_gu2, hBm]
    have e1 : h.bar (h.bar α) = α := h.bar_bar α
    have e2 : h.bar (h.bar β) = β := h.bar_bar β
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, e1, e2, map_sub, map_add, map_mul] <;> grind
  have hSUle : unitarySU ℓ f K 2 ≤ gu2 h := fun g hg =>
    (mem_gu2 h).2 ((mem_unitarySU_iff h).1 hg).2
  have hcard := card_image_ge_prim h (Y.subgroupOf (gu2 h)) hμ₁ hμ₂ hν₁ hν₂ hαβ hα hβ
    hμ6 hsf hν3 (A := ⟨A, hAu⟩) (B := ⟨B, hBu⟩) hAm hBm hA hB
  rw [card_map_gu2ProjE] at hcard
  have := su2_le_of_card_ge h hq4 (Y.subgroupOf (gu2 h)) hcard
  intro g hg
  exact this ⟨g, hSUle hg⟩ hg

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
