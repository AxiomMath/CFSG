module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {f n : ℕ}

@[expose] noncomputable def suAdj (h : UnitaryFieldData 2 f K) (X : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (X.map h.bar)ᵀ

theorem isInvol_suAdj (h : UnitaryFieldData 2 f K) : IsInvol (suAdj (n := n) h) where
  map_add x y := by
    ext i j
    simp [suAdj, map_add]
  map_mul x y := by simp only [suAdj, Matrix.map_mul, transpose_mul]
  map_one := by simp only [suAdj, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
    transpose_one]
  invol x := by
    simp only [suAdj, transpose_map, transpose_transpose, Matrix.map_map]
    ext i j
    simp [UnitaryFieldData.bar_bar]

theorem mem_unitarySU_iff_suAdj (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K} :
    g ∈ unitarySU 2 f K n ↔ g ∈ unitaryOf (isInvol_suAdj h) ∧
      (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [mem_unitarySU_iff h, mem_unitaryOf, and_comm]
  rfl

theorem suAdj_eq_inv (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : g ∈ unitaryOf (isInvol_suAdj h)) :
    suAdj h (g : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  calc suAdj h (g : Matrix (Fin n) (Fin n) K)
      = suAdj h g * ((g * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = _ := by rw [Units.val_mul, ← Matrix.mul_assoc, mem_unitaryOf.mp hg, Matrix.one_mul]

theorem suAdj_mul_suAdj_inv (h : UnitaryFieldData 2 f K) (g : GL (Fin n) K) :
    suAdj h (g : Matrix (Fin n) (Fin n) K) *
      suAdj h ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← (isInvol_suAdj h).map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    (isInvol_suAdj h).map_one]

theorem suAdj_inv_mul_suAdj (h : UnitaryFieldData 2 f K) (g : GL (Fin n) K) :
    suAdj h ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      suAdj h (g : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← (isInvol_suAdj h).map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    (isInvol_suAdj h).map_one]

@[expose] noncomputable def suGram (h : UnitaryFieldData 2 f K) (a : GL (Fin n) K) :
    GL (Fin n) K where
  val := suAdj h (a : Matrix (Fin n) (Fin n) K) * a
  inv := ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
    suAdj h ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  val_inv := by
    calc suAdj h (a : Matrix (Fin n) (Fin n) K) * a * (((a⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * suAdj h ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = suAdj h (a : Matrix (Fin n) (Fin n) K) * ((a * a⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * suAdj h ((a⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by rw [Units.val_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_inv_cancel, Units.val_one, Matrix.mul_one, suAdj_mul_suAdj_inv]
  inv_val := by
    calc ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          suAdj h ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (suAdj h (a : Matrix (Fin n) (Fin n) K) * a)
        = ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (suAdj h ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            suAdj h (a : Matrix (Fin n) (Fin n) K)) * a := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [suAdj_inv_mul_suAdj, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
          Units.val_one]

theorem coe_suGram (h : UnitaryFieldData 2 f K) (a : GL (Fin n) K) :
    ((suGram h a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      suAdj h (a : Matrix (Fin n) (Fin n) K) * a :=
  rfl

theorem exists_suAdj_mul_eq_smul (h : UnitaryFieldData 2 f K) {a : GL (Fin n) K}
    (ha : a ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K))) :
    ∃ c : K, suAdj h (a : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) =
      c • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  have hcomm : ∀ s ∈ unitarySU 2 f K n, suGram h a * s = s * suGram h a := by
    intro s hs
    have ht : a * s * a⁻¹ ∈ unitarySU 2 f K n := (Subgroup.mem_normalizer_iff.mp ha s).mp hs
    have ht1 := mem_unitaryOf.mp ((mem_unitarySU_iff_suAdj h).mp ht).1
    have hs1 := suAdj_eq_inv h ((mem_unitarySU_iff_suAdj h).mp hs).1
    rw [Units.val_mul, Units.val_mul, (isInvol_suAdj h).map_mul,
      (isInvol_suAdj h).map_mul] at ht1
    have hAAi : (a : Matrix (Fin n) (Fin n) K) * ((a⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hAiA : ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (a : Matrix (Fin n) (Fin n) K) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hSSi : (s : Matrix (Fin n) (Fin n) K) * ((s⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have had := suAdj_mul_suAdj_inv h a
    have key : suAdj h (s : Matrix (Fin n) (Fin n) K) *
        (suAdj h (a : Matrix (Fin n) (Fin n) K) * a) * s =
        suAdj h (a : Matrix (Fin n) (Fin n) K) * a := by
      calc suAdj h (s : Matrix (Fin n) (Fin n) K) * (suAdj h (a : Matrix (Fin n) (Fin n) K) * a) *
            s
          = (suAdj h (a : Matrix (Fin n) (Fin n) K) *
              suAdj h ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (suAdj h (s : Matrix (Fin n) (Fin n) K) *
              (suAdj h (a : Matrix (Fin n) (Fin n) K) * a) * s) *
            (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a) := by
            rw [had, hAiA, Matrix.one_mul, Matrix.mul_one]
        _ = suAdj h (a : Matrix (Fin n) (Fin n) K) *
            (suAdj h ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (suAdj h (s : Matrix (Fin n) (Fin n) K) * suAdj h (a : Matrix (Fin n) (Fin n) K)) *
              ((a : Matrix (Fin n) (Fin n) K) * s * ((a⁻¹ : GL (Fin n) K) :
                Matrix (Fin n) (Fin n) K))) * a := by
            simp only [Matrix.mul_assoc]
        _ = suAdj h (a : Matrix (Fin n) (Fin n) K) * a := by rw [ht1, Matrix.mul_one]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_suGram]
    calc suAdj h (a : Matrix (Fin n) (Fin n) K) * a * s
        = (s : Matrix (Fin n) (Fin n) K) * ((s⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (suAdj h (a : Matrix (Fin n) (Fin n) K) * a) * s := by rw [hSSi, Matrix.one_mul]
      _ = (s : Matrix (Fin n) (Fin n) K) * (suAdj h (s : Matrix (Fin n) (Fin n) K) *
          (suAdj h (a : Matrix (Fin n) (Fin n) K) * a) * s) := by
          rw [hs1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [key]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ f + 1 ≠ 1 by have := Nat.one_le_two_pow (n := f); omega)
  have := h.finite
  obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_commute h hp hpd hcomm
  refine ⟨c, ?_⟩
  have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
  simp only [GeneralLinearGroup.coe_scalar, coe_suGram] at h1
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at h1
  exact h1.symm

theorem suAdj_mul_comm (h : UnitaryFieldData 2 f K) {A : Subgroup (GL (Fin n) K)}
    (hAN : A ≤ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)))
    (X : Matrix (Fin n) (Fin n) K)
    (hX : ∀ g ∈ A, X * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * X)
    {g : GL (Fin n) K} (hg : g ∈ A) :
    suAdj h X * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * suAdj h X := by
  obtain ⟨c, hc⟩ := exists_suAdj_mul_eq_smul h (hAN hg)
  have hg' : suAdj h (g : Matrix (Fin n) (Fin n) K) =
      c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc suAdj h (g : Matrix (Fin n) (Fin n) K)
        = suAdj h (g : Matrix (Fin n) (Fin n) K) * ((g * g⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
          rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (suAdj h (g : Matrix (Fin n) (Fin n) K) * g) * ((g⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
          rw [Units.val_mul, Matrix.mul_assoc]
      _ = _ := by rw [hc, Matrix.smul_mul, Matrix.one_mul]
  have hXg : suAdj h (g : Matrix (Fin n) (Fin n) K) * X = X * suAdj h g := by
    rw [hg', Matrix.smul_mul, Matrix.mul_smul, (hX _ (Subgroup.inv_mem _ hg)).symm]
  have h1 := congrArg (suAdj h) hXg
  rwa [(isInvol_suAdj h).map_mul, (isInvol_suAdj h).map_mul, (isInvol_suAdj h).invol] at h1

theorem exists_add_bar_eq_one (h : UnitaryFieldData 2 f K) : ∃ c : K, c + h.bar c = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have ht : c₀ + h.bar c₀ ≠ 0 := by
    intro h0
    apply hc₀
    rw [eq_neg_of_add_eq_zero_right h0, CharTwo.neg_eq]
  have hbt : h.bar (c₀ + h.bar c₀) = c₀ + h.bar c₀ := by
    rw [map_add, h.bar_bar, add_comm]
  refine ⟨c₀ * (c₀ + h.bar c₀)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hbt, ← add_mul, mul_inv_cancel₀ ht]

theorem suAdj_smul_one (h : UnitaryFieldData 2 f K) (c : K) :
    suAdj h (c • (1 : Matrix (Fin n) (Fin n) K)) = h.bar c • (1 : Matrix (Fin n) (Fin n) K) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [suAdj]
  · simp [suAdj, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem ggSUCentralizerCoreInput_of (hHerm : HermCoreInput) (hAlt : AltCoreInput) :
    GGSUCentralizerCoreInput := by
  intro K _ f h n _ A hA hAN
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hsymd : ∃ Y : Matrix (Fin n) (Fin n) K, (∀ g ∈ A, Y * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * Y) ∧ Y + suAdj h Y = 1 := by
    obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
    refine ⟨c • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one], ?_⟩
    rw [suAdj_smul_one, ← add_smul, hc, one_smul]
  obtain ⟨β, S, hS⟩ := exists_coreFamily_adjCent hHerm hAlt hA (isInvol_suAdj h)
    (fun X hX g hg => suAdj_mul_comm h hAN X hX hg) hsymd
  set H₀ : Subgroup (GL (Fin n) K) :=
    adjCent A (isInvol_suAdj (n := n) h) ⊓ (Matrix.GeneralLinearGroup.det).ker with hH₀
  have hSdet : ∀ c, S c ≤ H₀ := by
    intro c
    refine le_inf (hS.1 c) ?_
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (hS.2.2.1 c)]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 := hS.mono inf_le_left hSdet
  have hdet : ∀ g : GL (Fin n) K, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hle : H₀ ≤ (unitarySU 2 f K n).subtype.range := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨(Subgroup.mem_inf.mp hg1).2, (hdet g).mp hg2⟩⟩,
      rfl⟩
  have hC : H₀.comap (unitarySU 2 f K n).subtype =
      (Subgroup.centralizer (A : Set (GL (Fin n) K))).comap (unitarySU 2 f K n).subtype := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hH₀, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hx := (mem_unitarySU_iff_suAdj h).mp x.2
    exact ⟨fun hx' => hx'.1.1, fun hx' => ⟨⟨hx', hx.1⟩, (hdet _).mpr hx.2⟩⟩
  have h2 := hS0.comap (unitarySU 2 f K n).subtype (Subgroup.subtype_injective _) hle
  rw [hC] at h2
  exact ⟨β, fun c => (S c).comap (unitarySU 2 f K n).subtype, h2⟩

end LayerCores

end CFSG.StandardType
