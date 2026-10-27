module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountP27

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck158

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup)

section Matrices

open Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem conj_mul_eq_scalar_mul {y g h : GL (Fin 3) K} {s t : Kˣ}
    (hg : g * y * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) s * y)
    (hh : h * y * h⁻¹ = GeneralLinearGroup.scalar (Fin 3) t * y) :
    (g * h) * y * (g * h)⁻¹ = GeneralLinearGroup.scalar (Fin 3) (s * t) * y := by
  have hc : g * GeneralLinearGroup.scalar (Fin 3) t = GeneralLinearGroup.scalar (Fin 3) t * g :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t g).eq
  calc (g * h) * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ := by group
    _ = g * (GeneralLinearGroup.scalar (Fin 3) t * y) * g⁻¹ := by rw [hh]
    _ = GeneralLinearGroup.scalar (Fin 3) t * (g * y * g⁻¹) := by
        rw [← mul_assoc g, hc]
        group
    _ = GeneralLinearGroup.scalar (Fin 3) (s * t) * y := by
        rw [hg, ← mul_assoc, ← map_mul, mul_comm t s]

theorem commutator_pow_three_of_conj_scalar {A B Y : GL (Fin 3) K} (hY : Y = B * A * B⁻¹ * A⁻¹)
    (hA3 : A ^ 3 ∈ StatedScalars (Fin 3) K) {s : Kˣ}
    (hs : A * Y * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) s * Y) (hs3 : s ^ 3 = 1) :
    Y ^ 3 = 1 := by
  obtain ⟨α, hα⟩ := hA3
  have hS : ∀ g : GL (Fin 3) K, g * GeneralLinearGroup.scalar (Fin 3) s =
      GeneralLinearGroup.scalar (Fin 3) s * g := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s g).eq
  have hyx : A * Y = Y * A * GeneralLinearGroup.scalar (Fin 3) s := by
    calc A * Y = (A * Y * A⁻¹) * A := by group
      _ = GeneralLinearGroup.scalar (Fin 3) s * Y * A := by rw [hs]
      _ = Y * GeneralLinearGroup.scalar (Fin 3) s * A := by rw [← hS Y]
      _ = Y * (GeneralLinearGroup.scalar (Fin 3) s * A) := by group
      _ = Y * (A * GeneralLinearGroup.scalar (Fin 3) s) := by rw [← hS A]
      _ = Y * A * GeneralLinearGroup.scalar (Fin 3) s := by group
  have h3 := RonanK432.mul_pow_three_of_commutator (x := Y) (y := A)
    (c := GeneralLinearGroup.scalar (Fin 3) s) hS hyx
  have hcS : GeneralLinearGroup.scalar (Fin 3) s ^ 3 = 1 := by
    rw [← map_pow, hs3, map_one]
  rw [hcS, mul_one] at h3
  have hYA : Y * A = B * A * B⁻¹ := by rw [hY]; group
  have h4 : (B * A * B⁻¹) ^ 3 = A ^ 3 := by
    rw [_root_.conj_pow, ← hα, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar α B).eq,
      mul_inv_cancel_right]
  rw [hYA, h4] at h3
  have h5 : Y ^ 3 * A ^ 3 = 1 * A ^ 3 := by rw [one_mul]; exact h3.symm
  exact mul_right_cancel h5

theorem exists_regular_eigenbasis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {Y : GL (Fin 3) K} (hYL : Y ∈ slPi π 3 (p ^ f) K) (hYZ : Y ∉ zPi π 3 (p ^ f) K)
    (hY3 : Y ^ 3 = 1) :
    ∃ (bb : Fin 3 → (Fin 3 → K)) (d : Fin 3 → K), LinearIndependent K bb ∧
      Function.Injective d ∧ ∀ i, (Y : Matrix (Fin 3) (Fin 3) K) *ᵥ bb i = d i • bb i := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hYne : Y ≠ 1 := fun h => hYZ (by rw [h]; exact one_mem _)
  obtain ⟨g, -, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 hYL hYZ (orderOf_eq_prime hY3 hYne)
  have hYg : Y * g = g * diagTau hτ := by
    calc Y * g = g * (g⁻¹ * Y * g) := by group
      _ = g * diagTau hτ := by rw [hgD]
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  refine ⟨(g : Matrix (Fin 3) (Fin 3) K).col, ![τ, τ ^ 2, 1],
    Matrix.linearIndependent_cols_iff_isUnit.mpr g.isUnit, ?_, fun i => ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hττ2, hτ1, hτ2, Ne.symm hττ2, Ne.symm hτ1, Ne.symm hτ2] at hij ⊢
  · have h1 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hYg
    simp only [Units.val_mul, coe_diagTau_eq_diagonal hτ] at h1
    ext r
    have h2 := congrFun (congrFun h1 r) i
    rw [Matrix.mul_diagonal] at h2
    simp only [Matrix.mul_apply] at h2
    simp only [Matrix.mulVec, dotProduct, Matrix.col, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact h2

theorem exists_commuting_lift_of_conj_scalar {A B Y : GL (Fin 3) K} {sA sB : Kˣ}
    (hsA : A * Y * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) sA * Y)
    (hsB : B * Y * B⁻¹ = GeneralLinearGroup.scalar (Fin 3) sB * Y)
    (hsA3 : sA ^ 3 = 1) (hsB3 : sB ^ 3 = 1) :
    A * Y = Y * A ∨ B * Y = Y * B ∨ (A * B) * Y = Y * (A * B) ∨
      (A * (A * B)) * Y = Y * (A * (A * B)) := by
  have hfin : ∀ g : GL (Fin 3) K,
      g * Y * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) 1 * Y → g * Y = Y * g := by
    intro g h
    rw [map_one, one_mul] at h
    calc g * Y = g * Y * g⁻¹ * g := by group
      _ = Y * g := by rw [h]
  by_cases hA1 : sA = 1
  · exact Or.inl (hfin A (hA1 ▸ hsA))
  have hsA3' : (sA : K) ^ 3 = 1 := by
    have := congrArg Units.val hsA3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hsA1' : (sA : K) ≠ 1 := fun h => hA1 (Units.ext h)
  have hsB3' : ((sB⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    have h1 : (sB⁻¹) ^ 3 = 1 := by rw [inv_pow, hsB3, inv_one]
    have := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  rcases Sec4.cube_root_cases hsA3' hsA1' hsB3' with h | h | h
  · have hsB1 : sB = 1 := inv_eq_one.mp (Units.ext (by rw [h, Units.val_one]))
    exact Or.inr (Or.inl (hfin B (hsB1 ▸ hsB)))
  · have hsB1 : sA * sB = 1 := by
      have : sB⁻¹ = sA := Units.ext h
      rw [← this, inv_mul_cancel]
    exact Or.inr (Or.inr (Or.inl (hfin _ (hsB1 ▸ conj_mul_eq_scalar_mul hsA hsB))))
  · have hsB1 : sA * (sA * sB) = 1 := by
      have : sB⁻¹ = sA ^ 2 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h)
      rw [← mul_assoc, ← sq, ← this, inv_mul_cancel]
    exact Or.inr (Or.inr (Or.inr
      (hfin _ (hsB1 ▸ conj_mul_eq_scalar_mul hsA (conj_mul_eq_scalar_mul hsA hsB)))))

end Matrices

theorem commutator_central_of_card_27 {Q : Type} [Group Q] {R : Subgroup Q}
    (hR27 : Nat.card R = 27) (hRnc : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) {x y : Q} (hx : x ∈ R)
    (hy : y ∈ R) : ∀ r ∈ R, r * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * r := by
  obtain ⟨a, ha, b, hb, hab⟩ := hRnc
  obtain ⟨c, hc, -, hyx⟩ := Sec4.RonanK432.exists_commutator_data (P := ↥R) hR27
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩ ⟨x, hx⟩ ⟨y, hy⟩
  have hcomm : (⟨y, hy⟩ * ⟨x, hx⟩ * ⟨y, hy⟩⁻¹ * ⟨x, hx⟩⁻¹ : ↥R) = c := by
    calc (⟨y, hy⟩ * ⟨x, hx⟩ * ⟨y, hy⟩⁻¹ * ⟨x, hx⟩⁻¹ : ↥R)
        = ⟨x, hx⟩ * ⟨y, hy⟩ * c * ⟨y, hy⟩⁻¹ * ⟨x, hx⟩⁻¹ := by rw [hyx]
      _ = ⟨x, hx⟩ * ⟨y, hy⟩ * (c * ⟨y, hy⟩⁻¹) * ⟨x, hx⟩⁻¹ := by group
      _ = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨y, hy⟩⁻¹ * c) * ⟨x, hx⟩⁻¹ := by rw [← hc ⟨y, hy⟩⁻¹]
      _ = ⟨x, hx⟩ * c * ⟨x, hx⟩⁻¹ := by group
      _ = c := by rw [hc ⟨x, hx⟩]; group
  intro r hr
  have h2 := congrArg Subtype.val (hc ⟨r, hr⟩)
  have h3 := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2 h3
  rw [h3]
  exact h2

section Pgl

open Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_typeC_of_pgl_nonabelian (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (R : Subgroup (ProjGenLinGroup (Fin 3) K))
    (hRH : R ≤ projImage (glPi π 3 (p ^ f) K)) (hR27 : Nat.card R = 27)
    (hR3 : ∀ r ∈ R, r ^ 3 = 1) (hRnc : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) :
    ∃ D : Subgroup (GL (Fin 3) K), IsTypeC π (p ^ f) K D ∧
      (∀ y ∈ D, ProjGenLinGroup.mk y ∈ R) ∧ Nat.card (D.map ProjGenLinGroup.mk) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk (QuotientGroup.mk'_surjective _)
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨a, ha, b, hb, hab⟩ := hRnc
  obtain ⟨A, hAH, hAa⟩ := hRH ha
  obtain ⟨B, hBH, hBb⟩ := hRH hb
  have hAR : ProjGenLinGroup.mk A ∈ R := by rw [hAa]; exact ha
  have hBR : ProjGenLinGroup.mk B ∈ R := by rw [hBb]; exact hb
  set Y : GL (Fin 3) K := B * A * B⁻¹ * A⁻¹ with hY
  have hYmk : ProjGenLinGroup.mk Y = b * a * b⁻¹ * a⁻¹ := by
    simp only [hY, map_mul, map_inv, hAa, hBb]
  have hYH : Y ∈ glPi π 3 (p ^ f) K :=
    mul_mem (mul_mem (mul_mem hBH hAH) (inv_mem hBH)) (inv_mem hAH)
  have hYR : ProjGenLinGroup.mk Y ∈ R := by
    rw [hYmk]
    exact mul_mem (mul_mem (mul_mem hb ha) (inv_mem hb)) (inv_mem ha)
  have hYc : ∀ r ∈ R, r * ProjGenLinGroup.mk Y = ProjGenLinGroup.mk Y * r := by
    rw [hYmk]
    exact commutator_central_of_card_27 hR27 ⟨a, ha, b, hb, hab⟩ ha hb
  have hY1 : ProjGenLinGroup.mk Y ≠ 1 := by
    rw [hYmk]
    intro h
    apply hab
    have : b * a = a * b := by
      calc b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
        _ = a * b := by rw [h, one_mul]
    exact this.symm
  have hconj : ∀ g : GL (Fin 3) K, ProjGenLinGroup.mk g ∈ R →
      ∃ s : Kˣ, g * Y * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) s * Y := fun g hg =>
    Sec15.KL3FactsProof.exists_scalar_of_mk_commute (hYc _ hg)
  have hcube : ∀ g : GL (Fin 3) K, ProjGenLinGroup.mk g ∈ R → g ^ 3 ∈ StatedScalars (Fin 3) K := by
    intro g hg
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', map_pow]
    exact hR3 _ hg
  obtain ⟨sA, hsA⟩ := hconj A hAR
  obtain ⟨sB, hsB⟩ := hconj B hBR
  have hsA3 : sA ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hsA
  have hsB3 : sB ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hsB
  have hY3 : Y ^ 3 = 1 := commutator_pow_three_of_conj_scalar hY (hcube A hAR) hsA hsA3
  have hdetY : GeneralLinearGroup.det Y = 1 := by
    rw [hY, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (GeneralLinearGroup.det B),
      mul_inv_cancel_right, mul_inv_cancel]
  have hYL : Y ∈ slPi π 3 (p ^ f) K :=
    (mem_slPi_iff hπ).mpr ⟨hYH, by rw [← GeneralLinearGroup.val_det_apply, hdetY, Units.val_one]⟩
  have hYZ : Y ∉ zPi π 3 (p ^ f) K := fun h =>
    hY1 (KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h))
  obtain ⟨bb, d, hbli, hd, hbz⟩ := exists_regular_eigenbasis hK hq hYL hYZ hY3
  have key : ∃ g₀ : GL (Fin 3) K, g₀ ∈ glPi π 3 (p ^ f) K ∧ ProjGenLinGroup.mk g₀ ∈ R ∧
      g₀ * Y = Y * g₀ ∧ ∃ r ∈ R, ProjGenLinGroup.mk g₀ * r ≠ r * ProjGenLinGroup.mk g₀ := by
    rcases exists_commuting_lift_of_conj_scalar hsA hsB hsA3 hsB3 with h | h | h | h
    · refine ⟨A, hAH, hAR, h, b, hb, ?_⟩
      rw [hAa]
      exact hab
    · refine ⟨B, hBH, hBR, h, a, ha, ?_⟩
      rw [hBb]
      exact fun h' => hab h'.symm
    · refine ⟨A * B, mul_mem hAH hBH, ?_, h, a, ha, ?_⟩
      · rw [map_mul]
        exact mul_mem hAR hBR
      · rw [map_mul, hAa, hBb]
        intro h'
        apply hab
        have h'' : a * (b * a) = a * (a * b) := by
          calc a * (b * a) = a * b * a := by group
            _ = a * (a * b) := h'
        exact (mul_left_cancel h'').symm
    · refine ⟨A * (A * B), mul_mem hAH (mul_mem hAH hBH), ?_, h, a, ha, ?_⟩
      · rw [map_mul, map_mul]
        exact mul_mem hAR (mul_mem hAR hBR)
      · rw [map_mul, map_mul, hAa, hBb]
        intro h'
        apply hab
        have h'' : a * (a * (b * a)) = a * (a * (a * b)) := by
          calc a * (a * (b * a)) = a * (a * b) * a := by group
            _ = a * (a * (a * b)) := h'
        exact (mul_left_cancel (mul_left_cancel h'')).symm
  obtain ⟨g₀, hg₀H, hg₀R, hg₀Y, r₀, hr₀, hr₀c⟩ := key
  set D : Subgroup (GL (Fin 3) K) :=
    glPi π 3 (p ^ f) K ⊓ R.comap ProjGenLinGroup.mk ⊓ Subgroup.centralizer {Y} with hD
  have hDmem : ∀ x, x ∈ D ↔ (x ∈ glPi π 3 (p ^ f) K ∧ ProjGenLinGroup.mk x ∈ R) ∧
      x * Y = Y * x := by
    intro x
    simp only [hD, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.mem_centralizer_singleton_iff]
  have hDlines : ∀ x ∈ D, ∀ i, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ bb i = c • bb i := by
    intro x hx i
    have hxY := ((hDmem x).mp hx).2
    refine exists_smul_of_commute_regular hbli hd hbz ?_ i
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hxY
    simpa only [Units.val_mul] using this
  have hDcomm : ∀ x ∈ D, ∀ x' ∈ D, x * x' = x' * x := by
    intro x hx x' hx'
    apply Units.ext
    apply eq_of_mulVec_eq_of_linearIndependent hbli
    intro r
    obtain ⟨c₁, hc₁⟩ := hDlines x hx r
    obtain ⟨c₂, hc₂⟩ := hDlines x' hx' r
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, hc₁, hc₂, Matrix.mulVec_smul, smul_smul]
    rw [mul_comm]
  set Dbar : Subgroup (ProjGenLinGroup (Fin 3) K) := D.map ProjGenLinGroup.mk with hDbar
  have hDbarR : Dbar ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((hDmem x).mp hx).1.2
  have hdvd : Nat.card Dbar ∣ 27 := hR27 ▸ Subgroup.card_dvd_of_le hDbarR
  have hYD : Y ∈ D := (hDmem Y).mpr ⟨⟨hYH, hYR⟩, rfl⟩
  have hg₀D : g₀ ∈ D := (hDmem g₀).mpr ⟨⟨hg₀H, hg₀R⟩, hg₀Y⟩
  have hcc3 : ProjGenLinGroup.mk Y ^ 3 = 1 := hR3 _ hYR
  have hccord : orderOf (ProjGenLinGroup.mk Y) = 3 := orderOf_eq_prime hcc3 hY1
  have hzp : Nat.card (Subgroup.zpowers (ProjGenLinGroup.mk Y)) = 3 := by
    rw [Nat.card_zpowers, hccord]
  have hzpD : Subgroup.zpowers (ProjGenLinGroup.mk Y) ≤ Dbar :=
    Subgroup.zpowers_le.mpr ⟨Y, hYD, rfl⟩
  have hgt : 3 < Nat.card Dbar := by
    by_contra hle
    push Not at hle
    have heq : Subgroup.zpowers (ProjGenLinGroup.mk Y) = Dbar :=
      Subgroup.eq_of_le_of_card_ge hzpD (by rw [hzp]; exact hle)
    have hw : ProjGenLinGroup.mk g₀ ∈ Subgroup.zpowers (ProjGenLinGroup.mk Y) :=
      heq ▸ ⟨g₀, hg₀D, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    apply hr₀c
    rw [← hk]
    exact (Commute.zpow_right (show Commute r₀ (ProjGenLinGroup.mk Y) from hYc r₀ hr₀) k).eq.symm
  have hne27 : Nat.card Dbar ≠ 27 := by
    intro h27
    have hDR : Dbar = R := Subgroup.eq_of_le_of_card_ge hDbarR (by rw [hR27, h27])
    have haD : a ∈ Dbar := hDR ▸ ha
    have hbD : b ∈ Dbar := hDR ▸ hb
    obtain ⟨A', hA'D, hA'a⟩ := haD
    obtain ⟨B', hB'D, hB'b⟩ := hbD
    apply hab
    rw [← hA'a, ← hB'b, ← map_mul, ← map_mul, hDcomm A' hA'D B' hB'D]
  have hDbar9 : Nat.card Dbar = 9 := by
    have hle : Nat.card Dbar ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card Dbar <;> omega
  refine ⟨D, ⟨fun x hx => ((hDmem x).mp hx).1.1, fun x hx => hcube x ((hDmem x).mp hx).1.2, ?_,
    bb, hbli, hDlines⟩, fun x hx => ((hDmem x).mp hx).1.2, hDbar9⟩
  have hker : (ProjGenLinGroup.mk.comp D.subtype).ker =
      ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp D.subtype).ker := by
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      KFacts.mk_eq_one_iff_mem_statedScalars']
  have h1 := card_range_eq_of_ker_eq _ _ hker
  rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype] at h1
  rw [← h1]
  exact hDbar9

end Pgl

theorem exists_typeC_of_nonabelian {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {X : Type} [Group X] [Finite X] (φ : X ≃* projImage (slPi π 3 (p ^ f) K))
    (P : Subgroup (MulAut X)) (hP3 : IsPGroup 3 P) (hP27 : Nat.card P = 27)
    (hPnc : ¬ IsMulCommutative P) (hPexp : ∀ σ ∈ P, σ ^ 3 = 1)
    (hA : ∀ σ ∈ P, ∃ y ∈ glPi π 3 (p ^ f) K, ∀ z : X,
      ((φ (σ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ∃ P₀ : Subgroup (MulAut X), P₀ ≤ P ∧ Nat.card P₀ = 9 ∧
      ∃ D : Subgroup (GL (Fin 3) K), IsTypeC π (p ^ f) K D ∧
        (∀ τ ∈ P₀, ∃ y ∈ D, ∀ z : X,
          ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
            ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) *
              (ProjGenLinGroup.mk y)⁻¹) ∧
        ∀ y ∈ D, ∃ τ ∈ P₀, ∀ z : X,
          ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
            ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) *
              (ProjGenLinGroup.mk y)⁻¹ := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk (QuotientGroup.mk'_surjective _)
  set H := projImage (glPi π 3 (p ^ f) K) with hH
  set Γ₀ : ↥H →* MulAut ↥(projImage (slPi π 3 (p ^ f) K)) :=
    (projImage (slPi π 3 (p ^ f) K)).normalizerMonoidHom.comp
      (Subgroup.inclusion (Sec16.ProofKSL3Two.projImage_glPi_le_normalizer hK)) with hΓ₀
  set Γ : ↥H →* MulAut X := (MulAut.congr φ).symm.toMonoidHom.comp Γ₀ with hΓ
  have hΓapp : ∀ (h : ↥H) (z : X), ((φ (Γ h z) : ↥(projImage (slPi π 3 (p ^ f) K))) :
      ProjGenLinGroup (Fin 3) K) = (h : ProjGenLinGroup (Fin 3) K) *
        (φ z : ProjGenLinGroup (Fin 3) K) * (h : ProjGenLinGroup (Fin 3) K)⁻¹ := by
    intro h z
    have h1 : Γ h z = φ.symm ((Γ₀ h) (φ z)) := rfl
    rw [h1, MulEquiv.apply_symm_apply]
    rfl
  have hΓinj : Function.Injective Γ :=
    (MulAut.congr φ).symm.injective.comp (Sec16.ProofKSL3Two.conjHom_injective hK hq hq2)
  have hPΓ : P ≤ Γ.range := by
    intro σ hσ
    obtain ⟨y, hy, hσy⟩ := hA σ hσ
    refine ⟨⟨ProjGenLinGroup.mk y, y, hy, rfl⟩, ?_⟩
    ext z
    apply φ.injective
    apply Subtype.ext
    rw [hΓapp, hσy]
  set Rt := P.comap Γ with hRt
  have hRtmap : Rt.map Γ = P := Subgroup.map_comap_eq_self hPΓ
  have hRt27 : Nat.card Rt = 27 := by
    rw [← Subgroup.card_map_of_injective hΓinj, hRtmap, hP27]
  have hRt3 : ∀ x ∈ Rt, x ^ 3 = 1 := by
    intro x hx
    apply hΓinj
    rw [map_pow, hPexp _ hx, map_one]
  have hRtnc : ∃ x ∈ Rt, ∃ y ∈ Rt, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hPnc
    refine ⟨⟨fun σ τ => ?_⟩⟩
    obtain ⟨x, hx⟩ := hPΓ σ.2
    obtain ⟨y, hy⟩ := hPΓ τ.2
    have hxR : x ∈ Rt := by
      show Γ x ∈ P
      rw [hx]
      exact σ.2
    have hyR : y ∈ Rt := by
      show Γ y ∈ P
      rw [hy]
      exact τ.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
      hcon x hxR y hyR]
  obtain ⟨D, hDC, hDR, hDcard⟩ := exists_typeC_of_pgl_nonabelian hK hq (Rt.map H.subtype)
    (Subgroup.map_subtype_le Rt)
    (by rw [Subgroup.card_map_of_injective H.subtype_injective, hRt27])
    (by
      rintro _ ⟨x, hx, rfl⟩
      change (x : ProjGenLinGroup (Fin 3) K) ^ 3 = 1
      rw [← Subgroup.coe_pow, hRt3 x hx, Subgroup.coe_one])
    (by
      obtain ⟨x, hx, y, hy, hxy⟩ := hRtnc
      exact ⟨x, ⟨x, hx, rfl⟩, y, ⟨y, hy, rfl⟩, fun h => hxy (Subtype.ext h)⟩)
  have hDH : ∀ y ∈ D, ProjGenLinGroup.mk y ∈ H := fun y hy => ⟨y, hDC.1 hy, rfl⟩
  set Dt : Subgroup ↥H := (D.map ProjGenLinGroup.mk).subgroupOf H with hDt
  have hDtRt : Dt ≤ Rt := by
    rintro ⟨_, hz⟩ hzD
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_subgroupOf.mp hzD
    obtain ⟨x, hx, hxy⟩ := hDR y hy
    have : x = ⟨_, hz⟩ := Subtype.ext (hxy.trans hyz)
    rwa [this] at hx
  have hDt9 : Nat.card Dt = 9 := by
    rw [hDt, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      exact hDH y hy)).toEquiv]
    exact hDcard
  refine ⟨Dt.map Γ, ?_, ?_, D, hDC, ?_, ?_⟩
  · rw [← hRtmap]
    exact Subgroup.map_mono hDtRt
  · rw [Subgroup.card_map_of_injective hΓinj, hDt9]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hx
    refine ⟨y, hy, fun z => ?_⟩
    rw [hΓapp, ← hyx]
  · intro y hy
    refine ⟨Γ ⟨ProjGenLinGroup.mk y, hDH y hy⟩,
      ⟨⟨ProjGenLinGroup.mk y, hDH y hy⟩, Subgroup.mem_subgroupOf.mpr ⟨y, hy, rfl⟩, rfl⟩,
      fun z => ?_⟩
    rw [hΓapp]

end CFSG.RankThree.PartTwo.Sec15.Liebeck158
