module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.QuasithinUnique.AGFusion

public section

namespace CFSG.LocalAnalysis

namespace SymplecticFourFusion

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K]

@[expose] def blockMat (s t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; s, t, 0, 0; 0, 0, 0, s⁻¹; 0, 0, 1, -(t * s⁻¹)]

@[expose] def blockInvMat (s t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![-(t * s⁻¹), s⁻¹, 0, 0; 1, 0, 0, 0; 0, 0, t, 1; 0, 0, s, 0]

theorem blockMat_mul_blockInvMat {s : K} (hs : s ≠ 0) (t : K) :
    blockMat s t * blockInvMat s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, blockInvMat, Matrix.mul_apply, Fin.sum_univ_four, hs]
  all_goals field_simp
  all_goals ring

theorem blockInvMat_mul_blockMat {s : K} (hs : s ≠ 0) (t : K) :
    blockInvMat s t * blockMat s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, blockInvMat, Matrix.mul_apply, Fin.sum_univ_four, hs]
  all_goals field_simp
  all_goals ring

theorem blockMat_mem {s : K} (hs : s ≠ 0) (t : K) :
    (blockMat s t)ᵀ * minorJ K * blockMat s t = minorJ K := by
  ext k l
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases l <;> simp [blockMat, hs]
  all_goals field_simp
  all_goals ring

theorem blockMat_conj [CharP K 2] {s : K} (hs : s ≠ 0) (t b : K) :
    blockMat s t * uMat 0 b (t ^ 2) (s ^ 2) * blockInvMat s t =
      uMat 0 (s ^ 2 * t + b * s) (s ^ 2) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, blockInvMat, uMat, Matrix.mul_apply, Fin.sum_univ_four, hs]
  all_goals first
    | ring1
    | (field_simp; ring1)
    | linear_combination (s * b * t + s ^ 2 * t ^ 2) * h2

@[expose] def blockElt {s : K} (hs : s ≠ 0) (t : K) : antiSp K :=
  ⟨⟨blockMat s t, blockInvMat s t, blockMat_mul_blockInvMat hs t,
    blockInvMat_mul_blockMat hs t⟩, blockMat_mem hs t⟩

section CharTwo

variable [CharP K 2]

theorem exists_conj_mem_center_of_mem_radA1 [Finite K] {y : antiSp K} (hy : y ∈ radA1 K) :
    ∃ h : antiSp K, h * y * h⁻¹ ∈ antiUnipotentCenter K := by
  obtain ⟨b, c, d, rfl⟩ := hy
  by_cases hd : d = 0
  · exact ⟨1, by rw [hd, one_mul, inv_one, mul_one]; exact ⟨b, c, rfl⟩⟩
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' d
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' c
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hd (by rw [hs, mul_zero])
  refine ⟨blockElt hs0 t, s ^ 2 * t + b * s, s ^ 2, antiSp_ext ?_⟩
  change blockMat s t * uMat 0 b c d * blockInvMat s t = uMat 0 (s ^ 2 * t + b * s) (s ^ 2) 0
  rw [hs, ht, ← sq, ← sq]
  exact blockMat_conj hs0 t b

theorem minorHom_mem_center [Finite K] {z : antiSp K} (hz : z ∈ antiUnipotentCenter K) :
    minorHom K z ∈ antiUnipotentCenter K := by
  obtain ⟨b, c, rfl⟩ := hz
  refine ⟨c, b ^ 2, antiSp_ext ?_⟩
  rw [glMat_minorHom, glMat_uElt, minorMap_uMat, glMat_uElt]
  congr 1 <;> ring

theorem exists_conj_mem_center_of_mem_radA2 [Finite K] {x : antiSp K} (hx : x ∈ radA2 K) :
    ∃ h : antiSp K, h * x * h⁻¹ ∈ antiUnipotentCenter K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, b, c, rfl⟩ := hx
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (c + a * b)
  have hy : minorHom K (uElt 0 r b a) = uElt a b c 0 := by
    apply antiSp_ext
    rw [glMat_minorHom, glMat_uElt, minorMap_uMat, glMat_uElt]
    congr 1
    · ring
    · linear_combination -hr + a * b * h2
    · ring
  obtain ⟨h, hh⟩ := exists_conj_mem_center_of_mem_radA1 (K := K) ⟨r, b, a, rfl⟩
  refine ⟨minorHom K h, ?_⟩
  rw [← hy, ← map_inv, ← map_mul, ← map_mul]
  exact minorHom_mem_center hh

theorem centralizer_center_eq :
    Subgroup.centralizer (antiUnipotentCenter K : Set (antiSp K)) = antiUnipotent K := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    have h1 := congrArg (fun h : antiSp K => glMat (h : GL (Fin 4) K))
      (hg (uElt 0 0 1 0) ⟨0, 1, rfl⟩)
    have h2 := congrArg (fun h : antiSp K => glMat (h : GL (Fin 4) K))
      (hg (uElt 0 1 0 0) ⟨1, 0, rfl⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, glMat_uElt] at h1 h2
    set M : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
    have e1 : ∀ i j : Fin 4, (uMat (0 : K) 0 1 0 * M) i j = (M * uMat (0 : K) 0 1 0) i j :=
      fun i j => by rw [h1]
    have e2 : ∀ i j : Fin 4, (uMat (0 : K) 1 0 0 * M) i j = (M * uMat (0 : K) 1 0 0) i j :=
      fun i j => by rw [h2]
    have t13 := e1 1 3
    have t23 := e1 2 3
    have t33 := e1 3 3
    have t01 := e1 0 1
    have t02 := e1 0 2
    have t03 := e1 0 3
    have u01 := e2 0 1
    have u02 := e2 0 2
    have u13 := e2 1 3
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at t13 t23 t33 t01 t02 t03 u01 u02 u13
    have m33 : M 3 3 = M 0 0 := by linear_combination t03
    have m22 : M 2 2 = M 0 0 := by linear_combination u02
    have m11 : M 1 1 = M 0 0 := by linear_combination m33 - u13
    have hJ := congrFun (congrFun (mem_antiSp.mp g.2) 0) 3
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at hJ
    change M 0 0 * M 3 3 + M 1 0 * M 2 3 + M 2 0 * M 1 3 + M 3 0 * M 0 3 = _ at hJ
    rw [t13, t23, t33, m33] at hJ
    norm_num at hJ
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (M 0 0 - 1) ^ 2 = 0 := by linear_combination hJ - (M 0 0 - 1) * h2
    have m00 : M 0 0 = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
    rw [mem_antiUnipotent_iff_upper]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd hij (by decide)
        | exact t13
        | exact t23
        | exact u01
        | exact t33
        | exact t01
        | exact t02
    · fin_cases i
      · exact m00
      · exact m11.trans m00
      · exact m22.trans m00
      · exact m33.trans m00
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact antiUnipotentCenter_comm hz hu

theorem normalizer_center_eq :
    Subgroup.normalizer (antiUnipotentCenter K : Set (antiSp K)) =
      Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    rw [← centralizer_center_eq, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh y hy
      have hy' : g⁻¹ * y * g ∈ antiUnipotentCenter K :=
        (hg _).mpr (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group])
      have h1 := hh _ hy'
      calc y * (g * h * g⁻¹) = g * ((g⁻¹ * y * g) * h) * g⁻¹ := by group
        _ = g * (h * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = g * h * g⁻¹ * y := by group
    · intro hh y hy
      have h1 := hh _ ((hg y).mp hy)
      calc y * h = g⁻¹ * ((g * y * g⁻¹) * (g * h * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * h * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
        _ = h * y := by group
  · intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    have hconj : ∀ g' : antiSp K, (∀ h, h ∈ antiUnipotent K ↔ g' * h * g'⁻¹ ∈ antiUnipotent K) →
        ∀ z ∈ antiUnipotentCenter K, g' * z * g'⁻¹ ∈ antiUnipotentCenter K := by
      intro g' hg' z hz
      rw [mem_antiUnipotentCenter_iff_central] at hz ⊢
      refine ⟨(hg' z).mp hz.1, fun u hu => ?_⟩
      have hu' : g'⁻¹ * u * g' ∈ antiUnipotent K :=
        (hg' _).mpr (by rwa [show g' * (g'⁻¹ * u * g') * g'⁻¹ = u by group])
      have h1 := hz.2 _ hu'
      calc g' * z * g'⁻¹ * u = g' * (z * (g'⁻¹ * u * g')) * g'⁻¹ := by group
        _ = g' * ((g'⁻¹ * u * g') * z) * g'⁻¹ := by rw [h1]
        _ = u * (g' * z * g'⁻¹) := by group
    have hginv : ∀ h, h ∈ antiUnipotent K ↔ g⁻¹ * h * g⁻¹⁻¹ ∈ antiUnipotent K := by
      intro h
      constructor
      · intro hh
        apply (hg _).mpr
        rwa [show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h by group]
      · intro hh
        have := (hg _).mp hh
        rwa [show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h by group] at this
    intro z
    refine ⟨hconj g hg z, fun hz => ?_⟩
    have := hconj g⁻¹ hginv _ hz
    rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this

theorem exists_conj_mem_center [Finite K] {x : antiSp K} (hx : x * x = 1) :
    ∃ g : antiSp K, g * x * g⁻¹ ∈ antiUnipotentCenter K := by
  have hT := (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  have hB : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, sq, hx,
      _root_.one_zpow]
  obtain ⟨m, -, hm⟩ := CFSG.QuasithinUnique.BenderStart.exists_mem_conj_mem_of_isSylowTwoOf hT
    le_top le_top hB
  have hxU := hm x (Subgroup.mem_zpowers x)
  have hsq : m⁻¹ * x * m * (m⁻¹ * x * m) = 1 := by
    rw [show m⁻¹ * x * m * (m⁻¹ * x * m) = m⁻¹ * (x * x) * m by group, hx]
    group
  rcases (mul_self_eq_one_iff hxU).mp hsq with h1 | h1
  · obtain ⟨h, hh⟩ := exists_conj_mem_center_of_mem_radA1 h1
    exact ⟨h * m⁻¹, by rwa [show h * m⁻¹ * x * (h * m⁻¹)⁻¹ = h * (m⁻¹ * x * m) * h⁻¹ by group]⟩
  · obtain ⟨h, hh⟩ := exists_conj_mem_center_of_mem_radA2 h1
    exact ⟨h * m⁻¹, by rwa [show h * m⁻¹ * x * (h * m⁻¹)⁻¹ = h * (m⁻¹ * x * m) * h⁻¹ by group]⟩

end CharTwo

end SymplecticFourFusion

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b in
theorem even_symplectic_four_Sylow_center_normalizer_and_fusion {K : Type} [Field K] [CharP K 2]
    [Finite K] :
    (∀ g : antiSp K, g ∈ antiUnipotentCenter K ↔
      g ∈ antiUnipotent K ∧ ∀ h ∈ antiUnipotent K, g * h = h * g) ∧
      Subgroup.normalizer (antiUnipotentCenter K : Set (antiSp K)) =
        Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) ∧
      ∀ x : antiSp K, orderOf x = 2 → ∃ g : antiSp K, g * x * g⁻¹ ∈ antiUnipotentCenter K :=
  ⟨mem_antiUnipotentCenter_iff_central, SymplecticFourFusion.normalizer_center_eq,
    fun _ hx => SymplecticFourFusion.exists_conj_mem_center
      (by rw [← sq, ← hx, pow_orderOf_eq_one])⟩

end CFSG.LocalAnalysis
