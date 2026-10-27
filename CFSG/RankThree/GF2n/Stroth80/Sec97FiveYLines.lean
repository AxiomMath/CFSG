module

import CFSG.RankThree.GF2n.Stroth80.Sec715IrrALin
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveLineX
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Line
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Schur

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.G11.P3Ortho.Om4
open scoped commutatorElement Matrix

namespace HS9

section Generic

variable {G : Type} [Group G]

theorem uline_conj {Z C Y : Subgroup G} {g : G} (hZ : conjSubgroup g Z = Z)
    (hY : conjSubgroup g Y = Y) :
    conjSubgroup g (Uline Z C Y) = Uline Z (conjSubgroup g C) Y := by
  unfold Uline
  change (Z ⊔ ⨆ (y : G) (_ : y ∈ Y), conjSubgroup y C).map
      (MulAut.conj g).toMonoidHom =
    Z ⊔ ⨆ (y : G) (_ : y ∈ Y), conjSubgroup y (conjSubgroup g C)
  have hZ' : Subgroup.map (MulAut.conj g).toMonoidHom Z = Z := hZ
  rw [Subgroup.map_sup, Subgroup.map_iSup]
  simp only [Subgroup.map_iSup, hZ']
  congr 1
  have key : ∀ y : G, conjSubgroup (g * y * g⁻¹) (conjSubgroup g C) =
      conjSubgroup g (conjSubgroup y C) := by
    intro y
    rw [← conjSubgroup_mul ((g * y) * g⁻¹) g C,
      show (g * y) * g⁻¹ * g = g * y by group, conjSubgroup_mul]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun y => iSup_le fun hy => ?_
    have hy' : g * y * g⁻¹ ∈ Y := by
      have hmem : g * y * g⁻¹ ∈ conjSubgroup g Y := by
        rw [mem_conjSubgroup]
        have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        rwa [e]
      rwa [hY] at hmem
    change conjSubgroup g (conjSubgroup y C) ≤
      ⨆ y ∈ Y, conjSubgroup y (conjSubgroup g C)
    rw [← key y]
    exact le_iSup_of_le (g * y * g⁻¹) (le_iSup_of_le hy' le_rfl)
  · refine iSup_le fun y => iSup_le fun hy => ?_
    have hy' : g⁻¹ * y * g ∈ Y := by
      have hmem : y ∈ conjSubgroup g Y := by rw [hY]; exact hy
      rwa [mem_conjSubgroup] at hmem
    have e : conjSubgroup g (conjSubgroup (g⁻¹ * y * g) C) =
        conjSubgroup y (conjSubgroup g C) := by
      rw [← key (g⁻¹ * y * g), show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    rw [← e]
    exact le_iSup_of_le (g⁻¹ * y * g) (le_iSup_of_le hy' le_rfl)

private theorem conj_mem_commutator {U I : Subgroup G} {g : G}
    (hI : conjSubgroup g I = I) (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ I) :
    ∀ x ∈ conjSubgroup g U, ∀ y ∈ conjSubgroup g U, ⁅x, y⁆ ∈ I := by
  intro x hx y hy
  rw [mem_conjSubgroup] at hx hy
  set x₀ : G := g⁻¹ * x * g with hx₀def
  set y₀ : G := g⁻¹ * y * g with hy₀def
  have hx' : x = g * x₀ * g⁻¹ := by rw [hx₀def]; group
  have hy' : y = g * y₀ * g⁻¹ := by rw [hy₀def]; group
  have hmem : ⁅x₀, y₀⁆ ∈ I := hcomm x₀ hx y₀ hy
  have hconj : g * ⁅x₀, y₀⁆ * g⁻¹ ∈ conjSubgroup g I := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * ⁅x₀, y₀⁆ * g⁻¹) * g = ⁅x₀, y₀⁆ := by group
    rwa [e]
  have hconj' : g * ⁅x₀, y₀⁆ * g⁻¹ ∈ I := by rwa [hI] at hconj
  have e : ⁅x, y⁆ = g * ⁅x₀, y₀⁆ * g⁻¹ := by
    rw [hx', hy']
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hconj'

private theorem conj_mem_sq {U I : Subgroup G} {g : G}
    (hI : conjSubgroup g I = I) (hsq : ∀ x ∈ U, x ^ 2 ∈ I) :
    ∀ x ∈ conjSubgroup g U, x ^ 2 ∈ I := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  set x₀ : G := g⁻¹ * x * g with hx₀def
  have hx' : x = g * x₀ * g⁻¹ := by rw [hx₀def]; group
  have hmem : x₀ ^ 2 ∈ I := hsq x₀ hx
  have hconj : g * x₀ ^ 2 * g⁻¹ ∈ conjSubgroup g I := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * x₀ ^ 2 * g⁻¹) * g = x₀ ^ 2 := by group
    rwa [e]
  have hconj' : g * x₀ ^ 2 * g⁻¹ ∈ I := by rwa [hI] at hconj
  have e : (g * x₀ * g⁻¹) ^ 2 = g * x₀ ^ 2 * g⁻¹ := by
    rw [pow_two, pow_two]
    group
  rw [hx', e]
  exact hconj'

private theorem conj_lt {U I : Subgroup G} {g : G} (hI : conjSubgroup g I = I) (hlt : I < U) :
    I < conjSubgroup g U := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have h : conjSubgroup g I < conjSubgroup g U :=
    (Subgroup.map_lt_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom) hinj).mpr hlt
  rwa [hI] at h

private theorem conj_max {R U I : Subgroup G} {g : G} (hR : conjSubgroup g R = R)
    (hI : conjSubgroup g I = I)
    (hmax : ∀ A : Subgroup G, I ≤ A → A ≤ U → (∀ r ∈ R, conjSubgroup r A = A) →
      A = I ∨ A = U) :
    ∀ A : Subgroup G, I ≤ A → A ≤ conjSubgroup g U →
      (∀ r ∈ R, conjSubgroup r A = A) → A = I ∨ A = conjSubgroup g U := by
  intro A hIA hAU hAinv
  have hI1 : I ≤ conjSubgroup g⁻¹ A := by
    have h1 : conjSubgroup g⁻¹ I ≤ conjSubgroup g⁻¹ A := Subgroup.map_mono hIA
    have h2 : conjSubgroup g⁻¹ I = I := by
      calc conjSubgroup g⁻¹ I = conjSubgroup g⁻¹ (conjSubgroup g I) := by rw [hI]
        _ = conjSubgroup (g⁻¹ * g) I := by rw [conjSubgroup_mul]
        _ = conjSubgroup 1 I := by rw [inv_mul_cancel]
        _ = I := conjSubgroup_one I
    rwa [h2] at h1
  have hI2 : conjSubgroup g⁻¹ A ≤ U := by
    have h1 : conjSubgroup g⁻¹ A ≤ conjSubgroup g⁻¹ (conjSubgroup g U) :=
      Subgroup.map_mono hAU
    have h2 : conjSubgroup g⁻¹ (conjSubgroup g U) = U := by
      calc conjSubgroup g⁻¹ (conjSubgroup g U) = conjSubgroup (g⁻¹ * g) U := by
            rw [conjSubgroup_mul]
        _ = conjSubgroup 1 U := by rw [inv_mul_cancel]
        _ = U := conjSubgroup_one U
    rwa [h2] at h1
  have hI3 : ∀ r ∈ R, conjSubgroup r (conjSubgroup g⁻¹ A) = conjSubgroup g⁻¹ A := by
    intro r hr
    have hr' : g * r * g⁻¹ ∈ R := by
      have hmem : g * r * g⁻¹ ∈ conjSubgroup g R := by
        rw [mem_conjSubgroup]
        have e : g⁻¹ * (g * r * g⁻¹) * g = r := by group
        rwa [e]
      rwa [hR] at hmem
    have hAr : conjSubgroup (g * r * g⁻¹) A = A := hAinv _ hr'
    have e : conjSubgroup r (conjSubgroup g⁻¹ A) =
        conjSubgroup g⁻¹ (conjSubgroup (g * r * g⁻¹) A) := by
      rw [← conjSubgroup_mul r g⁻¹ A, ← conjSubgroup_mul g⁻¹ (g * r * g⁻¹) A]
      congr 1
      group
    rw [e, hAr]
  have hAe : conjSubgroup g (conjSubgroup g⁻¹ A) = A := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  rcases hmax (conjSubgroup g⁻¹ A) hI1 hI2 hI3 with hA | hA
  · left
    rw [hA, hI] at hAe
    exact hAe.symm
  · right
    rw [hA] at hAe
    exact hAe.symm

theorem isIrredModule_conj {R U I : Subgroup G} {g : G} (hR : conjSubgroup g R = R)
    (hI : conjSubgroup g I = I) (h : IsIrredModule R U I) :
    IsIrredModule R (conjSubgroup g U) I := by
  obtain ⟨hcomm, hsq, hlt, hmax⟩ := h
  exact ⟨conj_mem_commutator hI hcomm, conj_mem_sq hI hsq, conj_lt hI hlt,
    conj_max hR hI hmax⟩

end Generic

section Ctx

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem le_normalizer_uline (hc : Ctx M Q Z B) {Y : Subgroup G} (hYM : Y ≤ M) :
    Y ≤ Subgroup.normalizer (Uline Z B Y : Set G) := by
  intro y hy
  exact conjSubgroup_eq_self_iff.mp (conj_Uline hc hYM hy)

end Ctx

section MatrixAlgebra

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem range_eq_outerL {H : Subgroup
    (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hH : H = leftF K) (hA : ActsNat H Φ) {a b w₀ : Fin 2 → K} (hb : b ≠ 0)
    (hw₀ : w₀ ≠ 0) (hu : Φ w₀ = Matrix.vecMulVec a b) :
    LinearMap.range Φ = LinearMap.range (outerL b) := by
  have hL : ∀ h ∈ leftF K, ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      rho' K (A, 1) = h := by
    intro h hh
    exact MonoidHom.mem_range.mp hh
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨w, rfl⟩
    by_cases hw : w = 0
    · rw [hw, map_zero]
      exact ⟨0, by simp [outerL]⟩
    · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw₀ hw
      obtain ⟨h, hhH, hh⟩ := hA.lift g
      have hhL : h ∈ leftF K := by rwa [hH] at hhH
      obtain ⟨A, hA'⟩ := hL h hhL
      refine ⟨A *ᵥ a, ?_⟩
      have e : Φ w = outerL b (A *ᵥ a) := by
        calc Φ w = h (Φ w₀) := by rw [hh, hg]
          _ = h (Matrix.vecMulVec a b) := by rw [hu]
          _ = rho' K (A, 1) (Matrix.vecMulVec a b) := by rw [hA']
          _ = (A : Matrix (Fin 2) (Fin 2) K) * Matrix.vecMulVec a b := by
              rw [rho'_inl_apply]
          _ = Matrix.vecMulVec (A *ᵥ a) b := Matrix.mul_vecMulVec _ _ _
          _ = outerL b (A *ᵥ a) := rfl
      exact e.symm
  · rw [LinearMap.finrank_range_of_inj hA.inj,
      LinearMap.finrank_range_of_inj (outerL_injective hb)]

private theorem range_eq_outerR {H : Subgroup
    (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hH : H = rightF K) (hA : ActsNat H Φ) {a b w₀ : Fin 2 → K} (ha : a ≠ 0)
    (hw₀ : w₀ ≠ 0) (hu : Φ w₀ = Matrix.vecMulVec a b) :
    LinearMap.range Φ = LinearMap.range (outerR a) := by
  have hR : ∀ h ∈ rightF K, ∃ B : Matrix.SpecialLinearGroup (Fin 2) K,
      rho' K (1, B) = h := by
    intro h hh
    exact MonoidHom.mem_range.mp hh
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨w, rfl⟩
    by_cases hw : w = 0
    · rw [hw, map_zero]
      exact ⟨0, by simp [outerR]⟩
    · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw₀ hw
      obtain ⟨h, hhH, hh⟩ := hA.lift g
      have hhR : h ∈ rightF K := by rwa [hH] at hhH
      obtain ⟨B, hB'⟩ := hR h hhR
      refine ⟨b ᵥ* ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K), ?_⟩
      have e : Φ w = outerR a (b ᵥ* ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) := by
        calc Φ w = h (Φ w₀) := by rw [hh, hg]
          _ = h (Matrix.vecMulVec a b) := by rw [hu]
          _ = rho' K (1, B) (Matrix.vecMulVec a b) := by rw [hB']
          _ = Matrix.vecMulVec a b * ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K) := by rw [rho'_inr_apply]
          _ = Matrix.vecMulVec a (b ᵥ* ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := Matrix.vecMulVec_mul _ _ _
          _ = outerR a (b ᵥ* ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := rfl
      exact e.symm
  · rw [LinearMap.finrank_range_of_inj hA.inj,
      LinearMap.finrank_range_of_inj (outerR_injective ha)]

private theorem mem_range_outerL_of_mulVec_eq_zero {b c : Fin 2 → K} (hb : b ≠ 0)
    (hc : c ≠ 0) (hbc : b ⬝ᵥ c = 0) {X : Matrix (Fin 2) (Fin 2) K} (hX : X *ᵥ c = 0) :
    X ∈ LinearMap.range (outerL b) := by
  have hrow : ∀ i, X.row i ⬝ᵥ c = 0 := by
    intro i
    have h := congrFun hX i
    simpa [Matrix.mulVec, dotProduct, Matrix.row] using h
  have hcb : c ⬝ᵥ b = 0 := by rwa [dotProduct_comm] at hbc
  choose t ht using fun i => S715L.exists_eq_smul_of_dotProduct_eq_zero hc hb hcb
    (by rw [dotProduct_comm]; exact hrow i)
  refine ⟨t, ?_⟩
  ext i j
  have h := congrFun (ht i) j
  simpa [outerL, Matrix.vecMulVec_apply, Matrix.row, Pi.smul_apply, smul_eq_mul] using h.symm

private theorem mem_range_outerR_of_transpose_mulVec_eq_zero {a c : Fin 2 → K} (ha : a ≠ 0)
    (hc : c ≠ 0) (hac : a ⬝ᵥ c = 0) {X : Matrix (Fin 2) (Fin 2) K} (hX : Xᵀ *ᵥ c = 0) :
    X ∈ LinearMap.range (outerR a) := by
  have hcol : ∀ i, X.col i ⬝ᵥ c = 0 := by
    intro i
    have h := congrFun hX i
    simpa [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose] using h
  have hca : c ⬝ᵥ a = 0 := by rwa [dotProduct_comm] at hac
  choose t ht using fun i => S715L.exists_eq_smul_of_dotProduct_eq_zero hc ha hca
    (by rw [dotProduct_comm]; exact hcol i)
  refine ⟨t, ?_⟩
  ext i j
  have h := congrFun (ht j) i
  simp only [outerR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply, Matrix.col,
    Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [mul_comm]
  exact h.symm

end MatrixAlgebra

section ImageDichotomy

variable {G : Type} [Group G] {V Z B Y D : Subgroup G}
  [((Z.subgroupOf V).Normal)]
variable {K : Type} [Field K]
variable {ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)}
variable {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K}

private def imageSubgroup {G : Type} [Group G] {V Z D : Subgroup G}
    [((Z.subgroupOf V).Normal)] {K : Type} [Field K]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (hDV : D ≤ V) (π : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K)) :
    AddSubgroup (Fin 2 → K) :=
  { carrier := {z | ∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = z}
    zero_mem' := by
      refine ⟨⟨1, D.one_mem⟩, ?_⟩
      have h1 : cmat ψ ⟨(1 : G), hDV D.one_mem⟩ = 0 :=
        (cmat_eq_zero_iff ψ _).mpr Z.one_mem
      show π (cmat ψ ⟨(1 : G), hDV D.one_mem⟩) = 0
      rw [h1, map_zero]
    add_mem' := by
      intro z₁ z₂ hz₁ hz₂
      obtain ⟨x₁, hx₁⟩ := hz₁
      obtain ⟨x₂, hx₂⟩ := hz₂
      rw [← hx₁, ← hx₂]
      refine ⟨⟨x₁.1 * x₂.1, D.mul_mem x₁.2 x₂.2⟩, ?_⟩
      have e : cmat ψ ⟨x₁.1 * x₂.1, hDV (D.mul_mem x₁.2 x₂.2)⟩ =
          cmat ψ ⟨x₁.1, hDV x₁.2⟩ + cmat ψ ⟨x₂.1, hDV x₂.2⟩ := by
        simpa using cmat_mul ψ ⟨x₁.1, hDV x₁.2⟩ ⟨x₂.1, hDV x₂.2⟩
      show π (cmat ψ ⟨x₁.1 * x₂.1, hDV (D.mul_mem x₁.2 x₂.2)⟩) =
        π (cmat ψ ⟨x₁.1, hDV x₁.2⟩) + π (cmat ψ ⟨x₂.1, hDV x₂.2⟩)
      rw [e, map_add]
    neg_mem' := by
      intro z hz
      obtain ⟨x, hx⟩ := hz
      rw [← hx]
      refine ⟨⟨x.1⁻¹, D.inv_mem x.2⟩, ?_⟩
      have e : cmat ψ ⟨x.1⁻¹, hDV (D.inv_mem x.2)⟩ = -cmat ψ ⟨x.1, hDV x.2⟩ := by
        have h := cmat_inv ψ ⟨x.1, hDV x.2⟩
        rwa [show (⟨x.1, hDV x.2⟩ : ↥V)⁻¹ = ⟨x.1⁻¹, hDV (D.inv_mem x.2)⟩ from
          Subtype.ext rfl] at h
      show π (cmat ψ ⟨x.1⁻¹, hDV (D.inv_mem x.2)⟩) = -π (cmat ψ ⟨x.1, hDV x.2⟩)
      rw [e, map_neg] }

private theorem eq_uline_of_image_of_bot (hDV : D ≤ V)
    (π : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K))
    (hker : ∀ X : Matrix (Fin 2) (Fin 2) K, π X = 0 → X ∈ LinearMap.range Φ)
    (hU : ∀ x : G, x ∈ Uline Z B Y ↔ ∃ hx : x ∈ V, cmat ψ ⟨x, hx⟩ ∈ LinearMap.range Φ)
    (hlo : Uline Z B Y ≤ D) (hSbot : imageSubgroup ψ hDV π = ⊥) :
    D = Uline Z B Y := by
  refine le_antisymm ?_ hlo
  intro x hx
  have hxV : x ∈ V := hDV hx
  have h0 : π (cmat ψ ⟨x, hxV⟩) = 0 := by
    have hmem : π (cmat ψ ⟨x, hxV⟩) ∈ imageSubgroup ψ hDV π := ⟨⟨x, hx⟩, rfl⟩
    rw [hSbot] at hmem
    exact AddSubgroup.mem_bot.mp hmem
  exact (hU x).mpr ⟨hxV, hker _ h0⟩

private theorem not_le_of_image_ne_bot (hDV : D ≤ V)
    (π : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K))
    (hker : ∀ X : Matrix (Fin 2) (Fin 2) K, π X = 0 → X ∈ LinearMap.range Φ)
    (hstab : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ z : Fin 2 → K,
      (∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = z) →
      ∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = g *ᵥ z)
    (hU : ∀ x : G, x ∈ Uline Z B Y ↔ ∃ hx : x ∈ V, cmat ψ ⟨x, hx⟩ ∈ LinearMap.range Φ)
    (hlo : Uline Z B Y ≤ D) (hne : ¬ V ≤ D)
    (hSne : imageSubgroup ψ hDV π ≠ ⊥) : False := by
  have hne0 : ∃ s ∈ imageSubgroup ψ hDV π, s ≠ 0 := by
    by_contra h
    push Not at h
    apply hSne
    rw [eq_bot_iff]
    intro s hs
    exact AddSubgroup.mem_bot.mpr (h s hs)
  obtain ⟨s, hsS, hs0⟩ := hne0
  have hStop : imageSubgroup ψ hDV π = ⊤ := by
    refine le_antisymm le_top ?_
    intro z _
    by_cases hz : z = 0
    · rw [hz]; exact (imageSubgroup ψ hDV π).zero_mem
    · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hs0 hz
      rw [← hg]
      exact hstab g s hsS
  have hVD : V ≤ D := by
    intro u hu
    have hmem : π (cmat ψ ⟨u, hu⟩) ∈ imageSubgroup ψ hDV π := by
      rw [hStop]; exact AddSubgroup.mem_top _
    obtain ⟨d, hdπ⟩ := hmem
    have hdV : d.1 ∈ V := hDV d.2
    have hmemV : u * d.1⁻¹ ∈ V := V.mul_mem hu (V.inv_mem hdV)
    have hcm : cmat ψ ⟨u * d.1⁻¹, hmemV⟩ =
        cmat ψ ⟨u, hu⟩ - cmat ψ ⟨d.1, hdV⟩ := by
      calc cmat ψ ⟨u * d.1⁻¹, hmemV⟩ = cmat ψ (⟨u, hu⟩ * ⟨d.1, hdV⟩⁻¹) := rfl
        _ = cmat ψ ⟨u, hu⟩ + cmat ψ ⟨d.1, hdV⟩⁻¹ := cmat_mul ψ _ _
        _ = cmat ψ ⟨u, hu⟩ + (-cmat ψ ⟨d.1, hdV⟩) := by rw [cmat_inv]
        _ = cmat ψ ⟨u, hu⟩ - cmat ψ ⟨d.1, hdV⟩ := by rw [sub_eq_add_neg]
    have hdπ' : π (cmat ψ ⟨d.1, hdV⟩) = π (cmat ψ ⟨u, hu⟩) := by
      simpa [imageSubgroup] using hdπ
    have hπ0 : π (cmat ψ ⟨u * d.1⁻¹, hmemV⟩) = 0 := by
      rw [hcm, map_sub, hdπ', sub_self]
    have hU' : u * d.1⁻¹ ∈ Uline Z B Y := (hU _).mpr ⟨hmemV, hker _ hπ0⟩
    have hD' : u * d.1⁻¹ ∈ D := hlo hU'
    have e : u = (u * d.1⁻¹) * d.1 := by group
    rw [e]
    exact D.mul_mem hD' d.2
  exact hne hVD

private theorem eq_uline_of_image (hDV : D ≤ V)
    (π : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K))
    (hker : ∀ X : Matrix (Fin 2) (Fin 2) K, π X = 0 → X ∈ LinearMap.range Φ)
    (hstab : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ z : Fin 2 → K,
      (∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = z) →
      ∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = g *ᵥ z)
    (hU : ∀ x : G, x ∈ Uline Z B Y ↔ ∃ hx : x ∈ V, cmat ψ ⟨x, hx⟩ ∈ LinearMap.range Φ)
    (hlo : Uline Z B Y ≤ D) (hne : ¬ V ≤ D) : D = Uline Z B Y := by
  by_cases hSbot : imageSubgroup ψ hDV π = ⊥
  · exact eq_uline_of_image_of_bot hDV π hker hU hlo hSbot
  · exact False.elim (not_le_of_image_ne_bot hDV π hker hstab hU hlo hne hSbot)

end ImageDichotomy

section LeftFactor

variable {G : Type} [Group G] {V Z B Y D R : Subgroup G} [((Z.subgroupOf V).Normal)]
variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K}
variable {ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)}
variable {u : Fin 2 ⊕ Fin 2 → K}
variable {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
variable {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ a b : Fin 2 → K}

private theorem eq_uline_of_inv_coord_left
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    (hA : ActsNat H Φ) (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀)
    (hHF : H = leftF K) (hM : toMat K u = Matrix.vecMulVec a b) (hb : b ≠ 0)
    (hDV : D ≤ V) (hD : ∀ y ∈ Y, conjSubgroup y D = D)
    (hlo : Uline Z B Y ≤ D) (hne : ¬ V ≤ D) : D = Uline Z B Y := by
  have hΦw : Φ w₀ = Matrix.vecMulVec a b := by rw [← hu, hM]
  have hrange : LinearMap.range Φ = LinearMap.range (outerL b) :=
    range_eq_outerL hHF hA hb hw₀ hΦw
  obtain ⟨c, hc0, hcb⟩ := exists_ne_zero_dotProduct_eq_zero b
  have hbc : b ⬝ᵥ c = 0 := by rwa [dotProduct_comm] at hcb
  let π : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K) :=
    { toFun := fun X => X *ᵥ c
      map_add' := fun X Y => Matrix.add_mulVec X Y c
      map_smul' := fun r X => Matrix.smul_mulVec r X c }
  have hπapply : ∀ X, π X = X *ᵥ c := fun X => rfl
  have hker : ∀ X : Matrix (Fin 2) (Fin 2) K, π X = 0 → X ∈ LinearMap.range Φ := by
    intro X hX
    rw [hrange]
    exact mem_range_outerL_of_mulVec_eq_zero hb hc0 hbc (by rwa [hπapply] at hX)
  have hstab : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ z : Fin 2 → K,
      (∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = z) →
      ∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = g *ᵥ z := by
    intro g z hz
    obtain ⟨x, rfl⟩ := hz
    have hmemH : rho' K (g, 1) ∈ H := by
      rw [hHF]
      exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
    obtain ⟨s, hsY, hsΨ⟩ := (hH (rho' K (g, 1))).mp hmemH
    have hmemD : (s : G) * x.1 * (s : G)⁻¹ ∈ D := by
      have hmem : (s : G) * x.1 * (s : G)⁻¹ ∈ conjSubgroup (s : G) D := by
        rw [mem_conjSubgroup]
        have e : (s : G)⁻¹ * ((s : G) * x.1 * (s : G)⁻¹) * (s : G) = x.1 := by group
        rw [e]
        exact x.2
      rwa [hD (s : G) hsY] at hmem
    have hmemV : (s : G) * x.1 * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hnorm s.2) x.1).mp (hDV x.2)
    refine ⟨⟨(s : G) * x.1 * (s : G)⁻¹, hmemD⟩, ?_⟩
    have hcm : cmat ψ ⟨(s : G) * x.1 * (s : G)⁻¹, hDV hmemD⟩ =
        Ψ K (φ s) (cmat ψ ⟨x.1, hDV x.2⟩) := by
      have h := cmat_conj ψ φ hψ s ⟨x.1, hDV x.2⟩
        ⟨(s : G) * x.1 * (s : G)⁻¹, hmemV⟩ rfl
      simpa using h
    rw [hcm, hsΨ, rho'_inl_apply]
    show ((g : Matrix (Fin 2) (Fin 2) K) * cmat ψ ⟨x.1, hDV x.2⟩) *ᵥ c =
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (cmat ψ ⟨x.1, hDV x.2⟩ *ᵥ c)
    rw [← Matrix.mulVec_mulVec]
  exact eq_uline_of_image hDV π hker hstab
    (fun x => uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu x) hlo hne

end LeftFactor

section RightFactor

variable {G : Type} [Group G] {V Z B Y D R : Subgroup G} [((Z.subgroupOf V).Normal)]
variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K}
variable {ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)}
variable {u : Fin 2 ⊕ Fin 2 → K}
variable {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
variable {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ a b : Fin 2 → K}

private theorem eq_uline_of_inv_coord_right
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    (hA : ActsNat H Φ) (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀)
    (hHF : H = rightF K) (hM : toMat K u = Matrix.vecMulVec a b) (ha : a ≠ 0)
    (hDV : D ≤ V) (hD : ∀ y ∈ Y, conjSubgroup y D = D)
    (hlo : Uline Z B Y ≤ D) (hne : ¬ V ≤ D) : D = Uline Z B Y := by
  have hΦw : Φ w₀ = Matrix.vecMulVec a b := by rw [← hu, hM]
  have hrange : LinearMap.range Φ = LinearMap.range (outerR a) :=
    range_eq_outerR hHF hA ha hw₀ hΦw
  obtain ⟨c, hc0, hca⟩ := exists_ne_zero_dotProduct_eq_zero a
  have hac : a ⬝ᵥ c = 0 := by rwa [dotProduct_comm] at hca
  let π : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K) :=
    { toFun := fun X => Xᵀ *ᵥ c
      map_add' := fun X Y => by rw [Matrix.transpose_add, Matrix.add_mulVec]
      map_smul' := fun r X => by
        rw [Matrix.transpose_smul, Matrix.smul_mulVec]
        rfl }
  have hπapply : ∀ X, π X = Xᵀ *ᵥ c := fun X => rfl
  have hker : ∀ X : Matrix (Fin 2) (Fin 2) K, π X = 0 → X ∈ LinearMap.range Φ := by
    intro X hX
    rw [hrange]
    exact mem_range_outerR_of_transpose_mulVec_eq_zero ha hc0 hac (by rwa [hπapply] at hX)
  have hstab : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ z : Fin 2 → K,
      (∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = z) →
      ∃ x : D, π (cmat ψ ⟨x.1, hDV x.2⟩) = g *ᵥ z := by
    intro g z hz
    obtain ⟨x, rfl⟩ := hz
    let B₀ : Matrix.SpecialLinearGroup (Fin 2) K := (g.transpose)⁻¹
    have hB₀ : (((B₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K))ᵀ = (g : Matrix (Fin 2) (Fin 2) K) := by
      simp [B₀, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.SpecialLinearGroup.coe_transpose]
    have hmemH : rho' K (1, B₀) ∈ H := by
      rw [hHF]
      exact MonoidHom.mem_range.mpr ⟨B₀, rfl⟩
    obtain ⟨s, hsY, hsΨ⟩ := (hH (rho' K (1, B₀))).mp hmemH
    have hmemD : (s : G) * x.1 * (s : G)⁻¹ ∈ D := by
      have hmem : (s : G) * x.1 * (s : G)⁻¹ ∈ conjSubgroup (s : G) D := by
        rw [mem_conjSubgroup]
        have e : (s : G)⁻¹ * ((s : G) * x.1 * (s : G)⁻¹) * (s : G) = x.1 := by group
        rw [e]
        exact x.2
      rwa [hD (s : G) hsY] at hmem
    have hmemV : (s : G) * x.1 * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hnorm s.2) x.1).mp (hDV x.2)
    refine ⟨⟨(s : G) * x.1 * (s : G)⁻¹, hmemD⟩, ?_⟩
    have hcm : cmat ψ ⟨(s : G) * x.1 * (s : G)⁻¹, hDV hmemD⟩ =
        Ψ K (φ s) (cmat ψ ⟨x.1, hDV x.2⟩) := by
      have h := cmat_conj ψ φ hψ s ⟨x.1, hDV x.2⟩
        ⟨(s : G) * x.1 * (s : G)⁻¹, hmemV⟩ rfl
      simpa using h
    rw [hcm, hsΨ, rho'_inr_apply]
    show (cmat ψ ⟨x.1, hDV x.2⟩ * ((B₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K))ᵀ *ᵥ c =
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ((cmat ψ ⟨x.1, hDV x.2⟩)ᵀ *ᵥ c)
    rw [Matrix.transpose_mul, hB₀, ← Matrix.mulVec_mulVec]
  exact eq_uline_of_image hDV π hker hstab
    (fun x => uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hH hA hw₀ hu x) hlo hne

end RightFactor

section InvCoord

variable {G : Type} [Group G] {V Z B Y D R : Subgroup G} [((Z.subgroupOf V).Normal)]
variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K}
variable {ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K)}
variable {u : Fin 2 ⊕ Fin 2 → K}
variable {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
variable {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} {w₀ : Fin 2 → K}

private theorem eq_uline_of_inv_coord
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) (hYR : Y ≤ R)
    (hZV : Z ≤ V) (hBV : B ≤ V)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hH : ∀ h, h ∈ H ↔ ∃ s : ↥R, (s : G) ∈ Y ∧ Ψ K (φ s) = h)
    (hA : ActsNat H Φ) (hw₀ : w₀ ≠ 0) (hu : toMat K u = Φ w₀)
    (hHF : H = leftF K ∨ H = rightF K) (hdet : (toMat K u).det = 0)
    (hDV : D ≤ V) (hD : ∀ y ∈ Y, conjSubgroup y D = D)
    (hlo : Uline Z B Y ≤ D) (hne : ¬ V ≤ D) : D = Uline Z B Y := by
  have hu0 : toMat K u ≠ 0 := by
    rw [hu]
    intro h
    exact hw₀ (hA.inj (by rw [h, map_zero]))
  obtain ⟨a, b, ha, hb, hM⟩ := exists_vecMulVec_of_det_eq_zero hdet hu0
  rcases hHF with hHF | hHF
  · exact eq_uline_of_inv_coord_left hψ hnorm hYR hZV hBV hBiff hH hA hw₀ hu
      hHF hM hb hDV hD hlo hne
  · exact eq_uline_of_inv_coord_right hψ hnorm hYR hZV hBV hBiff hH hA hw₀ hu
      hHF hM ha hDV hD hlo hne

end InvCoord

section Sec9Data

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem eq_ulineY_of_inv (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {k : G} (hk : k ∈ Rt M (LB M Q B) t) {D : Subgroup G}
    (hD : ∀ y ∈ Y, conjSubgroup y D = D) (hlo : Uline Z (conjSubgroup k B) Y ≤ D)
    (hhi : D ≤ Vt M (LB M Q B) B Z t) (hne : ¬ Vt M (LB M Q B) B Z t ≤ D) :
    D = Uline Z (conjSubgroup k B) Y := by
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, H, Φ, w₀, _, hψ, hnorm, hBiff, hH, hA, hw₀, hu,
    hHF, hdet⟩ := sec97_line_data_of h34 h311a hc hs hsplit (Or.inr rfl)
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := HS9.normalizer_of_commutator_le hQX hcomm
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hRY : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) := by
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le hXY' Subgroup.le_normalizer
  have hYk : conjSubgroup k Y = Y := conjSubgroup_eq_self_iff.mpr (hRY hk)
  have hMk : k ∈ M := Rt_le_M hc.LB_le_M t hk
  have hZk : conjSubgroup k Z = Z := hc.conj_Z_eq hMk
  have hVk : conjSubgroup k (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hk)
  have hUk : conjSubgroup k (Uline Z B Y) = Uline Z (conjSubgroup k B) Y :=
    uline_conj hZk hYk
  set D' : Subgroup G := conjSubgroup k⁻¹ D with hD'def
  have hD' : ∀ y ∈ Y, conjSubgroup y D' = D' := by
    intro y hy
    have hky : k * y * k⁻¹ ∈ Y := by
      have hmem : k * y * k⁻¹ ∈ conjSubgroup k Y := by
        rw [mem_conjSubgroup]
        have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
        rwa [e]
      rwa [hYk] at hmem
    rw [hD'def]
    calc conjSubgroup y (conjSubgroup k⁻¹ D)
        = conjSubgroup (y * k⁻¹) D := by rw [← conjSubgroup_mul]
      _ = conjSubgroup (k⁻¹ * (k * y * k⁻¹)) D := by congr 1; group
      _ = conjSubgroup k⁻¹ (conjSubgroup (k * y * k⁻¹) D) := by rw [conjSubgroup_mul]
      _ = conjSubgroup k⁻¹ D := by rw [hD _ hky]
  have hlo' : Uline Z B Y ≤ D' := by
    have h1 : conjSubgroup k (Uline Z B Y) ≤ D := by
      rw [hUk]
      exact hlo
    have h2 : Uline Z B Y = conjSubgroup k⁻¹ (conjSubgroup k (Uline Z B Y)) := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [h2, hD'def]
    exact Subgroup.map_mono h1
  have hhi' : D' ≤ Vt M (LB M Q B) B Z t := by
    rw [hD'def]
    calc conjSubgroup k⁻¹ D ≤ conjSubgroup k⁻¹ (Vt M (LB M Q B) B Z t) :=
          Subgroup.map_mono hhi
      _ = conjSubgroup k⁻¹ (conjSubgroup k (Vt M (LB M Q B) B Z t)) := by rw [hVk]
      _ = Vt M (LB M Q B) B Z t := by
          rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hne' : ¬ Vt M (LB M Q B) B Z t ≤ D' := by
    intro hle
    apply hne
    have h1 : conjSubgroup k (Vt M (LB M Q B) B Z t) ≤ conjSubgroup k D' :=
      Subgroup.map_mono hle
    have h2 : conjSubgroup k D' = D := by
      rw [hD'def, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    rwa [hVk, h2] at h1
  have hD'eq : D' = Uline Z B Y :=
    eq_uline_of_inv_coord hψ hnorm hYR sec39_Z_le_Vt (hc.B_le_Vt hs.mem) hBiff hH
      hA hw₀ hu hHF hdet hhi' hD' hlo' hne'
  have hDk : D = conjSubgroup k D' := by
    rw [hD'def, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  rw [hDk, hD'eq, hUk]

theorem uline_inf_CQt (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) :
    Uline Z B Y ⊓ CQtGrp hc (LB M Q B ⊓ Y) = B ⊔ Z := by
  obtain ⟨-, -, Y₀, hY₀Y, hY₀B, hY₀fix⟩ :=
    sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit
  have hY₀LB : Y₀ ≤ LB M Q B ⊓ Y := by
    intro y hy
    exact (h4.1 y).mpr ⟨hY₀Y hy, fun b hb => hY₀B b hb y hy⟩
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.mp hu
    have huC' : ∀ y ∈ LB M Q B ⊓ Y, ⁅y, u⁆ ∈ Z := (mem_CQtGrp.mp huC).2
    exact hY₀fix u huU fun y hy => huC' y (hY₀LB hy)
  · refine sup_le ?_ ?_
    · intro b hb
      refine Subgroup.mem_inf.mpr ⟨B_le_Uline Z B Y hb, ?_⟩
      rw [mem_CQtGrp]
      exact ⟨hc.le hb, fun s hs => hc.comm_B_mem_Z hs.1 hb⟩
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨Z_le_Uline Z B Y hz, ?_⟩
      rw [mem_CQtGrp]
      refine ⟨hc.hyp.Z_normal.1 hz, fun s hs => ?_⟩
      have h1 : s * z * s⁻¹ = z := hc.LB_centralizes_Z hs.1 z hz
      have e : ⁅s, z⁆ = 1 := by rw [commutatorElement_def, h1]; group
      rw [e]
      exact Z.one_mem

end Sec9Data

end HS9

end CFSG.RankThree.GF2n.Stroth80
