module

public import CFSG.Quasithin.MS93.S45RA

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

section Pairing

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]
variable {K Q D Vh Z : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}

theorem coord_conj_of_mem_ker (Nd : NatSec K Vh Z ψ true) (hQK : Q ≤ K)
    (hQ1 : ∀ x (hx : x ∈ Q), toSL3 ψ ⟨x, hQK hx⟩ = 1) {x u : 𝔾} (hx : x ∈ Q) (hu : u ∈ Vh) :
    x * u * x⁻¹ ∈ Vh ∧ Nd.coord (x * u * x⁻¹) = Nd.coord u := by
  have hc := Nd.coord_conj ⟨x, hQK hx⟩ hu
  rw [natAct_true, hQ1 x hx, dualMat_one, Matrix.one_mulVec] at hc
  exact ⟨Nd.conj_mem ⟨x, hQK hx⟩ hu, hc⟩

theorem coord_comm_mul_left (Nd : NatSec K Vh Z ψ true) (hQK : Q ≤ K)
    (hQ1 : ∀ x (hx : x ∈ Q), toSL3 ψ ⟨x, hQK hx⟩ = 1) (hDQ : D ≤ Q) (hDD : ⁅D, D⁆ ≤ Vh)
    {x₁ x₂ y : 𝔾} (hx₁ : x₁ ∈ D) (hx₂ : x₂ ∈ D) (hy : y ∈ D) :
    Nd.coord ⁅x₁ * x₂, y⁆ = Nd.coord ⁅x₁, y⁆ + Nd.coord ⁅x₂, y⁆ := by
  have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hm₂ : ⁅x₂, y⁆ ∈ Vh := hDD (Subgroup.commutator_mem_commutator hx₂ hy)
  have hm₁ : ⁅x₁, y⁆ ∈ Vh := hDD (Subgroup.commutator_mem_commutator hx₁ hy)
  obtain ⟨hmem, hc⟩ := coord_conj_of_mem_ker Nd hQK hQ1 (hDQ hx₁) hm₂
  rw [Nd.coord_mul hmem hm₁, hc, add_comm]

theorem coord_comm_mul_right (Nd : NatSec K Vh Z ψ true) (hQK : Q ≤ K)
    (hQ1 : ∀ x (hx : x ∈ Q), toSL3 ψ ⟨x, hQK hx⟩ = 1) (hDQ : D ≤ Q) (hDD : ⁅D, D⁆ ≤ Vh)
    {x y₁ y₂ : 𝔾} (hx : x ∈ D) (hy₁ : y₁ ∈ D) (hy₂ : y₂ ∈ D) :
    Nd.coord ⁅x, y₁ * y₂⁆ = Nd.coord ⁅x, y₁⁆ + Nd.coord ⁅x, y₂⁆ := by
  have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hm₂ : ⁅x, y₂⁆ ∈ Vh := hDD (Subgroup.commutator_mem_commutator hx hy₂)
  have hm₁ : ⁅x, y₁⁆ ∈ Vh := hDD (Subgroup.commutator_mem_commutator hx hy₁)
  obtain ⟨hmem, hc⟩ := coord_conj_of_mem_ker Nd hQK hQ1 (hDQ hy₁) hm₂
  rw [Nd.coord_mul hm₁ hmem, hc]

theorem coord_comm_conj (Nd : NatSec K Vh Z ψ true) (hDD : ⁅D, D⁆ ≤ Vh) (k : ↥K) {x y : 𝔾}
    (hx : x ∈ D) (hy : y ∈ D) :
    Nd.coord ⁅(k : 𝔾) * x * (k : 𝔾)⁻¹, (k : 𝔾) * y * (k : 𝔾)⁻¹⁆ =
      dualMat (toSL3 ψ k) *ᵥ Nd.coord ⁅x, y⁆ := by
  rw [← ML3.conj_commutatorElement,
    Nd.coord_conj k (hDD (Subgroup.commutator_mem_commutator hx hy)), natAct_true]

theorem exists_commutator_not_mem_of_pairing {W X' Y' C Cr V : Subgroup 𝔾}
    (hψ : Function.Surjective ψ) (Nd : NatSec K Vh Z ψ true)
    (Nx : NatSec K X' W ψ false) (Ny : NatSec K Y' W ψ false)
    (hQK : Q ≤ K) (hQ1 : ∀ x (hx : x ∈ Q), toSL3 ψ ⟨x, hQK hx⟩ = 1) (hDQ : D ≤ Q)
    (hDD : ⁅D, D⁆ ≤ Vh) (hWQ : ⁅W, Q⁆ ≤ Z) (hWD : W ≤ D)
    (hXD : C ⊔ X' ≤ D) (hYD : Cr ⊔ Y' ≤ D) (hVD : V ≤ D)
    (hC : ∀ k : ↥K, ∀ x ∈ C, x⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹) ∈ W)
    (hCr : ∀ k : ↥K, ∀ x ∈ Cr, x⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹) ∈ W)
    (hXV : X' ≤ V ⊔ W) (hYV : Y' ≤ V ⊔ W) (hKW : K ≤ Subgroup.normalizer (W : Set 𝔾))
    {z y : 𝔾} (hz : z ∈ C ⊔ X') (hy : y ∈ Cr ⊔ Y') (hzy : ⁅z, y⁆ ∉ Z) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, ⁅v₁, v₂⁆ ∉ Z := by
  classical
  have hDK : D ≤ K := hDQ.trans hQK
  have hCD : C ≤ D := le_sup_left.trans hXD
  have hX'D : X' ≤ D := le_sup_right.trans hXD
  have hCrD : Cr ≤ D := le_sup_left.trans hYD
  have hY'D : Y' ≤ D := le_sup_right.trans hYD
  have hcz : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ Vh := fun x hx y hy =>
    hDD (Subgroup.commutator_mem_commutator hx hy)
  have hadd₁ := fun {x₁ x₂ y : 𝔾} => coord_comm_mul_left (x₁ := x₁) (x₂ := x₂) (y := y) Nd hQK
    hQ1 hDQ hDD
  have hadd₂ := fun {x y₁ y₂ : 𝔾} => coord_comm_mul_right (x := x) (y₁ := y₁) (y₂ := y₂) Nd hQK
    hQ1 hDQ hDD
  have hBW₁ : ∀ w ∈ W, ∀ y ∈ D, Nd.coord ⁅w, y⁆ = 0 := fun w hw y hy =>
    (Nd.coord_eq_zero_iff (hcz w (hWD hw) y hy)).mpr
      (hWQ (Subgroup.commutator_mem_commutator hw (hDQ hy)))
  have hBW₂ : ∀ x ∈ D, ∀ w ∈ W, Nd.coord ⁅x, w⁆ = 0 := fun x hx w hw => by
    have hm := hWQ (Subgroup.commutator_mem_commutator hw (hDQ hx))
    rw [← commutatorElement_inv] at hm
    exact (Nd.coord_eq_zero_iff (hcz x hx w (hWD hw))).mpr (by simpa using Z.inv_mem hm)
  have hconj : ∀ {E : Subgroup 𝔾}, E ≤ D →
      (∀ k : ↥K, ∀ x ∈ E, x⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹) ∈ W) →
      ∀ k : ↥K, ∀ x ∈ E, ∃ w ∈ W, (k : 𝔾)⁻¹ * x * (k : 𝔾) = x * w := by
    intro E hED hE k x hx
    refine ⟨x⁻¹ * ((k : 𝔾)⁻¹ * x * (k : 𝔾)), ?_, by group⟩
    have := hE k⁻¹ x hx
    simpa using this
  have hCa : ∀ c ∈ C, ∀ y ∈ Cr ⊔ Y', Nd.coord ⁅c, y⁆ = 0 := by
    intro c hc
    refine eq_zero_of_natSec_of_trivial hψ Ny (fun y => Nd.coord ⁅c, y⁆) (hCrD.trans hDK)
      (fun y₁ hy₁ y₂ hy₂ => hadd₂ (hCD hc) (hYD hy₁) (hYD hy₂))
      (fun w hw => hBW₂ c (hCD hc) w hw) (fun k y hy => ?_) hCr
    obtain ⟨w, hw, hcw⟩ := hconj hCD hC k c hc
    have hc' : (k : 𝔾)⁻¹ * c * (k : 𝔾) ∈ D := by
      rw [hcw]; exact D.mul_mem (hCD hc) (hWD hw)
    have e : c = (k : 𝔾) * ((k : 𝔾)⁻¹ * c * (k : 𝔾)) * (k : 𝔾)⁻¹ := by group
    show Nd.coord ⁅c, (k : 𝔾) * y * (k : 𝔾)⁻¹⁆ = dualMat (toSL3 ψ k) *ᵥ Nd.coord ⁅c, y⁆
    conv_lhs => rw [e]
    rw [coord_comm_conj Nd hDD k hc' (hYD hy), hcw, hadd₁ (hCD hc) (hWD hw) (hYD hy),
      hBW₁ w hw y (hYD hy), add_zero]
  have hCb : ∀ c ∈ Cr, ∀ x ∈ C ⊔ X', Nd.coord ⁅x, c⁆ = 0 := by
    intro c hc
    refine eq_zero_of_natSec_of_trivial hψ Nx (fun x => Nd.coord ⁅x, c⁆) (hCD.trans hDK)
      (fun x₁ hx₁ x₂ hx₂ => hadd₁ (hXD hx₁) (hXD hx₂) (hCrD hc))
      (fun w hw => hBW₁ w hw c (hCrD hc)) (fun k x hx => ?_) hC
    obtain ⟨w, hw, hcw⟩ := hconj hCrD hCr k c hc
    have hc' : (k : 𝔾)⁻¹ * c * (k : 𝔾) ∈ D := by
      rw [hcw]; exact D.mul_mem (hCrD hc) (hWD hw)
    have e : c = (k : 𝔾) * ((k : 𝔾)⁻¹ * c * (k : 𝔾)) * (k : 𝔾)⁻¹ := by group
    show Nd.coord ⁅(k : 𝔾) * x * (k : 𝔾)⁻¹, c⁆ = dualMat (toSL3 ψ k) *ᵥ Nd.coord ⁅x, c⁆
    conv_lhs => rw [e]
    rw [coord_comm_conj Nd hDD k (hXD hx) hc', hcw, hadd₂ (hXD hx) (hCrD hc) (hWD hw),
      hBW₂ x (hXD hx) w hw, add_zero]
  have hzD : z ∈ D := hXD hz
  have hyD : y ∈ D := hYD hy
  have hB0 : Nd.coord ⁅z, y⁆ ≠ 0 := fun h0 => hzy ((Nd.coord_eq_zero_iff (hcz z hzD y hyD)).mp h0)
  have hCn : C ≤ Subgroup.normalizer (X' : Set 𝔾) := (hCD.trans hDK).trans Nx.norm
  have hCrn : Cr ≤ Subgroup.normalizer (Y' : Set 𝔾) := (hCrD.trans hDK).trans Ny.norm
  have hz' := hz
  have hy' := hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hz'
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCrn] at hy'
  obtain ⟨c₁, hc₁, x₁, hx₁, rfl⟩ := Set.mem_mul.mp hz'
  obtain ⟨c₂, hc₂, x₂, hx₂, rfl⟩ := Set.mem_mul.mp hy'
  rw [hadd₁ (hCD hc₁) (hX'D hx₁) hyD, hCa c₁ hc₁ _ hy, zero_add,
    hadd₂ (hX'D hx₁) (hCrD hc₂) (hY'D hx₂),
    hCb c₂ hc₂ x₁ (Subgroup.mem_sup_right hx₁), zero_add] at hB0
  have hVn : V ≤ Subgroup.normalizer (W : Set 𝔾) := (hVD.trans hDK).trans hKW
  have hx₁' := hXV hx₁
  have hx₂' := hYV hx₂
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVn] at hx₁' hx₂'
  obtain ⟨v₁, hv₁, w₁, hw₁, e₁⟩ := Set.mem_mul.mp hx₁'
  obtain ⟨v₂, hv₂, w₂, hw₂, e₂⟩ := Set.mem_mul.mp hx₂'
  rw [← e₁, ← e₂, hadd₁ (hVD hv₁) (hWD hw₁) (D.mul_mem (hVD hv₂) (hWD hw₂)),
    hBW₁ w₁ hw₁ _ (D.mul_mem (hVD hv₂) (hWD hw₂)), add_zero,
    hadd₂ (hVD hv₁) (hVD hv₂) (hWD hw₂), hBW₂ v₁ (hVD hv₁) w₂ hw₂, add_zero] at hB0
  exact ⟨v₁, hv₁, v₂, hv₂, fun hm => hB0
    ((Nd.coord_eq_zero_iff (hcz v₁ (hVD hv₁) v₂ (hVD hv₂))).mpr hm)⟩

end Pairing

end CFSG.Quasithin.MS93.S45R
