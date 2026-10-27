module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxK1

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

structure IsK (H A D₁ L R K : Subgroup Γ) : Prop where
  admits : Admits (H ⊔ A) K
  L_le : L ≤ K
  le_R : K ≤ R
  ne : K ⊔ D₁ ≠ R

theorem commutator_mul_of_commute {e t k : Γ} (h : e * t = t * e) : ⁅e, k * t⁆ = ⁅e, k⁆ := by
  have h1 : Commute t e := h.symm
  have h2 : t * e⁻¹ * t⁻¹ = e⁻¹ := by
    rw [h1.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅e, k * t⁆ = e * k * (t * e⁻¹ * t⁻¹) * k⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅e, k⁆ := by rw [h2]; rfl

namespace Red

theorem exists_maximal_K [Finite Γ] (c : Red p H A D D₁ D₂ E L R) :
    ∃ K, IsK H A D₁ L R K ∧ ∀ K', IsK H A D₁ L R K' → K ≤ K' → K' ≤ K := by
  have hL : IsK H A D₁ L R L := ⟨c.hLG, le_rfl, c.L_le_R, by
    rw [sup_eq_right.mpr c.L_le_D₁]
    exact c.R_ne_D₁.symm⟩
  obtain ⟨K, hK, hmax⟩ := (Set.toFinite {K | IsK H A D₁ L R K}).exists_maximal ⟨L, hL⟩
  exact ⟨K, hK, fun K' hK' h => hmax hK' h⟩

theorem exists_K₁ [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {K : Subgroup Γ}
    (hK : IsK H A D₁ L R K) (hmax : ∀ K', IsK H A D₁ L R K' → K ≤ K' → K' ≤ K) :
    ∃ K₁ : Subgroup Γ, Admits (H ⊔ A) K₁ ∧ K < K₁ ∧ K₁ ≤ R ∧
      (∀ M : Subgroup Γ, Admits (H ⊔ A) M → K ≤ M → M ≤ K₁ → M = K ∨ M = K₁) ∧
      K₁ ⊔ D₁ = R := by
  have hKR : K < R := by
    refine lt_of_le_of_ne hK.le_R fun h => hK.ne ?_
    rw [h, sup_eq_left.mpr c.D₁_le_R]
  obtain ⟨K₁, ⟨hK₁adm, hKK₁, hK₁R⟩, hmin⟩ := (Set.toFinite {K₁ : Subgroup Γ |
    Admits (H ⊔ A) K₁ ∧ K < K₁ ∧ K₁ ≤ R}).exists_minimal ⟨R, c.admits_R_G, hKR, le_rfl⟩
  refine ⟨K₁, hK₁adm, hKK₁, hK₁R, fun M hM hKM hMK₁ => ?_, ?_⟩
  · by_cases hMK : M = K
    · exact Or.inl hMK
    · exact Or.inr (le_antisymm hMK₁ (hmin ⟨hM, lt_of_le_of_ne hKM (Ne.symm hMK),
        hMK₁.trans hK₁R⟩ hMK₁))
  · by_contra hne
    have := hmax K₁ ⟨hK₁adm, hK.L_le.trans hKK₁.le, hK₁R, hne⟩ hKK₁.le
    exact absurd (this.trans_lt' hKK₁) (lt_irrefl _)

theorem A_le_centralizer (c : Red p H A D D₁ D₂ E L R) {e : Γ} (heA : e ∈ A) :
    A ≤ Subgroup.centralizer {e} := fun _ ha =>
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem c.h15.a1_elemAbelian.1 ha heA).eq

theorem D_le_centralizer_singleton (c : Red p H A D D₁ D₂ E L R) {e : Γ} (heA : e ∈ A) :
    D ≤ Subgroup.centralizer {e} := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (c.h15.D_le_centralizer hx) e heA).symm

theorem ne_of_cen [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {K K₁ : Subgroup Γ}
    (hK : Admits (H ⊔ A) K) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hKR : K ≤ R)
    (hK₁ : Admits (H ⊔ A) K₁) (hK₁R : K₁ ≤ R) (hK₁D : K₁ ⊔ D₁ = R)
    {e : Γ} (he : e ∈ E) (he1 : e ≠ 1) :
    K ⊔ (H ⊓ Subgroup.centralizer {e}) ⊔ A ≠ H ⊔ A := by
  intro heq
  have heA : e ∈ A := c.hEA he
  have heG : e ∈ H ⊔ A := Subgroup.mem_sup_right heA
  have hH₀H : K ⊔ (H ⊓ Subgroup.centralizer {e}) ≤ H := sup_le (hKR.trans c.R_le_H) inf_le_left
  have hH₀A : Admits A (K ⊔ (H ⊓ Subgroup.centralizer {e})) :=
    (hK.mono_left le_sup_right).sup (c.h15.a1_admits.inf
      (admits_centralizer_singleton (c.A_le_centralizer heA)))
  have hHle : H ≤ K ⊔ (H ⊓ Subgroup.centralizer {e}) := fun x hx =>
    c.h15.inf_sup_le_of_le hH₀H hH₀A (Subgroup.mem_inf.mpr ⟨hx, heq ▸ Subgroup.mem_sup_left hx⟩)
  have hXK : H ⊓ Subgroup.centralizer {e} ≤ Subgroup.normalizer (K : Set Γ) := fun g hg =>
    hK (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hg).1)
  refine he1 (c.eq_one_of_cen hK hKab hKR hK₁ hK₁R hK₁D he fun x hx => ?_)
  obtain ⟨k, hk, t, ht, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hXK).mp
    (hHle (c.R_le_H (hK₁R hx)))
  have htc : e * t = t * e :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ht).2).symm
  rw [commutator_mul_of_commute htc, commutatorElement_def]
  exact mul_mem (hK.conj_mem heG hk) (inv_mem hk)

theorem hasB_cen [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {K : Subgroup Γ}
    (hK : Admits (H ⊔ A) K) (hLK : L ≤ K) (hKR : K ≤ R) {e : Γ} (he : e ∈ E)
    (hne : K ⊔ (H ⊓ Subgroup.centralizer {e}) ⊔ A ≠ H ⊔ A) :
    HasB A D D₁ D₂ (K ⊔ (R ⊓ Subgroup.centralizer {e})) := by
  have heA : e ∈ A := c.hEA he
  have hDC := c.D_le_centralizer_singleton heA
  have hDAC : D ⊔ A ≤ Subgroup.centralizer {e} := sup_le hDC (c.A_le_centralizer heA)
  have hH₀H : K ⊔ (H ⊓ Subgroup.centralizer {e}) ≤ H := sup_le (hKR.trans c.R_le_H) inf_le_left
  have hDH₀ : D ≤ K ⊔ (H ⊓ Subgroup.centralizer {e}) :=
    (le_inf c.D_le hDC).trans le_sup_right
  have hKDA : Admits (D ⊔ A) K := hK.mono_left c.DA_le_G
  have hC : Admits (D ⊔ A) (Subgroup.centralizer {e}) := admits_centralizer_singleton hDAC
  have h6 := c.restrict _ hH₀H hDH₀ (hKDA.sup (c.admits_H.inf hC)) hne
  refine c.hasB_of_hypA6 h6 (sup_le_sup_left (inf_le_inf_right _ c.R_le_H) K)
    (hLK.trans le_sup_left) (sup_le hKR inf_le_left) (hKDA.sup (c.admits_R.inf hC)) ?_
  refine le_antisymm ((inf_le_inf_right D (sup_le hKR inf_le_left)).trans c.hRD.le)
    (le_inf ((le_inf c.D₁_le_R (c.D₁_le_D.trans hDC)).trans le_sup_right) c.D₁_le_D)

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
