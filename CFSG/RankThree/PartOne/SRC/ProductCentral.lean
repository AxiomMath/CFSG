module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.SL2MinimalFaithful Subgroup
open scoped commutatorElement

theorem commutator_eq_bot_of_le_center_left {G : Type*} [Group G] {C : Subgroup G}
    (hC : C ≤ center G) (H : Subgroup G) : ⁅C, H⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro c hc h _
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp (hC hc) h).symm)

theorem commute_of_commutator_le_center {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (hperf : ⁅H₁, H₁⁆ = H₁) (hc : ⁅H₁, H₂⁆ ≤ center G) : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x := by
  have h1 : ⁅⁅H₁, H₂⁆, H₁⁆ = ⊥ := commutator_eq_bot_of_le_center_left hc H₁
  have h2 : ⁅⁅H₂, H₁⁆, H₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm H₂ H₁]
    exact h1
  have h3 : ⁅⁅H₁, H₁⁆, H₂⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hperf] at h3
  intro x hx y hy
  have : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := h3 ▸ Subgroup.commutator_mem_commutator hx hy
  rw [Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem exists_elementaryAbelian_of_central_prod {p e₁ e₂ : ℕ} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] [CharP F₁ p] [CharP F₂ p] (hF₁ : Nat.card F₁ = p ^ e₁)
    (hF₂ : Nat.card F₂ = p ^ e₂) (h₁5 : 5 ≤ Nat.card F₁) (h₁9 : Nat.card F₁ ≠ 9)
    (h₂5 : 5 ≤ Nat.card F₂) (h₂9 : Nat.card F₂ ≠ 9) {W : Type*} [Group W]
    (ρ : W →* SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂)
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ center W) :
    ∃ E : Subgroup W, IsElementaryAbelian p E ∧ Nat.card E = p ^ (e₁ + e₂) := by
  classical
  let A₁ : Subgroup W := (MonoidHom.snd _ _).comp ρ |>.ker
  let ρ₁ : A₁ →* SpecialLinearGroup (Fin 2) F₁ := (MonoidHom.fst _ _).comp (ρ.comp A₁.subtype)
  have hρ₁s : Function.Surjective ρ₁ := by
    intro a
    obtain ⟨w, hw⟩ := hρ (a, 1)
    exact ⟨⟨w, by simp [A₁, hw]⟩, by simp [ρ₁, hw]⟩
  have hρ₁c : ρ₁.ker ≤ center A₁ := by
    intro x hx
    have hx1 : (ρ (x : W)).1 = 1 := hx
    have hx2 : (ρ (x : W)).2 = 1 := x.2
    have : (x : W) ∈ ρ.ker := Prod.ext hx1 hx2
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen this) (g : W))
  obtain ⟨σ₁, hσ₁⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
    (k := F₁) h₁5 h₁9 hρ₁s hρ₁c
  let s₁ : SpecialLinearGroup (Fin 2) F₁ →* W := A₁.subtype.comp σ₁
  have hs₁ : ∀ a, ρ (s₁ a) = (a, 1) := by
    intro a
    refine Prod.ext ?_ ?_
    · exact hσ₁ a
    · exact (σ₁ a).2
  let A₂ : Subgroup W := (MonoidHom.fst _ _).comp ρ |>.ker
  let ρ₂ : A₂ →* SpecialLinearGroup (Fin 2) F₂ := (MonoidHom.snd _ _).comp (ρ.comp A₂.subtype)
  have hρ₂s : Function.Surjective ρ₂ := by
    intro b
    obtain ⟨w, hw⟩ := hρ (1, b)
    exact ⟨⟨w, by simp [A₂, hw]⟩, by simp [ρ₂, hw]⟩
  have hρ₂c : ρ₂.ker ≤ center A₂ := by
    intro x hx
    have hx2 : (ρ (x : W)).2 = 1 := hx
    have hx1 : (ρ (x : W)).1 = 1 := x.2
    have : (x : W) ∈ ρ.ker := Prod.ext hx1 hx2
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen this) (g : W))
  obtain ⟨σ₂, hσ₂⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
    (k := F₂) h₂5 h₂9 hρ₂s hρ₂c
  let s₂ : SpecialLinearGroup (Fin 2) F₂ →* W := A₂.subtype.comp σ₂
  have hs₂ : ∀ b, ρ (s₂ b) = (1, b) := by
    intro b
    refine Prod.ext ?_ ?_
    · exact (σ₂ b).2
    · exact hσ₂ b
  have hperf₁ : ⁅s₁.range, s₁.range⁆ = s₁.range := by
    have hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F₁) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 F₁ le_rfl
        (Or.inr (by omega)) (Or.inr (by omega))
    have h1 := hQ.1.commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    rw [_root_.commutator_def] at h1
    rw [h1]
  have hcomm : ∀ x ∈ s₁.range, ∀ y ∈ s₂.range, x * y = y * x := by
    refine commute_of_commutator_le_center hperf₁ ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, hs₁, hs₂]
    ext <;> simp [commutatorElement_def]
  let τ : Multiplicative F₁ × Multiplicative F₂ →* W :=
    (s₁.comp unipotentHom).noncommCoprod (s₂.comp unipotentHom) fun a b =>
      (hcomm _ ⟨_, rfl⟩ _ ⟨_, rfl⟩)
  have hτ : ∀ u v, τ (u, v) = s₁ (unipotentHom u) * s₂ (unipotentHom v) := fun u v => rfl
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ h
    have h1 : ρ (τ (u, v)) = 1 := by rw [h, map_one]
    rw [hτ, map_mul, hs₁, hs₂] at h1
    have h2 : (unipotentHom u, unipotentHom v) = (1, 1) := by simpa using h1
    have hu : unipotentHom u = 1 := (Prod.ext_iff.mp h2).1
    have hv : unipotentHom v = 1 := (Prod.ext_iff.mp h2).2
    rw [← map_one unipotentHom] at hu hv
    exact Prod.ext (unipotentHom_injective hu) (unipotentHom_injective hv)
  have hpow : ∀ a : Multiplicative F₁ × Multiplicative F₂, a ^ p = 1 := by
    intro a
    refine Prod.ext ?_ ?_
    · show a.1 ^ p = 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    · show a.2 ^ p = 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  refine ⟨τ.range, isElementaryAbelian_range τ hpow, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd, hF₁, hF₂, pow_add]

end CFSG.RankThree.PartOne.SRC
