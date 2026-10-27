module

public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.OuterAutomorphisms

variable {M : Type*} [Group M]

@[expose] def conjOn (N : Subgroup M) (u : M) (hu : ∀ h ∈ N, u * h * u⁻¹ ∈ N)
    (hu' : ∀ h ∈ N, u⁻¹ * h * u ∈ N) : MulAut N where
  toFun h := ⟨u * h * u⁻¹, hu h h.2⟩
  invFun h := ⟨u⁻¹ * h * u, hu' h h.2⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (N : Subgroup M) (u : M) (hu : ∀ h ∈ N, u * h * u⁻¹ ∈ N)
    (hu' : ∀ h ∈ N, u⁻¹ * h * u ∈ N) (h : N) : (conjOn N u hu hu' h : M) = u * h * u⁻¹ := rfl

theorem inv_conj_mem (N : Subgroup M) {δ : M} (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N)
    (hδ2 : δ * δ ∈ N) : ∀ h ∈ N, δ⁻¹ * h * δ ∈ N := by
  intro h hh
  have : δ⁻¹ * h * δ = (δ * δ)⁻¹ * (δ * h * δ⁻¹) * (δ * δ) := by group
  rw [this]
  exact N.mul_mem (N.mul_mem (N.inv_mem hδ2) (hδ h hh)) hδ2

theorem conj_injective_of_center (N : Subgroup M) (hcenter : Subgroup.center N = ⊥) :
    Function.Injective (MulAut.conj : N →* MulAut N) := by
  intro g g' h
  have hc : g⁻¹ * g' ∈ Subgroup.center N := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut N => φ z) h
    simp only [MulAut.conj_apply] at hz
    calc z * (g⁻¹ * g') = g⁻¹ * (g * z * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * z * g'⁻¹) * g' := by rw [hz]
      _ = g⁻¹ * g' * z := by group
  rw [hcenter, Subgroup.mem_bot] at hc
  calc g = g * (g⁻¹ * g') := by rw [hc, mul_one]
    _ = g' := by group

theorem exists_eq_conj_of_outer (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) (α : MulAut N) (hα : α ∉ inner N) :
    ∃ g ∈ N, ∀ h : N, (α h : M) = g * δ * h * (g * δ)⁻¹ := by
  have hδ' := inv_conj_mem N hδ hδ2
  set cδ := conjOn N δ hδ hδ'
  have hcout : cδ ∉ inner N := by
    rintro ⟨k, hk⟩
    apply houter (δ⁻¹ * (k : M)⁻¹ * δ) (hδ' _ (N.inv_mem k.2))
    intro h hh
    have h1 := congrArg (fun φ : MulAut N => (φ ⟨h, hh⟩ : M)) hk
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, cδ, conjOn_apply] at h1
    calc δ * (δ⁻¹ * (k : M)⁻¹ * δ) * h = (k : M)⁻¹ * (δ * h * δ⁻¹) * δ := by group
      _ = (k : M)⁻¹ * ((k : M) * h * (k : M)⁻¹) * δ := by rw [h1]
      _ = h * (δ * (δ⁻¹ * (k : M)⁻¹ * δ)) := by group
  have hinj := conj_injective_of_center N hcenter
  let f : N × Bool → MulAut N := fun p => if p.2 then MulAut.conj p.1 * cδ else MulAut.conj p.1
  have hf : Function.Injective f := by
    rintro ⟨g, b⟩ ⟨g', b'⟩ h
    cases b <;> cases b' <;> simp only [f, Bool.false_eq_true, ↓reduceIte] at h
    · rw [hinj h]
    · exact absurd ⟨g'⁻¹ * g, by rw [map_mul, map_inv, h]; group⟩ hcout
    · exact absurd ⟨g⁻¹ * g', by rw [map_mul, map_inv, ← h]; group⟩ hcout
    · rw [hinj (mul_right_cancel h)]
  have hcardf : Nat.card (MulAut N) ≤ Nat.card (N × Bool) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]
    exact hcard
  have hfin : Finite (MulAut N) :=
    Finite.of_injective (fun α : MulAut N => (α : N → N)) DFunLike.coe_injective
  obtain ⟨⟨g, b⟩, hgb⟩ := (hf.bijective_of_nat_card_le hcardf).2 α
  cases b
  · exact absurd ⟨g, by simpa [f] using hgb⟩ hα
  · refine ⟨g, g.2, fun h => ?_⟩
    rw [← hgb]
    simp only [f, ↓reduceIte, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, cδ, conjOn_apply]
    group

theorem outer_oddCore_eq_bot (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N)
    (hw : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ mu vu : ℕ,
      Nat.card (centralizerIn N u) = 2 ^ vu * mu ∧ OddWitness (centralizerIn N u) mu)
    (α : MulAut N) (hα2 : α * α = 1) (hα : α ∉ inner N) : CFSG.oddCore (fixSub α) = ⊥ := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨mu, vu, hcardu, hwu⟩ := hw u hu ho
  exact fixSub_oddCore_eq_bot N α u hαg hcardu hwu

end CFSG.Sporadic.Schreier
