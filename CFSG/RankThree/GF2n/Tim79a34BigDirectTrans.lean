module

public import CFSG.RankThree.GF2n.Tim79a34SpRad

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

@[expose] def psiElt {G : Type} [Group G] {S : Subgroup G} {X : Type} [AddCommGroup X]
    (ψ : X ≃+ Additive ↥S) (w : X) : G :=
  ((Additive.toMul (ψ w) : ↥S) : G)

section Psi

variable {G : Type} [Group G] {S : Subgroup G} {X : Type} [AddCommGroup X] (ψ : X ≃+ Additive ↥S)

theorem psiElt_add (u v : X) : psiElt ψ (u + v) = psiElt ψ u * psiElt ψ v := by
  simp [psiElt]

theorem psiElt_zero : psiElt ψ 0 = 1 := by
  simp [psiElt]

theorem psiElt_mem (w : X) : psiElt ψ w ∈ S := (Additive.toMul (ψ w)).2

theorem psiElt_injective : Function.Injective (psiElt ψ) := by
  intro w w' h
  apply ψ.injective
  apply Additive.toMul.injective
  exact Subtype.ext h

theorem exists_psiElt {x : G} (hx : x ∈ S) : ∃ w : X, psiElt ψ w = x :=
  ⟨ψ.symm (Additive.ofMul ⟨x, hx⟩), by simp [psiElt]⟩

end Psi

theorem bigDirect_trans_step {K : Type} [Field K] [CharP K 2] {n : ℕ} {G : Type} [Group G]
    (φ : (Fin n ⊕ Fin n → K) → G) (hφ : ∀ u v, φ (u + v) = φ u * φ v)
    {a : Fin n ⊕ Fin n → K} {R A : Subgroup G}
    (hAφ : ∀ l : K, φ (l • a) ∈ A)
    (hroot : ∀ (c : Fin n ⊕ Fin n → K) (μ : K), spForm a c = 0 → (∀ l : K, c ≠ l • a) →
      μ ≠ 0 → ∃ r ∈ R, ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    {x y : Fin n ⊕ Fin n → K} (hx : spForm a x = 0) (hy : spForm a y = 0)
    (hxy : spForm x y ≠ 0) :
    ∃ r ∈ R, ∃ α ∈ A, r * φ x * r⁻¹ = φ y * α := by
  by_cases hc : ∃ l : K, x + y = l • a
  · obtain ⟨l, hl⟩ := hc
    refine ⟨1, R.one_mem, φ (l • a), hAφ l, ?_⟩
    rw [← hφ, ← hl]
    have h1 : y + (x + y) = x := by
      calc y + (x + y) = x + (y + y) := by abel
        _ = x := by rw [vec_add_self, add_zero]
    rw [h1]
    simp
  · push Not at hc
    have hca : spForm a (x + y) = 0 := by rw [spForm_add_right, hx, hy, add_zero]
    have hyx : spForm y x ≠ 0 := by
      rw [spForm_comm]
      exact neg_ne_zero.mpr hxy
    obtain ⟨r, hr, hact⟩ := hroot (x + y) (spForm y x)⁻¹ hca hc (inv_ne_zero hyx)
    refine ⟨r, hr, 1, A.one_mem, ?_⟩
    rw [hact x, mul_one]
    congr 1
    have h1 : spForm (x + y) x = spForm y x := by
      rw [spForm_add_left, spForm_self, zero_add]
    rw [h1, inv_mul_cancel₀ hyx, one_smul]
    calc x + (x + y) = (x + x) + y := by abel
      _ = y := by rw [vec_add_self, zero_add]

theorem bigDirect_trans {K : Type} [Field K] [CharP K 2] {n : ℕ} {G : Type} [Group G]
    (φ : (Fin n ⊕ Fin n → K) → G) (hφ : ∀ u v, φ (u + v) = φ u * φ v)
    {a : Fin n ⊕ Fin n → K} (ha : a ≠ 0) {R A : Subgroup G}
    (hRA : ∀ r ∈ R, ∀ α ∈ A, r * α * r⁻¹ = α)
    (hAφ : ∀ l : K, φ (l • a) ∈ A)
    (hroot : ∀ (c : Fin n ⊕ Fin n → K) (μ : K), spForm a c = 0 → (∀ l : K, c ≠ l • a) →
      μ ≠ 0 → ∃ r ∈ R, ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    {x y : Fin n ⊕ Fin n → K} (hx : spForm a x = 0) (hxa : ∀ l : K, x ≠ l • a)
    (hy : spForm a y = 0) (hya : ∀ l : K, y ≠ l • a) :
    ∃ r ∈ R, ∃ α ∈ A, r * φ x * r⁻¹ = φ y * α := by
  by_cases hxy : spForm x y ≠ 0
  · exact bigDirect_trans_step φ hφ hAφ hroot hx hy hxy
  · push Not at hxy
    obtain ⟨u₁, hu₁a, hxu₁⟩ := exists_dual ha hx hxa
    obtain ⟨u₂, hu₂a, hyu₂⟩ := exists_dual ha hy hya
    have hz : ∃ z, spForm a z = 0 ∧ spForm x z ≠ 0 ∧ spForm z y ≠ 0 := by
      by_cases h1 : spForm y u₁ = 0
      · by_cases h2 : spForm x u₂ = 0
        · refine ⟨u₁ + u₂, by rw [spForm_add_right, hu₁a, hu₂a, add_zero], ?_, ?_⟩
          · rw [spForm_add_right, hxu₁, h2, add_zero]
            exact one_ne_zero
          · rw [spForm_comm, spForm_add_right, h1, hyu₂, zero_add]
            exact neg_ne_zero.mpr one_ne_zero
        · refine ⟨u₂, hu₂a, h2, ?_⟩
          rw [spForm_comm, hyu₂]
          exact neg_ne_zero.mpr one_ne_zero
      · refine ⟨u₁, hu₁a, by rw [hxu₁]; exact one_ne_zero, ?_⟩
        rw [spForm_comm]
        exact neg_ne_zero.mpr h1
    obtain ⟨z, hza, hxz, hzy⟩ := hz
    obtain ⟨r₁, hr₁, α₁, hα₁, h₁⟩ := bigDirect_trans_step φ hφ hAφ hroot hx hza hxz
    obtain ⟨r₂, hr₂, α₂, hα₂, h₂⟩ := bigDirect_trans_step φ hφ hAφ hroot hza hy hzy
    refine ⟨r₂ * r₁, R.mul_mem hr₂ hr₁, α₂ * α₁, A.mul_mem hα₂ hα₁, ?_⟩
    calc r₂ * r₁ * φ x * (r₂ * r₁)⁻¹ = r₂ * (r₁ * φ x * r₁⁻¹) * r₂⁻¹ := by group
      _ = r₂ * (φ z * α₁) * r₂⁻¹ := by rw [h₁]
      _ = (r₂ * φ z * r₂⁻¹) * (r₂ * α₁ * r₂⁻¹) := by group
      _ = (φ y * α₂) * α₁ := by rw [h₂, hRA r₂ hr₂ α₁ hα₁]
      _ = φ y * (α₂ * α₁) := by group

theorem bigDirect_htrans {G : Type} [Group G] {V H P : Subgroup G} {n f : ℕ}
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (ha : a ≠ 0)
    (hiff : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0)
    (hAV : ∀ l : GaloisField 2 f, psiElt ψ (l • a) ∈ V)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
      (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c)) :
    ∀ x ∈ P ⊓ wOf V H, x ∉ V → ∀ y ∈ P ⊓ wOf V H, y ∉ V →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∃ α ∈ V ⊓ wOf V H,
        r * x * r⁻¹ = y * α := by
  have hcoord : ∀ x ∈ P ⊓ wOf V H, x ∉ V → ∃ x' : Fin n ⊕ Fin n → GaloisField 2 f,
      psiElt ψ x' = x ∧ spForm a x' = 0 ∧ ∀ l : GaloisField 2 f, x' ≠ l • a := by
    intro x hx hxV
    obtain ⟨hxP, hxW⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨x', rfl⟩ := exists_psiElt ψ hxW
    refine ⟨x', rfl, (hiff x').mp hxP, fun l hl => hxV ?_⟩
    rw [hl]
    exact hAV l
  intro x hx hxV y hy hyV
  obtain ⟨x', rfl, hx', hxa⟩ := hcoord x hx hxV
  obtain ⟨y', rfl, hy', hya⟩ := hcoord y hy hyV
  have hRA : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ α ∈ V ⊓ wOf V H,
      r * α * r⁻¹ = α := fun r hr α hα => by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 α (Subgroup.mem_inf.mp hα).1
    rw [← this]
    group
  exact bigDirect_trans (psiElt ψ) (psiElt_add ψ) ha hRA
    (fun l => Subgroup.mem_inf.mpr ⟨hAV l, psiElt_mem ψ _⟩) hroot hx' hxa hy' hya

end CFSG.RankThree.GF2n.Tim79a
