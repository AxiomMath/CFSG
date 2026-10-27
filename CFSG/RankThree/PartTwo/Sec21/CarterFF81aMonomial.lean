module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aX

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G]

theorem mulAut_commute_tau_of_monomial {B : Subgroup G} {b b₁ b₂ b₃ : G}
    (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    (hB : B = Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    {τ σ : MulAut ↥B}
    (hτb : τ ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hτ₁ : τ ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (hτ₂ : τ ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹)
    (hτ₃ : τ ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹)
    (hσb : σ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∨ σ ⟨b, hbB⟩ = (⟨b, hbB⟩)⁻¹)
    (hσ₁ : ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₁, hb₁B⟩ =
      (match j with | 0 => ⟨b₁, hb₁B⟩ | 1 => ⟨b₂, hb₂B⟩ | 2 => ⟨b₃, hb₃B⟩) ^ ε)
    (hσ₂ : ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₂, hb₂B⟩ =
      (match j with | 0 => ⟨b₁, hb₁B⟩ | 1 => ⟨b₂, hb₂B⟩ | 2 => ⟨b₃, hb₃B⟩) ^ ε)
    (hσ₃ : ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₃, hb₃B⟩ =
      (match j with | 0 => ⟨b₁, hb₁B⟩ | 1 => ⟨b₂, hb₂B⟩ | 2 => ⟨b₃, hb₃B⟩) ^ ε) :
    σ * τ = τ * σ := by
  subst hB
  let gen : Fin 3 → ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) := fun j =>
    match j with
    | 0 => ⟨b₁, hb₁B⟩
    | 1 => ⟨b₂, hb₂B⟩
    | 2 => ⟨b₃, hb₃B⟩
  have hτgen : ∀ j : Fin 3, τ (gen j) = (gen j)⁻¹ := by
    intro j
    fin_cases j <;> simp [gen, hτ₁, hτ₂, hτ₃]
  have key : ∀ (x y : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) (ε : ℤ),
      τ x = x⁻¹ → τ y = y⁻¹ → σ x = y ^ ε → σ (τ x) = τ (σ x) := by
    intro x y ε hx hy hxy
    calc σ (τ x) = σ x⁻¹ := by rw [hx]
      _ = (σ x)⁻¹ := map_inv σ x
      _ = (y ^ ε)⁻¹ := by rw [hxy]
      _ = y ^ (-ε) := (zpow_neg y ε).symm
      _ = (y⁻¹) ^ ε := (inv_zpow' y ε).symm
      _ = (τ y) ^ ε := by rw [hy]
      _ = τ (y ^ ε) := (map_zpow τ y ε).symm
      _ = τ (σ x) := by rw [hxy]
  have hgen : Set.EqOn
      (MulEquiv.toMonoidHom (σ * τ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))))
      (MulEquiv.toMonoidHom (τ * σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))))
      ({(⟨b, hbB⟩ : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))), ⟨b₁, hb₁B⟩,
        ⟨b₂, hb₂B⟩, ⟨b₃, hb₃B⟩} : Set ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    ·
      show σ (τ ⟨b, hbB⟩) = τ (σ ⟨b, hbB⟩)
      rcases hσb with h | h
      · rw [hτb, h, hτb]
      · rw [hτb, h, map_inv, hτb]
    ·
      obtain ⟨j, ε, hε⟩ := hσ₁
      show σ (τ ⟨b₁, hb₁B⟩) = τ (σ ⟨b₁, hb₁B⟩)
      exact key ⟨b₁, hb₁B⟩ (gen j) ε hτ₁ (hτgen j) (by simpa [gen] using hε)
    ·
      obtain ⟨j, ε, hε⟩ := hσ₂
      show σ (τ ⟨b₂, hb₂B⟩) = τ (σ ⟨b₂, hb₂B⟩)
      exact key ⟨b₂, hb₂B⟩ (gen j) ε hτ₂ (hτgen j) (by simpa [gen] using hε)
    ·
      obtain ⟨j, ε, hε⟩ := hσ₃
      show σ (τ ⟨b₃, hb₃B⟩) = τ (σ ⟨b₃, hb₃B⟩)
      exact key ⟨b₃, hb₃B⟩ (gen j) ε hτ₃ (hτgen j) (by simpa [gen] using hε)
  have htop : Subgroup.closure
      ({(⟨b, hbB⟩ : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))), ⟨b₁, hb₁B⟩,
        ⟨b₂, hb₂B⟩, ⟨b₃, hb₃B⟩} : Set ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) = ⊤ := by
    have hset : ({(⟨b, hbB⟩ : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))),
        ⟨b₁, hb₁B⟩, ⟨b₂, hb₂B⟩, ⟨b₃, hb₃B⟩} :
        Set ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) =
        ((↑) : ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) → G) ⁻¹'
          ({b, b₁, b₂, b₃} : Set G) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> simp
      · rintro (h | h | h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
    rw [hset]
    exact Subgroup.closure_closure_coe_preimage (k := ({b, b₁, b₂, b₃} : Set G))
  have h := MonoidHom.eqOn_closure hgen
  rw [htop] at h
  ext x
  simpa using h trivial

section

variable {b : G} {L : Subgroup G} [Finite G]

theorem FF81Hyp.monomial_le_cen_X_tau (h : FF81Hyp b L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hτ2 : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hσb : σ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∨ σ ⟨b, hbB⟩ = (⟨b, hbB⟩)⁻¹)
    (hσ₁ : ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₁, hb₁B⟩ =
      (match j with | 0 => ⟨b₁, hb₁B⟩ | 1 => ⟨b₂, hb₂B⟩ | 2 => ⟨b₃, hb₃B⟩) ^ ε)
    (hσ₂ : ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₂, hb₂B⟩ =
      (match j with | 0 => ⟨b₁, hb₁B⟩ | 1 => ⟨b₂, hb₂B⟩ | 2 => ⟨b₃, hb₃B⟩) ^ ε)
    (hσ₃ : ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₃, hb₃B⟩ =
      (match j with | 0 => ⟨b₁, hb₁B⟩ | 1 => ⟨b₂, hb₂B⟩ | 2 => ⟨b₃, hb₃B⟩) ^ ε) :
    σ * FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) =
      FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) * σ := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let hτN : τ ∈ Nor B := FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv
  let τX : MulAut ↥B := FF81X.tau hτN
  have hτXcoe : ∀ x : ↥B, (τX x : G) = τ * (x : G) * τ⁻¹ := by
    intro x
    change ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) x : G) = τ * (x : G) * τ⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hτXb : τX ⟨b, hbB⟩ = ⟨b, hbB⟩ := by
    apply Subtype.ext
    rw [hτXcoe]
    simpa using hb
  have hτX₁ : τX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹ := by
    apply Subtype.ext
    rw [hτXcoe]
    simpa using hinv.1
  have hτX₂ : τX ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹ := by
    apply Subtype.ext
    rw [hτXcoe]
    simpa using hinv.2.1
  have hτX₃ : τX ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹ := by
    apply Subtype.ext
    rw [hτXcoe]
    simpa using hinv.2.2
  change σ * τX = τX * σ
  exact mulAut_commute_tau_of_monomial hbB hb₁B hb₂B hb₃B rfl hτXb hτX₁ hτX₂ hτX₃
    hσb hσ₁ hσ₂ hσ₃

end

end CFSG.RankThree.PartTwo.Sec21.FF81
