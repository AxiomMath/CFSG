module

public import CFSG.Monster.B.TwoA.Amalgam.DeckCore
public import CFSG.Monster.B.TwoA.Amalgam.DeckData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary

theorem deck_centralizer_classical_images_of
    {G : Type*} [Group G]
    {Ht K P₁ P₄ Bt : Subgroup G} [Finite K] [Finite P₁]
    (hKn : ∀ g ∈ Ht, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hK : Nat.card K ∣ 3968055)
    (hP₁ : P₁ ≤ Ht) (hP₄ : P₄ ≤ Ht)
    (φ₁ : Pc 0 →* P₁) (hφ₁ : Function.Surjective φ₁)
    (φ₄ : P4 →* P₄) (hφ₄ : Function.Surjective φ₄)
    (hcompat : ∀ (x : Dfull) (h₀ : x ∈ Pc 0) (h₃ : x ∈ P4), (φ₁ ⟨x, h₀⟩ : G) = φ₄ ⟨x, h₃⟩)
    (α₁ : P₁ →* SigmaU6) (hα₁ : ∀ g, α₁ (φ₁ g) = rhoP1 g)
    (α₄ : P₄ →* OA8) (hα₄ : ∀ g, α₄ (φ₄ g) = p4Proj g)
    (hB₁ : Bt.subgroupOf P₁ = (Bam.subgroupOf (Pc 0)).map φ₁)
    (hB₄ : Bt.subgroupOf P₄ = (Bam.subgroupOf P4).map φ₄) :
    ((deckCent Ht K).subgroupOf Ht).Normal ∧
      psuSub.comap α₁ ≤ (deckCent Ht K).subgroupOf P₁ ∧
      orthD ≤ ((deckCent Ht K).subgroupOf P₄).map α₄ ∧
      psuSub ⊓ flagStabU ≤ ((deckCent Ht K ⊓ Bt).subgroupOf P₁).map α₁ ∧
      orthD ⊓ flagStabO ≤ ((deckCent Ht K ⊓ Bt).subgroupOf P₄).map α₄ := by
  have hk₁ := ker_eq_map_of_comp hφ₁ hα₁
  have hk₄ := ker_eq_map_of_comp hφ₄ hα₄
  have hN₁ : IsPGroup 2 α₁.ker := hk₁ ▸ isPGroup_ker_rhoP1.map φ₁
  have hN₁c : ⁅α₁.ker, ⊤⁆ = α₁.ker := hk₁ ▸ commutator_map_eq hφ₁ commutator_ker_rhoP1
  have hM : IsPGroup 2 α₄.ker := hk₄ ▸ isPGroup_ker_p4Proj.map φ₄
  have hBU : Bt.subgroupOf P₁ = flagStabU.comap α₁ := by
    rw [hB₁, Bam_subgroupOf_Pc0, comap_eq_map_comap_of_comp hφ₁ hα₁]
  have hBO : Bt.subgroupOf P₄ = flagStabO.comap α₄ := by
    rw [hB₄, Bam_subgroupOf_P4, comap_eq_map_comap_of_comp hφ₄ hα₄]
  obtain ⟨x, hx₀, hx₃, hx5⟩ := exists_orderOf_eq_five
  have hy₄ : ((φ₁ ⟨x, hx₀⟩ : P₁) : G) ∈ P₄ := by
    rw [hcompat x hx₀ hx₃]
    exact (φ₄ ⟨x, hx₃⟩).2
  have hy1 : ((φ₁ ⟨x, hx₀⟩ : P₁) : G) ≠ 1 := by
    intro h
    have h1 : φ₁ ⟨x, hx₀⟩ = 1 := Subtype.ext h
    have h2 : (⟨x, hx₀⟩ : Pc 0) ∈ rhoP1.ker := by
      rw [MonoidHom.mem_ker, ← hα₁, h1, map_one]
    exact not_mem_of_isPGroup_two isPGroup_ker_rhoP1
      (by rw [Subgroup.orderOf_mk]; exact hx5) h2
  have hy5 : ((φ₁ ⟨x, hx₀⟩ : P₁) : G) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow]
    have : (⟨x, hx₀⟩ : Pc 0) ^ 5 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hx5 ▸ pow_orderOf_eq_one x)
    rw [this, map_one, Subgroup.coe_one]
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := deck_centralizer_core hKn hK hP₁ hP₄ α₁
    (surjective_of_comp hα₁ rhoP1_surjective) hN₁ hN₁c psuSub isSimpleGroup_psuSub
    eleven_dvd_natCard_psuSub (by rw [natCard_quotient_psuSub]) α₄
    (surjective_of_comp hα₄ p4Proj_surjective) hM orthD isSimpleGroup_orthD sq_mem_orthD
    (φ₁ ⟨x, hx₀⟩).2 hy₄ hy1 hy5 flagStabU flagStabO hBU hBO
  exact ⟨h1, h2, h4, h5, h6⟩

end CFSG.Monster.B.TwoA.Amalgam
