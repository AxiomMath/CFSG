module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type*} [Group G]

theorem disjoint_of_scalar_image [Finite G] {B X J : Subgroup G} (hXB : X ≤ B)
    {k₀ : Type*} [Field k₀] [Finite k₀]
    (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀) (hker : ι.ker = J.subgroupOf B)
    (himage : (X.subgroupOf B).map ι = (SemidirectProduct.inl : k₀ˣ →* _).range)
    (hXcard : Nat.card X = Nat.card k₀ - 1) : Disjoint X J := by
  let XB := X.subgroupOf B
  let f := ι.domRestrict XB
  have hcardrange : Nat.card f.range = Nat.card X := by
    rw [MonoidHom.domRestrict_range, himage, hXcard, ← Nat.card_units k₀]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := ringAutUnits k₀))).toEquiv).symm
  have hXBcard : Nat.card XB = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXB).toEquiv
  have hprod : Nat.card f.ker * Nat.card f.range = Nat.card XB := by
    rw [← Subgroup.index_ker]
    exact f.ker.card_mul_index
  rw [hcardrange, hXBcard] at hprod
  have hker1 : Nat.card f.ker = 1 :=
    (Nat.mul_eq_right (Nat.card_pos (α := X)).ne').mp hprod
  have hkerbot : f.ker = ⊥ := Subgroup.card_eq_one.mp hker1
  rw [Subgroup.disjoint_def]
  intro x hxX hxJ
  have hmem : (⟨⟨x, hXB hxX⟩, hxX⟩ : XB) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    change ι ⟨x, hXB hxX⟩ = 1
    rw [← MonoidHom.mem_ker, hker]
    exact hxJ
  rw [hkerbot] at hmem
  exact congrArg (fun y : XB => ((y : B) : G)) (Subgroup.mem_bot.mp hmem)

theorem scalar_fixed_eq_one {B X J Q : Subgroup G} (hXB : X ≤ B)
    {k₀ : Type*} [Field k₀]
    (φ : Q ≃* Multiplicative k₀) (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀)
    (hker : ι.ker = J.subgroupOf B)
    (hact : ∀ (b : B) (x y : Q), (y : G) = (b : G) * x * (b : G)⁻¹ →
      (φ y).toAdd = ((ι b).left : k₀) * (ι b).right (φ x).toAdd)
    (himage : (X.subgroupOf B).map ι = (SemidirectProduct.inl : k₀ˣ →* _).range)
    (hdis : Disjoint X J) :
    ∀ x : G, x ∈ X → x ≠ 1 → ∀ m : G, m ∈ Q → x * m * x⁻¹ = m → m = 1 := by
  intro x hxX hx1 m hmQ hxm
  let b : B := ⟨x, hXB hxX⟩
  have hbX : b ∈ X.subgroupOf B := hxX
  obtain ⟨c, hc⟩ : ι b ∈ (SemidirectProduct.inl : k₀ˣ →* _).range := by
    rw [← himage]
    exact Subgroup.mem_map_of_mem ι hbX
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hx1
    have hbker : b ∈ ι.ker := by
      rw [MonoidHom.mem_ker, ← hc, hc1, map_one]
    rw [hker] at hbker
    exact (Subgroup.disjoint_def.mp hdis) hxX hbker
  have hformula := hact b ⟨m, hmQ⟩ ⟨m, hmQ⟩ hxm.symm
  rw [← hc, SemidirectProduct.left_inl, SemidirectProduct.right_inl] at hformula
  change (φ ⟨m, hmQ⟩).toAdd = (c : k₀) * (φ ⟨m, hmQ⟩).toAdd at hformula
  have hzero : (φ ⟨m, hmQ⟩).toAdd = 0 := by
    by_contra hne
    apply hc1
    apply Units.ext
    have h1 : (c : k₀) * (φ ⟨m, hmQ⟩).toAdd = 1 * (φ ⟨m, hmQ⟩).toAdd := by
      rw [one_mul]
      exact hformula.symm
    exact mul_right_cancel₀ hne h1
  have hone : φ ⟨m, hmQ⟩ = 1 := hzero
  have hm1 : (⟨m, hmQ⟩ : Q) = 1 := φ.map_eq_one_iff.mp hone
  exact congrArg Subtype.val hm1

end CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode
