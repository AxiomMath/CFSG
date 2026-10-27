module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43f

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem commutator_le_self_aux : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
  mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem commutator_perfect (hK : IsTypeLnq 2 2 2 K) :
    Group.IsPerfect ↥⁅K, K⁆ := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm
  · exact Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
      Subgroup.commutator_mem_commutator (commutator_le_self_aux h₁) (commutator_le_self_aux h₂)
  · refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    obtain ⟨k₁, hk₁, z₁, hz₁K, hz₁, rfl⟩ := K_decomp hK g₁ h₁
    obtain ⟨k₂, hk₂, z₂, hz₂K, hz₂, rfl⟩ := K_decomp hK g₂ h₂
    have hk₁K : k₁ ∈ K := commutator_le_self_aux hk₁
    have hk₂K : k₂ ∈ K := commutator_le_self_aux hk₂
    have c1 : z₁ * (k₂ * z₂) * z₁⁻¹ = k₂ * z₂ := by
      rw [← hz₁ _ (mul_mem hk₂K hz₂K)]; group
    have c2 : z₂ * k₁⁻¹ * z₂⁻¹ = k₁⁻¹ := by
      rw [← hz₂ _ (inv_mem hk₁K)]; group
    have e : (k₁ * z₁) * (k₂ * z₂) * (k₁ * z₁)⁻¹ * (k₂ * z₂)⁻¹ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by
      calc (k₁ * z₁) * (k₂ * z₂) * (k₁ * z₁)⁻¹ * (k₂ * z₂)⁻¹
          = k₁ * (z₁ * (k₂ * z₂) * z₁⁻¹) * k₁⁻¹ * (k₂ * z₂)⁻¹ := by group
        _ = k₁ * (k₂ * z₂) * k₁⁻¹ * (k₂ * z₂)⁻¹ := by rw [c1]
        _ = k₁ * k₂ * (z₂ * k₁⁻¹ * z₂⁻¹) * k₂⁻¹ := by group
        _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by rw [c2]
    show (k₁ * z₁) * (k₂ * z₂) * (k₁ * z₁)⁻¹ * (k₂ * z₂)⁻¹ ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆
    rw [e]
    exact Subgroup.commutator_mem_commutator hk₁ hk₂

theorem commutator_typeLnq (hK : IsTypeLnq 2 2 2 K) :
    IsTypeLnq 2 2 2 ⁅K, K⁆ := by
  let φ : ↥⁅K, K⁆ →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp
      (Subgroup.inclusion (commutator_le_self_aux (K := K)))
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) q
    obtain ⟨k, hk, z, hzK, hz, hxk⟩ := K_decomp hK (x : G) x.2
    refine ⟨⟨k, hk⟩, ?_⟩
    show QuotientGroup.mk (⟨k, commutator_le_self_aux hk⟩ : ↥K) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    have hxk' : (x : G) = k * z := hxk
    have : ((⟨k, commutator_le_self_aux hk⟩ : ↥K)⁻¹ * x : ↥K) = ⟨z, hzK⟩ := by
      apply Subtype.ext
      show k⁻¹ * (x : G) = z
      rw [hxk']; group
    rw [this]
    exact hz g g.2
  have hker : φ.ker = Subgroup.center ↥⁅K, K⁆ := by
    ext k
    constructor
    · intro hk
      have hk' : (⟨k, commutator_le_self_aux k.2⟩ : ↥K) ∈ Subgroup.center ↥K :=
        (QuotientGroup.eq_one_iff _).1 hk
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : G) * (k : G) = (k : G) * g
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hk'
        ⟨g, commutator_le_self_aux g.2⟩)
    · intro hk
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' (Subgroup.center ↥K) _ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro x
      obtain ⟨k₀, hk₀, z, hzK, hz, hxk⟩ := K_decomp hK (x : G) x.2
      apply Subtype.ext
      show (x : G) * (k : G) = (k : G) * x
      have hkk₀ : (k₀ : G) * k = k * k₀ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hk ⟨k₀, hk₀⟩)
      have hkz : (k : G) * z = z * k := hz k (commutator_le_self_aux k.2)
      rw [hxk]
      calc k₀ * z * (k : G) = k₀ * (z * k) := mul_assoc _ _ _
        _ = k₀ * (k * z) := by rw [← hkz]
        _ = (k₀ * k) * z := (mul_assoc _ _ _).symm
        _ = (k * k₀) * z := by rw [hkk₀]
        _ = (k : G) * (k₀ * z) := mul_assoc _ _ _
  let e : ↥⁅K, K⁆ ⧸ Subgroup.center ↥⁅K, K⁆ ≃* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hK

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
