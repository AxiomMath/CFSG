module

public import CFSG.Quasithin.Background.F6CatShapeG22
public import CFSG.Quasithin.Recognition.CertR2aBridges

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique

namespace F6

theorem lattice_inf_eq {N : Type*} [Group N] (L : TwoLocalLattice N) : L.P₁ ⊓ L.P₂ = L.S := by
  rcases L.lattice _ (le_inf L.S_le_P₁ L.S_le_P₂) with h | h | h | h
  · exact h
  · exact absurd (h.symm.le.trans inf_le_right) L.P₁_not_le_P₂
  · exact absurd (h.symm.le.trans inf_le_left) L.P₂_not_le_P₁
  · exact absurd (le_top.trans (h.symm.le.trans inf_le_right)) L.P₁_not_le_P₂

namespace G22Shape

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

theorem exists_conj
    [Finite k] {K₁ K₂ : Subgroup (G2Group k)} (hK₁ : IsMaximalTwoLocal K₁)
    (hK₂ : IsMaximalTwoLocal K₂) (hne : K₁ ≠ K₂) (hS : IsSylowTwoOf (K₁ ⊓ K₂) ⊤) :
    ∃ φ : G2Group k ≃* G2Group k,
      (K₁.map φ.toMonoidHom = (lat h2 hk2).P₁ ∧ K₂.map φ.toMonoidHom = (lat h2 hk2).P₂) ∨
        (K₁.map φ.toMonoidHom = (lat h2 hk2).P₂ ∧ K₂.map φ.toMonoidHom = (lat h2 hk2).P₁) := by
  have : Finite (G2Group k) := finite_g2Group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp', hidx'⟩ := hS
  have e1 : ((K₁ ⊓ K₂).subgroupOf ⊤).index = (K₁ ⊓ K₂).index := Subgroup.relIndex_top_right _
  have hidx : ¬ 2 ∣ (K₁ ⊓ K₂).index := by rwa [e1] at hidx'
  let S : Sylow 2 (G2Group k) := (lat h2 hk2).sylow.1.toSylow (lat h2 hk2).sylow.2
  let S' : Sylow 2 (G2Group k) := hp'.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G2Group k) S S'
  have hg' : MulAut.conj g • (lat h2 hk2).S = K₁ ⊓ K₂ := by
    have h1 := congrArg (fun P : Sylow 2 (G2Group k) => (P : Subgroup (G2Group k))) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hTmap : K₁ ⊓ K₂ = (lat h2 hk2).S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : G2Group k ≃* G2Group k := (MulAut.conj g).symm
  have hTφ : (K₁ ⊓ K₂).map φ.toMonoidHom = (lat h2 hk2).S := by
    rw [hTmap]
    exact map_map_symm_eq (MulAut.conj g) (lat h2 hk2).S
  have hT₁ : (lat h2 hk2).S ≤ K₁.map φ.toMonoidHom := hTφ ▸ Subgroup.map_mono inf_le_left
  have hT₂ : (lat h2 hk2).S ≤ K₂.map φ.toMonoidHom := hTφ ▸ Subgroup.map_mono inf_le_right
  have hne' : K₁.map φ.toMonoidHom ≠ K₂.map φ.toMonoidHom :=
    fun h => hne (Subgroup.map_injective φ.injective h)
  refine ⟨φ, ?_⟩
  rcases (lat h2 hk2).eq_P₁_or_P₂_of_maxTwoLocal (isMaximalTwoLocal_map φ hK₁) hT₁ with h₁ | h₁ <;>
    rcases (lat h2 hk2).eq_P₁_or_P₂_of_maxTwoLocal (isMaximalTwoLocal_map φ hK₂) hT₂ with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne'
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (h₁.trans h₂.symm) hne'

end G22Shape

theorem g22AmalgamShapeFact_holds
    : G22AmalgamShapeFact := by
  intro W _ _ K₁ K₂ hW hTL hQ₁ hQ₂ hsp₁ h₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ⟨ε⟩⟩ := isG22_equiv_g2Group W hW
  have h2 := two_eq_zero_of_card_two hk
  have hk2 := eq_zero_or_eq_one_of_card_two hk
  have : Finite (G2Group k) := finite_g2Group
  obtain ⟨hK₁, hK₂, hne, S, hS⟩ := hTL
  have hS' : IsSylowTwoOf (K₁.map ε.toMonoidHom ⊓ K₂.map ε.toMonoidHom) ⊤ := by
    rw [← Subgroup.map_inf _ _ _ ε.injective, ← hS]
    exact isSylowTwoOf_top_map ε (isSylowTwoOf_top_of_sylow S)
  obtain ⟨φ, hφ⟩ := G22Shape.exists_conj h2 hk2 (isMaximalTwoLocal_map ε hK₁)
    (isMaximalTwoLocal_map ε hK₂) (fun h => hne (Subgroup.map_injective ε.injective h)) hS'
  have hmap : ∀ K : Subgroup W,
      K.map (ε.trans φ).toMonoidHom = (K.map ε.toMonoidHom).map φ.toMonoidHom := fun K => by
    rw [Subgroup.map_map]
    rfl
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  ·
    exfalso
    obtain ⟨eK₁⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₁).trans hA)
    have hsp : IsSpecialTwoOnePlusFour ↥(pCoreOf 2 (G22Shape.lat h2 hk2).P₁) :=
      isSpecialTwoOnePlusFour_of_mulEquiv (pCoreOfCongr eK₁).symm hsp₁
    have hR := G22Shape.R1_eq_pCoreOf h2 hk2 (by rw [hsp.1]; norm_num)
    exact G22Shape.card_center_R1_ne h2 hk2
      (isSpecialTwoOnePlusFour_of_mulEquiv (MulEquiv.subgroupCongr hR) hsp).2.1
  ·
    obtain ⟨eK₁⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₁).trans hB)
    obtain ⟨eK₂⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₂).trans hA)
    have hinf : (K₁ ⊓ K₂).map (ε.trans φ).toMonoidHom = (G22Shape.lat h2 hk2).S := by
      rw [Subgroup.map_inf _ _ _ (ε.trans φ).injective, hmap, hmap, hA, hB, inf_comm,
        lattice_inf_eq]
    obtain ⟨eT⟩ := mulEquiv_of_map_eq (ε.trans φ) hinf
    have hO : Nat.card ↥(pCoreOf 2 (G22Shape.lat h2 hk2).P₂) = 2 ^ 5 :=
      (Nat.card_congr (pCoreOfCongr eK₁).toEquiv).symm.trans hsp₁.1
    have hR := G22Shape.R2_eq_pCoreOf h2 hk2 (by rw [hO]; norm_num)
    have hP192 : Nat.card ↥(G22Shape.lat h2 hk2).P₁ = 192 := by
      rw [← Nat.card_congr eK₂.toEquiv]
      obtain ⟨e₂⟩ := hQ₂
      have := CFSG.LieType.BorelTits.pCore_normal (G := ↥K₂) 2
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥K₂)
      have h3 : Nat.card ↥(Open.pCore 2 ↥K₂) = 2 ^ 5 := by
        rw [← h₂]
        exact Nat.card_congr ((Open.pCore 2 ↥K₂).equivMapOfInjective _
          K₂.subtype_injective).toEquiv
      rw [h1, Nat.card_congr e₂.toEquiv, h3, Nat.card_perm, Nat.card_fin]
      rfl
    exact ⟨isExtensionOf_of_mulEquiv eT (G22Shape.S_shape h2 hk2),
      isCentralProduct₂_of_mulEquiv ((pCoreOfCongr eK₁).trans (MulEquiv.subgroupCongr hR.symm))
        (G22Shape.isCentralProduct₂_R2 h2 hk2),
      isExtensionOf_of_mulEquiv eK₂ (G22Shape.P₁_shape h2 hk2 hP192)⟩

end F6

end CFSG.Quasithin
