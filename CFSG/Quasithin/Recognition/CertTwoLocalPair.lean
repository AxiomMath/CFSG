module

public import CFSG.Quasithin.Recognition.CertTwoLocal
public import CFSG.Quasithin.Recognition.CertF6Bridge

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique

section Transport

variable {G H : Type*} [Group G] [Group H]

private theorem map_symm_map' (φ : G ≃* H) (M : Subgroup G) :
    (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

theorem isSylowTwoOf_top_map (φ : G ≃* H) {S : Subgroup G} (h : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map φ.toMonoidHom) ⊤ := by
  obtain ⟨-, hp, hidx⟩ := h
  refine ⟨le_top, hp.map _, ?_⟩
  have e1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have e2 : ((S.map φ.toMonoidHom).subgroupOf ⊤).index = (S.map φ.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have e3 : (S.map φ.toMonoidHom).index = S.index := Subgroup.index_map_equiv S φ
  rw [e2, e3]
  rwa [e1] at hidx

theorem TwoLocalPairProp.of_mulEquiv (φ : G ≃* H) (h : TwoLocalPairProp G) : TwoLocalPairProp H := by
  intro S K₁ K₂ hS h₁ h₂ hne hS₁ hS₂
  have hS' : IsSylowTwoOf (S.map φ.symm.toMonoidHom) ⊤ := isSylowTwoOf_top_map φ.symm hS
  have h₁' : IsMaximalTwoLocal (K₁.map φ.symm.toMonoidHom) := isMaximalTwoLocal_map φ.symm h₁
  have h₂' : IsMaximalTwoLocal (K₂.map φ.symm.toMonoidHom) := isMaximalTwoLocal_map φ.symm h₂
  have hne' : K₁.map φ.symm.toMonoidHom ≠ K₂.map φ.symm.toMonoidHom := fun e =>
    hne (Subgroup.map_injective φ.symm.injective e)
  have hpair := h _ _ _ hS' h₁' h₂' hne' (Subgroup.map_mono hS₁) (Subgroup.map_mono hS₂)
  have := IsYAmalgamPair.map φ hpair
  rwa [show (S.map φ.symm.toMonoidHom).map φ.toMonoidHom = S from map_symm_map' φ.symm S,
    show (K₁.map φ.symm.toMonoidHom).map φ.toMonoidHom = K₁ from map_symm_map' φ.symm K₁,
    show (K₂.map φ.symm.toMonoidHom).map φ.toMonoidHom = K₂ from map_symm_map' φ.symm K₂] at this

end Transport

section Pair

variable {G ι κ : Type*} [Group G] {d : OvergroupData G ι κ}

theorem OvergroupData.Extra.eq_A_or_B_of_maxTwoLocal (e : d.Extra) {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hT : d.T ≤ M) : M = d.A ∨ M = d.B := by
  rcases d.lattice M hT with h | h | h | h
  · exfalso
    have hA := hM.2 d.A e.isTwoLocal_A (by rw [h]; exact d.T_le_A)
    exact d.T_ne_A (by rw [← h, hA])
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨P, hP, hPp, hPeq⟩ := hM.1
    rw [h] at hPeq
    exact hP (e.eq_bot_of_normal P (Subgroup.normalizer_eq_top_iff.1 hPeq.symm) hPp)

theorem OvergroupData.Extra.isYAmalgamPair_T (e : d.Extra) {K₁ K₂ : Subgroup G}
    (h₁ : IsMaximalTwoLocal K₁) (h₂ : IsMaximalTwoLocal K₂) (hne : K₁ ≠ K₂) (hT₁ : d.T ≤ K₁)
    (hT₂ : d.T ≤ K₂) : IsYAmalgamPair d.T K₁ K₂ := by
  refine ⟨⟨le_top, e.syl.1, ?_⟩, hne, fun M => ⟨?_, ?_⟩⟩
  · have e1 : (d.T.subgroupOf ⊤).index = d.T.index := Subgroup.relIndex_top_right d.T
    rw [e1]
    exact e.syl.2
  · rintro ⟨hM, hN⟩
    have hTM : d.T ≤ M := le_trans Subgroup.le_normalizer hN
    rcases e.eq_A_or_B_of_maxTwoLocal hM hTM with hM' | hM' <;>
    rcases e.eq_A_or_B_of_maxTwoLocal h₁ hT₁ with h1 | h1 <;>
    rcases e.eq_A_or_B_of_maxTwoLocal h₂ hT₂ with h2 | h2 <;>
    first
      | exact absurd (h1.trans h2.symm) hne
      | exact Or.inl (hM'.trans h1.symm)
      | exact Or.inr (hM'.trans h2.symm)
  · rintro (rfl | rfl)
    · exact ⟨h₁, by rw [e.normalizer_T]; exact hT₁⟩
    · exact ⟨h₂, by rw [e.normalizer_T]; exact hT₂⟩

theorem OvergroupData.Extra.isYAmalgamPair_of_two_locals [Finite G] (e : d.Extra)
    {S K₁ K₂ : Subgroup G} (hS : IsSylowTwoOf S ⊤) (h₁ : IsMaximalTwoLocal K₁)
    (h₂ : IsMaximalTwoLocal K₂) (hne : K₁ ≠ K₂) (hS₁ : S ≤ K₁) (hS₂ : S ≤ K₂) :
    IsYAmalgamPair S K₁ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp', hidx'⟩ := hS
  have e1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have hidx : ¬ 2 ∣ S.index := by rwa [e1] at hidx'
  let S₀ : Sylow 2 G := e.syl.1.toSylow e.syl.2
  let S' : Sylow 2 G := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G S₀ S'
  have hk' : MulAut.conj k • d.T = S := by
    have h1 := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hSmap : S = d.T.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : G ≃* G := (MulAut.conj k).symm
  have hSφ : S.map φ.toMonoidHom = d.T := by
    rw [hSmap]
    exact map_symm_map' (MulAut.conj k) d.T
  have hK₁ : IsMaximalTwoLocal (K₁.map φ.toMonoidHom) := isMaximalTwoLocal_map φ h₁
  have hK₂ : IsMaximalTwoLocal (K₂.map φ.toMonoidHom) := isMaximalTwoLocal_map φ h₂
  have hT₁ : d.T ≤ K₁.map φ.toMonoidHom := by
    rw [← hSφ]
    exact Subgroup.map_mono hS₁
  have hT₂ : d.T ≤ K₂.map φ.toMonoidHom := by
    rw [← hSφ]
    exact Subgroup.map_mono hS₂
  have hne' : K₁.map φ.toMonoidHom ≠ K₂.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hpair := e.isYAmalgamPair_T hK₁ hK₂ hne' hT₁ hT₂
  have hh := IsYAmalgamPair.map φ.symm hpair
  rw [map_symm_map' φ K₁, map_symm_map' φ K₂] at hh
  have hTS : d.T.map φ.symm.toMonoidHom = S := by
    rw [hSmap]
    rfl
  rw [hTS] at hh
  exact hh

theorem OvergroupData.Extra.twoLocalPairProp [Finite G] (e : d.Extra) : TwoLocalPairProp G :=
  fun _ _ _ hS h₁ h₂ hne hS₁ hS₂ => e.isYAmalgamPair_of_two_locals hS h₁ h₂ hne hS₁ hS₂

end Pair

end CFSG.Quasithin
