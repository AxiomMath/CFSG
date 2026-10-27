module

public import CFSG.Quasithin.Recognition.M12AmalE8Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12Amal CFSG.Quasithin.M12AmalE8
  CFSG.Quasithin.AmalTransport

open scoped Pointwise in
theorem m12_pair_cases {T' M₁ M₂ : Subgroup M12G} (h : IsYAmalgamPair T' M₁ M₂) :
    ∃ φ : M12G ≃* M12G, (M₁.map φ.toMonoidHom = m12Data.A ∧ M₂.map φ.toMonoidHom = m12Data.B) ∨
      (M₁.map φ.toMonoidHom = m12Data.B ∧ M₂.map φ.toMonoidHom = m12Data.A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsyl, hne, hiff⟩ := h
  obtain ⟨hM₁, hN₁⟩ := (hiff M₁).2 (Or.inl rfl)
  obtain ⟨hM₂, hN₂⟩ := (hiff M₂).2 (Or.inr rfl)
  obtain ⟨-, hp', hidx'⟩ := hsyl
  have e1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
  have hidx : ¬ 2 ∣ T'.index := by rwa [e1] at hidx'
  let S : Sylow 2 M12G := m12_syl.1.toSylow m12_syl.2
  let S' : Sylow 2 M12G := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M12G S S'
  have hk' : MulAut.conj k • m12Data.T = T' := by
    have h1 := congrArg (fun P : Sylow 2 M12G => (P : Subgroup M12G)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hT'map : T' = m12Data.T.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : M12G ≃* M12G := (MulAut.conj k).symm
  have hT'φ : T'.map φ.toMonoidHom = m12Data.T := by
    rw [hT'map]
    exact map_map_symm_eq (MulAut.conj k) m12Data.T
  have hTle : ∀ M : Subgroup M12G, IsMaximalTwoLocal M → Subgroup.normalizer (T' : Set M12G) ≤ M →
      m12Data.T ≤ M.map φ.toMonoidHom := by
    intro M _ hN
    rw [← hT'φ]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans hN)
  have hA₁ := m12Extra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hM₁) (hTle M₁ hM₁ hN₁)
  have hA₂ := m12Extra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hM₂) (hTle M₂ hM₂ hN₂)
  refine ⟨φ, ?_⟩
  rcases hA₁ with h₁ | h₁ <;> rcases hA₂ with h₂ | h₂
  · exact absurd (Subgroup.map_injective φ.injective (h₁.trans h₂.symm)) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (Subgroup.map_injective φ.injective (h₁.trans h₂.symm)) hne

theorem m12AmalgamE8_unfolded :
    ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseM12 H L2 → E8Concl H L2 := by
  intro G _ _ H L2 hcase
  obtain ⟨hAm, -, hQ8, -, -⟩ := hcase
  obtain ⟨Y, _, ⟨eY⟩, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hAm
  have hpair' := IsYAmalgamPair.map eY hpair
  obtain ⟨φ, hφ⟩ := m12_pair_cases hpair'
  have iso' := isoMap (isoMap iso eY) φ
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · have h : E8Concl ((M₁.map eY.toMonoidHom).map φ.toMonoidHom)
        ((M₂.map eY.toMonoidHom).map φ.toMonoidHom) := by
      rw [hA, hB]
      exact m12E8Concl_model
    have hcore : pCoreOf 2 ((M₁.map eY.toMonoidHom).map φ.toMonoidHom) ≤
        (M₁.map eY.toMonoidHom).map φ.toMonoidHom ⊓ (M₂.map eY.toMonoidHom).map φ.toMonoidHom := by
      rw [hA, hB]
      exact pCoreOf_A_le_inf
    exact E8Concl.of_iso iso' hcore h
  · exfalso
    have e₁ : ↥H ≃* ↥m12Data.B := iso'.φ1.trans (MulEquiv.subgroupCongr hB)
    exact false_of_isQ8Sq_pCoreOf_B (isQ8Sq_pCoreOf_of_mulEquiv H m12Data.B e₁ hQ8)

end CFSG.Quasithin
