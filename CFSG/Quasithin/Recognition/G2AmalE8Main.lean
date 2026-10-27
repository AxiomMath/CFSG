module

public import CFSG.Quasithin.Recognition.G2AmalE8Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G2AmalE8 CFSG.Quasithin.AmalTransport

theorem map_map_symm_eq_g2 {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (M : Subgroup G) :
    (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

open scoped Pointwise in
theorem g2_pair_cases
    {T' M₁ M₂ : Subgroup G2P} (h : IsYAmalgamPair T' M₁ M₂) :
    ∃ φ : G2P ≃* G2P, (M₁.map φ.toMonoidHom = g2AmalL.P₁ ∧ M₂.map φ.toMonoidHom = g2AmalL.P₂) ∨
      (M₁.map φ.toMonoidHom = g2AmalL.P₂ ∧ M₂.map φ.toMonoidHom = g2AmalL.P₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsyl, hne, hiff⟩ := h
  obtain ⟨hM₁, hN₁⟩ := (hiff M₁).2 (Or.inl rfl)
  obtain ⟨hM₂, hN₂⟩ := (hiff M₂).2 (Or.inr rfl)
  obtain ⟨-, hp', hidx'⟩ := hsyl
  have e1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
  have hidx : ¬ 2 ∣ T'.index := by rwa [e1] at hidx'
  let S : Sylow 2 G2P := g2AmalL.sylow.1.toSylow g2AmalL.sylow.2
  let S' : Sylow 2 G2P := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G2P S S'
  have hk' : MulAut.conj k • g2AmalL.S = T' := by
    have h1 := congrArg (fun P : Sylow 2 G2P => (P : Subgroup G2P)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hT'map : T' = g2AmalL.S.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : G2P ≃* G2P := (MulAut.conj k).symm
  have hT'φ : T'.map φ.toMonoidHom = g2AmalL.S := by
    rw [hT'map]
    exact map_map_symm_eq_g2 (MulAut.conj k) g2AmalL.S
  have hTle : ∀ M : Subgroup G2P, IsMaximalTwoLocal M → Subgroup.normalizer (T' : Set G2P) ≤ M →
      g2AmalL.S ≤ M.map φ.toMonoidHom := by
    intro M _ hN
    rw [← hT'φ]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans hN)
  have hA₁ := g2AmalL.eq_P₁_or_P₂_of_maxTwoLocal (isMaximalTwoLocal_map φ hM₁) (hTle M₁ hM₁ hN₁)
  have hA₂ := g2AmalL.eq_P₁_or_P₂_of_maxTwoLocal (isMaximalTwoLocal_map φ hM₂) (hTle M₂ hM₂ hN₂)
  refine ⟨φ, ?_⟩
  rcases hA₁ with h₁ | h₁ <;> rcases hA₂ with h₂ | h₂
  · exact absurd (Subgroup.map_injective φ.injective (h₁.trans h₂.symm)) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (Subgroup.map_injective φ.injective (h₁.trans h₂.symm)) hne

noncomputable def pCoreCongrG2 {D E : Type*} [Group D] [Group E] {H : Subgroup D} {K : Subgroup E}
    (e : ↥H ≃* ↥K) : ↥(pCoreOf 2 H) ≃* ↥(pCoreOf 2 K) :=
  ((pCoreEquiv H).symm.trans
    (((CFSG.pCore 2 ↥H).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (CFSG.pCore_map_iso 2 e)))).trans (pCoreEquiv K)

theorem cardCenterOfEqG2 {D E : Type*} [Group D] [Group E] {R : Subgroup D} {R' : Subgroup E}
    (e : ↥R ≃* ↥R') : Nat.card ↥(centerOf R) = Nat.card ↥(centerOf R') := by
  rw [card_centerOf_eq_card_center, card_centerOf_eq_card_center, ← Subgroup.map_center_eq e]
  exact Nat.card_congr ((Subgroup.center ↥R).equivMapOfInjective _ e.injective).toEquiv

theorem isQ8Sq_pCoreOf_of_mulEquiv_g2 {G K : Type*} [Group G] [Group K] (H : Subgroup G)
    (L : Subgroup K) (e : ↥H ≃* ↥L) (h : IsQ8Sq ↥(pCoreOf 2 H)) : IsQ8Sq ↥(pCoreOf 2 L) :=
  IsQ8Sq.of_mulEquiv (pCoreCongrG2 e) h

theorem g2AmalgamE8_unfolded :
    ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseG2 H L2 →
      IsQ8Sq ↥(pCoreOf 2 H) ∧ E8Concl H L2 := by
  intro G _ _ H L2 hcase
  obtain ⟨hAm, -, -, hSp, -⟩ := hcase
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hAm
  rcases hY with ⟨-, ⟨eY⟩⟩ | ⟨h2, -⟩
  swap
  · omega
  obtain ⟨eA⟩ := g2P_mulEquiv_aut
  let f : Y ≃* G2P := eY.trans eA.symm
  have hpair' := IsYAmalgamPair.map f hpair
  obtain ⟨φ, hφ⟩ := g2_pair_cases hpair'
  have iso' := isoMap (isoMap iso f) φ
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · exfalso
    have e₁ : ↥H ≃* ↥g2AmalL.P₁ := iso'.φ1.trans (MulEquiv.subgroupCongr hA)
    have hcard := cardCenterOfEqG2 (pCoreCongrG2 e₁)
    have h2' : Nat.card ↥(centerOf (pCoreOf 2 H)) = 2 :=
      (card_centerOf_eq_card_center (pCoreOf 2 H)).trans hSp.2.2
    exact card_center_pCoreOf_P₁_ne_two (hcard.symm.trans h2')
  · have h : E8Concl ((M₁.map f.toMonoidHom).map φ.toMonoidHom)
        ((M₂.map f.toMonoidHom).map φ.toMonoidHom) := by
      rw [hB, hA]
      exact g2E8Concl_model
    have hcore : pCoreOf 2 ((M₁.map f.toMonoidHom).map φ.toMonoidHom) ≤
        (M₁.map f.toMonoidHom).map φ.toMonoidHom ⊓ (M₂.map f.toMonoidHom).map φ.toMonoidHom := by
      rw [hB, hA]
      exact pCoreOf_P₂_le_inf
    refine ⟨?_, E8Concl.of_iso iso' hcore h⟩
    have e₁ : ↥g2AmalL.P₂ ≃* ↥H := (iso'.φ1.trans (MulEquiv.subgroupCongr hB)).symm
    exact isQ8Sq_pCoreOf_of_mulEquiv_g2 g2AmalL.P₂ H e₁ isQ8Sq_pCoreOf_P₂

end CFSG.Quasithin
