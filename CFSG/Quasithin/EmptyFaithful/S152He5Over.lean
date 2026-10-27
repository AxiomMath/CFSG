module

public import CFSG.Quasithin.EmptyFaithful.S14620B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def OverBool2 {Y : Type*} [Group Y] (T : Subgroup Y) : Prop :=
  ∃ C₁ C₂ : Subgroup Y, T < C₁ ∧ T < C₂ ∧ ¬ C₁ ≤ C₂ ∧ ¬ C₂ ≤ C₁ ∧
    ∀ S : Subgroup Y, T ≤ S → S = T ∨ S = C₁ ∨ S = C₂ ∨ S = ⊤

theorem OverBool2.map_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {T : Subgroup Y}
    (h : OverBool2 T) : OverBool2 (T.map e.toMonoidHom) := by
  obtain ⟨C₁, C₂, h1, h2, h12, h21, hall⟩ := h
  let φ : Subgroup Y ≃o Subgroup Y' := e.mapSubgroup
  have hφT : φ T = T.map e.toMonoidHom := rfl
  rw [← hφT]
  refine ⟨φ C₁, φ C₂, φ.lt_iff_lt.mpr h1, φ.lt_iff_lt.mpr h2,
    fun h => h12 (φ.le_iff_le.mp h), fun h => h21 (φ.le_iff_le.mp h), ?_⟩
  intro S' hS'
  obtain ⟨S, rfl⟩ : ∃ S, φ S = S' := ⟨φ.symm S', φ.apply_symm_apply S'⟩
  have hS : T ≤ S := φ.le_iff_le.mp hS'
  rcases hall S hS with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective)))

theorem OverBool2.conj {Y : Type*} [Group Y] (g : Y) {T : Subgroup Y} (h : OverBool2 T) :
    OverBool2 (T.map (MulAut.conj g).toMonoidHom) :=
  h.map_mulEquiv (MulAut.conj g)

theorem OverBool2.of_sylow {Y : Type*} [Group Y] [Finite Y] {Q T : Subgroup Y}
    (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (h : OverBool2 Q) : OverBool2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SQ : Sylow 2 Y := hQ.toSylow hQi
  let ST : Sylow 2 Y := hT.toSylow hTi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y SQ ST
  have hTeq : T = Q.map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun S : Sylow 2 Y => (S : Subgroup Y)) hg
    exact this.symm
  rw [hTeq]
  exact h.conj g

theorem OverBool2.sylow_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y'] (e : Y ≃* Y')
    {Q : Subgroup Y} (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) (h : OverBool2 Q)
    {T : Subgroup Y'} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) : OverBool2 T := by
  have hQ' : IsPGroup 2 (Q.map e.toMonoidHom) := hQ.map e.toMonoidHom
  have hQi' : ¬ 2 ∣ (Q.map e.toMonoidHom).index := by
    have := Subgroup.index_map_equiv (H := Q) e
    exact this ▸ hQi
  exact OverBool2.of_sylow hQ' hQi' hT hTi (h.map_mulEquiv e)

section Transfer

variable {G : Type} [Group G]

theorem isMaxSubgroupIn_of_overBool2 {X T : Subgroup G} (hT : IsSylowTwoOf T X)
    (h : OverBool2 (imageOTwoQuot X T)) : ∀ P ∈ uFamHat X T, IsMaxSubgroupIn P T := by
  classical
  obtain ⟨C₁, C₂, h1, h2, h12, h21, hall⟩ := h
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) with hπ
  have hQT : pCoreOf 2 X ≤ T := hT.pCoreOf_le
  have hTX : T ≤ X := hT.1
  let lift : Subgroup (OTwoQuot X) → Subgroup G := fun R => (R.comap π).map X.subtype
  have lift_le : ∀ R, lift R ≤ X := fun R => by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have image_lift : ∀ R, imageOTwoQuot X (lift R) = R := fun R => by
    unfold imageOTwoQuot
    have h : (lift R).subgroupOf X = R.comap π :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective X) (R.comap π)
    rw [h]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) R
  have T_le_lift : ∀ R, imageOTwoQuot X T ≤ R → T ≤ lift R := fun R hR t ht => by
    refine ⟨⟨t, hTX ht⟩, ?_, rfl⟩
    exact hR (mem_imageOTwoQuot_iff.mpr ⟨t, hTX ht, ht, rfl⟩)
  have le_of_image_le : ∀ {S S' : Subgroup G}, pCoreOf 2 X ≤ S' → S ≤ X →
      imageOTwoQuot X S ≤ imageOTwoQuot X S' → S ≤ S' := by
    intro S S' hpS' hSX hle s hs
    have hmem : (⟨s, hSX hs⟩ : ↥X) ∈ (imageOTwoQuot X S').comap π :=
      hle (mem_imageOTwoQuot_iff.mpr ⟨s, hSX hs, hs, rfl⟩)
    rw [imageOTwoQuot_comap hpS'] at hmem
    exact hmem
  have claimA : ∀ S : Subgroup G, T ≤ S → S ≤ X →
      S = T ∨ S = lift C₁ ∨ S = lift C₂ ∨ S = X := by
    intro S hTS hSX
    have hpS : pCoreOf 2 X ≤ S := hQT.trans hTS
    rcases hall (imageOTwoQuot X S) (imageOTwoQuot_mono hTS) with hS | hS | hS | hS
    · exact Or.inl (le_antisymm (le_of_image_le hQT hSX hS.le) hTS)
    · refine Or.inr (Or.inl (le_antisymm ?_ ?_))
      · exact le_of_image_le (hQT.trans (T_le_lift C₁ h1.le)) hSX (by rw [hS, image_lift])
      · exact le_of_image_le hpS (lift_le C₁) (by rw [hS, image_lift])
    · refine Or.inr (Or.inr (Or.inl (le_antisymm ?_ ?_)))
      · exact le_of_image_le (hQT.trans (T_le_lift C₂ h2.le)) hSX (by rw [hS, image_lift])
      · exact le_of_image_le hpS (lift_le C₂) (by rw [hS, image_lift])
    · refine Or.inr (Or.inr (Or.inr (le_antisymm hSX ?_)))
      exact le_of_image_le hpS le_rfl (by rw [hS, imageOTwoQuot_self_eq_top])
  have hTlt₁ : T < lift C₁ := by
    refine lt_of_le_of_ne (T_le_lift C₁ h1.le) fun hEq => ?_
    have := image_lift C₁
    rw [← hEq] at this
    exact h1.ne this
  have hTlt₂ : T < lift C₂ := by
    refine lt_of_le_of_ne (T_le_lift C₂ h2.le) fun hEq => ?_
    have := image_lift C₂
    rw [← hEq] at this
    exact h2.ne this
  have hn12 : ¬ lift C₁ ≤ lift C₂ := fun hle => h12 (by
    have := imageOTwoQuot_mono (M := X) hle
    rwa [image_lift, image_lift] at this)
  have hn21 : ¬ lift C₂ ≤ lift C₁ := fun hle => h21 (by
    have := imageOTwoQuot_mono (M := X) hle
    rwa [image_lift, image_lift] at this)
  have hnX₁ : lift C₁ ≠ X := fun hEq => h21 (by
    have := image_lift C₁
    rw [hEq, imageOTwoQuot_self_eq_top] at this
    rw [← this]
    exact le_top)
  have hnX₂ : lift C₂ ≠ X := fun hEq => h12 (by
    have := image_lift C₂
    rw [hEq, imageOTwoQuot_self_eq_top] at this
    rw [← this]
    exact le_top)
  have hmax₁ : IsMaxSubgroupIn X (lift C₁) := by
    refine ⟨lt_of_le_of_ne (lift_le C₁) hnX₁, fun K hK hKX => ?_⟩
    rcases claimA K (hTlt₁.le.trans hK.le) hKX with rfl | rfl | rfl | rfl
    · exact absurd (hTlt₁.trans hK) (lt_irrefl _)
    · exact absurd hK (lt_irrefl _)
    · exact absurd hK.le hn12
    · rfl
  have hmax₂ : IsMaxSubgroupIn X (lift C₂) := by
    refine ⟨lt_of_le_of_ne (lift_le C₂) hnX₂, fun K hK hKX => ?_⟩
    rcases claimA K (hTlt₂.le.trans hK.le) hKX with rfl | rfl | rfl | rfl
    · exact absurd (hTlt₂.trans hK) (lt_irrefl _)
    · exact absurd hK.le hn21
    · exact absurd hK (lt_irrefl _)
    · rfl
  intro P hP
  obtain ⟨⟨hPX, hTP, hcard⟩, -⟩ := hP
  rcases claimA P hTP.le hPX with hP4 | hP4 | hP4 | hP4
  · rw [hP4] at hTP
    exact absurd hTP (lt_irrefl _)
  · rw [hP4]
    refine ⟨hTlt₁, fun K hK hKP => ?_⟩
    rcases claimA K hK.le (hKP.trans (lift_le C₁)) with rfl | rfl | rfl | rfl
    · exact absurd hK (lt_irrefl _)
    · rfl
    · exact absurd hKP hn21
    · exact absurd (hnX₁ (le_antisymm (lift_le C₁) hKP)) (fun h => h)
  · rw [hP4]
    refine ⟨hTlt₂, fun K hK hKP => ?_⟩
    rcases claimA K hK.le (hKP.trans (lift_le C₂)) with rfl | rfl | rfl | rfl
    · exact absurd hK (lt_irrefl _)
    · exact absurd hKP hn12
    · rfl
    · exact absurd (hnX₂ (le_antisymm (lift_le C₂) hKP)) (fun h => h)
  · exfalso
    rw [hP4] at hcard
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcard
    have hm1 : lift C₁ ∈ maxOver X T := ⟨hmax₁, hTlt₁.le⟩
    have hm2 : lift C₂ ∈ maxOver X T := ⟨hmax₂, hTlt₂.le⟩
    rw [ha] at hm1 hm2
    have e1 : lift C₁ = a := hm1
    have e2 : lift C₂ = a := hm2
    exact hn12 (by rw [e1, e2])

end Transfer

end CFSG.Quasithin
