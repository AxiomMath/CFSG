module

public import CFSG.Quasithin.H13.Sp62DSystem
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {K : Type*} [Group K] [Finite K]

theorem exists_model_hom {X T : Subgroup G} (hiso : quasithinO2QuotientIso X K)
    (hT : IsSylowTwoOf T X) {P₀ : Subgroup K} (hP₀ : IsPGroup 2 P₀) (hP₀' : ¬ 2 ∣ P₀.index) :
    ∃ φ : ↥X →* K, Function.Surjective φ ∧ φ.ker = CFSG.Open.pCore 2 ↥X ∧
      (T.subgroupOf X).map φ = P₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, hφ₀, hker⟩ := hiso
  let S : Sylow 2 ↥X := A4.toSylow hT
  let SK : Sylow 2 K := S.mapSurjective hφ₀
  let P : Sylow 2 K := hP₀.toSylow hP₀'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P SK
  let c : K →* K := MulDistribMulAction.toMonoidEnd (MulAut K) K (MulAut.conj k⁻¹)
  have hc : ∀ x : K, c x = k⁻¹ * x * k := fun x => by
    show (MulAut.conj k⁻¹) x = _
    simp
  have hcinj : Function.Injective c := fun x y h => by
    rw [hc, hc] at h
    simpa using h
  have hcsurj : Function.Surjective c := fun y => ⟨k * y * k⁻¹, by rw [hc]; group⟩
  refine ⟨c.comp φ₀, hcsurj.comp hφ₀, ?_, ?_⟩
  · rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hcinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  · let d : K →* K := MulDistribMulAction.toMonoidEnd (MulAut K) K (MulAut.conj k)
    have h1 : ((T.subgroupOf X).map φ₀) = P₀.map d := by
      have := congrArg (fun Q : Sylow 2 K => (Q : Subgroup K)) hk
      exact this.symm
    rw [← Subgroup.map_map, h1, Subgroup.map_map]
    have hid : c.comp d = MonoidHom.id K := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hc]
      show k⁻¹ * ((MulAut.conj k) x) * k = x
      simp only [MulAut.conj_apply]
      group
    rw [hid, Subgroup.map_id]

section Abstract

variable {H : Type} [Group H]

omit [Finite K] in
theorem model_parabolics_aux (φ : H →* K) (hφ : Function.Surjective φ)
    {Tx Pa Pb : Subgroup H} (hker : φ.ker ≤ Tx) {P₀ X₁ X₂ : Subgroup K}
    (hTφ : Tx.map φ = P₀)
    (hcls : ∀ Y : Subgroup K, P₀ ≤ Y → Y = P₀ ∨ Y = X₁ ∨ Y = X₂ ∨ Y = ⊤)
    (h₁ : P₀ ≤ X₁) (h₂ : P₀ ≤ X₂) (h₁₂ : ¬ X₁ ≤ X₂) (h₂₁ : ¬ X₂ ≤ X₁) (hab : Pa ≠ Pb)
    (hmax : ∀ Y : Subgroup H, (Tx ≤ Y ∧ A6.IsMaxSubgroupIn Y ⊤) ↔ (Y = Pa ∨ Y = Pb)) :
    (Pa.map φ = X₁ ∧ Pb.map φ = X₂) ∨ (Pa.map φ = X₂ ∧ Pb.map φ = X₁) := by
  have hcm : ∀ Y : Subgroup H, Tx ≤ Y → (Y.map φ).comap φ = Y := fun Y hY => by
    rw [Subgroup.comap_map_eq, sup_eq_left.2 (hker.trans hY)]
  have hmc : ∀ W : Subgroup K, (W.comap φ).map φ = W := fun W =>
    Subgroup.map_comap_eq_self_of_surjective hφ W
  have key : ∀ Y : Subgroup H, (Tx ≤ Y ∧ A6.IsMaxSubgroupIn Y ⊤) →
      Y.map φ = X₁ ∨ Y.map φ = X₂ := by
    rintro Y ⟨hTY, hlt, hmaxY⟩
    have hP : P₀ ≤ Y.map φ := hTφ ▸ Subgroup.map_mono hTY
    rcases hcls _ hP with h | h | h | h
    · exfalso
      have hYT : Y = Tx := by
        rw [← hcm Y hTY, h, ← hTφ, hcm Tx le_rfl]
      have hW : Tx ≤ X₁.comap φ := by
        rw [← hcm Tx le_rfl, hTφ]
        exact Subgroup.comap_mono h₁
      rcases hmaxY (X₁.comap φ) (by rw [hYT]; exact hW) le_top with hh | hh
      · apply h₁₂
        have : X₁ = P₀ := by
          rw [← hmc X₁, hh, hYT, hTφ]
        exact this ▸ h₂
      · apply h₂₁
        have : X₁ = ⊤ := by rw [← hmc X₁, hh, Subgroup.map_top_of_surjective φ hφ]
        rw [this]; exact le_top
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have : Y = ⊤ := by rw [← hcm Y hTY, h, Subgroup.comap_top]
      exact (lt_irrefl _) (this ▸ hlt)
  have hPa := (hmax Pa).2 (Or.inl rfl)
  have hPb := (hmax Pb).2 (Or.inr rfl)
  have hne : Pa.map φ ≠ Pb.map φ := fun h => hab (by
    rw [← hcm Pa hPa.1, h, hcm Pb hPb.1])
  rcases key Pa hPa with h1 | h1 <;> rcases key Pb hPb with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Abstract

omit [Finite G] [Finite K] in
theorem ker_le_of_model {X T : Subgroup G} (hT : IsSylowTwoOf T X) (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) : φ.ker ≤ T.subgroupOf X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hker]
  exact IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) (A4.toSylow hT)

omit [Finite G] [Finite K] in
theorem subgroupOf_eq_comap_map {X T Y : Subgroup G} (hT : IsSylowTwoOf T X) (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) (hTY : T ≤ Y) :
    Y.subgroupOf X = ((Y.subgroupOf X).map φ).comap φ := by
  rw [Subgroup.comap_map_eq, sup_eq_left.2 ((ker_le_of_model hT φ hker).trans
    (Subgroup.subgroupOf_mono _ hTY))]

theorem exists_model_parabolics {X T Pa Pb : Subgroup G} (hiso : quasithinO2QuotientIso X K)
    (hT : IsSylowTwoOf T X) {P₀ X₁ X₂ : Subgroup K} (hP₀ : IsPGroup 2 P₀)
    (hP₀' : ¬ 2 ∣ P₀.index)
    (hcls : ∀ Y : Subgroup K, P₀ ≤ Y → Y = P₀ ∨ Y = X₁ ∨ Y = X₂ ∨ Y = ⊤)
    (h₁ : P₀ ≤ X₁) (h₂ : P₀ ≤ X₂) (h₁₂ : ¬ X₁ ≤ X₂) (h₂₁ : ¬ X₂ ≤ X₁)
    (hPaX : Pa ≤ X) (hPbX : Pb ≤ X) (hab : Pa ≠ Pb)
    (hmax : ∀ Y : Subgroup G, (T ≤ Y ∧ A6.IsMaxSubgroupIn Y X) ↔ (Y = Pa ∨ Y = Pb)) :
    ∃ φ : ↥X →* K, Function.Surjective φ ∧ φ.ker = CFSG.Open.pCore 2 ↥X ∧
      (T.subgroupOf X).map φ = P₀ ∧
      (((Pa.subgroupOf X).map φ = X₁ ∧ (Pb.subgroupOf X).map φ = X₂) ∨
       ((Pa.subgroupOf X).map φ = X₂ ∧ (Pb.subgroupOf X).map φ = X₁)) := by
  obtain ⟨φ, hφ, hker, hTφ⟩ := exists_model_hom hiso hT hP₀ hP₀'
  refine ⟨φ, hφ, hker, hTφ, model_parabolics_aux φ hφ (ker_le_of_model hT φ hker) hTφ hcls h₁ h₂
    h₁₂ h₂₁ ?_ ?_⟩
  · intro h
    exact hab (by
      have := congrArg (Subgroup.map X.subtype) h
      rwa [map_subtype_subgroupOf hPaX, map_subtype_subgroupOf hPbX] at this)
  · intro Y'
    have hYle : Y'.map X.subtype ≤ X := Subgroup.map_subtype_le _
    have h := hmax (Y'.map X.subtype)
    have hTle : T ≤ Y'.map X.subtype ↔ T.subgroupOf X ≤ Y' := by
      rw [← Subgroup.map_subtype_le_map_subtype, map_subtype_subgroupOf hT.1]
    have hmx : A6.IsMaxSubgroupIn (Y'.map X.subtype) X ↔ A6.IsMaxSubgroupIn Y' ⊤ := by
      rw [isMaxSubgroupIn_map_iff Y' ⊤, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hsub : ∀ A : Subgroup G, A ≤ X → (Y'.map X.subtype = A ↔ Y' = A.subgroupOf X) := by
      intro A hA
      constructor
      · intro h'
        rw [← h']
        exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Y').symm
      · intro h'; rw [h', map_subtype_subgroupOf hA]
    rw [hTle, hmx, hsub Pa hPaX, hsub Pb hPbX] at h
    exact h

end CFSG.Quasithin.H13.I51
