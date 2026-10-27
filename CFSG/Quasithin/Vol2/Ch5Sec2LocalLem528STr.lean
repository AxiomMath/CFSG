module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.Quasithin.Vol2.Lie2ParabolicRadicalSp4
public import CFSG.Quasithin.Vol2.KGNatLevi
public import CFSG.Quasithin.Recognition.F112RShapes

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem map_centerOf_of_injective (φ : A →* B) (hφ : Function.Injective φ) (H : Subgroup A) :
    (centerOf H).map φ = centerOf (H.map φ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨⟨x, hx'.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx'.2 h hh]
  · intro hy
    obtain ⟨⟨x, hx, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hy
    refine ⟨x, Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun h hh => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hc (φ h) ⟨h, hh, rfl⟩

theorem map_le_centralizer_map_iff (φ : A →* B) (hφ : Function.Injective φ)
    (H₁ H₂ : Subgroup A) :
    H₁.map φ ≤ Subgroup.centralizer (H₂.map φ : Set B) ↔
      H₁ ≤ Subgroup.centralizer (H₂ : Set A) := by
  constructor
  · intro h x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => hφ ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (h ⟨x, hx, rfl⟩) (φ y) ⟨y, hy, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h hx) y hy]

theorem map_le_normalizer_map_iff (φ : A →* B) (hφ : Function.Injective φ)
    (H₁ H₂ : Subgroup A) :
    H₁.map φ ≤ Subgroup.normalizer (H₂.map φ : Set B) ↔
      H₁ ≤ Subgroup.normalizer (H₂ : Set A) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (h ⟨x, hx, rfl⟩) (φ y)
    constructor
    · intro hy
      obtain ⟨z, hz, hz'⟩ := h1.mp ⟨y, hy, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul] at hz'
      rw [← hφ hz']
      exact hz
    · intro hy
      have h2 : φ x * φ y * (φ x)⁻¹ ∈ H₂.map φ :=
        ⟨x * y * x⁻¹, hy, by rw [map_mul, map_mul, map_inv]⟩
      obtain ⟨z, hz, hz'⟩ := h1.mpr h2
      rw [← hφ hz']
      exact hz
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨x * z * x⁻¹, (Subgroup.mem_normalizer_iff.mp (h hx) z).mp hz, by
        rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨z, hz, hz'⟩
      have h3 : x⁻¹ * z * x⁻¹⁻¹ ∈ H₂ :=
        (Subgroup.mem_normalizer_iff.mp (H₁.inv_mem hx |> h) z).mp hz
      rw [inv_inv] at h3
      refine ⟨x⁻¹ * z * x, h3, ?_⟩
      rw [map_mul, map_mul, map_inv, hz']
      group

end Transport

section Model

variable {G : Type} [Group G] {G₂ : Subgroup G} {Y : Type} [Group Y] {M : Subgroup Y}

theorem model_data (e : ↥G₂ ≃* ↥M) :
    ∃ K' : Subgroup ↥G₂,
      perfectCore G₂ = K'.map G₂.subtype ∧
      perfectCore M = K'.map (M.subtype.comp e.toMonoidHom) ∧
      pCoreOf 2 (perfectCore G₂) = (pCoreOf 2 K').map G₂.subtype ∧
      pCoreOf 2 (perfectCore M) = (pCoreOf 2 K').map (M.subtype.comp e.toMonoidHom) ∧
      centerOf (pCoreOf 2 (perfectCore G₂)) = (centerOf (pCoreOf 2 K')).map G₂.subtype ∧
      centerOf (pCoreOf 2 (perfectCore M)) =
        (centerOf (pCoreOf 2 K')).map (M.subtype.comp e.toMonoidHom) := by
  have hg : Function.Injective G₂.subtype := G₂.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hKg : perfectCore G₂ = (CFSG.perfectResidual ↥G₂).map G₂.subtype :=
    perfectCore_eq_map_perfectResidual G₂
  have hKf : perfectCore M = (CFSG.perfectResidual ↥G₂).map (M.subtype.comp e.toMonoidHom) := by
    rw [perfectCore_eq_map_perfectResidual M, ← Subgroup.map_map,
      CFSG.Quasithin.Vol2.KGNat.map_perfectResidual_equiv e]
  refine ⟨CFSG.perfectResidual ↥G₂, hKg, hKf, ?_, ?_, ?_, ?_⟩
  · rw [hKg, Lie2Parabolic.pCoreOf_map_of_injective _ hg]
  · rw [hKf, Lie2Parabolic.pCoreOf_map_of_injective _ hf]
  · rw [hKg, Lie2Parabolic.pCoreOf_map_of_injective _ hg, map_centerOf_of_injective _ hg]
  · rw [hKf, Lie2Parabolic.pCoreOf_map_of_injective _ hf, map_centerOf_of_injective _ hf]

theorem isSpecialPow_model (e : ↥G₂ ≃* ↥M) {q w : ℕ}
    (h : IsSpecialPow 2 q w ↥(pCoreOf 2 (perfectCore G₂))) :
    IsSpecialPow 2 q w ↥(pCoreOf 2 (perfectCore M)) := by
  obtain ⟨K', -, -, hQg, hQf, -, -⟩ := model_data e
  have hg : Function.Injective G₂.subtype := G₂.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  let e1 : ↥(pCoreOf 2 (perfectCore G₂)) ≃* ↥(pCoreOf 2 K') :=
    (MulEquiv.subgroupCongr hQg).trans
      ((pCoreOf 2 K').equivMapOfInjective G₂.subtype hg).symm
  let e2 : ↥(pCoreOf 2 K') ≃* ↥(pCoreOf 2 (perfectCore M)) :=
    ((pCoreOf 2 K').equivMapOfInjective _ hf).trans (MulEquiv.subgroupCongr hQf.symm)
  exact IsSpecialPow.of_mulEquiv (e1.trans e2) h

theorem exists_map_subtype_of_le {W W₀ : Subgroup G} (hW₀ : W₀ ≤ G₂) (hW : W ≤ W₀) :
    ∃ W' : Subgroup ↥G₂, W'.map G₂.subtype = W :=
  ⟨_, Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hW.trans hW₀)⟩

theorem irred_transport (e : ↥G₂ ≃* ↥M)
    (h1 : perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y))
    (h2 : ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore M) → perfectCore M ≤ Subgroup.normalizer (W : Set Y) →
        W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M)) :
    perfectCore G₂ ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) ∧
      ∀ W : Subgroup G, centerOf (pCoreOf 2 (perfectCore G₂)) ≤ W →
        W ≤ pCoreOf 2 (perfectCore G₂) → perfectCore G₂ ≤ Subgroup.normalizer (W : Set G) →
          W = centerOf (pCoreOf 2 (perfectCore G₂)) ∨ W = pCoreOf 2 (perfectCore G₂) := by
  obtain ⟨K', hKg, hKf, hQg, hQf, hZg, hZf⟩ := model_data e
  have hg : Function.Injective G₂.subtype := G₂.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hQ₀ : pCoreOf 2 (perfectCore G₂) ≤ G₂ := by
    rw [hQg]
    exact (Subgroup.map_le_range _ _).trans (le_of_eq (Subgroup.range_subtype G₂))
  rw [hZf, hKf] at h1
  refine ⟨?_, fun W hZW hWQ hKW => ?_⟩
  · rw [hZg, hKg, map_le_centralizer_map_iff _ hg]
    exact (map_le_centralizer_map_iff _ hf _ _).mp h1
  obtain ⟨W', rfl⟩ := exists_map_subtype_of_le hQ₀ hWQ
  rw [hZg, Subgroup.map_le_map_iff_of_injective hg] at hZW
  rw [hQg, Subgroup.map_le_map_iff_of_injective hg] at hWQ
  rw [hKg, map_le_normalizer_map_iff _ hg] at hKW
  rcases h2 (W'.map (M.subtype.comp e.toMonoidHom))
      ((le_of_eq hZf).trans (Subgroup.map_mono hZW))
      ((Subgroup.map_mono hWQ).trans (le_of_eq hQf.symm))
      (by rw [hKf]; exact (map_le_normalizer_map_iff _ hf _ _).mpr hKW) with h | h
  · left
    rw [hZf] at h
    rw [hZg, Subgroup.map_injective hf h]
  · right
    rw [hQf] at h
    rw [hQg, Subgroup.map_injective hf h]

theorem center_transport (e : ↥G₂ ≃* ↥M)
    (h1 : perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y))
    (h2 : ∀ R : Subgroup Y, R ≤ pCoreOf 2 (perfectCore M) →
      perfectCore M ≤ Subgroup.normalizer (R : Set Y) →
      ¬ R ≤ centerOf (pCoreOf 2 (perfectCore M)) →
        centerOf R ≤ centerOf (pCoreOf 2 (perfectCore M))) :
    perfectCore G₂ ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) ∧
      ∀ R : Subgroup G, R ≤ pCoreOf 2 (perfectCore G₂) →
        perfectCore G₂ ≤ Subgroup.normalizer (R : Set G) →
        ¬ R ≤ centerOf (pCoreOf 2 (perfectCore G₂)) →
          centerOf R ≤ centerOf (pCoreOf 2 (perfectCore G₂)) := by
  obtain ⟨K', hKg, hKf, hQg, hQf, hZg, hZf⟩ := model_data e
  have hg : Function.Injective G₂.subtype := G₂.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hQ₀ : pCoreOf 2 (perfectCore G₂) ≤ G₂ := by
    rw [hQg]
    exact (Subgroup.map_le_range _ _).trans (le_of_eq (Subgroup.range_subtype G₂))
  rw [hZf, hKf] at h1
  refine ⟨?_, fun R hRQ hKR hRZ => ?_⟩
  · rw [hZg, hKg, map_le_centralizer_map_iff _ hg]
    exact (map_le_centralizer_map_iff _ hf _ _).mp h1
  obtain ⟨R', rfl⟩ := exists_map_subtype_of_le hQ₀ hRQ
  rw [hQg, Subgroup.map_le_map_iff_of_injective hg] at hRQ
  rw [hKg, map_le_normalizer_map_iff _ hg] at hKR
  rw [hZg, Subgroup.map_le_map_iff_of_injective hg] at hRZ
  have h3 := h2 (R'.map (M.subtype.comp e.toMonoidHom))
    ((Subgroup.map_mono hRQ).trans (le_of_eq hQf.symm))
    (by rw [hKf]; exact (map_le_normalizer_map_iff _ hf _ _).mpr hKR)
    (by rw [hZf, Subgroup.map_le_map_iff_of_injective hf]; exact hRZ)
  rw [← map_centerOf_of_injective _ hf, hZf, Subgroup.map_le_map_iff_of_injective hf] at h3
  rw [← map_centerOf_of_injective _ hg, hZg]
  exact Subgroup.map_mono h3

theorem x3_transport (e : ↥G₂ ≃* ↥M)
    (h : ∃ x ∈ M, orderOf x = 3 ∧
      ∀ k ∈ perfectCore M, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M)) :
    ∃ x ∈ G₂, orderOf x = 3 ∧
      ∀ k ∈ perfectCore G₂, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore G₂) := by
  obtain ⟨K', hKg, hKf, hQg, hQf, -, -⟩ := model_data e
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  obtain ⟨x, hxM, hx3, hxk⟩ := h
  set x' : ↥G₂ := e.symm ⟨x, hxM⟩ with hx'
  have hfx : (M.subtype.comp e.toMonoidHom) x' = x := by
    simp [hx']
  refine ⟨(x' : G), x'.2, ?_, fun k hk => ?_⟩
  · rw [Subgroup.orderOf_coe, ← orderOf_injective _ hf x', hfx, hx3]
  rw [hKg] at hk
  obtain ⟨k', hk', rfl⟩ := hk
  have h1 := hxk ((M.subtype.comp e.toMonoidHom) k')
    (by rw [hKf]; exact ⟨k', hk', rfl⟩)
  have h1' : (M.subtype.comp e.toMonoidHom) (x' * k' * x'⁻¹ * k'⁻¹) ∈
      (pCoreOf 2 K').map (M.subtype.comp e.toMonoidHom) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfx, ← hQf]
    exact h1
  obtain ⟨c, hc, hc'⟩ := h1'
  rw [hQg]
  refine ⟨c, hc, ?_⟩
  rw [hf hc']
  simp

end Model

section Amalgam

variable {G : Type} [Group G] {G₁ G₂ : Subgroup G}

theorem irred_of_amalgam (hIrr : FactG2D4ParabolicIrred) {n : ℕ}
    (h : (3 ≤ n ∧ IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .G2 0 n) ∧
        IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 (perfectCore G₂))) ∨
      (1 ≤ n ∧
        IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .trialityD4 0 n) ∧
        IsSpecialPow 2 (2 ^ n) 4 ↥(pCoreOf 2 (perfectCore G₂)))) :
    perfectCore G₂ ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) ∧
      ∀ W : Subgroup G, centerOf (pCoreOf 2 (perfectCore G₂)) ≤ W →
        W ≤ pCoreOf 2 (perfectCore G₂) → perfectCore G₂ ≤ Subgroup.normalizer (W : Set G) →
          W = centerOf (pCoreOf 2 (perfectCore G₂)) ∨ W = pCoreOf 2 (perfectCore G₂) := by
  rcases h with ⟨hn, ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩, hsp⟩ |
      ⟨hn, ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩, hsp⟩
  · have h1 := hIrr Y n T M₁ M₂ (Or.inl ⟨hn, hY, isSpecialPow_model φ.φ2 hsp⟩) hpair
    exact irred_transport φ.φ2 h1.1 h1.2
  · have h1 := hIrr Y n T M₁ M₂ (Or.inr ⟨hn, hY, isSpecialPow_model φ.φ2 hsp⟩) hpair
    exact irred_transport φ.φ2 h1.1 h1.2

theorem center_of_amalgam (hG24 : FactG24ParabolicCenter)
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .G2 0 2))
    (hsp : IsSpecialPow 2 4 2 ↥(pCoreOf 2 (perfectCore G₂))) :
    perfectCore G₂ ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore G₂)) : Set G) ∧
      ∀ R : Subgroup G, R ≤ pCoreOf 2 (perfectCore G₂) →
        perfectCore G₂ ≤ Subgroup.normalizer (R : Set G) →
        ¬ R ≤ centerOf (pCoreOf 2 (perfectCore G₂)) →
          centerOf R ≤ centerOf (pCoreOf 2 (perfectCore G₂)) := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ := h
  have h1 := hG24 Y T M₁ M₂ hY hpair (isSpecialPow_model φ.φ2 hsp)
  exact center_transport φ.φ2 h1.1 h1.2

theorem exists_x3_of_amalgam (hXG : FactX3ParabolicG2) (hXU : FactX3ParabolicU4)
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .G2 0 2) ∨
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .PSU 4 2) ∨
      IsU4ExtTwo 2 (RankTwoAmalgam.ofSubgroups G₁ G₂))
    (hsp : IsSpecialPow 2 4 2 ↥(pCoreOf 2 (perfectCore G₂))) :
    ∃ x ∈ G₂, orderOf x = 3 ∧
      ∀ k ∈ perfectCore G₂, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore G₂) := by
  rcases h with ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ | ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ |
      ⟨Y₀, _, Y, _, ι, hY₀, hι, hidx, T, M₁, M₂, hpair, ⟨φ⟩⟩
  · exact x3_transport φ.φ2 (hXG Y T M₁ M₂ hY hpair (isSpecialPow_model φ.φ2 hsp))
  · exact x3_transport φ.φ2 (hXU Y T M₁ M₂ (Or.inl hY) hpair (isSpecialPow_model φ.φ2 hsp))
  · exact x3_transport φ.φ2 (hXU Y T M₁ M₂ (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩) hpair
      (isSpecialPow_model φ.φ2 hsp))

end Amalgam

end CFSG.Quasithin.H13
