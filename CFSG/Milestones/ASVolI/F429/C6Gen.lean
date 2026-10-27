module

public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Thompson

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

variable {G : Type*} [Group G]

theorem burnsideF429_isMaxElemAbelian_iff {S T R : Subgroup G} (hST : S ≤ T) (hRS : R ≤ S)
    (hR : IsElemAbelian 2 R)
    (hT : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ S → Nat.card A < Nat.card R)
    (A : Subgroup G) : IsMaxElemAbelian T A ↔ IsMaxElemAbelian S A := by
  constructor
  · rintro ⟨hAT, hAe, hmax⟩
    have hRA := hmax R (hRS.trans hST) hR
    have hAS : A ≤ S := by
      by_contra h
      exact absurd hRA (not_le.mpr (hT A hAT hAe h))
    exact ⟨hAS, hAe, fun B hB hBe => hmax B (hB.trans hST) hBe⟩
  · rintro ⟨hAS, hAe, hmax⟩
    refine ⟨hAS.trans hST, hAe, fun B hB hBe => ?_⟩
    by_cases hBS : B ≤ S
    · exact hmax B hBS hBe
    · exact (hT B hB hBe hBS).le.trans (hmax R hRS hR)

theorem burnsideF429_thompsonJ_eq {S T R : Subgroup G} (hST : S ≤ T) (hRS : R ≤ S)
    (hR : IsElemAbelian 2 R)
    (hT : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ S → Nat.card A < Nat.card R) :
    thompsonJ T = thompsonJ S := by
  unfold thompsonJ
  simp only [burnsideF429_isMaxElemAbelian_iff hST hRS hR hT]

theorem burnsideF429_thompsonJ_le (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup₂_le fun _ hA => hA.1

theorem burnsideF429_le_omegaOneCenterOf {S R W : Subgroup G} (hR : IsMaxElemAbelian S R)
    (hWR : W ≤ R) (hWc : W ≤ Subgroup.centralizer (S : Set G)) (hW2 : ∀ w ∈ W, w ^ 2 = 1) :
    W ≤ omegaOneCenterOf (thompsonJ S) := by
  intro w hw
  refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hW2 w hw⟩
  · exact (le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) R hR) (hWR hw)
  · exact Subgroup.centralizer_le (burnsideF429_thompsonJ_le S) (hWc hw)

theorem burnsideF429_thompsonJ_eq_glauberman (S : Subgroup G) :
    thompsonJ S = CFSG.SignalizerFunctorTheorem.Glauberman.thompsonJ 2 S := by
  unfold thompsonJ CFSG.SignalizerFunctorTheorem.Glauberman.thompsonJ
  rw [sSup_eq_iSup]
  rfl

theorem burnsideF429_le_omegaOneCenterOf' [Finite G] {S W : Subgroup G} (hWS : W ≤ S)
    (hWc : W ≤ Subgroup.centralizer (S : Set G)) (hW2 : ∀ w ∈ W, w ^ 2 = 1) :
    W ≤ omegaOneCenterOf (thompsonJ S) := by
  have hWO : W ≤ CFSG.SignalizerFunctorTheorem.Glauberman.omegaCenter 2 S := fun w hw =>
    ⟨hWS hw, fun t ht => (Subgroup.mem_centralizer_iff.mp (hWc hw) t ht).symm, hW2 w hw⟩
  intro w hw
  refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hW2 w hw⟩
  · rw [burnsideF429_thompsonJ_eq_glauberman]
    exact CFSG.SignalizerFunctorTheorem.Glauberman.omegaCenter_le_thompsonJ 2 S (hWO hw)
  · exact Subgroup.centralizer_le (burnsideF429_thompsonJ_le S) (hWc hw)

theorem burnsideF429_baum_eq {S T : Subgroup G} (hST : S ≤ T) (hJ : thompsonJ T = thompsonJ S)
    (hC : T ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set G) ≤ S) :
    baum T = baum S := by
  unfold baum
  rw [hJ]
  exact le_antisymm (fun x hx => ⟨hC hx, hx.2⟩) (inf_le_inf_right _ hST)

theorem burnsideF429_card_le_two_mul_of [Finite G] {S A : Subgroup G} {t : G} (htA : t ∈ A)
    (htt : t * t = 1) (hsplit : ∀ a ∈ A, a ∉ S → t * a ∈ S) :
    Nat.card A ≤ 2 * Nat.card (A ⊓ S : Subgroup G) := by
  classical
  have hmemX : ∀ a : A, (a : G) ∉ S → t * (a : G) ∈ A ⊓ S :=
    fun a ha => ⟨A.mul_mem htA a.2, hsplit a a.2 ha⟩
  let φ : A → Bool × (A ⊓ S : Subgroup G) := fun a =>
    if h : (a : G) ∈ S then (false, ⟨a, a.2, h⟩) else (true, ⟨t * a, hmemX a h⟩)
  have hleft : ∀ a : A, (fun p : Bool × (A ⊓ S : Subgroup G) =>
      if p.1 then t * (p.2 : G) else (p.2 : G)) (φ a) = a := by
    intro a
    by_cases ha : (a : G) ∈ S
    · have e : φ a = (false, ⟨a, a.2, ha⟩) := dif_pos ha
      rw [e]
      rfl
    · have e : φ a = (true, ⟨t * a, hmemX a ha⟩) := dif_neg ha
      rw [e]
      show t * (t * (a : G)) = a
      rw [← mul_assoc, htt, one_mul]
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (by rw [← hleft a, ← hleft b, hab])
  calc Nat.card A ≤ Nat.card (Bool × (A ⊓ S : Subgroup G)) := Nat.card_le_card_of_injective φ hφ
    _ = 2 * Nat.card (A ⊓ S : Subgroup G) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

theorem burnsideF429_conj_mul_conj {Y : Type*} [Group Y] (g g' : Y) (σ σ' : MulAut Y) :
    MulAut.conj g * σ * (MulAut.conj g' * σ') = MulAut.conj (g * σ g') * (σ * σ') := by
  refine MulEquiv.ext fun x => ?_
  show g * σ (g' * σ' x * g'⁻¹) * g⁻¹ = g * σ g' * σ (σ' x) * (g * σ g')⁻¹
  rw [map_mul, map_mul, map_inv]
  group

theorem burnsideF429_c6_of {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ T R W : Subgroup E}
    (hST : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ T) (hR : IsMaxElemAbelian (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) R)
    (hT : ∀ A : Subgroup E, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      Nat.card A < Nat.card R)
    (hWR : W ≤ R) (hWc : W ≤ Subgroup.centralizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E))
    (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hC : T ⊓ Subgroup.centralizer (W : Set E) ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :
    burnsideF429_C6 κ f Gp M₁ M₂ T := by
  have hJ := burnsideF429_thompsonJ_eq hST hR.1 hR.2.1 hT
  refine Or.inl ⟨hJ, burnsideF429_baum_eq hST hJ ?_⟩
  exact (inf_le_inf_left T
    (Subgroup.centralizer_le (burnsideF429_le_omegaOneCenterOf hR hWR hWc hW2))).trans hC

theorem burnsideF429_c6_of' {κ : GLKind} {f : ℕ} {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ T R W : Subgroup E}
    (hST : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ T) (hRS : R ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hR : IsElemAbelian 2 R)
    (hT : ∀ A : Subgroup E, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      Nat.card A < Nat.card R)
    (hWS : W ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hWc : W ≤ Subgroup.centralizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E))
    (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hC : T ⊓ Subgroup.centralizer (W : Set E) ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :
    burnsideF429_C6 κ f Gp M₁ M₂ T := by
  have hJ := burnsideF429_thompsonJ_eq hST hRS hR hT
  refine Or.inl ⟨hJ, burnsideF429_baum_eq hST hJ ?_⟩
  exact (inf_le_inf_left T
    (Subgroup.centralizer_le (burnsideF429_le_omegaOneCenterOf' hWS hWc hW2))).trans hC

theorem burnsideF429_thompsonJ_eq_of_unique [Finite G] {S R : Subgroup G} (hRS : R ≤ S)
    (hR : IsElemAbelian 2 R)
    (hB : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → B ≤ R ∨ Nat.card B < Nat.card R) :
    thompsonJ S = R := by
  have hRmax : IsMaxElemAbelian S R := ⟨hRS, hR, fun B hBS hBe => by
    rcases hB B hBS hBe with h | h
    · exact Subgroup.card_le_of_le h
    · exact h.le⟩
  refine le_antisymm (iSup₂_le fun A hA => ?_)
    (le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) R hRmax)
  rcases hB A hA.1 hA.2.1 with h | h
  · exact h
  · exact absurd (hA.2.2 R hRS hR) (not_le.mpr h)

theorem burnsideF429_omegaOneCenterOf_eq {R : Subgroup G} (hR : IsElemAbelian 2 R) :
    omegaOneCenterOf R = R := by
  have hc : ∀ x ∈ R, x ∈ Subgroup.centralizer (R : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => isMulCommutative_iff_of_setLike.mp hR.1 y hy x hx
  unfold omegaOneCenterOf omegaOneOf centerOf
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun x hx => ?_
  · rintro x ⟨⟨hx, -⟩, -⟩
    exact hx
  · exact Subgroup.subset_closure (show x ∈ {y | y ∈ R ⊓ Subgroup.centralizer (R : Set G) ∧
      y ^ 2 = 1} from ⟨⟨hx, hc x hx⟩, hR.2 x hx⟩)

theorem burnsideF429_c6_of_unique {κ : GLKind} {f : ℕ} {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ T R : Subgroup E}
    (hST : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ T) (hRS : R ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hR : IsElemAbelian 2 R)
    (hB : ∀ B : Subgroup E, B ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → IsElemAbelian 2 B →
      B ≤ R ∨ Nat.card B < Nat.card R)
    (hT : ∀ A : Subgroup E, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      Nat.card A < Nat.card R)
    (hC : T ⊓ Subgroup.centralizer (R : Set E) ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :
    burnsideF429_C6 κ f Gp M₁ M₂ T := by
  have hJ := burnsideF429_thompsonJ_eq hST hRS hR hT
  refine Or.inl ⟨hJ, burnsideF429_baum_eq hST hJ ?_⟩
  rw [burnsideF429_thompsonJ_eq_of_unique hRS hR hB, burnsideF429_omegaOneCenterOf_eq hR]
  exact hC

end CFSG.ASVolI
