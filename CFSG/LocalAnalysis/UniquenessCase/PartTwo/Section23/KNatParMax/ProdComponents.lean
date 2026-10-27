module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsComp
import CFSG.Goldschmidt.Steps.G37CoreSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

private lemma map_conj_eq_of_mem_normalizer_M07 {H : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj r).toMonoidHom = H := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hr y).mp hy
  · intro z hz
    refine ⟨r⁻¹ * z * r, ?_, ?_⟩
    · have hz' : r⁻¹ * z * r ∈ H := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (H : Set G)).inv_mem hr) z).mp hz
      exact hz'
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private lemma isComponentOf_map_conj_of_mem_normalizer_M07 {L H : Subgroup G}
    (hL : IsComponentOf L H) {r : G} (hr : r ∈ Subgroup.normalizer (H : Set G)) :
    IsComponentOf (L.map (MulAut.conj r).toMonoidHom) H := by
  have h := CFSG.Goldschmidt.G37.open_isComponentOf_map (MulAut.conj r) hL
  rwa [map_conj_eq_of_mem_normalizer_M07 hr] at h

private lemma ne_bot_of_isComponentOf_M07 {F H : Subgroup G} (h : IsComponentOf F H) :
    F ≠ ⊥ := by
  intro hF
  haveI : Subsingleton ↥F := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : G) = 1 := by simpa only [hF, Subgroup.mem_bot] using x.2
    have hy : (y : G) = 1 := by simpa only [hF, Subgroup.mem_bot] using y.2
    rw [hx, hy]
  haveI : IsSimpleGroup (↥F ⧸ Subgroup.center ↥F) := h.2.2.2
  exact not_subsingleton _ (inferInstance : Subsingleton (↥F ⧸ Subgroup.center ↥F))

private lemma ne_top_of_isComponentOf_of_disjoint_M07 {F₁ F₂ H : Subgroup G}
    (hH : F₁ ⊔ F₂ = H) (hd : Disjoint F₁ F₂) (h₂ : IsComponentOf F₂ H) : F₁ ≠ H := by
  intro hF
  have hle : F₂ ≤ (⊥ : Subgroup G) :=
    (le_inf (by rw [hF]; exact h₂.1) le_rfl).trans hd.le_bot
  exact ne_bot_of_isComponentOf_M07 h₂ (le_bot_iff.mp hle)

private lemma isMulCommutative_of_ne_factors_M07 {F₁ F₂ H K : Subgroup G}
    (hH : F₁ ⊔ F₂ = H) (h₁ : IsComponentOf F₁ H) (h₂ : IsComponentOf F₂ H)
    (hK : IsComponentOf K H) (hK₁ : K ≠ F₁) (hK₂ : K ≠ F₂) :
    IsMulCommutative ↥K := by
  have hc1 : ∀ k ∈ K, ∀ k' ∈ F₁, k * k' = k' * k :=
    (CFSG.LocalAnalysis.WeakClosure81.eq_or_commute_of_isComponentOf hK h₁).resolve_left hK₁
  have hc2 : ∀ k ∈ K, ∀ k' ∈ F₂, k * k' = k' * k :=
    (CFSG.LocalAnalysis.WeakClosure81.eq_or_commute_of_isComponentOf hK h₂).resolve_left hK₂
  refine ⟨⟨fun a b => ?_⟩⟩
  have h1c : F₁ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hc1 a a.2 f hf
  have h2c : F₂ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hc2 a a.2 f hf
  have hHc : H ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [← hH]
    exact sup_le h1c h2c
  refine Subtype.ext ?_
  exact Subgroup.mem_centralizer_iff.mp (hHc (hK.1 b.2)) a (Set.mem_singleton (a : G))

theorem eq_factor_of_isComponentOf {F₁ F₂ H K : Subgroup G} (hH : F₁ ⊔ F₂ = H)
    (h₁ : IsComponentOf F₁ H) (h₂ : IsComponentOf F₂ H) (hK : IsComponentOf K H) :
    K = F₁ ∨ K = F₂ := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hK₁, hK₂⟩ := h
  haveI : IsMulCommutative ↥K := isMulCommutative_of_ne_factors_M07 hH h₁ h₂ hK hK₁ hK₂
  have hbot : commutator ↥K = ⊥ := commutator_eq_bot ↥K
  have htopbot : (⊤ : Subgroup ↥K) = ⊥ := hK.2.2.1.symm.trans hbot
  haveI : Subsingleton ↥K := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : x = 1 := by
      have hx' : x ∈ (⊥ : Subgroup ↥K) := htopbot ▸ Subgroup.mem_top x
      simpa only [Subgroup.mem_bot] using hx'
    have hy : y = 1 := by
      have hy' : y ∈ (⊥ : Subgroup ↥K) := htopbot ▸ Subgroup.mem_top y
      simpa only [Subgroup.mem_bot] using hy'
    rw [hx, hy]
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  exact not_subsingleton _ (inferInstance : Subsingleton (↥K ⧸ Subgroup.center ↥K))

private lemma not_le_of_iSup_map_conj_M07 {H K R X : Subgroup G}
    (hgen : H = ⨆ r ∈ R, K.map (MulAut.conj r).toMonoidHom)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hXH : X < H) : ¬ K ≤ X := by
  intro hKX
  refine not_le_of_gt hXH ?_
  rw [hgen]
  refine iSup₂_le fun r hr => ?_
  calc K.map (MulAut.conj r).toMonoidHom
      ≤ X.map (MulAut.conj r).toMonoidHom := Subgroup.map_mono hKX
    _ = X := map_conj_eq_of_mem_normalizer_M07 (hRX hr)

private lemma aux_M07 {F₁ F₂ H K R X : Subgroup G} (hH : F₁ ⊔ F₂ = H)
    (hd : Disjoint F₁ F₂) (h₁ : IsComponentOf F₁ H) (h₂ : IsComponentOf F₂ H)
    (hK : IsComponentOf K H) (hR : R ≤ Subgroup.normalizer (H : Set G))
    (hgen : H = ⨆ r ∈ R, K.map (MulAut.conj r).toMonoidHom)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hXH : X < H) (hle : F₁ ≤ X) : False := by
  have hKX : ¬ K ≤ X := not_le_of_iSup_map_conj_M07 hgen hRX hXH
  rcases eq_factor_of_isComponentOf hH h₁ h₂ hK with hKF₁ | hKF₂
  · exact hKX (hKF₁ ▸ hle)
  · have hF2H : F₂ ≠ H :=
      ne_top_of_isComponentOf_of_disjoint_M07 (F₁ := F₂) (F₂ := F₁)
        (by rw [sup_comm]; exact hH) hd.symm h₁
    have hswap : ∃ r ∈ R, F₂.map (MulAut.conj r).toMonoidHom ≠ F₂ := by
      by_contra h
      have h' : ∀ r ∈ R, F₂.map (MulAut.conj r).toMonoidHom = F₂ := by
        intro r hr
        by_contra hne
        exact h ⟨r, hr, hne⟩
      have hleF2 : H ≤ F₂ := by
        rw [hgen]
        refine iSup₂_le fun r hr => ?_
        rw [hKF₂, h' r hr]
      exact hF2H (le_antisymm hleF2 h₂.1).symm
    obtain ⟨r, hr, hne⟩ := hswap
    have hcomp : IsComponentOf (F₂.map (MulAut.conj r).toMonoidHom) H :=
      isComponentOf_map_conj_of_mem_normalizer_M07 h₂ (hR hr)
    have hCF1 : F₂.map (MulAut.conj r).toMonoidHom = F₁ := by
      rcases eq_factor_of_isComponentOf hH h₁ h₂ hcomp with hC | hC
      · exact hC
      · exact absurd hC hne
    have hcomp' : (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj r).toMonoidHom
        = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    have hmap : F₂ = F₁.map (MulAut.conj r⁻¹).toMonoidHom := by
      have h1 : F₂ = (F₂.map (MulAut.conj r).toMonoidHom).map
          (MulAut.conj r⁻¹).toMonoidHom := by
        rw [Subgroup.map_map, hcomp', Subgroup.map_id]
      rw [h1, hCF1]
    have hrX : r⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normalizer (X : Set G)).inv_mem (hRX hr)
    have hF2le : F₂ ≤ X := by
      rw [hmap]
      calc F₁.map (MulAut.conj r⁻¹).toMonoidHom
          ≤ X.map (MulAut.conj r⁻¹).toMonoidHom := Subgroup.map_mono hle
        _ = X := map_conj_eq_of_mem_normalizer_M07 hrX
    exact not_le_of_gt hXH (hH ▸ sup_le hle hF2le)

theorem not_factor_le_of_swap {F₁ F₂ H K R X : Subgroup G} (hH : F₁ ⊔ F₂ = H)
    (hd : Disjoint F₁ F₂) (h₁ : IsComponentOf F₁ H) (h₂ : IsComponentOf F₂ H)
    (hK : IsComponentOf K H) (hR : R ≤ Subgroup.normalizer (H : Set G))
    (hgen : H = ⨆ r ∈ R, K.map (MulAut.conj r).toMonoidHom)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hXH : X < H) : ¬ F₁ ≤ X ∧ ¬ F₂ ≤ X := by
  refine ⟨fun hle => aux_M07 hH hd h₁ h₂ hK hR hgen hRX hXH hle, fun hle => ?_⟩
  exact aux_M07 (by rw [sup_comm]; exact hH) hd.symm h₂ h₁ hK hR hgen hRX hXH hle

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
