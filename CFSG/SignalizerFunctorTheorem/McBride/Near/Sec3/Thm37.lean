module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm33Transport
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm37Aux2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem thm37'
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A) {X : Subgroup G}
    (hX : X ∈ mtil p A θ) {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ X) (h₂ : X₂ ≤ X)
    (hd₁ : Admits (dsub A θ ⊔ A) X₁) (hd₂ : Admits (dsub A θ ⊔ A) X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ dsub A θ ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) (hX₂ : X₂ ⊓ dsub A θ ≤ Y)
    (hXC : X ∈ cset p A θ Y) :
    X₁ ≤ thetaM p A θ Y X ∧
      (X₁ ⊓ dsub A θ ≤ Y ∨
        ((X₁ ⊔ dsub A θ) ⊓ thetaM p A θ Y X, (X₂ ⊔ dsub A θ) ⊓ thetaL p A θ Y X) ∈
          pairsY p A θ Y) := by
  have hXD : cenIn X (A : Set G) = dsub A θ := cenIn_eq_dsub hθ hX
  obtain ⟨hYD, hYadm⟩ := Thm36.dset_le_admits hθ hY
  have hDX : dsub A θ ≤ X := hX.2
  have hDn₁ : dsub A θ ≤ Subgroup.normalizer (X₁ : Set G) := le_sup_left.trans hd₁
  have hDn₂ : dsub A θ ≤ Subgroup.normalizer (X₂ : Set G) := le_sup_left.trans hd₂
  have hZX : X₁ ⊔ Y ≤ X := sup_le h₁ (hYD.trans hDX)
  by_cases hfa : X₁ ⊓ dsub A θ ≤ Y
  · refine ⟨?_, Or.inl hfa⟩
    have hDA : IsDAIn A X (X₁ ⊔ Y) :=
      ⟨hZX, by rw [hXD]; exact Admits.sup hd₁ hYadm⟩
    have hinf : (X₁ ⊔ Y) ⊓ dsub A θ = Y := by
      refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hYD)
      obtain ⟨hxS, hxD⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, y, hy, rfl⟩ := (Thm32.mem_sup_iff_mul (hYD.trans hDn₁)).mp hxS
      have haD : a ∈ dsub A θ := by
        have := mul_mem hxD (inv_mem (hYD hy))
        simpa using this
      exact mul_mem (hfa ⟨ha, haD⟩) hy
    have hmem : X₁ ⊔ Y ∈ esetX p A θ Y X :=
      ⟨⟨((mem_mhat_iff_isDAIn hθ hX).mpr hDA).2, hinf⟩, hZX⟩
    exact le_sup_left.trans ((le_iSup₂ (f := fun Z (_ : Z ∈ esetX p A θ Y X) => Z) _ hmem).trans
      (thetaY_le_thetaM' hθ hY hXC))
  · have hpair : (X₁ ⊔ Y, X₂ ⊔ Y) ∈ pairsY p A θ Y :=
      (thm36' hθ hrank hX h₁ h₂ hd₁ hd₂ hc hns hY hX₂).resolve_left hfa
    have hpairX : (X₁ ⊔ Y, X₂ ⊔ Y) ∈ pairsYX p A θ Y X := ⟨hpair, hZX⟩
    have hML := thetaM_thetaL_mem_pairsYX' hθ hY hXC
    have hZM : X₁ ⊔ Y ≤ thetaM p A θ Y X :=
      le_iSup₂ (f := fun P (_ : P ∈ pairsYX p A θ Y X) => P.1) _ hpairX
    have hZL : X₂ ⊔ Y ≤ thetaL p A θ Y X :=
      le_iSup₂ (f := fun P (_ : P ∈ pairsYX p A θ Y X) => P.2) _ hpairX
    refine ⟨le_sup_left.trans hZM, Or.inr ?_⟩
    have hLD : thetaL p A θ Y X ⊓ dsub A θ = Y := hML.1.2
    have hnear : NearAsolvAction p A X := Thm33a.nearAsolvAction_of_mem_mtil hθ hX
    have hML' : (thetaM p A θ Y X, thetaL p A θ Y X) ∈ iPairsY A X Y := by
      rw [← pairsYX_eq_iPairsY hθ hX]
      exact hML
    have hZ' : (X₁ ⊔ Y, X₂ ⊔ Y) ∈ iPairsY A X Y := by
      rw [← pairsYX_eq_iPairsY hθ hX]
      exact hpairX
    have hZ₁L : ¬ X₁ ⊔ Y ≤ thetaL p A θ Y X := by
      intro hle
      apply hfa
      intro x hx
      obtain ⟨hxX₁, hxD⟩ := Subgroup.mem_inf.mp hx
      rw [← hLD]
      exact Subgroup.mem_inf.mpr ⟨hle (Subgroup.mem_sup_left hxX₁), hxD⟩
    have hkey := Thm37.inf_cenIn_le_of_pairs hnear hML' hZ' hZM hZL hZ₁L
    rw [hXD] at hkey
    have e₁ : (X₁ ⊔ dsub A θ) ⊓ thetaM p A θ Y X = X₁ ⊔ Y := by
      refine le_antisymm (fun x hx => ?_) (le_inf (sup_le_sup_left hYD X₁) hZM)
      obtain ⟨hxS, hxM⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, d, hd, rfl⟩ := (Thm32.mem_sup_iff_mul hDn₁).mp hxS
      have haM : a ∈ thetaM p A θ Y X := hZM (Subgroup.mem_sup_left ha)
      have hdM : d ∈ thetaM p A θ Y X := by
        have := mul_mem (inv_mem haM) hxM
        simpa using this
      exact mul_mem (Subgroup.mem_sup_left ha) (hkey ⟨hdM, hd⟩)
    have e₂ : (X₂ ⊔ dsub A θ) ⊓ thetaL p A θ Y X = X₂ ⊔ Y := by
      refine le_antisymm (fun x hx => ?_) (le_inf (sup_le_sup_left hYD X₂) hZL)
      obtain ⟨hxS, hxL⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, d, hd, rfl⟩ := (Thm32.mem_sup_iff_mul hDn₂).mp hxS
      have haL : a ∈ thetaL p A θ Y X := hZL (Subgroup.mem_sup_left ha)
      have hdL : d ∈ thetaL p A θ Y X := by
        have := mul_mem (inv_mem haL) hxL
        simpa using this
      have hdY : d ∈ Y := by
        rw [← hLD]
        exact Subgroup.mem_inf.mpr ⟨hdL, hd⟩
      exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hdY)
    rw [e₁, e₂]
    exact hpair

end CFSG.SignalizerFunctorTheorem.McBride.Near
