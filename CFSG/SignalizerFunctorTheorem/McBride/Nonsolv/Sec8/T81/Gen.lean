module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Coord
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Decomp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Diagonal

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem thetaOf_inf_centralizer_eq (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) :
    thetaOf θ B ⊓ Subgroup.centralizer (A : Set G) = thetaOf θ A := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.ne_bot_of_mem_E2 hB)
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  refine le_antisymm ?_ (le_inf (thetaOf_anti hB.1) (h.isFunctor.thetaOf_le_centralizer le_rfl))
  rw [← h.isFunctor.inf_centralizer_self (hB.1 ha) ha1']
  exact inf_le_inf_right _ (thetaOf_le_apply ha ha1')

theorem le_projIn_mFam
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {L : Subgroup G}
    (hL : L ∈ lcal (thetaOf θ B)) :
    L ≤ projIn (mFam θ (zOf S) B) (mL θ (zOf S) B L) (thetaOf θ A) := by
  have hΩ := h.isRegFam_plane_of_typeA hA hB
  have hT := hΩ.isDirectProduct
  have hT' := isDirectProduct_mFam h hA hr hS hB
  have hHM : thetaOf θ B ≤ sSup (Msig p A θ) :=
    le_sSup (h.thetaOf_mem_msig hB.1 (h.ne_bot_of_mem_E2 hB))
  have hinj : ∀ K ∈ lcal (thetaOf θ B), ∀ K' ∈ lcal (thetaOf θ B),
      mL θ (zOf S) B K = mL θ (zOf S) B K' → K = K' := by
    intro K hK K' hK' heq
    by_contra hne
    exact mL_ne_of_ne h hA hB hK hK' hne heq
  have h1 := projIn_le_projIn_of_le (mL θ (zOf S) B) hT hT' hHM (fun K hK => ⟨K, hK, rfl⟩)
    (fun K _ => le_mL θ (zOf S) B K) hinj (thetaOf_anti hB.1 : thetaOf θ A ≤ thetaOf θ B) hL
  refine le_trans ?_ h1
  have h2 := projIn_centralizer_eq hT (fun a ha J hJ => hΩ.map_conj_mem a ha J hJ) hL
  rw [thetaOf_inf_centralizer_eq h hB, hΩ.stabilizer L hL] at h2
  refine le_trans ?_ h2.ge
  exact le_inf le_rfl (Subgroup.le_centralizer_iff.mpr (h.le_centralizer_of_mem_lcal hB.1 hL))

theorem thetaOf_plane_le_sSup_projFam
    (h : Counterexample p A θ) (hA : TypeA p A θ)
    (hr : InPiTheta A θ r) (hS : IsSr p A θ r S) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {Ω : Set (Subgroup G)}
    (hΩ : IsDirectProduct Ω (sSup (Msig p A θ)))
    (href : ∀ X ∈ Ω, ∃ Y ∈ mFam θ (zOf S) B, X ≤ Y) :
    thetaOf θ B ≤ sSup (projFam Ω (thetaOf θ A)) := by
  rw [← (h.isRegFam_plane_of_typeA hA hB).isDirectProduct.sSup_eq]
  refine sSup_le fun L hL => ?_
  refine (le_projIn_mFam h hA hr hS hB hL).trans ?_
  refine (projIn_le_iSup_projIn_of_refines hΩ (isDirectProduct_mFam h hA hr hS hB) href
    (show mL θ (zOf S) B L ∈ mFam θ (zOf S) B from ⟨L, hL, rfl⟩)).trans ?_
  exact iSup₂_le fun X hX => le_sSup ⟨X, hX, rfl⟩

theorem theta_le_of_lines
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B₁ B₂ : Subgroup G}
    (hB₁ : B₁ ∈ signalizerFunctorEk p 2 A) (hB₂ : B₂ ∈ signalizerFunctorEk p 2 A) {c : G}
    (hc1 : c ≠ 1) (hc : Subgroup.zpowers c = B₁ ⊓ B₂) {W' : Subgroup G}
    (h₁ : thetaOf θ B₁ ≤ W') (h₂ : thetaOf θ B₂ ≤ W') : θ c ≤ W' := by
  have hcB₁ : c ∈ B₁ := (inf_le_left : B₁ ⊓ B₂ ≤ B₁) (hc ▸ Subgroup.mem_zpowers c)
  have hcB₂ : c ∈ B₂ := (inf_le_right : B₁ ⊓ B₂ ≤ B₂) (hc ▸ Subgroup.mem_zpowers c)
  have hcA : c ∈ A := hB₁.1 hcB₁
  have hE := h.zpowers_mem_E1 hcA hc1
  have hΩ := h.isRegFam_line_of_typeA hA hE
  rw [h.isFunctor.thetaOf_zpowers hcA hc1] at hΩ
  obtain ⟨a, haB, hac⟩ := exists_mem_not_mem_zpowers h hB₁ hcB₁ hc1
  obtain ⟨b, hbB, hbc⟩ := exists_mem_not_mem_zpowers h hB₂ hcB₂ hc1
  have hDS : DiagSetting p A (θ c) := ⟨h.prime, h.elemAbelian, h.isFunctor.normalized c hcA hc1,
    hΩ.isDirectProduct, hΩ.nonempty, hΩ.transitive⟩
  have hab : (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) =
      Subgroup.zpowers c := by
    rw [sup_comm, zpowers_sup_eq h hB₁ hcB₁ hc1 haB hac, sup_comm,
      zpowers_sup_eq h hB₂ hcB₂ hc1 hbB hbc, hc]
  have h3 := DiagSetting.sup_eq_top hDS (fun J hJ => (hΩ.stabilizer J hJ).symm) (hB₁.1 haB)
    (hB₂.1 hbB) hac hbc hab
  rw [← thetaOf_plane_eq h hB₁ hcB₁ hc1 haB hac, ← thetaOf_plane_eq h hB₂ hcB₂ hc1 hbB hbc] at h3
  rw [← h3]
  exact sup_le h₁ h₂

theorem sSup_msig_le_of_lines
    (h : Counterexample p A θ) (hA : TypeA p A θ) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ A) (hc₁1 : c₁ ≠ 1) (hc₂ : c₂ ∈ A) (hc₂1 : c₂ ≠ 1)
    (hne : c₂ ∉ Subgroup.zpowers c₁) {W' : Subgroup G} (h₁ : θ c₁ ≤ W') (h₂ : θ c₂ ≤ W') :
    sSup (Msig p A θ) ≤ W' := by
  have hm₁ : Maximal (· ∈ Msig p A θ) (θ c₁) := by
    have := hA.maximal c₁ hc₁ hc₁1
    rwa [h.isFunctor.thetaOf_zpowers hc₁ hc₁1] at this
  have hm₂ : Maximal (· ∈ Msig p A θ) (θ c₂) := by
    have := hA.maximal c₂ hc₂ hc₂1
    rwa [h.isFunctor.thetaOf_zpowers hc₂ hc₂1] at this
  have hT : ({θ c₁, θ c₂} : Set (Subgroup G)) ⊆ Msig p A θ := by
    rintro _ (rfl | rfl)
    · exact h.apply_mem_msig hc₁ hc₁1
    · exact h.apply_mem_msig hc₂ hc₂1
  have hX : sSup ({θ c₁, θ c₂} : Set (Subgroup G)) ≤ W' := by
    rw [sSup_pair]
    exact sup_le h₁ h₂
  rcases h.lemma_6_12 ⟨_, hT, rfl⟩ with ⟨hall, -⟩ | ⟨hXM, -⟩
  · exact sSup_le fun Y hY => (hall Y hY).trans hX
  · exfalso
    have h12 : θ c₂ ≤ θ c₁ := (le_sSup (show θ c₂ ∈ ({θ c₁, θ c₂} : Set (Subgroup G)) from
      Or.inr rfl)).trans (hm₁.2 hXM (le_sSup (show θ c₁ ∈ ({θ c₁, θ c₂} : Set (Subgroup G)) from
      Or.inl rfl)))
    have h21 : θ c₁ ≤ θ c₂ := hm₂.2 (h.apply_mem_msig hc₁ hc₁1) h12
    have hE := h.zpowers_mem_E1 hc₁ hc₁1
    have hΩ := h.isRegFam_line_of_typeA hA hE
    rw [h.isFunctor.thetaOf_zpowers hc₁ hc₁1] at hΩ
    obtain ⟨L, hL⟩ := hΩ.nonempty
    apply hne
    rw [← hΩ.stabilizer L hL]
    refine Subgroup.mem_inf.mpr ⟨hc₂, Subgroup.centralizer_le_normalizer _ ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx2 : x ∈ θ c₂ := h12.antisymm' h21 ▸ lcal_le hL hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.isFunctor.le_centralizer c₂ hc₂ hc₂1 hx2)

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
