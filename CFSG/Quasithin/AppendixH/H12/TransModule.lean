module

public import CFSG.Quasithin.AppendixH.H12.TransGroup

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

namespace Trans

variable {Γ : Type*} [Group Γ] {L' : Subgroup Γ} {G : Type*} [Group G] {L : Subgroup G}
  {V' V : Type*} [CommGroup V'] [CommGroup V] {ρ' : Γ →* MulAut V'} {ρ : G →* MulAut V}
  (τ : Trans L' L ρ' ρ)

private lemma congr_apply_mulAut (β : V' ≃* V) (a : MulAut V') (v : V') :
    (MulAut.congr β a) (β v) = β (a v) := by
  rw [MulAut.congr_apply]
  simp

private lemma map_map_congr (β : V' ≃* V) (a : MulAut V') (P : Subgroup V') :
    (P.map β.toMonoidHom).map (MulAut.congr β a).toMonoidHom =
      (P.map a.toMonoidHom).map β.toMonoidHom := by
  rw [Subgroup.map_map]
  have h : (MulAut.congr β a).toMonoidHom.comp β.toMonoidHom =
      β.toMonoidHom.comp a.toMonoidHom := by
    ext x
    simpa using congr_apply_mulAut β a x
  rw [h, ← Subgroup.map_map]

private lemma fixV_map_congr (β : V' ≃* V) (Y : Subgroup (MulAut V')) :
    fixV (Y.map (MulAut.congr β).toMonoidHom) = (fixV Y).map β.toMonoidHom := by
  ext v
  rw [mem_fixV, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨β.symm v, ?_, β.apply_symm_apply v⟩
    rw [mem_fixV]
    intro y hy
    apply β.injective
    have h1 : (MulAut.congr β y) v = v := h (MulAut.congr β y) (Subgroup.mem_map_of_mem _ hy)
    rw [MulAut.congr_apply] at h1
    simpa using h1
  · rintro ⟨w, hw, rfl⟩
    rw [mem_fixV] at hw
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (MulAut.congr β y) (β w) = β w
    simp [MulAut.congr_apply, hw y hy]

private lemma commV_map_congr (β : V' ≃* V) (Y : Subgroup (MulAut V')) :
    commV (Y.map (MulAut.congr β).toMonoidHom) = (commV Y).map β.toMonoidHom := by
  rw [commV, commV, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a', ha', u, rfl⟩
    rw [Subgroup.mem_map] at ha'
    obtain ⟨a, ha, rfl⟩ := ha'
    refine ⟨a (β.symm u) * (β.symm u)⁻¹, ⟨a, ha, β.symm u, rfl⟩, ?_⟩
    change β (a (β.symm u) * (β.symm u)⁻¹) = (MulAut.congr β a) u * u⁻¹
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, ← congr_apply_mulAut,
      MulEquiv.apply_symm_apply]
  · rintro ⟨w, ⟨a, ha, v, rfl⟩, rfl⟩
    refine ⟨MulAut.congr β a, ⟨a, ha, rfl⟩, β v, ?_⟩
    change (MulAut.congr β a) (β v) * (β v)⁻¹ = β (a v * v⁻¹)
    rw [congr_apply_mulAut, map_mul, map_inv]

private lemma rho_phi (g : ↥L') :
    ρ (τ.φ g : G) = MulAut.congr τ.β (ρ' (g : Γ)) := by
  ext v
  have h := τ.compat g (τ.β.symm v)
  simpa [MulAut.congr_apply] using h

private lemma rho_phi_apply (g : ↥L') (v : V) :
    ρ (τ.φ g : G) v = τ.β (ρ' (g : Γ) (τ.β.symm v)) := by
  rw [rho_phi, MulAut.congr_apply]
  simp

theorem mem_toV {P : Subgroup V'} {v : V} : v ∈ τ.toV P ↔ τ.β.symm v ∈ P := by
  rw [Trans.toV]
  exact Subgroup.mem_map_equiv

theorem toV_ofV (Q : Subgroup V) : τ.toV (Q.map τ.β.symm.toMonoidHom) = Q := by
  rw [Trans.toV, Subgroup.map_map]
  have h : τ.β.toMonoidHom.comp τ.β.symm.toMonoidHom = MonoidHom.id V := by
    ext x
    exact τ.β.apply_symm_apply x
  rw [h, Subgroup.map_id]

theorem card_toV (P : Subgroup V') : Nat.card (τ.toV P) = Nat.card P := by
  rw [Trans.toV]
  exact Subgroup.card_map_of_injective τ.β.injective

theorem toV_mono_iff {P Q : Subgroup V'} : τ.toV P ≤ τ.toV Q ↔ P ≤ Q := by
  constructor
  · intro h p hp
    have hp' : τ.β p ∈ τ.toV P := ⟨p, hp, rfl⟩
    have hq := h hp'
    rw [mem_toV, MulEquiv.symm_apply_apply] at hq
    exact hq
  · intro h
    exact Subgroup.map_mono h

theorem toV_inj {P Q : Subgroup V'} (h : τ.toV P = τ.toV Q) : P = Q := by
  refine le_antisymm ?_ ?_
  · exact (toV_mono_iff τ).mp (le_of_eq h)
  · exact (toV_mono_iff τ).mp (le_of_eq h.symm)

theorem toV_sup (P Q : Subgroup V') : τ.toV (P ⊔ Q) = τ.toV P ⊔ τ.toV Q := by
  rw [Trans.toV, Trans.toV, Trans.toV]
  exact Subgroup.map_sup P Q τ.β.toMonoidHom

theorem map_toG_rho {X : Subgroup Γ} (hX : X ≤ L') :
    (τ.toG X).map ρ = (X.map ρ').map (MulAut.congr τ.β).toMonoidHom := by
  ext a
  constructor
  · intro ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    rw [mem_toG] at hg
    obtain ⟨h, hL, hhX, hgh⟩ := hg
    rw [Subgroup.mem_map_equiv]
    have hconj : ρ g = MulAut.congr τ.β (ρ' h) := by rw [hgh.symm, rho_phi]
    rw [hconj, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_map_of_mem ρ' hhX
  · intro ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    rw [Subgroup.mem_map] at ha'
    obtain ⟨h, hhX, rfl⟩ := ha'
    rw [Subgroup.mem_map]
    exact ⟨(τ.φ ⟨h, hX hhX⟩ : G),
      by rw [mem_toG]; exact ⟨h, hX hhX, hhX, rfl⟩, rho_phi τ ⟨h, hX hhX⟩⟩

theorem fixV_toG {X : Subgroup Γ} (hX : X ≤ L') :
    fixV ((τ.toG X).map ρ) = τ.toV (fixV (X.map ρ')) := by
  rw [map_toG_rho τ hX, fixV_map_congr τ.β]
  rfl

theorem commV_toG {X : Subgroup Γ} (hX : X ≤ L') :
    commV ((τ.toG X).map ρ) = τ.toV (commV (X.map ρ')) := by
  rw [map_toG_rho τ hX, commV_map_congr τ.β]
  rfl

theorem ptStab_toG {X : Subgroup Γ} (hX : X ≤ L') (P : Subgroup V') :
    ptStab ρ (τ.toG X) (τ.toV P) = τ.toG (ptStab ρ' X P) := by
  ext g
  constructor
  · intro hg
    rw [ptStab, Subgroup.mem_inf, Subgroup.mem_comap] at hg
    obtain ⟨hgX, hgstab⟩ := hg
    rw [mem_toG] at hgX ⊢
    obtain ⟨h, hL, hhX, hgh⟩ := hgX
    refine ⟨h, hL, ?_, hgh⟩
    rw [ptStab, Subgroup.mem_inf, Subgroup.mem_comap, mem_stabSub]
    refine ⟨hhX, fun u => ?_⟩
    have h1 := (mem_stabSub.mp hgstab) (τ.β u)
    rw [mem_toV, mem_toV] at h1
    have h2 : ρ g (τ.β u) = τ.β (ρ' h u) := by
      rw [hgh.symm, rho_phi_apply, MulEquiv.symm_apply_apply]
    rw [h2] at h1
    simpa using h1
  · intro hg
    rw [ptStab, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [mem_toG] at hg
    obtain ⟨h, hL, hh, hgh⟩ := hg
    rw [ptStab, Subgroup.mem_inf, Subgroup.mem_comap, mem_stabSub] at hh
    obtain ⟨hhX, hhstab⟩ := hh
    refine ⟨?_, ?_⟩
    · rw [mem_toG]; exact ⟨h, hL, hhX, hgh⟩
    · rw [mem_stabSub]
      intro w
      rw [mem_toV, mem_toV]
      have h2 : ρ g w = τ.β (ρ' h (τ.β.symm w)) := by
        rw [hgh.symm, rho_phi_apply]
      rw [h2, MulEquiv.symm_apply_apply]
      exact hhstab (τ.β.symm w)

theorem cenIn_toG {X : Subgroup Γ} (hX : X ≤ L') (W : Subgroup V') :
    cenIn ρ (τ.toG X) (τ.toV W) = τ.toG (cenIn ρ' X W) := by
  ext g
  constructor
  · intro hg
    rw [cenIn, Subgroup.mem_inf, Subgroup.mem_comap] at hg
    obtain ⟨hgX, hgcent⟩ := hg
    rw [mem_toG] at hgX ⊢
    obtain ⟨h, hL, hhX, hgh⟩ := hgX
    refine ⟨h, hL, ?_, hgh⟩
    rw [cenIn, Subgroup.mem_inf, Subgroup.mem_comap, mem_centSub]
    refine ⟨hhX, fun u hu => ?_⟩
    have h1 : ρ g (τ.β u) = τ.β u :=
      (mem_centSub.mp hgcent) (τ.β u) (by rw [mem_toV, MulEquiv.symm_apply_apply]; exact hu)
    have h2 : ρ g (τ.β u) = τ.β (ρ' h u) := by
      rw [hgh.symm, rho_phi_apply, MulEquiv.symm_apply_apply]
    rw [h2] at h1
    exact τ.β.injective h1
  · intro hg
    rw [cenIn, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [mem_toG] at hg
    obtain ⟨h, hL, hh, hgh⟩ := hg
    rw [cenIn, Subgroup.mem_inf, Subgroup.mem_comap, mem_centSub] at hh
    obtain ⟨hhX, hhcent⟩ := hh
    refine ⟨?_, ?_⟩
    · rw [mem_toG]; exact ⟨h, hL, hhX, hgh⟩
    · rw [mem_centSub]
      intro w hw
      rw [mem_toV] at hw
      have h2 : ρ g w = τ.β (ρ' h (τ.β.symm w)) := by
        rw [hgh.symm, rho_phi_apply]
      rw [h2, hhcent (τ.β.symm w) hw, MulEquiv.apply_symm_apply]

theorem isConjPt_toG {X : Subgroup Γ} (hX : X ≤ L') (P P' : Subgroup V') :
    IsConjPt ρ (τ.toG X) (τ.toV P) (τ.toV P') ↔ IsConjPt ρ' X P P' := by
  constructor
  · rintro ⟨g, hg, hmap⟩
    rw [mem_toG] at hg
    obtain ⟨h, hL, hhX, hgh⟩ := hg
    refine ⟨h, hhX, ?_⟩
    refine Subgroup.map_injective (f := τ.β.toMonoidHom) τ.β.injective ?_
    have hconj : ρ g = MulAut.congr τ.β (ρ' h) := by rw [hgh.symm, rho_phi]
    rw [← map_map_congr τ.β (ρ' h) P, ← hconj]
    exact hmap
  · rintro ⟨h, hhX, hmap⟩
    refine ⟨(τ.φ ⟨h, hX hhX⟩ : ↥L), ?_, ?_⟩
    · rw [mem_toG]; exact ⟨h, hX hhX, hhX, rfl⟩
    · rw [show ρ (τ.φ ⟨h, hX hhX⟩ : G) = MulAut.congr τ.β (ρ' h) from
        rho_phi τ ⟨h, hX hhX⟩]
      rw [Trans.toV, Trans.toV, map_map_congr τ.β (ρ' h) P, hmap]

theorem forall_toG_forall_toV {T : Subgroup Γ} (hT : T ≤ L') (P : Subgroup V') :
    (∀ t ∈ τ.toG T, ∀ x ∈ τ.toV P, ρ t x ∈ τ.toV P) ↔ (∀ t ∈ T, ∀ x ∈ P, ρ' t x ∈ P) := by
  constructor
  · intro h t ht x hx
    have htG : (τ.φ ⟨t, hT ht⟩ : G) ∈ τ.toG T := by
      rw [mem_toG]; exact ⟨t, hT ht, ht, rfl⟩
    have hxV : τ.β x ∈ τ.toV P := by rw [mem_toV, MulEquiv.symm_apply_apply]; exact hx
    have h1 := h _ htG _ hxV
    rw [mem_toV] at h1
    rw [rho_phi_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro h t ht x hx
    rw [mem_toG] at ht
    obtain ⟨t', ht'L, ht'T, ht'eq⟩ := ht
    rw [mem_toV] at hx
    have hβ : τ.β (ρ' t' (τ.β.symm x)) ∈ τ.toV P := by
      rw [mem_toV, MulEquiv.symm_apply_apply]
      exact h t' ht'T (τ.β.symm x) hx
    have hρ : ρ t x = τ.β (ρ' t' (τ.β.symm x)) := by
      rw [← ht'eq, rho_phi_apply]
    rwa [hρ]

theorem kSmul_iota {K : Type*} [Field K] (ι : K →+* AddMonoid.End (Additive V')) (c : K)
    (v : V') : kSmul (τ.iota ι) c (τ.β v) = τ.β (kSmul ι c v) := by
  simp only [kSmul]
  rw [show τ.iota ι c (Additive.ofMul (τ.β v)) =
      τ.β.toAdditive ((ι c) (τ.β.toAdditive.symm (Additive.ofMul (τ.β v)))) from rfl]
  simp

theorem form_apply {K : Type*} (f : V' → V' → K) (u v : V') :
    τ.form f (τ.β u) (τ.β v) = f u v := by
  simp [Trans.form]

theorem kLine_iota {K : Type*} [Field K] (ι : K →+* AddMonoid.End (Additive V')) (v : V') :
    kLine (τ.iota ι) (τ.β v) = τ.toV (kLine ι v) := by
  rw [kLine, kLine, Trans.toV, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨kSmul ι c v, ⟨c, rfl⟩, (kSmul_iota τ ι c v).symm⟩
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (kSmul_iota τ ι c v).symm⟩

theorem isUnitaryForm_iota {K : Type*} [Field K] {ι : K →+* AddMonoid.End (Additive V')}
    {f : V' → V' → K} (h : IsUnitaryForm ι f) : IsUnitaryForm (τ.iota ι) (τ.form f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u u' v
    simp only [Trans.form]
    rw [map_mul]
    exact h1 _ _ _
  · intro u v v'
    simp only [Trans.form]
    rw [map_mul]
    exact h2 _ _ _
  · intro c u v
    have hk : τ.β.symm (kSmul (τ.iota ι) c u) = kSmul ι c (τ.β.symm u) := by
      conv_lhs => rw [← τ.β.apply_symm_apply u]
      rw [kSmul_iota, MulEquiv.symm_apply_apply]
    simp only [Trans.form, hk]
    exact h3 c (τ.β.symm u) (τ.β.symm v)
  · intro c u v
    have hk : τ.β.symm (kSmul (τ.iota ι) c v) = kSmul ι c (τ.β.symm v) := by
      conv_lhs => rw [← τ.β.apply_symm_apply v]
      rw [kSmul_iota, MulEquiv.symm_apply_apply]
    simp only [Trans.form, hk]
    exact h4 c (τ.β.symm u) (τ.β.symm v)
  · intro u v
    simp only [Trans.form]
    exact h5 (τ.β.symm u) (τ.β.symm v)
  · intro u hu
    have hu' : τ.β.symm u ≠ 1 := by
      intro hh
      apply hu
      rw [← τ.β.apply_symm_apply u, hh, map_one]
    obtain ⟨w, hw⟩ := h6 (τ.β.symm u) hu'
    exact ⟨τ.β w, by simpa only [Trans.form, MulEquiv.symm_apply_apply] using hw⟩

theorem isIsoPoint_toV {K : Type*} [Field K] {ι : K →+* AddMonoid.End (Additive V')}
    {f : V' → V' → K} {P : Subgroup V'} :
    IsIsoPoint (τ.iota ι) (τ.form f) (τ.toV P) ↔ IsIsoPoint ι f P := by
  constructor
  · rintro ⟨v, hv, hf, hP⟩
    refine ⟨τ.β.symm v, ?_, ?_, ?_⟩
    · intro h
      apply hv
      rw [← τ.β.apply_symm_apply v, h, map_one]
    · have := hf
      rwa [Trans.form] at this
    · apply toV_inj τ
      have hk := kLine_iota τ ι (τ.β.symm v)
      simp only [MulEquiv.apply_symm_apply] at hk
      rw [hP]
      exact hk
  · rintro ⟨v, hv, hf, hP⟩
    refine ⟨τ.β v, ?_, ?_, ?_⟩
    · intro h
      apply hv
      exact τ.β.injective (by rw [h, map_one])
    · rw [form_apply]; exact hf
    · rw [hP, kLine_iota]

end Trans

end CFSG.Quasithin.AppendixH.H12
