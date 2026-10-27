module

public import CFSG.Quasithin.AppendixH.H12.TransModule

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

namespace Trans

variable {Γ : Type*} [Group Γ] {L' : Subgroup Γ} {G : Type*} [Group G] {L : Subgroup G}
  {V' V : Type*} [CommGroup V'] [CommGroup V] {ρ' : Γ →* MulAut V'} {ρ : G →* MulAut V}
  (τ : Trans L' L ρ' ρ)

private theorem h12pCoreOf_le {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

private theorem h12exists_lift {g : G} (hg : g ∈ L) : ∃ g' : ↥L', ((τ.φ g' : ↥L) : G) = g := by
  have hg' : g ∈ τ.toG L' := by rwa [toG_top τ]
  obtain ⟨h, hL, _, hgh⟩ := (mem_toG τ (X := L') (g := g)).mp hg'
  exact ⟨⟨h, hL⟩, hgh⟩

private theorem h12beta_symm_rho_phi (g' : ↥L') (v : V) :
    τ.β.symm (ρ (τ.φ g' : G) v) = ρ' (g' : Γ) (τ.β.symm v) := by
  have h := congrArg τ.β.symm (τ.compat g' (τ.β.symm v))
  simpa using h

private theorem h12rho_phi_eq_congr (g' : ↥L') :
    ρ (τ.φ g' : G) = MulAut.congr τ.β (ρ' (g' : Γ)) := by
  ext v
  show ρ (τ.φ g' : G) v = τ.β (ρ' (g' : Γ) (τ.β.symm v))
  conv_lhs => rw [← τ.β.apply_symm_apply v]
  rw [τ.compat]

theorem formClause_toG {K : Type*} [Field K] {ι : K →+* AddMonoid.End (Additive V')}
    {f : V' → V' → K} (h : FormClause ρ' L' ι f) : FormClause ρ L (τ.iota ι) (τ.form f) := by
  unfold FormClause at h ⊢
  obtain ⟨hunit, hact, hq⟩ := h
  obtain ⟨q', hquad, hqq, hqf, hqact⟩ := hq
  refine ⟨isUnitaryForm_iota τ hunit, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', rfl⟩ := h12exists_lift τ hg
    refine ⟨?_, ?_⟩
    · intro c v
      have hv : kSmul (τ.iota ι) c v = τ.β (kSmul ι c (τ.β.symm v)) := by
        rw [← kSmul_iota, MulEquiv.apply_symm_apply]
      rw [hv, τ.compat, (hact (g' : Γ) g'.2).1 c (τ.β.symm v),
        ← kSmul_iota τ ι c (ρ' (g' : Γ) (τ.β.symm v)),
        ← h12beta_symm_rho_phi τ g' v, MulEquiv.apply_symm_apply]
    · intro u v
      show f (τ.β.symm (ρ (τ.φ g' : G) u)) (τ.β.symm (ρ (τ.φ g' : G) v)) =
        f (τ.β.symm u) (τ.β.symm v)
      rw [h12beta_symm_rho_phi τ g' u, h12beta_symm_rho_phi τ g' v]
      exact (hact (g' : Γ) g'.2).2 (τ.β.symm u) (τ.β.symm v)
  · refine ⟨fun u => q' (τ.β.symm u), ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa using hquad.1
      · intro x x' y
        have := hquad.2 (τ.β.symm x) (τ.β.symm x') (τ.β.symm y)
        simpa only [map_mul] using this
    · intro u
      simpa [Trans.form] using hqq (τ.β.symm u)
    · intro u
      simpa [Trans.form] using hqf (τ.β.symm u)
    · intro g hg u
      obtain ⟨g', rfl⟩ := h12exists_lift τ hg
      show q' (τ.β.symm (ρ (τ.φ g' : G) u)) = q' (τ.β.symm u)
      rw [h12beta_symm_rho_phi τ g' u]
      exact hqact (g' : Γ) g'.2 (τ.β.symm u)

theorem clause4_toG {T' M' N' : Subgroup Γ} (hT : T' ≤ L') (hM : M' ≤ L') (hN : N' ≤ L')
    (h : Clause4 L' T' M' N') : Clause4 L (τ.toG T') (τ.toG M') (τ.toG N') := by
  unfold Clause4 at h ⊢
  have hE : pCoreOf 2 M' ≤ L' := (h12pCoreOf_le 2 M').trans hM
  refine ⟨isMaximalIn_toG τ hM h.1, isMaximalIn_toG τ hN h.2.1,
    (toG_mono_iff τ hT hM).mpr h.2.2.1, (toG_mono_iff τ hT hN).mpr h.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact h.2.2.2.2.1 (toG_inj τ hM hN heq)
  · intro X hX hTX
    have hXL : X ≤ L := le_of_lt hX.1
    have hTX' : T' ≤ τ.fromG X :=
      (toG_mono_iff τ hT (fromG_le τ X)).mp (by rw [toG_fromG τ hXL]; exact hTX)
    rcases h.2.2.2.2.2.1 (τ.fromG X) (isMaximalIn_fromG τ hX) hTX' with hc | hc
    · left; rw [← toG_fromG τ hXL, hc]
    · right; rw [← toG_fromG τ hXL, hc]
  · refine ⟨?_, ?_, ?_⟩
    · rw [pCoreOf_toG τ 2 hM]
      exact isElemAbelian_toG τ hE h.2.2.2.2.2.2.1.1
    · rw [pCoreOf_toG τ 2 hM, card_toG τ hE]
      exact h.2.2.2.2.2.2.1.2.1
    · rw [pCoreOf_toG τ 2 hM]
      exact isExtHatOf_toG τ hM h.2.2.2.2.2.2.1.2.2
  · obtain ⟨X', hdirect, hX'ab, hX'card, hX'ext⟩ := h.2.2.2.2.2.2.2
    have hZ' : ((Subgroup.center ↥L').map L'.subtype) ≤ L' := Subgroup.map_subtype_le _
    have hX'le : X' ≤ L' := hdirect.1.trans hN
    have hid : IsIntDirect (τ.toG N') (τ.toG X')
        (τ.toG ((Subgroup.center ↥L').map L'.subtype)) :=
      isIntDirect_toG τ hN hX'le hZ' hdirect
    have hab : IsElemAbelian 2 (τ.toG (pCoreOf 2 X')) :=
      isElemAbelian_toG τ ((h12pCoreOf_le 2 X').trans hX'le) hX'ab
    have hcard : Nat.card ↥(τ.toG (pCoreOf 2 X')) = 16 := by
      rw [card_toG τ ((h12pCoreOf_le 2 X').trans hX'le)]; exact hX'card
    have hext : IsExtOf (τ.toG X') (τ.toG (pCoreOf 2 X')) (Equiv.Perm (Fin 5)) :=
      isExtOf_toG τ hX'le hX'ext
    refine ⟨τ.toG X', ?_, ?_, ?_, ?_⟩
    · rw [center_toG τ]; exact hid
    · rw [pCoreOf_toG τ 2 hX'le]; exact hab
    · rw [pCoreOf_toG τ 2 hX'le]; exact hcard
    · rw [pCoreOf_toG τ 2 hX'le]; exact hext

theorem clause5_toG {K : Type*} [Field K] {ι : K →+* AddMonoid.End (Additive V')}
    {f : V' → V' → K} {T' N' : Subgroup Γ} {V₁ : Subgroup V'} (hT : T' ≤ L') (hN : N' ≤ L')
    (h : Clause5 ρ' L' T' N' ι f V₁) :
    Clause5 ρ L (τ.toG T') (τ.toG N') (τ.iota ι) (τ.form f) (τ.toV V₁) := by
  unfold Clause5 at h ⊢
  refine ⟨(isIsoPoint_toV τ).mpr h.1, (forall_toG_forall_toV τ hT V₁).mpr h.2.1, ?_, ?_⟩
  · intro P hP hstab
    have hP' : IsIsoPoint ι f (P.map τ.β.symm.toMonoidHom) :=
      (isIsoPoint_toV τ).mp (by rw [toV_ofV τ P]; exact hP)
    have hstab' : ∀ t ∈ T', ∀ x ∈ P.map τ.β.symm.toMonoidHom,
        ρ' t x ∈ P.map τ.β.symm.toMonoidHom :=
      (forall_toG_forall_toV τ hT (P.map τ.β.symm.toMonoidHom)).mp (by rw [toV_ofV τ P]; exact hstab)
    calc P = τ.toV (P.map τ.β.symm.toMonoidHom) := (toV_ofV τ P).symm
      _ = τ.toV V₁ := by rw [h.2.2.1 _ hP' hstab']
  · calc ptStab ρ L (τ.toV V₁)
        = ptStab ρ (τ.toG L') (τ.toV V₁) := by rw [toG_top τ]
      _ = τ.toG (ptStab ρ' L' V₁) := ptStab_toG τ (le_refl L') V₁
      _ = τ.toG N' := by rw [h.2.2.2]

theorem clause6_toG {K : Type*} [Field K] {f : V' → V' → K} {M' : Subgroup Γ} (hM : M' ≤ L')
    (h : Clause6 ρ' L' M' f) : Clause6 ρ L (τ.toG M') (τ.form f) := by
  unfold Clause6 at h ⊢
  have hE : pCoreOf 2 M' ≤ L' := (h12pCoreOf_le 2 M').trans hM
  rw [pCoreOf_toG τ 2 hM]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fixV_toG τ hE, commV_toG τ hE, h.1]
  · intro u hu v hv
    rw [fixV_toG τ hE] at hu hv
    show f (τ.β.symm u) (τ.β.symm v) = 0
    exact h.2.1 _ ((mem_toV τ).mp hu) _ ((mem_toV τ).mp hv)
  · rw [fixV_toG τ hE, card_toV]; exact h.2.2.1
  · calc cenIn ρ L (fixV (Subgroup.map ρ (τ.toG (pCoreOf 2 M'))))
        = cenIn ρ (τ.toG L') (fixV (Subgroup.map ρ (τ.toG (pCoreOf 2 M')))) := by
            rw [toG_top τ]
      _ = cenIn ρ (τ.toG L') (τ.toV (fixV (Subgroup.map ρ' (pCoreOf 2 M')))) := by
            rw [fixV_toG τ hE]
      _ = τ.toG (cenIn ρ' L' (fixV (Subgroup.map ρ' (pCoreOf 2 M')))) :=
            cenIn_toG τ (le_refl L') _
      _ = τ.toG (pCoreOf 2 M') := by rw [h.2.2.2]

theorem clause78_toG {K : Type*} [Field K] {ι : K →+* AddMonoid.End (Additive V')}
    {f : V' → V' → K} {M' : Subgroup Γ} {V₁ V₂ : Subgroup V'} (hM : M' ≤ L')
    (h : Clause78 ρ' L' M' ι f V₁ V₂) :
    Clause78 ρ L (τ.toG M') (τ.iota ι) (τ.form f) (τ.toV V₁) (τ.toV V₂) := by
  unfold Clause78 at h ⊢
  have hE : pCoreOf 2 M' ≤ L' := (h12pCoreOf_le 2 M').trans hM
  rw [pCoreOf_toG τ 2 hM]
  refine ⟨(isIsoPoint_toV τ).mpr h.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fixV_toG τ hE]; exact (toV_mono_iff τ).mpr h.2.1
  · rw [fixV_toG τ hE]; exact (toV_mono_iff τ).mpr h.2.2.1
  · intro heq
    exact h.2.2.2.1 (toV_inj τ heq)
  · intro P hP hPfix
    have hP' : IsIsoPoint ι f (P.map τ.β.symm.toMonoidHom) :=
      (isIsoPoint_toV τ).mp (by rw [toV_ofV τ P]; exact hP)
    have hPfix' : P.map τ.β.symm.toMonoidHom ≤ fixV (Subgroup.map ρ' (pCoreOf 2 M')) :=
      (toV_mono_iff τ).mp (calc
        τ.toV (P.map τ.β.symm.toMonoidHom) = P := toV_ofV τ P
        _ ≤ fixV (Subgroup.map ρ (τ.toG (pCoreOf 2 M'))) := hPfix
        _ = τ.toV (fixV (Subgroup.map ρ' (pCoreOf 2 M'))) := by
              rw [fixV_toG τ hE])
    rcases h.2.2.2.2.1 _ hP' hPfix' with hc | hc
    · left
      simpa only [toV_ofV τ P] using
        (isConjPt_toG τ hM (P.map τ.β.symm.toMonoidHom) V₁).mpr hc
    · right
      simpa only [toV_ofV τ P] using
        (isConjPt_toG τ hM (P.map τ.β.symm.toMonoidHom) V₂).mpr hc
  · intro hc
    exact h.2.2.2.2.2.1 ((isConjPt_toG τ hM V₁ V₂).mp hc)
  · calc ptStab ρ (τ.toG M') (τ.toV V₂)
        = τ.toG (ptStab ρ' M' V₂) := ptStab_toG τ hM V₂
      _ = τ.toG (ptStab ρ' L' V₂) := by rw [h.2.2.2.2.2.2.1]
      _ = ptStab ρ L (τ.toV V₂) := by
            rw [← ptStab_toG τ (le_refl L') V₂, toG_top τ]
  · obtain ⟨X', hdirect, hX'ab, hX'card, hX'ext⟩ := h.2.2.2.2.2.2.2.1
    have hN' : ptStab ρ' L' V₂ ≤ L' := by
      show L' ⊓ _ ≤ L'
      exact inf_le_left
    have hZ' : ((Subgroup.center ↥L').map L'.subtype) ≤ L' := Subgroup.map_subtype_le _
    have hX'le : X' ≤ L' := hdirect.1.trans hN'
    have hid : IsIntDirect (τ.toG (ptStab ρ' L' V₂)) (τ.toG X')
        (τ.toG ((Subgroup.center ↥L').map L'.subtype)) :=
      isIntDirect_toG τ hN' hX'le hZ' hdirect
    have hab : IsElemAbelian 2 (τ.toG (pCoreOf 2 X')) :=
      isElemAbelian_toG τ ((h12pCoreOf_le 2 X').trans hX'le) hX'ab
    have hcard : Nat.card ↥(τ.toG (pCoreOf 2 X')) = 16 := by
      rw [card_toG τ ((h12pCoreOf_le 2 X').trans hX'le)]; exact hX'card
    have hext : IsExtOf (τ.toG X') (τ.toG (pCoreOf 2 X')) ↥(alternatingGroup (Fin 5)) :=
      isExtOf_toG τ hX'le hX'ext
    refine ⟨τ.toG X', ?_, ?_, ?_, ?_⟩
    · rw [← center_toG τ, ← ptStab_toG τ (le_refl L') V₂, toG_top τ] at hid
      exact hid
    · rw [pCoreOf_toG τ 2 hX'le]; exact hab
    · rw [pCoreOf_toG τ 2 hX'le]; exact hcard
    · rw [pCoreOf_toG τ 2 hX'le]; exact hext
  · intro P hP
    have hP' : IsIsoPoint ι f (P.map τ.β.symm.toMonoidHom) :=
      (isIsoPoint_toV τ).mp (by rw [toV_ofV τ P]; exact hP)
    rcases h.2.2.2.2.2.2.2.2.1 _ hP' with hc | hc
    · left
      simpa only [toV_ofV τ P, toG_top τ] using
        (isConjPt_toG τ (le_refl L') (P.map τ.β.symm.toMonoidHom) V₁).mpr hc
    · right
      simpa only [toV_ofV τ P, toG_top τ] using
        (isConjPt_toG τ (le_refl L') (P.map τ.β.symm.toMonoidHom) V₂).mpr hc
  · intro hc
    have hc' : IsConjPt ρ (τ.toG L') (τ.toV V₁) (τ.toV V₂) :=
      Eq.mp (congrArg (fun X : Subgroup G => IsConjPt ρ X (τ.toV V₁) (τ.toV V₂))
        (toG_top τ).symm) hc
    exact h.2.2.2.2.2.2.2.2.2.1 ((isConjPt_toG τ (le_refl L') V₁ V₂).mp hc')
  · obtain ⟨t', ht', hord', hcomm'⟩ := h.2.2.2.2.2.2.2.2.2.2
    have ht'L : t' ∈ L' := (h12pCoreOf_le 2 M').trans hM ht'
    have hX'zp : Subgroup.zpowers t' ≤ L' := Subgroup.zpowers_le.mpr ht'L
    have hmap : Subgroup.map ρ (τ.toG (Subgroup.zpowers t')) =
        Subgroup.zpowers (ρ ((τ.φ ⟨t', ht'L⟩ : ↥L) : G)) := by
      rw [map_toG_rho τ hX'zp, MonoidHom.map_zpowers ρ' t',
        MonoidHom.map_zpowers (MulAut.congr τ.β).toMonoidHom (ρ' t')]
      exact congrArg Subgroup.zpowers (h12rho_phi_eq_congr τ ⟨t', ht'L⟩).symm
    refine ⟨((τ.φ ⟨t', ht'L⟩ : ↥L) : G), ?_, ?_, ?_⟩
    · exact (mem_toG τ (X := pCoreOf 2 M')).mpr ⟨t', ht'L, ht', rfl⟩
    · have h2 : orderOf (τ.φ ⟨t', ht'L⟩) = orderOf (⟨t', ht'L⟩ : ↥L') :=
        orderOf_injective τ.φ.toMonoidHom τ.φ.injective ⟨t', ht'L⟩
      rw [Subgroup.orderOf_coe, h2, ← Subgroup.orderOf_coe]
      exact hord'
    · calc commV (Subgroup.zpowers (ρ ((τ.φ ⟨t', ht'L⟩ : ↥L) : G)))
          = commV (Subgroup.map ρ (τ.toG (Subgroup.zpowers t'))) := by rw [hmap]
        _ = τ.toV (commV (Subgroup.map ρ' (Subgroup.zpowers t'))) := commV_toG τ hX'zp
        _ = τ.toV (V₁ ⊔ V₂) := by rw [MonoidHom.map_zpowers, hcomm']
        _ = τ.toV V₁ ⊔ τ.toV V₂ := toV_sup τ V₁ V₂

end Trans

end CFSG.Quasithin.AppendixH.H12
