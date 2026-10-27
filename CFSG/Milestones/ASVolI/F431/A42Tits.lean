module

public import CFSG.Milestones.ASVolI.F431.A35Tits
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDDatum
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Sporadic.Schreier.Tits

@[expose] def burnsideF4m_A42Rest'' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .D4tw ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨
      (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f < 2)) →
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε

section Tits

set_option linter.unusedSectionVars false


variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_tits_zbar (hyp : HypF_4_31 .Tits f Gp M₁ M₂ β ε z) (θ : E ≃* ↥titsD)
    (h1 : ∀ e, θ e ∈ titsHD ↔ e ∈ M₁) :
    ∃ (x : E) (hx1 : x ∈ M₁), x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) ∧
      burnsideF4d_bOne β ε ⟨x, hx1⟩ = z ∧ θ x = CFSG.Quasithin.H13.F431.TitsD.zD := by
  have hGp : Gp = ⊤ := hyp.amalgam.canonical (Or.inr rfl)
  have hz := hyp.z_mem.1 (by decide)
  rw [burnsideF4j_Z1_eq hyp] at hz
  obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
  refine ⟨x, hx1, hxZ, hxz, ?_⟩
  have hbinj := burnsideF4j_bOne_injective hyp
  have hx2 : x * x = 1 := by
    have : burnsideF4d_bOne β ε (⟨x, hx1⟩ * ⟨x, hx1⟩) = burnsideF4d_bOne β ε 1 := by
      rw [map_mul, hxz, map_one]
      exact hyp.z_inv.2
    exact congrArg Subtype.val (hbinj this)
  have hxne : x ≠ 1 := by
    intro h
    apply hyp.z_inv.1
    rw [← hxz]
    have e : (⟨x, hx1⟩ : ↥M₁) = 1 := Subtype.ext h
    rw [e, map_one]
  have hmap : (Gp ⊓ M₁).map θ.toMonoidHom = titsHD := by
    ext y
    constructor
    · rintro ⟨m, ⟨-, hm⟩, rfl⟩
      exact (h1 m).2 hm
    · intro hy
      refine ⟨θ.symm y, ⟨by rw [hGp]; exact Subgroup.mem_top _,
        (h1 _).1 (by rwa [MulEquiv.apply_symm_apply])⟩, ?_⟩
      exact θ.apply_symm_apply y
  have hO : ∀ m ∈ M₁, m ∈ oPPrime 2 (Gp ⊓ M₁) := by
    intro m hm
    have h := burnsideF4d_oPPrime_map θ.toMonoidHom θ.injective 2 (Gp ⊓ M₁)
    rw [hmap, burnsideF4gF4TwoInv_titsD_oPPrime] at h
    have hθm : θ m ∈ titsHD := (h1 m).2 hm
    rw [h] at hθm
    obtain ⟨m', hm', he⟩ := hθm
    have he' : θ m' = θ m := he
    rw [θ.injective he'] at hm'
    exact hm'
  have hcent : ∀ m ∈ M₁, m * x = x * m := fun m hm =>
    (Subgroup.mem_centralizer_iff.mp hxZ.2) m (hO m hm)
  apply Subtype.ext
  have hxH : ((θ x : ↥titsD) : Equiv.Perm (Fin 1755)) ∈ titsH := (h1 x).2 hx1
  refine CFSG.Quasithin.H13.F431.TitsD.eq_titsZ_of_central hxH ?_ ?_ ?_
  · intro y hy
    have hyD : y ∈ titsD := titsH_le_titsD hy
    have hyHD : (⟨y, hyD⟩ : ↥titsD) ∈ titsHD := hy
    have hm : θ.symm ⟨y, hyD⟩ ∈ M₁ := (h1 _).1 (by rwa [MulEquiv.apply_symm_apply])
    have hc := congrArg θ (hcent _ hm)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at hc
    exact congrArg Subtype.val hc
  · have h := congrArg θ hx2
    rw [map_mul, map_one] at h
    exact congrArg Subtype.val h
  · intro h
    apply hxne
    apply θ.injective
    rw [map_one]
    exact Subtype.ext h

theorem burnsideF4m_A42_Tits_cent (hyp : HypF_4_31 .Tits f Gp M₁ M₂ β ε z) (θ : E ≃* ↥titsD)
    (h1 : ∀ e, θ e ∈ titsHD ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ titsND ↔ e ∈ M₂)
    (ht : θ.symm CFSG.Quasithin.H13.F431.TitsD.tD ∈ M₂) :
    Subgroup.centralizer ({epsG β ε (f2 (c := β) ⟨θ.symm CFSG.Quasithin.H13.F431.TitsD.tD, ht⟩)} :
      Set M) ≤ MiTwo β ε := by
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  obtain ⟨x, hx1, -, hxz, hθx⟩ := burnsideF4m_tits_zbar hyp θ h1
  obtain ⟨hC, hr1, hr2, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  set b1 := (burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1) with hb1
  set b2 := (burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2) with hb2
  have hz₀ : CFSG.Quasithin.H13.F431.TitsD.zD ∈ titsHD := by
    rw [← hθx]
    exact (h1 x).2 hx1
  have hφz : amalgamMap b1 b2 CFSG.Quasithin.H13.F431.TitsD.zD = z := by
    rw [amalgamMap_of_mem₁ _ _ hz₀, ← hxz]
    show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨_, hz₀⟩) = _
    congr 1
    apply Subtype.ext
    rw [burnsideF4m_psi_apply]
    show θ.symm CFSG.Quasithin.H13.F431.TitsD.zD = x
    rw [← hθx, MulEquiv.symm_apply_apply]
  have hb : Subgroup.centralizer
      ({amalgamMap b1 b2 CFSG.Quasithin.H13.F431.TitsD.zD} : Set M) ≤ b1.range := by
    rw [hφz, hr1]
    exact hyp.hb
  have hnc := burnsideF4m_lieI_hnc hyp θ h1 h2 CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI hx1
    hθx hxz (r := 3) (by rw [card_titsHD]; decide)
    CFSG.Quasithin.H13.F431.TitsD.three_dvd_card_cent_tD
  have h442 := loc442 CFSG.Quasithin.H13.F431.TitsD.titsD_Loc442Datum hC hb hnc
  have htN : CFSG.Quasithin.H13.F431.TitsD.tD ∈ titsND :=
    CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI.T_le₂
      CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI.t_mem
  have hφt : amalgamMap b1 b2 CFSG.Quasithin.H13.F431.TitsD.tD =
      epsG β ε (f2 (c := β) ⟨θ.symm CFSG.Quasithin.H13.F431.TitsD.tD, ht⟩) := by
    rw [amalgamMap_of_mem₂ _ _ hC.agree htN]
    show burnsideF4d_bTwo β ε (burnsideF4m_psi θ h2 ⟨_, htN⟩) = _
    have hpsi : burnsideF4m_psi θ h2 ⟨_, htN⟩ = ⟨θ.symm CFSG.Quasithin.H13.F431.TitsD.tD, ht⟩ :=
      Subtype.ext (by rw [burnsideF4m_psi_apply])
    rw [hpsi]
    rfl
  rw [← hφt, ← hr2]
  exact h442

theorem burnsideF4m_A42_Tits_of
    (htK : CFSG.Quasithin.H13.F431.TitsD.tD ∈ pCoreOf 2 titsND)
    (hyp : HypF_4_31 .Tits f Gp M₁ M₂ β ε z) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .Tits Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  classical
  haveI := hyp.amalgam.finite
  have hGp : Gp = ⊤ := hyp.amalgam.canonical (Or.inr rfl)
  obtain ⟨θ, h1, h2⟩ := burnsideF4m_tits_thetaD hyp.amalgam
  obtain ⟨x, hx1, hxZ, hxz, hθx⟩ := burnsideF4m_tits_zbar hyp θ h1
  have htN : CFSG.Quasithin.H13.F431.TitsD.tD ∈ titsND :=
    CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI.T_le₂
      CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI.t_mem
  have hθt : θ (θ.symm CFSG.Quasithin.H13.F431.TitsD.tD) = CFSG.Quasithin.H13.F431.TitsD.tD :=
    θ.apply_symm_apply _
  have ht : θ.symm CFSG.Quasithin.H13.F431.TitsD.tD ∈ M₂ := (h2 _).1 (by rw [hθt]; exact htN)
  refine ⟨⟨θ.symm CFSG.Quasithin.H13.F431.TitsD.tD, ht⟩, ?_, ?_,
    burnsideF4m_A42_Tits_cent hyp θ h1 h2 ht⟩
  ·
    have hmap : (Gp ⊓ M₂).map θ.toMonoidHom = titsND := by
      ext y
      constructor
      · rintro ⟨m, ⟨-, hm⟩, rfl⟩
        exact (h2 m).2 hm
      · intro hy
        refine ⟨θ.symm y, ⟨by rw [hGp]; exact Subgroup.mem_top _,
          (h2 _).1 (by rwa [MulEquiv.apply_symm_apply])⟩, ?_⟩
        exact θ.apply_symm_apply y
    have h := CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective θ.toMonoidHom θ.injective
      (Gp ⊓ M₂)
    rw [hmap] at h
    rw [h] at htK
    obtain ⟨y, hy, hey⟩ := htK
    have hey' : θ y = CFSG.Quasithin.H13.F431.TitsD.tD := hey
    show θ.symm CFSG.Quasithin.H13.F431.TitsD.tD ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [← hey', MulEquiv.symm_apply_apply]
    exact hy
  ·
    have h27 := as_F_4_27 .Tits f E Gp M₁ M₂ hyp.amalgam hGp
    dsimp only at h27
    obtain ⟨hχm, -, -, h3, h4, -⟩ := h27
    obtain ⟨-, ⟨C, ⟨-, -⟩, hCu⟩, hls, hliff, -⟩ := h3 ⟨by decide, by decide, by decide⟩
    have h4' := (h4 (by decide)).1
    have hxZ' : x ∈ ctr (oPPrime 2 M₁) := by
      have e : Gp ⊓ M₁ = M₁ := by rw [hGp, top_inf_eq]
      rw [← e]
      exact hxZ
    have hx1' : x ≠ 1 := by
      intro h
      apply hyp.z_inv.1
      rw [← hxz]
      have e : (⟨x, hx1⟩ : ↥M₁) = 1 := Subtype.ext h
      rw [e, map_one]
    have hxL := ((h4' x hxZ' hx1').1) (by decide)
    have hx2 : x * x = 1 := hxL.2.2.1
    have hto := CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI.ht
    have htD1 : θ.symm CFSG.Quasithin.H13.F431.TitsD.tD ≠ 1 := by
      intro h
      have h' : CFSG.Quasithin.H13.F431.TitsD.tD = 1 := by rw [← hθt, h, map_one]
      rw [h', orderOf_one] at hto
      exact absurd hto (by decide)
    have htD2 : θ.symm CFSG.Quasithin.H13.F431.TitsD.tD *
        θ.symm CFSG.Quasithin.H13.F431.TitsD.tD = 1 := by
      apply θ.injective
      rw [map_mul, hθt, map_one]
      have := pow_orderOf_eq_one CFSG.Quasithin.H13.F431.TitsD.tD
      rwa [hto, pow_two] at this
    have hmem : ∀ y : E, y ≠ 1 → y * y = 1 → ConjClasses.mk y ∈ InvClasses E :=
      fun y hy1 hy2 => ⟨y, ConjClasses.mem_carrier_mk, hy1, hy2⟩
    have hlongC : ∀ y : E, y ≠ 1 → y * y = 1 →
        hyp.amalgam.toHypF_4_4g.chart.RootInvolution false y → ConjClasses.mk y = C := by
      intro y hy1 hy2 hyL
      obtain ⟨c, -, hc⟩ := (hliff y hy1 hy2).mp hyL
      refine hCu _ ⟨hmem y hy1 hy2, c * y * c⁻¹, ?_, hc⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨c, rfl⟩).symm
    rcases hls _ htD1 htD2 with htL | htS
    · exfalso
      have hcl := (hlongC _ htD1 htD2 htL).trans (hlongC x hx1' hx2 hxL).symm
      have hc := θ.toMonoidHom.map_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hcl)
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hc
      rw [hθx] at hc
      exact CFSG.Quasithin.H13.F431.TitsD.not_conj_D hc.symm
    · exact ⟨f, hyp.amalgam.toHypF_4_4g.chart, hχm, htS⟩

theorem burnsideF4m_A42Rest'_of''_of_tD
    (htK : CFSG.Quasithin.H13.F431.TitsD.tD ∈ pCoreOf 2 titsND)
    (hrest : burnsideF4m_A42Rest'') : burnsideF4m_A42Rest' := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hodd hk
  rcases hk with hk | hk | hk | rfl | hk | hk
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inl hk)
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inl hk))
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inl hk)))
  · exact burnsideF4m_A42_Tits_of htK hyp
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inr (Or.inr hk))))

end Tits

end CFSG.ASVolI
