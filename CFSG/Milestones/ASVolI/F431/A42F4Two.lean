module

public import CFSG.Milestones.ASVolI.F431.A42TitsC
public import CFSG.Milestones.ASVolI.F431.F4Two
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocDatum
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F431.TwoF4

@[expose] def burnsideF4m_A42Rest''' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .D4tw ∧ f < 2) ∨ (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f < 2)) →
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε

section F4Two

set_option linter.unusedSectionVars false


theorem burnsideF4m_pCore_titsN_le : pCoreOf 2 titsN ≤ pCoreOf 2 twoF4N := by
  have hmapN : titsN.map (MulAut.conj tπ).toMonoidHom = titsN := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp tπ_norm_N n).mp hn
    · intro hy
      refine ⟨tπ⁻¹ * y * tπ, ?_, ?_⟩
      · apply (Subgroup.mem_normalizer_iff.mp tπ_norm_N _).mpr
        have e : tπ * (tπ⁻¹ * y * tπ) * tπ⁻¹ = y := by group
        rw [e]
        exact hy
      · show tπ * (tπ⁻¹ * y * tπ) * tπ⁻¹ = y
        group
  have hπ : tπ ∈ Subgroup.normalizer
      ((pCoreOf 2 titsN : Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) := by
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have h := CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective (MulAut.conj tπ).toMonoidHom
      (MulAut.conj tπ).injective titsN
    rw [hmapN] at h
    show tπ * y * tπ⁻¹ ∈ pCoreOf 2 titsN
    rw [h]
    exact ⟨y, hy, rfl⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 titsN).trans le_extSub) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 titsN)
  intro x hx
  rcases hx with hx | hx
  · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 titsN hx
  · have e : x = (x * tπ⁻¹) * tπ := by group
    rw [e]
    exact mul_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 titsN hx) hπ

theorem burnsideF4m_tM_mem_O2N : tM ∈ pCoreOf 2 twoF4M2 := by
  have hp : IsPGroup 2 titsK := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 10) (by rw [titsQK_facts.2.2.2]; norm_num)
  have hK : titsK ≤ pCoreOf 2 titsN :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 titsK_le_titsN titsK_normal_N hp
  have ht : (tM : Equiv.Perm (Fin 1755)) ∈ pCoreOf 2 twoF4N :=
    burnsideF4m_pCore_titsN_le (hK burnsideF4m_tEl_mem_titsK)
  have hmap : twoF4M2.map twoF4M.subtype = twoF4N := by
    show (twoF4N.subgroupOf twoF4M).map twoF4M.subtype = twoF4N
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr CFSG.Quasithin.RuType.J47.twoF4N_le_M
  have h := CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective twoF4M.subtype
    twoF4M.subtype_injective twoF4M2
  rw [hmap] at h
  rw [h] at ht
  obtain ⟨y, hy, hye⟩ := ht
  have hyt : y = tM := Subtype.ext hye
  rw [← hyt]
  exact hy

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_A42_F4Two (hyp : HypF_4_31 .F4tw f Gp M₁ M₂ β ε z) (hf : f < 3) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .F4tw Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  obtain ⟨hGp, Ξ, h1, h2⟩ := burnsideF4m_F4Two_xi hyp.amalgam hf
  obtain ⟨zb, hzb, hΞz, hbz⟩ := burnsideF4m_F4Two_zbar hyp hGp Ξ h1
  have hz := hyp.z_mem.1 (by decide)
  rw [burnsideF4j_Z1_eq hyp] at hz
  obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
  have hxzb : x = zb :=
    congrArg Subtype.val (burnsideF4j_bOne_injective hyp (hxz.trans hbz.symm))
  subst hxzb
  obtain ⟨hC, hr1, hr2, -⟩ := burnsideF4m_comp_data hyp Ξ h1 h2
  set b1 := (burnsideF4d_bOne β ε).comp (burnsideF4m_psi Ξ h1) with hb1
  set b2 := (burnsideF4d_bTwo β ε).comp (burnsideF4m_psi Ξ h2) with hb2
  have hz₀ : zM ∈ twoF4M1 := by
    rw [← hΞz]
    exact (h1 x).2 hx1
  have hφz : amalgamMap b1 b2 zM = z := by
    rw [amalgamMap_of_mem₁ _ _ hz₀, ← hxz]
    show burnsideF4d_bOne β ε (burnsideF4m_psi Ξ h1 ⟨_, hz₀⟩) = _
    congr 1
    apply Subtype.ext
    rw [burnsideF4m_psi_apply]
    show Ξ.symm zM = x
    rw [← hΞz, MulEquiv.symm_apply_apply]
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 zM} : Set M) ≤ b1.range := by
    rw [hφz, hr1]
    exact hyp.hb
  have hnc := burnsideF4m_lieI_hnc hyp Ξ h1 h2 twoF4_F431LieI hx1 hΞz hxz (r := 3)
    (by rw [card_twoF4M1]; decide) three_dvd_card_cent_t
  have h442 := loc442 twoF4_Loc442Datum hC hb hnc
  have htN : tM ∈ twoF4M2 := twoF4_F431LieI.T_le₂ twoF4_F431LieI.t_mem
  have hθt : Ξ (Ξ.symm tM) = tM := Ξ.apply_symm_apply _
  have ht : Ξ.symm tM ∈ M₂ := (h2 _).1 (by rw [hθt]; exact htN)
  have hφt : amalgamMap b1 b2 tM = epsG β ε (f2 (c := β) ⟨Ξ.symm tM, ht⟩) := by
    rw [amalgamMap_of_mem₂ _ _ hC.agree htN]
    show burnsideF4d_bTwo β ε (burnsideF4m_psi Ξ h2 ⟨_, htN⟩) = _
    have hpsi : burnsideF4m_psi Ξ h2 ⟨_, htN⟩ = ⟨Ξ.symm tM, ht⟩ :=
      Subtype.ext (by rw [burnsideF4m_psi_apply])
    rw [hpsi]
    rfl
  refine ⟨⟨Ξ.symm tM, ht⟩, ?_, ?_, ?_⟩
  ·
    have hmap : (Gp ⊓ M₂).map Ξ.toMonoidHom = twoF4M2 := by
      ext y
      constructor
      · rintro ⟨m, ⟨-, hm⟩, rfl⟩
        exact (h2 m).2 hm
      · intro hy
        refine ⟨Ξ.symm y, ⟨by rw [hGp]; exact Subgroup.mem_top _,
          (h2 _).1 (by rwa [MulEquiv.apply_symm_apply])⟩, ?_⟩
        exact Ξ.apply_symm_apply y
    have h := CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Ξ.toMonoidHom Ξ.injective
      (Gp ⊓ M₂)
    rw [hmap] at h
    have htK := burnsideF4m_tM_mem_O2N
    rw [h] at htK
    obtain ⟨y, hy, hey⟩ := htK
    have hey' : Ξ y = tM := hey
    show Ξ.symm tM ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [← hey', MulEquiv.symm_apply_apply]
    exact hy
  ·
    have h27 := as_F_4_27 .F4tw f E Gp M₁ M₂ hyp.amalgam hGp
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
    have hto := twoF4_F431LieI.ht
    have htD1 : Ξ.symm tM ≠ 1 := by
      intro h
      have h' : tM = 1 := by rw [← hθt, h, map_one]
      rw [h', orderOf_one] at hto
      exact absurd hto (by decide)
    have htD2 : Ξ.symm tM * Ξ.symm tM = 1 := by
      apply Ξ.injective
      rw [map_mul, hθt, map_one]
      have := pow_orderOf_eq_one tM
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
      have hc := Ξ.toMonoidHom.map_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hcl)
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hc
      rw [hΞz] at hc
      exact twoF4_F431LieI.not_conj hc.symm
    · exact ⟨f, hyp.amalgam.toHypF_4_4g.chart, hχm, htS⟩
  · rw [← hφt, ← hr2]
    exact h442

theorem burnsideF4m_A42Rest''_of''' (hrest : burnsideF4m_A42Rest''') : burnsideF4m_A42Rest'' := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hodd hk
  rcases hk with hk | hk | ⟨rfl, hf⟩ | hk | hk
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inl hk)
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inl hk))
  · exact burnsideF4m_A42_F4Two hyp hf
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inl hk)))
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inr hk)))

end F4Two

end CFSG.ASVolI
