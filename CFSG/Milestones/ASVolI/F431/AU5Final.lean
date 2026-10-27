module

public import CFSG.Milestones.ASVolI.F431.A42Final
public import CFSG.Milestones.ASVolI.F431.AU5Syl
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ClassicalGroups.UnitaryFlag

@[expose] def burnsideF4m_A42Rest' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .D4tw ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨ κ = .Tits ∨
      (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f < 2)) →
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε

@[expose] def burnsideF4m_A35Rest' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .D4tw ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨ κ = .Tits ∨
      (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f < 2)) →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

section U5

set_option linter.unusedSectionVars false


theorem burnsideF4m_A42_U5gen {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .U5 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) (hodd : Odd Gp.index)
    (hZ1 : burnsideF4m_Core1 Gp M₁) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .U5 Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε) ∧
    ∃ (K' : Type) (_ : Group K') (_ : Finite K') (θ : E ≃* K') (N1 N2 : Subgroup K')
      (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂)
      (T : Subgroup K') (I : Finset K') (z₀' : K'), F431LieK T N1 N2 I z₀' ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
          (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j) := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp.amalgam
  have h27 := as_F_4_27 .U5 f ↥Gp ⊤ _ _ hyp' rfl
  dsimp only at h27
  obtain ⟨hχm, -, -, h3, h4, -⟩ := h27
  obtain ⟨-, ⟨C, ⟨-, -⟩, hCu⟩, hls, hliff, -⟩ := h3 ⟨by decide, by decide, by decide⟩
  have h4' := (h4 (by decide)).1
  have hM1' : (Gp ⊓ M₁).subgroupOf Gp = M₁.subgroupOf Gp := Subgroup.inf_subgroupOf_left M₁ Gp
  have hM2' : (Gp ⊓ M₂).subgroupOf Gp = M₂.subgroupOf Gp := Subgroup.inf_subgroupOf_left M₂ Gp
  obtain ⟨w, hwZ, hw1⟩ : ∃ w : ↥Gp, w ∈ ctr (oPPrime 2 (M₁.subgroupOf Gp)) ∧ w ≠ 1 := by
    have hz := hyp.z_mem.1 (by decide)
    rw [burnsideF4j_Z1_eq hyp] at hz
    obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
    have hmap : ctr (oPPrime 2 (Gp ⊓ M₁)) =
        (ctr (oPPrime 2 (M₁.subgroupOf Gp))).map Gp.subtype := by
      have e : (M₁.subgroupOf Gp).map Gp.subtype = Gp ⊓ M₁ := by
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      rw [← e, burnsideF4d_oPPrime_map _ Gp.subtype_injective,
        burnsideF4j_ctr_map _ Gp.subtype_injective]
    rw [hmap] at hxZ
    obtain ⟨w, hw, rfl⟩ := hxZ
    refine ⟨w, hw, fun h => hyp.z_inv.1 ?_⟩
    subst h
    rw [← hxz]
    have e : (⟨Gp.subtype 1, hx1⟩ : ↥M₁) = 1 := Subtype.ext (map_one Gp.subtype)
    rw [e, map_one]
  have hwZ' : w ∈ ctr (oPPrime 2 ((Gp ⊓ M₁).subgroupOf Gp)) := by
    rw [hM1']
    exact hwZ
  obtain ⟨hwRI, -, -, -⟩ := h4' w hwZ' hw1
  have hwL := hwRI (by decide)
  have hw2 : w * w = 1 := hwL.2.2.1
  obtain ⟨K, _, h, Ψ, hG1, hG2⟩ := burnsideF4m_U5_chart hyp.amalgam.toHypF_4_4g
  haveI : Finite (hypPSU h 2 1) := CFSG.RankThree.PartOne.U5K.Hyp.finite_hypPSU h
  have hsub : ∀ X : Subgroup (hypPSU h 2 1),
      (X.map (Gp.subtype.comp Ψ.toMonoidHom)).subgroupOf Gp = X.map Ψ.toMonoidHom := by
    intro X
    rw [← Subgroup.map_map]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have h1 : M₁.subgroupOf Gp = (H13.Sec53F.Unit.u5PtP h).map Ψ.toMonoidHom := by
    rw [← hM1', hG1, hsub]
  have h2 : M₂.subgroupOf Gp = (H13.Sec53F.Unit.u5LnP h).map Ψ.toMonoidHom := by
    rw [← hM2', hG2, hsub]
  have S1 := Un.stdTwo_Y (h := h) hf
  have SV := Un.unStdV_Y (h := h) hf
  have SL := Un.L5.burnsideF4m_unStdLoc_u5Y (h := h) hf
  have YS := H13.Sec53F.Unit.u5_yamStd (h := h)
  have hU0 := YS.sylow
  have hUP : hypProjUnitriangular h 2 1 ≤ H13.Sec53F.Unit.u5PtP h :=
    Subgroup.le_normalizer.trans YS.le₀
  have hmodel := burnsideF4g_lieModel_U5 hyp.amalgam.model
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel hmodel (by decide)
  obtain ⟨hcent, hlieK⟩ := burnsideF4m_A42_engineU hyp (Or.inr rfl) hodd hZ1 S1 SV SL
    YS.isYAmalgamPair YS.above Ψ h1 h2 hBT
  obtain ⟨g, -, hgz⟩ := burnsideF4m_A42_center_conj Ψ S1 hU0
    (by rw [h1]; exact Subgroup.map_mono hUP) hwZ hw1 hw2
  have ht₀1 : Un.t5Y h ≠ 1 := fun h0 => by
    have h3 := S1.t_two
    rw [h0, orderOf_one] at h3
    exact absurd h3 (by decide)
  have ht₀2 : Un.t5Y h * Un.t5Y h = 1 := by
    have := pow_orderOf_eq_one (Un.t5Y h)
    rwa [S1.t_two, pow_two] at this
  have htQ : Un.t5Y h ∈ pCoreOf 2 (H13.Sec53F.Unit.u5LnP h) := by
    have h := SV.V4_zt.2
    rw [SV.V4_eq] at h
    exact h.1
  have htP : Un.t5Y h ∈ H13.Sec53F.Unit.u5LnP h :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ htQ
  have ht : ((Ψ (Un.t5Y h) : ↥Gp) : E) ∈ M₂ := by
    have h' : Ψ (Un.t5Y h) ∈ M₂.subgroupOf Gp := by
      rw [h2]
      exact ⟨_, htP, rfl⟩
    exact h'
  have hψt1 : Ψ (Un.t5Y h) ≠ 1 := fun h' => ht₀1 (Ψ.injective (h'.trans (map_one Ψ).symm))
  have hψt2 : Ψ (Un.t5Y h) * Ψ (Un.t5Y h) = 1 := by rw [← map_mul, ht₀2, map_one]
  refine ⟨⟨⟨_, ht⟩, ?_, ?_, hcent ht⟩, hlieK⟩
  ·
    have hGM : Gp ⊓ M₂ = ((H13.Sec53F.Unit.u5LnP h).map Ψ.toMonoidHom).map Gp.subtype := by
      rw [← h2, Subgroup.subgroupOf_map_subtype, inf_comm]
    show ((Ψ (Un.t5Y h) : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Ψ.injective]
    exact ⟨Ψ (Un.t5Y h), ⟨Un.t5Y h, htQ, rfl⟩, rfl⟩
  ·
    have hmem : ∀ x : ↥Gp, x ≠ 1 → x * x = 1 →
        ConjClasses.mk x ∈ InvClasses ↥Gp := fun x hx1 hx2 =>
      ⟨x, ConjClasses.mem_carrier_mk, hx1, hx2⟩
    have hlongC : ∀ x : ↥Gp, x ≠ 1 → x * x = 1 →
        hyp'.toHypF_4_4g.chart.RootInvolution false x → ConjClasses.mk x = C := by
      intro x hx1 hx2 hxL
      obtain ⟨c, -, hc⟩ := ((hliff x hx1 hx2).mp hxL)
      refine hCu _ ⟨hmem x hx1 hx2, c * x * c⁻¹, ?_, hc⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨c, rfl⟩).symm
    rcases hls (Ψ (Un.t5Y h)) hψt1 hψt2 with htL | htS
    · exfalso
      have hcl := (hlongC _ hψt1 hψt2 htL).trans (hlongC w hw1 hw2 hwL).symm
      have h1c : IsConj (Ψ (Un.t5Y h)) w := ConjClasses.mk_eq_mk_iff_isConj.mp hcl
      have h3c : IsConj w (Ψ (Un.z5Y h)) := by
        refine isConj_iff.mpr ⟨(Ψ g)⁻¹, ?_⟩
        have e1 : w = Ψ (g * Un.z5Y h * g⁻¹) := by rw [hgz, MulEquiv.apply_symm_apply]
        rw [e1, map_mul, map_mul, map_inv]
        group
      have h4c := Ψ.symm.toMonoidHom.map_isConj (h1c.trans h3c)
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4c
      obtain ⟨c₀, hc₀⟩ := isConj_iff.mp h4c.symm
      exact S1.noconj (MulAut.conj c₀) (by rw [MulAut.conj_apply]; exact hc₀)
    · obtain ⟨chartE, hEm, hEri⟩ := burnsideF4m_A42_chart_extend_U5 _ hχm
      exact ⟨f, chartE, hEm, hEri true _ htS⟩

theorem burnsideF4m_A42Rest_of' (hrest : burnsideF4m_A42Rest') : burnsideF4m_A42Rest := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hodd hk
  rcases hk with hk | hk | hk | hk | hk | ⟨rfl, hf⟩
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inl hk)
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inl hk))
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inl hk)))
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))
  · by_cases hf2 : f < 2
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp hL43 hodd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf2⟩)))))
    · exact (burnsideF4m_A42_U5gen hyp (by omega) hodd
        (burnsideF4m_core12_U5 hyp.amalgam (by omega)).1).1

theorem burnsideF4m_A35Rest_of' (hrest : burnsideF4m_A35Rest') : burnsideF4m_A35Rest := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hk i j hi hj hi1 hj1 hi2 hj2
  rcases hk with hk | hk | hk | hk | hk | ⟨rfl, hf⟩
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inl hk) i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inl hk)) i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inl hk))) i j hi hj hi1 hj1 hi2
      hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr (Or.inl hk)))) i j hi hj hi1
      hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))) i j
      hi hj hi1 hj1 hi2 hj2
  · by_cases hf2 : f < 2
    · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf2⟩))))) i j hi hj hi1 hj1 hi2 hj2
    · have hU : ¬ ((GLKind.U5 = .U4 ∨ GLKind.U5 = .U5) ∧ f = 1) := by
        rintro ⟨-, hf1⟩
        omega
      obtain ⟨-, K', _, _, θ, N1, N2, h1, h2, T, I, z₀', L, hnf⟩ :=
        burnsideF4m_A42_U5gen hyp (by omega) (burnsideF4m_odd_index_nonU2 hyp hU)
          (burnsideF4m_core12_U5 hyp.amalgam (by omega)).1
      exact burnsideF4m_F_4_35_of_lieK hyp (by decide) (by decide) θ h1 h2 L hnf i j hi hj hi1 hi2
        hj1 hj2

end U5

end CFSG.ASVolI
