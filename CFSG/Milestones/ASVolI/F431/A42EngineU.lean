module

public import CFSG.Milestones.ASVolI.F431.A42Engine
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocCore
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocV

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section EngineU

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_A42_engineU (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hκ : κ = .U4 ∨ κ = .U5)
    (hodd : Odd Gp.index) (hZ1 : burnsideF4m_Core1 Gp M₁)
    {C : Type} [Group C] {U P P' : Subgroup C} {z₀ t₀ : C} {V4 V Uc R K : Subgroup C}
    (S1 : Lift.StdTwo C U P P' z₀ t₀) (SV : Un.UnStdV C U P P' z₀ t₀ V4)
    (SL : Un.UnStdLoc C U z₀ t₀ V Uc R K)
    (hYam : IsYAmalgamPair U P P')
    (habove : ∀ B : Subgroup C, Subgroup.normalizer (U : Set C) ≤ B → B ≠ ⊤ → B ≤ P ∨ B ≤ P')
    (ψ : C ≃* ↥Gp) (hP : M₁.subgroupOf Gp = P.map ψ.toMonoidHom)
    (hP' : M₂.subgroupOf Gp = P'.map ψ.toMonoidHom)
    (hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2) :
    (∀ ht : ((ψ t₀ : ↥Gp) : E) ∈ M₂,
      Subgroup.centralizer ({epsG β ε (f2 (c := β) ⟨((ψ t₀ : ↥Gp) : E), ht⟩)} : Set M) ≤
        MiTwo β ε) ∧
    ∃ (K' : Type) (_ : Group K') (_ : Finite K') (θ : E ≃* K') (N1 N2 : Subgroup K')
      (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂)
      (T : Subgroup K') (I : Finset K') (z₀' : K'), F431LieK T N1 N2 I z₀' ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
          (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j) := by
  classical
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hyam : IsYAmalgamPair (U.map ψ.toMonoidHom) (M₁.subgroupOf Gp) (M₂.subgroupOf Gp) := by
    rw [hP, hP']
    exact CFSG.Quasithin.IsYAmalgamPair.map ψ hYam
  have hgen := burnsideF4m_hgen hyp.amalgam.toHypF_4_4g hyam
  have hcen := burnsideF4m_center_Gp hyp.amalgam.toHypF_4_4g
  have hodd' := burnsideF4m_not_two_dvd hyp.amalgam.toHypF_4_4g hyam hgen hcen hodd
  set A := (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).toLieAmalgamExt with hA
  have hU : A.TD.map ψ.symm.toMonoidHom = U := burnsideF4m_A42_map_symm_map ψ U
  have hQP : A.P1.map ψ.symm.toMonoidHom = P := by
    show (M₁.subgroupOf Gp).map ψ.symm.toMonoidHom = P
    rw [hP]
    exact burnsideF4m_A42_map_symm_map ψ P
  have hQP' : A.P2.map ψ.symm.toMonoidHom = P' := by
    show (M₂.subgroupOf Gp).map ψ.symm.toMonoidHom = P'
    rw [hP']
    exact burnsideF4m_A42_map_symm_map ψ P'
  have H := Lift.twoClassD_of_std A ψ.symm S1 (Or.inl ⟨rfl, rfl⟩) hQP hQP' hU
  have hinj : Function.Injective (MulAut.conj : ↥Gp →* MulAut ↥Gp) :=
    F45.conj_injective_of_center hcen
  have habove' := Lift.above_of_std A ψ.symm habove hQP hQP' hU
  have hag : ∀ E' : Subgroup ↥A.K, IsAGMember (A.TD.map (Lift.iK A hgen)) E' →
      Subgroup.normalizer (E' : Set ↥A.K) ≤ A.Mb1 ∨
        Subgroup.normalizer (E' : Set ↥A.K) ≤ A.Mb2 := by
    intro E' hE'
    have e : Lift.iK A hgen = AG.innK A hgen := MonoidHom.ext fun _ => rfl
    rw [e] at hE'
    exact AG.ag_of_borelTits A hinj hgen hBT habove' hE'
  have LK := Lift.f431LieK_of_twoClassD A hgen hcen hodd' H hag
  have hLie := Un.unLoc442Lie_of_std (A := A) (hgen := hgen) hcen SL hU
  have hnc : ¬ IsConj (Un.lamK A hgen ψ.symm z₀) (Un.lamK A hgen ψ.symm t₀) :=
    Lift.not_isConj_iK A hgen hcen H.noconj
  have hzt : Un.lamK A hgen ψ.symm z₀ * Un.lamK A hgen ψ.symm t₀ =
      Un.lamK A hgen ψ.symm t₀ * Un.lamK A hgen ψ.symm z₀ := by
    rw [← map_mul, ← map_mul, SL.comm]
  have hTD : A.TD = U.map ψ.symm.symm.toMonoidHom := (Lift.map_symm_eq_of_map_eq ψ.symm hU).symm
  have hcent : (Subgroup.centralizer ({t₀} : Set C)).map ψ.symm.symm.toMonoidHom =
      Subgroup.centralizer ({ψ.symm.symm t₀} : Set ↥Gp) :=
    Lift.map_centralizer_singleton ψ.symm.symm t₀
  have hsyl0 : IsSylowTwoOf (A.TD ⊓ Subgroup.centralizer ({ψ.symm.symm t₀} : Set ↥Gp))
      (Subgroup.centralizer ({ψ.symm.symm t₀} : Set ↥Gp)) := by
    have := Lift.isSylowTwoOf_map_inj ψ.symm.symm.toMonoidHom ψ.symm.symm.injective SL.sylow_t
    rwa [Subgroup.map_inf _ _ _ ψ.symm.symm.injective, ← hTD, hcent] at this
  have hSylt := Lift.sylow_cent_K A hgen hcen hodd' hsyl0
  have hV4T := Un.lamK_V4_le A hgen ψ.symm SV hU
  have hV4ab := Un.lamK_V4_ab A hgen ψ.symm SV
  have hV4sq := Un.lamK_V4_sq A hgen ψ.symm SV
  have hV4u := Un.lamK_V4_unique A hgen hcen ψ.symm SV hU
  have hzV4 : Un.lamK A hgen ψ.symm z₀ ∈ V4.map (Un.lamK A hgen ψ.symm) := ⟨z₀, SV.V4_zt.1, rfl⟩
  have htV4 : Un.lamK A hgen ψ.symm t₀ ∈ V4.map (Un.lamK A hgen ψ.symm) := ⟨t₀, SV.V4_zt.2, rfl⟩
  have hI : ({Lift.iK A hgen (ψ.symm.symm z₀), Lift.iK A hgen (ψ.symm.symm t₀)} : Finset ↥A.K) =
      {Un.lamK A hgen ψ.symm z₀, Un.lamK A hgen ψ.symm t₀} := rfl
  have hzZ := Un.lamK_z_mem_centerOf_perfectCore A hgen hcen ψ.symm hodd'
    (Lift.Mb1_inf_range A hgen) SV hQP
  have hV4e := Un.lamK_V4_eq A hgen hcen ψ.symm hodd' SV (Lift.Mb2_inf_range A hgen) hQP'
  have cz := Lift.cent_le_Mb1 A hgen hcen
    ((Lift.centralizer_le_transport ψ.symm hQP z₀).mpr SV.cz) H.aut_z
  have ct := Lift.cent_le_Mb2 A hgen hcen
    ((Lift.centralizer_le_transport ψ.symm hQP' t₀).mpr SV.ct) H.aut_t
  obtain ⟨θ, h1, h2, hθ⟩ := burnsideF4m_A42_exists_theta hyp.amalgam hyam
  haveI : Finite ↥A.K := Finite.of_equiv E θ.toEquiv
  obtain ⟨hC, hr1, hr2, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hL3 : κ ≠ .L3 := by rcases hκ with rfl | rfl <;> decide
  have hyp1 : ∀ w ∈ centerOf (perfectCore (MiOne β ε)), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set M) ≤ MiOne β ε :=
    fun w hw hw2 => burnsideF4m_cent_MiOne hyp hL3 hZ1 hw hw2
  have hQ2 : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) := by
    rw [CFSG.Quasithin.H13.F431.pCoreOf_eq_inf_of_odd M₂ hodd, inf_comm]
  have hnorm : Subgroup.normalizer ((centerOf (pCoreOf 2 (MiTwo β ε)) : Subgroup M) : Set M) =
      MiTwo β ε := by
    rw [burnsideF4m_centerOf_pCore_MiTwo hyp hQ2]
    exact (hyp.ha (Or.inr hκ)).2
  have SG : Un.UnGSetup A.Mb1 A.Mb2 ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
      ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (MiOne β ε) (MiTwo β ε) :=
    ⟨hC, hr1, hr2, hyp1, hnorm⟩
  obtain ⟨hnf, -, hbt⟩ := Un.un_local_core LK SG hI hzt cz ct hSylt hzZ hV4T hV4ab hV4sq hV4e
    hV4u hzV4 htV4 hnc hLie
  refine ⟨fun ht => ?_, ↥A.K, inferInstance, inferInstance, θ, A.Mb1, A.Mb2, h1, h2, _, _, _, LK,
    Lift.hnfI_of_hnf hnf⟩
  have hiK : Lift.iK A hgen (ψ t₀) = θ ((ψ t₀ : ↥Gp) : E) := by
    apply Subtype.ext
    rw [Lift.iK_coe, hθ]
    ext x
    rw [burnsideF4d_rho_apply, MulAut.conj_apply]
    rfl
  have hmem2 : Lift.iK A hgen (ψ t₀) ∈ A.Mb2 := by
    rw [hiK]
    exact (h2 _).2 ht
  have hpsi : burnsideF4m_psi θ h2 ⟨Lift.iK A hgen (ψ t₀), hmem2⟩ =
      ⟨((ψ t₀ : ↥Gp) : E), ht⟩ := by
    apply Subtype.ext
    rw [burnsideF4m_psi_apply]
    show θ.symm (Lift.iK A hgen (ψ t₀)) = ((ψ t₀ : ↥Gp) : E)
    rw [hiK, MulEquiv.symm_apply_apply]
  have e : amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
      ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (Lift.iK A hgen (ψ t₀)) =
      epsG β ε (f2 (c := β) ⟨((ψ t₀ : ↥Gp) : E), ht⟩) := by
    rw [amalgamMap_of_mem₂ _ _ hC.agree hmem2]
    show burnsideF4d_bTwo β ε (burnsideF4m_psi θ h2 ⟨Lift.iK A hgen (ψ t₀), hmem2⟩) = _
    rw [hpsi]
    rfl
  rw [← e]
  exact hbt

end EngineU

end CFSG.ASVolI
