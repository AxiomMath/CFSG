module

public import CFSG.Milestones.ASVolI.F431.A42Engine

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open scoped commutatorElement

section Engine3

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_A42_engine3 (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3)
    (hodd : Odd Gp.index) (hZ1 : burnsideF4m_Core1 Gp M₁)
    {C : Type} [Group C] {U P P' : Subgroup C} {z₀ t₀ : C} {V L : Subgroup C}
    (S1 : Lift.StdTwo C U P P' z₀ t₀) (S2 : Lift.StdLoc C U z₀ t₀ V L)
    (S3 : Lift.StdOrient3 C P P' z₀ t₀)
    (hF3 : ∀ x y : MulAut C, ⁅x, y⁆ ∈ (MulAut.conj : C →* MulAut C).range)
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
  have HL := Lift.locD_of_std A ψ.symm S2 hU
  have HO := Lift.orientD3_of_std3 ψ.symm S3 hQP hQP'
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
  have LKloc := Lift.locK_of_dlevel A hgen hcen hodd' HL
  have hF3' := Lift.commutator_aut_mem_range_of_equiv ψ.symm hF3
  have hz3 := Lift.not_three_dvd_commutator_cent_iK A hgen hcen hF3' HO.F1
  have ht3 := Lift.three_dvd_commutator_cent_iK A hgen hcen HO.F2
  obtain ⟨θ, h1, h2, hθ⟩ := burnsideF4m_A42_exists_theta hyp.amalgam hyam
  haveI : Finite ↥A.K := Finite.of_equiv E θ.toEquiv
  obtain ⟨hC, hr1, hr2, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hyp1 : ∀ w ∈ centerOf (perfectCore (MiOne β ε)), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set M) ≤ MiOne β ε :=
    fun w hw hw2 => burnsideF4m_cent_MiOne hyp hL3 hZ1 hw hw2
  obtain ⟨hnf, -, hbt⟩ := Lift.local_core3 LK hC rfl hr1 hr2 hyp1
    (Lift.cent_le_Mb1 A hgen hcen HO.cz H.aut_z) (Lift.cent_le_Mb2 A hgen hcen HO.ct H.aut_t)
    (Lift.iK_mem_centerOf_perfectCore_Mb1 A hgen hcen hodd' HO.Zperf) hz3 ht3 LKloc
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

end Engine3

end CFSG.ASVolI
