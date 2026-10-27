module

public import CFSG.Milestones.ASVolI.F431.A42Engine

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.NF CFSG.Quasithin.Loc442Q

universe u

section Core

variable {Mb : Type u} [Group Mb] [Finite Mb] [DecidableEq Mb] {G : Type} [Group G] [Finite G]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t v nr na : Mb} {b1 : ↥M1 →* G} {b2 : ↥M2 →* G}
  {M1G : Subgroup G} {Q Z X Y : Subgroup Mb} {q n : ℕ}

theorem burnsideF4m_local_nf (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : I = {z, t}) (hrange1 : b1.range = M1G)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1G), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1G)
    (NF : NFK T Q Z X Y M1 M2 z v nr na q n) (Zperf : Z ≤ centerOf (perfectCore M1))
    (conj_tv : IsConj t v) :
    ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) := by
  have hz1 : z ∈ M1 := NF.z_mem₁
  have hcent1 : ∀ (w : Mb) (hw : w ∈ Z), w ≠ 1 →
      Subgroup.centralizer ({b1 ⟨w, NF.Z_le_M₁ hw⟩} : Set G) ≤ M1G := by
    intro w hw hw1
    have hwo : orderOf w = 2 := orderOf_eq_prime (by
      have := NF.Z_exp w hw
      rwa [← sq] at this) hw1
    have h := map_mem_centerOf_perfectCore (b := b1) C.inj₁ hrange1 (NF.Z_le_M₁ hw) (Zperf hw)
    exact hyp1 _ h ((orderOf_img C.inj₁ (NF.Z_le_M₁ hw)).trans hwo)
  have hb1 : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ M1G := by
    rw [amalgamMap_of_mem₁ b1 b2 hz1]
    exact hcent1 z NF.z_mem (NF.z_ne)
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ b1.range := hrange1 ▸ hb1
  have hsyl : IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤ := D.lemma_F433 C (Or.inl hb)
  have hcentb : ∀ x ∈ (Z.subgroupOf M1).map b1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ b1.range := by
    rintro _ ⟨⟨w, hw1⟩, hw, rfl⟩ hne
    have hwZ : w ∈ Z := hw
    have hw1' : w ≠ 1 := fun h => hne (by
      subst h
      exact map_one b1)
    exact hrange1 ▸ hcent1 w hwZ hw1'
  have hnfzv := NF.not_isConj_amalgam C hsyl hcentb
  have ht : t ∈ I := by
    rw [hI]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  intro h
  exact hnfzv (h.trans (D.fusion_forward C (D.mem_T t ht) (NF.Q_le_T NF.v_mem) conj_tv))

end Core

end CFSG.Quasithin.H13.F431.Lift

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Engine

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_A35_engine (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3)
    (hodd : Odd Gp.index) (hZ1 : burnsideF4m_Core1 Gp M₁)
    {C : Type} [Group C] {U P P' : Subgroup C} {z₀ t₀ v nr na : C}
    {Zd Qd Xd Yd : Subgroup C} {q n : ℕ}
    (S1 : Lift.StdTwo C U P P' z₀ t₀)
    (S3 : Lift.StdOrient C U P P' z₀ t₀ v nr na Zd Qd Xd Yd q n)
    (hYam : IsYAmalgamPair U P P')
    (habove : ∀ B : Subgroup C, Subgroup.normalizer (U : Set C) ≤ B → B ≠ ⊤ → B ≤ P ∨ B ≤ P')
    (ψ : C ≃* ↥Gp) (hP : M₁.subgroupOf Gp = P.map ψ.toMonoidHom)
    (hP' : M₂.subgroupOf Gp = P'.map ψ.toMonoidHom)
    (hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2) :
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
  have HO := Lift.orientD_of_std A ψ.symm S3 hQP hQP' hU
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
  have NF := Lift.nfk_of_nfd A hgen hcen HO.nfd
  obtain ⟨θ, h1, h2, -⟩ := burnsideF4m_A42_exists_theta hyp.amalgam hyam
  haveI : Finite ↥A.K := Finite.of_equiv E θ.toEquiv
  obtain ⟨hC, hr1, -, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hyp1 : ∀ w ∈ centerOf (perfectCore (MiOne β ε)), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set M) ≤ MiOne β ε :=
    fun w hw hw2 => burnsideF4m_cent_MiOne hyp hL3 hZ1 hw hw2
  have hnf := Lift.burnsideF4m_local_nf LK hC rfl hr1 hyp1 NF
    (by
      rintro _ ⟨w, hw, rfl⟩
      exact Lift.iK_mem_centerOf_perfectCore_Mb1 A hgen hcen hodd' (HO.Zperf hw))
    ((Lift.iK A hgen).map_isConj HO.conj_tv)
  exact ⟨↥A.K, inferInstance, inferInstance, θ, A.Mb1, A.Mb2, h1, h2, _, _, _, LK,
    Lift.hnfI_of_hnf hnf⟩

end Engine

end CFSG.ASVolI
