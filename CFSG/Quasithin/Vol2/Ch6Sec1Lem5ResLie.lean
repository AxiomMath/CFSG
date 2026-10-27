module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Res
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517
public import CFSG.Quasithin.Background.E2TwoLieQuotBlocks
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.Background.E2TwoLieQuotLift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

namespace Res615Lie

theorem normal_subgroupOf_subgroupOf {X : Type} [Group X] {A B C : Subgroup X} (hBC : B ≤ C)
    (h : (B.subgroupOf C).Normal) : ((B.subgroupOf A).subgroupOf (C.subgroupOf A)).Normal := by
  have hle : B.subgroupOf A ≤ C.subgroupOf A := fun x hx => hBC hx
  rw [Subgroup.normal_subgroupOf_iff hle]
  rw [Subgroup.normal_subgroupOf_iff hBC] at h
  exact fun x c hx hc => h _ _ hx hc

theorem card_sup_le_of_commute {X : Type} [Group X] [Finite X] {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b => h a a.2 b b.2
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype hc with hφ
  have hr : φ.range = A ⊔ B := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_prod]
  exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

theorem card_le_thirtySix {X : Type} [Group X] [Finite X] {J : Subgroup X}
    {I : Finset (Subgroup X)} (hJ : J = ⨆ L ∈ I, L) (hcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (h6 : ∀ L ∈ I, Nat.card L = 6) : Nat.card J ≤ 36 := by
  classical
  subst hJ
  rcases hcard with h1 | h2
  · obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.iSup_singleton, h6 L₁ (Finset.mem_singleton_self L₁)]
    norm_num
  · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have h1 : L₁ ∈ ({L₁, L₂} : Finset (Subgroup X)) := Finset.mem_insert_self _ _
    have h2' : L₂ ∈ ({L₁, L₂} : Finset (Subgroup X)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.iSup_insert, Finset.iSup_singleton]
    calc Nat.card ↥(L₁ ⊔ L₂) ≤ Nat.card L₁ * Nat.card L₂ :=
          card_sup_le_of_commute (hcomm L₁ h1 L₂ h2' hne)
      _ = 36 := by rw [h6 L₁ h1, h6 L₂ h2']

variable {G : Type} [Group G] [Finite G]

theorem false_of_simple_of_isSubnormal (he22 : E2.E22StatementNoN) {H T M U : Subgroup G}
    (hMP : MinParabolic H T M) (hsq : SQTKGroup ↥H) (hred : IsTwoReducedIn H U)
    (hHU : ¬ H ≤ Subgroup.centralizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hno : ∀ K ∈ cComp H, ¬ E2.HasE22LieQuot K) {S : Subgroup (MulAut (IntMod U hU))}
    (hSA : S ≤ autI hU H) (hSs : (S.subgroupOf (autI hU H)).IsSubnormal)
    (hsimp : IsSimpleGroup ↥S) (hnc : ∃ a b : ↥S, a * b ≠ b * a) {k : ℕ} (hk : 2 ≤ k)
    (htype : E2.IsE22LieType k ↥S) : False := by
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  set f : ↥H →* ↥(autI hU H) := (MulEquiv.subgroupCongr (range_convHom hU H hHN)).toMonoidHom.comp
    (convHom hU H hHN).rangeRestrict with hf
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr (range_convHom hU H hHN)).surjective.comp
      (convHom hU H hHN).rangeRestrict_surjective
  have hf1 : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (U : Set G) → f h = 1 := by
    intro h hh
    apply Subtype.ext
    show convHom hU H hHN h = 1
    rw [convHom_apply, convI_eq_one_iff]
    exact hh
  have : Finite ↥(autI hU H) := Finite.of_surjective f hfs
  have eS : ↥(S.subgroupOf (autI hU H)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSA
  have hSc : CFSG.IsComponent (S.subgroupOf (autI hU H)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eS.symm (E2.isQuasisimple_of_isSimpleGroup hnc),
      hSs⟩
  by_cases hsol : Group.IsSolvable ↥H
  · have hAs : Group.IsSolvable ↥(autI hU H) := Group.isSolvable_of_surjective hfs
    have hS's : Group.IsSolvable ↥(S.subgroupOf (autI hU H)) := subgroup_solvable_of_solvable _
    have hSs' : Group.IsSolvable ↥S := Group.isSolvable_of_surjective (f := eS.toMonoidHom)
      eS.surjective
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hSs' a b)
  · obtain ⟨⟨K, hK, hHK, hq, -⟩, -⟩ := he22 G H T M hMP hsq hsol
    have hKH : K ≤ H := le_of_mem_cComp hK
    have hO2 : ∀ x : ↥K, x ∈ CFSG.Open.pCore 2 ↥K → f (Subgroup.inclusion hKH x) = 1 := by
      intro x hx
      apply hf1
      have h2 := CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hK)
        (⟨x, hx, rfl⟩ : (x : G) ∈ CFSG.Open.pCoreOf 2 K)
      rw [← hMP.inf_centralizer_eq_pCoreOf hred hHU] at h2
      exact h2.2
    obtain ⟨g, hg⟩ := E2.exists_surjective_of_isComponent hMP.isSylow.1 hMP.isSylow.2.1 hKH
      (E2.isSubnormal_subgroupOf_of_open (subnormal_of_mem_cComp hK)) hHK hq f hfs hO2 hSc
    exact hno K hK ⟨↥S, inferInstance, eS.toMonoidHom.comp g, eS.surjective.comp hg, k, hk, htype⟩

theorem isL2Natural_one_of_mem (he22 : E2.E22StatementNoN)
    {H T M U : Subgroup G} (hMP : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hred : IsTwoReducedIn H U) (hHU : ¬ H ≤ Subgroup.centralizer (U : Set G))
    (hU : IsElemAbelian 2 U) (hno : ∀ K ∈ cComp H, ¬ E2.HasE22LieQuot K)
    {C : Subgroup (IntMod U hU)} {I : Finset (Subgroup (MulAut (IntMod U hU)))}
    (hJ : autI hU (thompsonJ H) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (htype : ∀ L ∈ I, (∃ m : ℕ, E2.IsL2Natural L C m) ∨ E2.IsA5Module L)
    {L : Subgroup (MulAut (IntMod U hU))} (hL : L ∈ I) : E2.IsL2Natural L C 1 := by
  by_contra hne
  obtain ⟨S, hSL, hSn, hsimp, hnc, k, hk, hSt⟩ :=
    E2.exists_simple_normal_of_block (htype L hL) hne
  have hLJ : L ≤ autI hU (thompsonJ H) := hJ ▸ le_iSup₂_of_le L hL le_rfl
  have hJA : autI hU (thompsonJ H) ≤ autI hU H := autI_mono hU (B6.thompsonJ_le H)
  have hLn : (L.subgroupOf (autI hU (thompsonJ H))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLJ, hJ]
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm L' hL' L hL h a ha b hb).symm
  have hJn : ((autI hU (thompsonJ H)).subgroupOf (autI hU H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJA]
    intro φ hφ
    obtain ⟨g, hgH, rfl⟩ := (mem_autI hU).1 hφ
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨j, hjJ, rfl⟩ := (mem_autI hU).1 hn
    refine (mem_autI hU).2 ⟨g * j * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_thompsonJ H hgH) (j : G)).1 hjJ
    simpa using this
  have hLs : (L.subgroupOf (autI hU H)).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (fun x hx => hLJ hx) hJn.isSubnormal
      (normal_subgroupOf_subgroupOf hLJ hLn)
  have hSs : (S.subgroupOf (autI hU H)).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (fun x hx => hSL hx) hLs (normal_subgroupOf_subgroupOf hSL hSn)
  exact false_of_simple_of_isSubnormal he22 hMP hsq hred hHU hU hno (hSL.trans (hLJ.trans hJA))
    hSs hsimp hnc hk hSt

end Res615Lie

open Res615Lie

theorem res615Blocks_of (h331 : Stmt3_3_1) (h5172 : Stmt5_1_7_two)
    (he23 : E2.E23Statement) (he22 : E2.E22StatementNoN) : Res615Blocks := by
  intro G _ _ T M L V H n hyp hH hZ hU I _ hJ htype K hK
  by_contra hne
  have hT : IsSylowTwoOf T H := hyp.toHyp5_0_1.isSylowTwoOf hH.1.1
  have hMP : MinParabolic H T (H ⊓ M) := (hyp.toHyp5_0_1.minParabolic_of_isHStar h331 hH).1
  have hch : CharTwo H := charTwo_of_inH' hyp.qtke hyp.sylow hH.1
  have hsq : SQTKGroup ↥H := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH hyp.qtke hyp.simple hyp.nonabelian hH.1
    exact ⟨hq, hk⟩
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hch le_rfl
  have hHU : ¬ H ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) H : Set G) := by
    intro hle
    exact hZ (hle.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ H))))
  have hJT : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) H : Set G) := by
    have hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
      intro hb
      apply hZ
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
      exact hb
    obtain ⟨-, hKeq, -⟩ := h5172 G T M L V H n hyp.toHyp5_0_1 hyp.module hH hZH
    have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
    have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    intro hJC
    have hJO : thompsonJ T ≤ pCoreOf 2 H := by
      rw [← hMP.inf_centralizer_eq_pCoreOf hred hHU]
      exact le_inf hJT hJC
    have hii := hMP.commutator_lt_iff_le_pCoreOf hJT hTJ
    rw [twoResidual_eq_oTwoUpper'] at hii
    have hlt := hii.mpr hJO
    rw [← hKeq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨-, I₀, hcard₀, hJ₀, hcomm₀, -, -, htype₀, -⟩ :=
    he23 G H T (H ⊓ M) _ hU hMP hsq hch hred hJT
  have h36 : Nat.card ↥(autI hU (thompsonJ H)) ≤ 36 :=
    card_le_thirtySix hJ₀ hcard₀ hcomm₀ fun L₀ hL₀ => E2.card_of_isL2Natural_one
      (isL2Natural_one_of_mem he22 hMP hsq hred hHU hU (hyp.noLie H hH) hJ₀ hcomm₀ htype₀ hL₀)
  have h60 := E2.sixty_le_card_of_block (htype K hK) hne
  have hKJ : K ≤ autI hU (thompsonJ H) := hJ ▸ le_iSup₂_of_le K hK le_rfl
  have hle := Subgroup.card_le_of_le hKJ
  omega

end CFSG.Quasithin.H13
