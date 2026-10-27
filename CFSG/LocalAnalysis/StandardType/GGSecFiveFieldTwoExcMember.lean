module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoE8Rows
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoMemberModels
public import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLong
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.LocalAnalysis.StandardType.GGLangRatCompFieldLen
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78Kac
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
public import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.StandardType

namespace FieldTwoExc

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos CFSG.LieType.AlgebraicGroups
open CFSG.Open (StatedLieTag)

theorem markDeg_eq_one_of_labelIso {c lab : LargeEvenLabel} (hi : GGLabelIso c lab)
    (hc1 : c.n = 1) (hcne : c ≠ ⟨.twD, 2, 1⟩) (hchar : markChar lab = 2) : markDeg lab = 1 := by
  obtain ⟨tc, rc, nc⟩ := c
  obtain ⟨tl, rl, nl⟩ := lab
  simp only at hc1
  subst hc1
  rcases hi with h | ⟨-, htl, -, hn⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, h'⟩
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases tc <;> simp_all [markDeg, markChar]
  · simp only at htl hn
    subst hn
    rcases htl with rfl | rfl <;> rfl
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · exact absurd h hcne
  · simp only [LargeEvenLabel.mk.injEq] at h'
    omega

section Cert


theorem nonempty_mulEquiv_of_frame {t : StatedLieTag} {G : Type} [Group G] [Finite G]
    {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {n : ℕ} {ψ : (ggU t n 1).K →* G}
    (hZ : Subgroup.center ↥(ggG0 3 B x L D J) = ⊥)
    (F : ExcLangFrame t n 1 3 ψ (ggG0 3 B x L D J) (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    {R : Subgroup (ModGL (langTag t) GGL)}
    (hL : (L.subgroupOf (ggG0 3 B x L D J)).map F.η = R) : Nonempty (↥L ≃* ↥R) := by
  have hLG0 : L ≤ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J
  have hηinj : Function.Injective F.η := by
    rw [← MonoidHom.ker_eq_bot_iff, F.ker_η, hZ]
  exact ⟨(Subgroup.subgroupOfEquivOfLe hLG0).symm.trans
    ((Subgroup.equivMapOfInjective _ F.η hηinj).trans (MulEquiv.subgroupCongr hL))⟩

theorem componentOrbitLength_eq_one_of_qTwo {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    {ψ : (ggU t n 1).K →* G} (hZ : Subgroup.center ↥(ggG0 3 B x L D J) = ⊥)
    (F : ExcLangFrame t n 1 3 ψ (ggG0 3 B x L D J) (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    (i : KernelComponent (rootCharHom (F.coord x)))
    (hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus)
    (hap : ∀ j, F.coord x j ^ 3 = 1) (h1 : rootDiagUnit (langTag t) (F.coord x) ≠ 1)
    (hqs : CFSG.IsQuasisimple
      ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i))
    (hL : (L.subgroupOf (ggG0 3 B x L D J)).map F.η =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) :
    componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 := by
  have hτ : langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨lab, hlab, hchar, hdeg, -, -, -, hhas, -⟩ :=
    LangRat.langRatCompFieldLen_holds (langTag t) GGL 5 F.setup hτ 3 Nat.prime_three
      (by norm_num) (F.coord x) hT hap h1 i hqs
  have hq2 : F.setup.D.q = 2 := by
    change F.Δ.q = 2
    rw [F.q_eq, pow_one]
  rw [hq2] at hdeg
  obtain ⟨e⟩ := nonempty_mulEquiv_of_frame hZ F hL
  have hhasL : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
    ggHasLabel_quotCenter_of_mulEquiv e.symm hhas
  obtain ⟨c, hc, hc1, hcne, -, -, hhasc⟩ := hC.exists_markedModel_and_hasLabel_of_qTwo hq
  have hi := ggLabelRigidInput_holds c lab (↥L ⧸ Subgroup.center ↥L) hc hlab hhasc hhasL
  rw [markDeg_eq_one_of_labelIso hi hc1 hcne hchar, pow_one] at hdeg
  have h2 : (2 : ℕ) ^ componentOrbitLength F.setup.ρ
      (componentRoots (rootCharHom (F.coord x)) i) = 2 ^ 1 := by
    rw [← hdeg, pow_one]
  exact Nat.pow_right_injective (le_refl 2) h2

theorem exists_longSelectedSL2Model_E6 :
    ∃ δ, GGLongRoot (ggU .E6 0 1).D δ ∧
      Nonempty (SelectedRoot.SelectedSL2Model (ggU .E6 0 1).D (GaloisField 2 1) δ) := by
  obtain ⟨δ, ⟨m⟩⟩ := exists_selectedSL2Model_E6
  exact ⟨δ, ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6
    (cartanE_symm 6) rfl m.root_mem, ⟨m⟩⟩

theorem exists_longSelectedSL2Model_E8 :
    ∃ δ, GGLongRoot (ggU .E8 0 1).D δ ∧
      Nonempty (SelectedRoot.SelectedSL2Model (ggU .E8 0 1).D (GaloisField 2 1) δ) := by
  obtain ⟨δ, ⟨m⟩⟩ := FieldTwoE8.exists_selectedSL2Model_E8
  exact ⟨δ, ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E8
    (cartanE_symm 8) rfl m.root_mem, ⟨m⟩⟩

theorem exists_longModel_of_carrierModel_of_not_triD4 {τ : Tag} {p₀ : ℕ}
    {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)}
    {M : LieUniversal} (hM : CarrierModel S a i M 1) (hsolv : ¬ Group.IsSolvable M.K)
    (htri : ¬ (twistKind S.ρ (rootCharHom a) i = .exc ∧
      compRank (componentRoots (rootCharHom a) i) = 4 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F), S2MathFi1035Pos.TriField F σ 1 ∧
        M = S2MathFi1035Pos.triD4Universal F σ)) :
    ∃ (t' : StatedLieTag) (n' : ℕ), M = ggU t' n' 1 ∧ StatedLieAdmissible t' n' 2 1 ∧
      2 ≤ (ggU t' n' 1).D.rank ∧ ∃ δ, GGLongRoot (ggU t' n' 1).D δ ∧
        Nonempty (SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ) := by
  unfold CarrierModel at hM
  generalize hr : compRank (componentRoots (rootCharHom a) i) = r at hM htri
  rcases hM with ⟨-, rfl⟩ | ⟨-, hr2, -, rfl⟩ | ⟨hk, rfl⟩ | ⟨-, hr4, -, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨-, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ | ⟨hk, ⟨-, rfl⟩ | ⟨hr4, hF⟩⟩
  ·
    exfalso
    apply hsolv
    have hK : Nat.card (GaloisField 2 1) ≤ 3 := by
      rw [GaloisField.card 2 1 one_ne_zero]
      norm_num
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_of_card_dvd_216
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.card_sl2_dvd_216 hK)
  · obtain ⟨δ, -, hδ, hm⟩ := SelectedRoot.exists_selectedSL2Model_PSL_long (m := r) hr2
    refine ⟨.PSL, r + 1, rfl, ⟨Nat.prime_two, le_rfl, by omega, fun h => ?_, fun h => ?_⟩, ?_,
      δ, hδ, hm⟩
    · simp only [Prod.mk.injEq] at h
      omega
    · simp only [Prod.mk.injEq] at h
      omega
    · change 2 ≤ r
      exact hr2
  · have hr2 := (CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hk).1
    rw [hr] at hr2
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    ·
      exfalso
      apply hsolv
      have hr' : r = 2 := by omega
      rw [hr']
      have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
        rw [GaloisField.card 2 (2 * 1) (by norm_num)]
        norm_num
      have h := CFSG.Quasithin.isSolvable_statedSU_one (F := GaloisField 2 (2 * 1)) hF
      exact solvable_of_solvable_injective
        (f := (Unitary.equivStatedSU (F := GaloisField 2 (2 * 1)) (p := 2) (f := 1) hF 3).toMonoidHom)
        (Unitary.equivStatedSU (F := GaloisField 2 (2 * 1)) (p := 2) (f := 1) hF 3).injective
    · obtain ⟨δ, -, hδ, hm⟩ := SelectedRoot.exists_selectedSL2Model_PSU_long (n := r + 1) (by omega)
      refine ⟨.PSU, r + 1, rfl, ⟨Nat.prime_two, le_rfl, by omega, fun h => ?_⟩, ?_, δ, hδ, hm⟩
      · simp only [Prod.mk.injEq] at h
        omega
      · change 2 ≤ (r + 1) / 2
        omega
  · obtain ⟨m, hm⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
    rw [hm]
    obtain ⟨δ, -, hδ, hmd⟩ :=
      SelectedRoot.exists_selectedSL2Model_POmegaPlus_long (n := m + 3) (by omega)
    refine ⟨.POmegaPlus, m + 3, rfl, ⟨Nat.prime_two, le_rfl, by omega⟩, ?_, δ, hδ, hmd⟩
    change 2 ≤ m + 3
    omega
  · have hr4 := (CFSG.HardMathSupport.Timmesfeld.CrossChar.twoD_kind_unpack hk).2.1
    rw [hr] at hr4
    obtain ⟨δ, -, hδ, hm⟩ := SelectedRoot.exists_selectedSL2Model_POmegaMinus_long (n := r) hr4
    refine ⟨.POmegaMinus, r, rfl, ⟨Nat.prime_two, le_rfl, hr4⟩, ?_, δ, hδ, hm⟩
    change 2 ≤ r - 1
    omega
  · exact ⟨.E6, 0, rfl, ⟨Nat.prime_two, le_rfl, rfl⟩, by change 2 ≤ 6; norm_num,
      exists_longSelectedSL2Model_E6⟩
  · exact ⟨.E7, 0, rfl, ⟨Nat.prime_two, le_rfl, rfl⟩, by change 2 ≤ 7; norm_num,
      FieldTwoE8.exists_longSelectedSL2Model_E7⟩
  · exact ⟨.E8, 0, rfl, ⟨Nat.prime_two, le_rfl, rfl⟩, by change 2 ≤ 8; norm_num,
      exists_longSelectedSL2Model_E8⟩
  · exact ⟨.twistedE6, 0, rfl, ⟨Nat.prime_two, le_rfl, rfl⟩, by change 2 ≤ 4; norm_num,
      FieldTwoE8.exists_longSelectedSL2Model_twistedE6⟩
  · exact absurd ⟨hk, hr4, hF⟩ htri

theorem exists_longModel_of_carrierModel {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀}
    {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)} {M : LieUniversal}
    (hM : CarrierModel S a i M 1) (hsolv : ¬ Group.IsSolvable M.K)
    (h4 : compRank (componentRoots (rootCharHom a) i) ≠ 4) :
    ∃ (t' : StatedLieTag) (n' : ℕ), M = ggU t' n' 1 ∧ StatedLieAdmissible t' n' 2 1 ∧
      2 ≤ (ggU t' n' 1).D.rank ∧ ∃ δ, GGLongRoot (ggU t' n' 1).D δ ∧
        Nonempty (SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ) :=
  exists_longModel_of_carrierModel_of_not_triD4 hM hsolv fun ⟨_, hr4, _⟩ => h4 hr4

variable {G : Type} [Group G]

theorem selected_of_carrier {t : StatedLieTag} {n f : ℕ} {L : Subgroup G}
    (ψ : (ggU t n f).K →* G) (hψ : Function.Injective ψ) (hLψ : L ≤ ψ.range)
    {t' : StatedLieTag} {n' : ℕ} (α : (ggU t' n' 1).K →* G)
    (hadm : StatedLieAdmissible t' n' 2 1) (hrk : 2 ≤ (ggU t' n' 1).D.rank)
    (hker : α.ker ≤ Subgroup.center (ggU t' n' 1).K) (hrange : α.range = L)
    {δ : Fin (ggU t' n' 1).D.rank → ℤ}
    (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ)
    {β' : Fin (ggU t n f).D.rank → ℤ} (hβ' : β' ∈ (ggU t n f).D.roots) (k : (ggU t n f).K)
    (hroot : ((ggU t' n' 1).D.rootGroup δ).map α = ggRootSub (ggU t n f).D ψ β' k) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
        ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 1) γ)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
          ∃ u₀ : (ggU t n f).K,
            ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
              (ψ'.comp model'.phi).range := by
  have hα : ∀ y, α y ∈ ψ.range := fun y => hLψ (hrange ▸ ⟨y, rfl⟩)
  let ψ₀ : (ggU t' n' 1).K →* (ggU t n f).K :=
    (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp (α.codRestrict ψ.range hα)
  have hcomp : ψ.comp ψ₀ = α := by
    ext y
    change ψ ((MonoidHom.ofInjective hψ).symm ⟨α y, hα y⟩) = α y
    have h := MonoidHom.ofInjective_apply hψ (x := (MonoidHom.ofInjective hψ).symm ⟨α y, hα y⟩)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hML : ψ₀.range.map ψ = L := by
    rw [← MonoidHom.range_comp, hcomp, hrange]
  have hker₀ : ψ₀.ker ≤ Subgroup.center (ggU t' n' 1).K := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [← hcomp, MonoidHom.comp_apply, hy, map_one]
  have hroot₀ : ((ggU t' n' 1).D.rootGroup δ).map ψ₀ =
      ((ggU t n f).D.rootGroup β').map (MulAut.conj k).toMonoidHom := by
    apply Subgroup.map_injective hψ
    rw [Subgroup.map_map, hcomp, hroot]
    rfl
  exact FieldTwoE8.selected_of_member ψ hψ hML ψ₀ hadm hrk hker₀ rfl model' hβ' k hroot₀

section ComponentFieldReduction

theorem ggSecFiveQTwoFieldTwoSelectedAt_noncentral_of_core {t : StatedLieTag}
    (ht : t = .E7 ∨ t = .E8) :
    ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig 3 B Bs x L D J → GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
        ∀ (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ →
            GGPsiInnerDiag (ggU t n f).D ψ x →
              x ∉ Subgroup.centralizer (ggG0 3 B x L D J : Set G) →
                ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
                  StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
                    ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
                    ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
                      (model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 1) γ)
                      (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
                      ∃ u₀ : (ggU t n f).K,
                        ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
                          (ψ'.comp model'.phi).range := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag hnc
  have ht3 : t = .E6 ∨ t = .E7 ∨ t = .E8 := by
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨hf, hψ, F, i, hT, hap, h1, hqs, hL, -, hmem⟩ :=
    exists_member_of_ggConfig_exc ht3 hC hq ψ hpres hdiag hnc
  subst hf
  obtain ⟨-, hZ⟩ :=
    injective_and_center_eq_bot hpres.2.1.1 hpres.2.1.2 (center_ggU_exc_eq_bot ht3 n)
  have hs := componentOrbitLength_eq_one_of_qTwo ht hC hq hZ F i hT hap h1 hqs hL
  obtain ⟨M, α, hCM, -, hrange, hker, -, hperf, hpair⟩ := hmem hs
  have hτ : langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h3 : ((3 : ℕ) : GGL) ≠ 0 := by
    intro h
    have h2 : 2 ∣ 3 := (CharP.cast_eq_zero_iff GGL 2 3).1 h
    omega
  have h4 := (TablePThreeKG.e78_three_classes hτ h3 hap).1 i
  have hRnt : Nontrivial ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) := by
    obtain ⟨-, -, a, b, hab⟩ := hqs
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a', b', fun h => hab (by rw [h])⟩⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_of_frame hZ F hL
  have hLnt : Nontrivial ↥L := e.toEquiv.nontrivial
  have hMnt : Nontrivial M.K := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have hLbot : L = ⊥ := by
      rw [← hrange, eq_bot_iff]
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_bot, Subsingleton.elim y 1, map_one]
    obtain ⟨a, b, hab⟩ := hLnt.exists_pair_ne
    apply hab
    have ha : (a : G) ∈ (⊥ : Subgroup G) := hLbot ▸ a.2
    have hb : (b : G) ∈ (⊥ : Subgroup G) := hLbot ▸ b.2
    exact Subtype.ext ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)
  have hsolv : ¬ Group.IsSolvable M.K := Group.IsPerfect.not_isSolvable M.K
  obtain ⟨t', n', rfl, hadm, hrk, δ, hlong, ⟨model'⟩⟩ :=
    exists_longModel_of_carrierModel hCM hsolv h4
  obtain ⟨β', hβ', -, k, hroot, -⟩ := hpair δ model'.root_mem hlong
  have hLψ : L ≤ ψ.range := hpres.2.1.1 ▸ le_ggG0_left 3 B x L D J
  exact selected_of_carrier ψ hψ hLψ α hadm hrk hker hrange model' hβ' k hroot

end ComponentFieldReduction

end Cert

end FieldTwoExc

end CFSG.StandardType

end
