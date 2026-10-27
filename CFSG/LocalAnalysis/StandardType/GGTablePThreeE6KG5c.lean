module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TorsionLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Labels
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableZ
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
import CFSG.LocalAnalysis.StandardType.KGCoverLift
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rawDatum_elim_const' {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun _ _ _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear, LargeEvenRecipeUnitary,
    LargeEvenRecipeSymplectic, LargeEvenRecipeOmegaPlus, LargeEvenRecipeOmegaMinus,
    LargeEvenRecipeChevalley, LargeEvenRecipeTwisted, LargeEvenRecipeSuzuki,
    LargeEvenRecipeG2Derived, LargeEvenRecipeTwF4Inherited] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq)

private theorem eq_of_ggLabelIso_of_twA2 {labJ lab : LargeEvenLabel}
    (h : GGLabelIso labJ lab) (hJ : labJ.tag = .twA ∧ labJ.rank = 2) : labJ = lab := by
  obtain ⟨t, l, n⟩ := labJ
  obtain ⟨t', l', n'⟩ := lab
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -, -, -⟩
    rcases h1 with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .D := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨h1, -⟩
    have hl : l = 3 := congrArg LargeEvenLabel.rank h1
    have hl2 : l = 2 := hJ.2
    omega
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    simp_all
  · rcases h with ⟨-, h1⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    simp_all

private theorem e6_split_concl {lab : LargeEvenLabel} (hsplit : LargeEvenSplit 3 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) (hn : lab.tag = .E6 → 2 ≤ lab.n) :
    (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨t, l, n⟩ := lab
  rcases hsplit with ⟨hunt, hdiv⟩ | ⟨hunt, -, hdiv⟩ | ⟨htag', hdiv⟩ | ⟨hn1, _⟩
  · rcases htag with rfl | rfl
    · exact Or.inl ⟨rfl, hdiv⟩
    · exact absurd hunt (by simp [LargeEvenUntwisted])
  · rcases htag with rfl | rfl
    · exact absurd trivial (by simpa [LargeEvenUntwisted] using hunt)
    · exact Or.inr ⟨rfl, hdiv⟩
  · rcases htag with rfl | rfl <;> rcases htag' with htag'' | htag'' <;>
      exact absurd htag'' (by simp)
  · rcases htag with rfl | rfl
    · exact absurd (hn rfl) (by rw [hn1]; omega)
    · exact Or.inr ⟨rfl, by rw [hn1]; norm_num⟩

section CenterAux

open scoped commutatorElement

private theorem comap_center_eq_center_of_perfect {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    (hperf : commutator G = ⊤) :
    (Subgroup.center H).comap f = Subgroup.center G := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    have hval : ∀ g : G, ⁅x, g⁆ ∈ Subgroup.center G := by
      intro g
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hx (f g)).symm
    have hmul : ∀ g h : G, ⁅x, g * h⁆ = ⁅x, g⁆ * ⁅x, h⁆ := by
      intro g h
      have hc : ⁅x, h⁆ ∈ Subgroup.center G := hval h
      have hac : x * h = ⁅x, h⁆ * h * x := by
        rw [commutatorElement_def]; group
      have hab : x * g = ⁅x, g⁆ * g * x := by
        rw [commutatorElement_def]; group
      have hk := Subgroup.mem_center_iff.1 hc
      generalize ⁅x, h⁆ = k at hac hk ⊢
      have e : ⁅x, g * h⁆ * ((g * h) * x) = x * (g * h) := by
        rw [commutatorElement_def]; group
      have e' : x * (g * h) = ⁅x, g⁆ * k * ((g * h) * x) := by
        calc x * (g * h) = (x * g) * h := by group
          _ = ⁅x, g⁆ * g * (x * h) := by rw [hab]; group
          _ = ⁅x, g⁆ * g * (k * h * x) := by rw [hac]
          _ = ⁅x, g⁆ * (g * k) * h * x := by group
          _ = ⁅x, g⁆ * (k * g) * h * x := by rw [hk g]
          _ = ⁅x, g⁆ * k * ((g * h) * x) := by group
      rw [e'] at e
      exact mul_right_cancel e
    let ψ : G →* G :=
      { toFun := fun g => ⁅x, g⁆
        map_one' := by simp [commutatorElement_def]
        map_mul' := hmul }
    have hψker : commutator G ≤ ψ.ker := by
      rw [_root_.commutator_def G]
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker]
      change ψ ⁅a, b⁆ = 1
      rw [map_commutatorElement ψ a b]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hval a) (ψ b)).symm
    rw [hperf] at hψker
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : ⁅x, g⁆ = 1 := hψker (Subgroup.mem_top g)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hg).symm
  · intro x hx
    rw [Subgroup.mem_comap]
    exact Subgroup.map_center_le_center (f := f) hf (Subgroup.mem_map_of_mem f hx)

end CenterAux

section CertificatesKG5c

theorem kg5c_E6eps
    (hZ : TwE6A2CentreInput) {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J)
    (hq : LargeEvenMarking X fun lab _ _ _ _ _ => 2 ≤ lab.n) :
    ¬ (LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) ∧
      Subgroup.center J ≠ ⊥) := by
  rintro ⟨hJ, hZJ⟩
  have hδmem : δ ∈ A := hD.1.1.2.1
  have hδ3 : δ ^ 3 = 1 := hD.1.1.1.2 δ hδmem
  have hδne1 : δ ≠ 1 := hD.1.1.2.2.1
  have hcomp : IsComponentOf J (ggAutFixedSubgroup δ) := hD.1.1.2.2.2.1
  have hdat : GGTorsionDatum (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 δ J := by
    refine ⟨Nat.prime_three, by norm_num, hδ3, hδne1, hcomp, ?_⟩
    refine largeEvenMarking_mono ?_ hD.2.2.2
    intro lab R _ I F θ h
    exact ⟨h.1, h.2.2 δ hδmem⟩
  obtain ⟨-, labX, hlabX, hrawX⟩ := ggTorsion_E6eps_unique_label hdat hq hD.2.1
  have hHasX : GGHasLabel labX (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawX
  have hpropX : (labX.tag = .E6 ∨ labX.tag = .twE6) ∧
      ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
        GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧ E6CompLabel (2 ^ labX.n) lab' :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun θ hh => hh) hrawX)
  obtain ⟨lab', hlab', hHasJ', hE6X⟩ := hpropX.2
  obtain ⟨-, labD, hlabD, hrawD⟩ := hD.2.2.2
  have hHasD : GGHasLabel labD (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawD
  obtain ⟨RD, _, ID, FD, hQD⟩ := largeEvenRawDatum_exists hrawD
  obtain ⟨hsD, hnaD, θD, hDpay⟩ := hQD
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  have hIsoXD : GGLabelIso labX labD := hrigid labX labD _ hlabX hlabD hHasX hHasD
  have hEqXD : labX = labD := eq_of_ggLabelIso_of_e6Tag hIsoXD hpropX.1
  obtain ⟨-, labc, hlabc, hrawc⟩ := hJ
  have hHasc : GGHasLabel labc (↥J ⧸ Subgroup.center ↥J) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawc
  have hpropc : GGLabelA2 labc ∧ labc.tag = .twA :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun θ hh => hh) hrawc)
  have hr2 : labc.rank = 2 := hpropc.1.1
  have hIsoCl : GGLabelIso labc lab' := hrigid labc lab' _ hlabc hlab' hHasc hHasJ'
  have hEqCl : labc = lab' := eq_of_ggLabelIso_of_twA2 hIsoCl ⟨hpropc.2, hr2⟩
  have hE6c : E6CompLabel (2 ^ labX.n) labc := by rw [hEqCl]; exact hE6X
  have hlast : labc.rank = 2 ∧ 2 ^ labc.n = (2 ^ labX.n) ^ 3 ∧
      (((2 ^ labX.n : ℕ) : ZMod 3) = 1 ∧ labc.tag = .A ∨
        ((2 ^ labX.n : ℕ) : ZMod 3) = 2 ∧ labc.tag = .twA) := by
    unfold E6CompLabel at hE6c
    rcases hE6c with ⟨-, hrank, -⟩ | ⟨-, hrank, -⟩ | ⟨htri, -⟩ | hlast
    · omega
    · omega
    · rw [hpropc.2] at htri; simp at htri
    · exact hlast
  have hq2 : ((2 ^ labX.n : ℕ) : ZMod 3) = 2 := by
    rcases hlast.2.2 with ⟨h1, ht⟩ | ⟨h2, ht⟩
    · rw [hpropc.2] at ht; simp at ht
    · exact h2
  have hnX : labc.n = 3 * labX.n := by
    have hp : 2 ^ labc.n = 2 ^ (3 * labX.n) := by
      rw [hlast.2.1, ← pow_mul]
      congr 1; ring
    exact Nat.pow_right_injective (a := 2) (by norm_num) hp
  have hnD : labc.n = 3 * labD.n := by rw [hEqXD] at hnX; exact hnX
  have hq2D : ((2 ^ labD.n : ℕ) : ZMod 3) = 2 := by rw [hEqXD] at hq2; exact hq2
  have hn2D : 2 ≤ labD.n := by
    obtain ⟨-, labq, hlabq, hrawq⟩ := hq
    have hHasq : GGHasLabel labq (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawq
    have hq2n : 2 ≤ labq.n :=
      rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun θ hh => hh) hrawq)
    have hIsoDq : GGLabelIso labD labq := hrigid labD labq _ hlabD hlabq hHasD hHasq
    have hEqDq : labD = labq := eq_of_ggLabelIso_of_e6Tag hIsoDq hDpay.1
    rw [hEqDq]; exact hq2n
  have hsplitConcl := e6_split_concl hDpay.2.1 hDpay.1 (fun _ => hn2D)
  have htagDtw : labD.tag = .twE6 := by
    rcases hsplitConcl with ⟨hE6, hdiv⟩ | ⟨htw, hdiv⟩
    · exfalso
      have hcast : ((2 ^ labD.n : ℕ) : ZMod 3) = 1 := by
        have hzero : ((2 ^ labD.n - 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff (2 ^ labD.n - 1) 3).mpr hdiv
        have hle : 1 ≤ 2 ^ labD.n := by
          have : 0 < 2 ^ labD.n := by positivity
          omega
        rw [Nat.cast_sub hle] at hzero
        exact sub_eq_zero.mp hzero
      rw [hcast] at hq2D
      exact absurd hq2D (by decide)
    · exact htw
  have hdivD : 3 ∣ 2 ^ labD.n + 1 := by
    rcases hsplitConcl with ⟨hE6, -⟩ | ⟨-, hdiv⟩
    · exfalso
      rw [htagDtw] at hE6
      simp at hE6
    · exact hdiv
  have hn3D : 3 ≤ labD.n := by
    rcases Nat.lt_or_ge labD.n 3 with h | h
    · have hn2 : labD.n = 2 := by omega
      rw [hn2] at hdivD
      norm_num at hdivD
    · exact h
  have hZlabD : LargeEvenLabelAll labD (TwE6A2CentreCont labD.n) :=
    hZ labD hlabD htagDtw hn3D hdivD
  have hrawD2 := hZlabD _ hrawD
  obtain ⟨R, _, I, F, hQ2⟩ := largeEvenRawDatum_exists hrawD2
  obtain ⟨hsR, hnaR, θ, hLD⟩ := hQ2.1
  have hTw : TwE6A2CentreCont labD.n R I F := hQ2.2
  obtain ⟨hfinC, hCperf, θC, κ, lift, hκsurj, hκker, hκmk, hκlift, hkg⟩ :=
    CFSG.StandardType.KGUniv.exists_universal_cover_lift hX θ
  haveI : Finite (CFSG.RankThree.PerfectCover.HopfCover R) := hfinC
  have hα3 : (lift δ) ^ 3 = 1 := by
    simpa using congrArg lift hδ3
  have hαne : lift δ ≠ 1 := by
    intro h1
    apply hδne1
    ext y
    obtain ⟨x, rfl⟩ := hκsurj y
    have h := hκlift δ x
    rw [h1] at h
    simpa using h.symm
  have hαI : ggInducedAut θC (lift δ) ∈ I := by
    change kgInducedAut θC (lift δ) ∈ I
    rw [hkg]
    change ggInducedAut θ δ ∈ I
    exact hLD.2.2 δ hδmem
  have hJcompA : CFSG.Assembly.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ =
        ggAutFixedSubgroup δ := Subgroup.ext fun _ => Iff.rfl
    rw [hfix]
    exact hcomp
  obtain ⟨Jt, hJtcomp, hJtmap⟩ :=
    CFSG.StandardType.TCJ.tcjLin_component_lift κ hκsurj hκker (lift δ) δ
      (fun x => hκlift δ x) hJcompA
  have hJtcomp' : CFSG.Assembly.IsComponentOf Jt (ggAutFixedSubgroup (lift δ)) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (lift δ) =
        ggAutFixedSubgroup (lift δ) := Subgroup.ext fun _ => Iff.rfl
    rw [hfix] at hJtcomp
    exact hJtcomp
  let f : ↥Jt →* ↥J :=
    (MulEquiv.subgroupCongr hJtmap).toMonoidHom.comp (κ.subgroupMap Jt)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hJtmap).surjective.comp (κ.subgroupMap_surjective Jt)
  have hkerf : f.ker ≤ Subgroup.center ↥Jt := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (MulEquiv.subgroupCongr hJtmap) (κ.subgroupMap Jt x) =
        (MulEquiv.subgroupCongr hJtmap) 1 := by simpa [f] using hx
    have hx1 : κ.subgroupMap Jt x = 1 := (MulEquiv.subgroupCongr hJtmap).injective hx'
    have hx2 : κ (x : CFSG.RankThree.PerfectCover.HopfCover R) = 1 := by
      simpa using congrArg Subtype.val hx1
    have hxcent : (x : CFSG.RankThree.PerfectCover.HopfCover R) ∈
        Subgroup.center (CFSG.RankThree.PerfectCover.HopfCover R) :=
      hκker (MonoidHom.mem_ker.mpr hx2)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxcent
      (y : CFSG.RankThree.PerfectCover.HopfCover R))
  let g : ↥Jt →* ↥J ⧸ Subgroup.center ↥J :=
    (QuotientGroup.mk' (Subgroup.center ↥J)).comp f
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).comp hf
  have hgker : Subgroup.center ↥Jt = g.ker := by
    rw [← comap_center_eq_center_of_perfect f hf hkerf hJtcomp'.2.2.1]
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    change f x ∈ Subgroup.center ↥J ↔
      QuotientGroup.mk' (Subgroup.center ↥J) (f x) = 1
    exact (QuotientGroup.eq_one_iff (f x)).symm
  let e : ↥Jt ⧸ Subgroup.center ↥Jt ≃* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.liftEquiv (Subgroup.center ↥Jt) hg hgker
  have hmJt : LargeEvenMarking ↥Jt
      (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3 * labD.n) := by
    refine ⟨hJtcomp'.2.2.1, labc, hlabc, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F h => ⟨h.1, h.2.1, ?_⟩) hrawc
    obtain ⟨θc, hθc⟩ := h.2.2
    exact ⟨e.trans θc, hpropc.2, hr2, hnD⟩
  have hcenterJt : Subgroup.center ↥Jt = ⊥ :=
    hTw θC (lift δ) hα3 hαne hαI Jt hJtcomp' hmJt
  have hcomap := comap_center_eq_center_of_perfect f hf hkerf hJtcomp'.2.2.1
  have hcenterJ : Subgroup.center ↥J = ⊥ := by
    have hmap := congrArg (Subgroup.map f) hcomap
    rw [Subgroup.map_comap_eq_self_of_surjective hf, hcenterJt, Subgroup.map_bot] at hmap
    exact hmap
  exact hZJ hcenterJ

end CertificatesKG5c

end CFSG.StandardType.TablePThreeKG

end
