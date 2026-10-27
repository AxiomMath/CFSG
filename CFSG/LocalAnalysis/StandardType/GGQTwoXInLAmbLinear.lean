module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAmbDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLQuot
public import CFSG.LocalAnalysis.StandardType.GGLinCentCompLabel
public import CFSG.LocalAnalysis.StandardType.GGXInLDispatch
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggLabelIso_not_of_tagA {lab lab' : LargeEvenLabel}
    (hA : lab.tag = .A) (h' : lab'.tag = .twA ∨ lab'.tag = .twE6) :
    ¬ GGLabelIso lab lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only [LargeEvenLabel.tag] at hA h'
  subst hA
  rcases h' with h' | h' <;> subst h'
  all_goals
    intro hiso
    rcases hiso with h | h | h | h | h | h | h | h
    · have ht := congrArg LargeEvenLabel.tag h
      simp at ht
    · rcases h with ⟨h1, -⟩
      rcases h1 with h1 | h1 <;> simp at h1
    · have ht := congrArg LargeEvenLabel.tag h.1
      simp at ht
    · have ht := congrArg LargeEvenLabel.tag h.2
      simp at ht
    · have ht := congrArg LargeEvenLabel.tag h.1
      simp at ht
    · have ht := congrArg LargeEvenLabel.tag h.1
      simp at ht
    · have ht := congrArg LargeEvenLabel.tag h.1
      simp at ht
    · have ht := congrArg LargeEvenLabel.tag h.1
      simp at ht

theorem ggQTwoXInL_ambient_linear_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (_hI : GGQTwoI1 Bs D J)
    (hxL : x ∈ L) (hA : GGQTwoXInLAmbOn (fun t => t = .A) Bs (ggG0 3 B x L D J)) : False := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSStar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSStar.2.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hx3 : x ^ 3 = 1 := hcfg.2.1.2.1.2 x hxBs
  let G0 : Subgroup G := ggG0 3 B x L D J
  have hxG0 : x ∈ G0 := le_ggG0_left 3 B x L D J hxL
  let xbar : (↥G0) ⧸ Subgroup.center ↥G0 :=
    QuotientGroup.mk' (Subgroup.center ↥G0) ⟨x, hxG0⟩
  let Lbar : Subgroup ((↥G0) ⧸ Subgroup.center ↥G0) :=
    (L.subgroupOf G0).map (QuotientGroup.mk' (Subgroup.center ↥G0))
  have hLbar : IsComponentOf Lbar (Subgroup.centralizer {xbar}) := by
    simpa only [G0, Lbar, xbar] using GGConfig.isComponentOf_map_ggG0_center hcfg hxL
  have hA0 : GGQTwoXInLAmbOn (fun t => t = .A) Bs G0 := hA
  unfold GGQTwoXInLAmbOn at hA0
  obtain ⟨-, lab, hlab, hraw⟩ := hA0
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, _, htag0, -⟩ := hQ0
  have hlabA : lab = ⟨.A, lab.rank, lab.n⟩ := by
    obtain ⟨t, r, n⟩ := lab
    cases t <;> simp_all
  rw [hlabA] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hKf, hKfin, hKcard, hQ⟩ := hraw
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨-, -, θ, -, -, -⟩ := hQ
  let J' : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K)) :=
    Lbar.map θ.toMonoidHom
  have hmapCent : (Subgroup.centralizer {xbar}).map θ.toMonoidHom =
      Subgroup.centralizer {θ xbar} :=
    CFSG.centralizer_singleton_map θ xbar
  have hJ' : IsComponentOf J' (Subgroup.centralizer {θ xbar}) := by
    change IsComponentOf (Lbar.map θ.toMonoidHom) (Subgroup.centralizer {θ xbar})
    rw [← hmapCent]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff θ.injective).mpr hLbar
  have hx3G : (⟨x, hxG0⟩ : ↥G0) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hx3
  have hxbar3 : xbar ^ 3 = 1 := by
    dsimp only [xbar]
    rw [← map_pow, hx3G, map_one]
  have hθ3 : (θ xbar) ^ 3 = 1 := by
    rw [← map_pow, hxbar3, map_one]
  have hodd : Odd (orderOf (θ xbar)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hθ3)
  have hrank : 2 ≤ lab.rank + 1 := by
    have h := hlab
    rw [hlabA] at h
    dsimp only [LargeEvenInLambda2] at h
    omega
  obtain ⟨labA, htagA, hΛA, hhasA⟩ :=
    exists_labelA_of_isComponentOf_centralizer_linear (d := lab.rank + 1)
      (K := K) (n := lab.n) hrank hKcard hodd hJ'
  let eJ : ↥J' ≃* ↥Lbar := (Lbar.equivMapOfInjective θ.toMonoidHom θ.injective).symm
  have hhasLbar : GGHasLabel labA (↥Lbar ⧸ Subgroup.center ↥Lbar) :=
    ggHasLabel_quotCenter_of_mulEquiv eJ hhasA
  let G' : Subgroup ↥G0 := L.subgroupOf G0
  let eL : ↥G' ≃* ↥L := Subgroup.subgroupOfEquivOfLe (le_ggG0_left 3 B x L D J)
  have hG'perf : commutator ↥G' = ⊤ := by
    have hLperf : commutator ↥L = ⊤ := hcomp.2.2.1
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) eL.symm.toMonoidHom
    rw [← commutator_def, hLperf,
      Subgroup.map_top_of_surjective _ eL.symm.surjective, ← commutator_def] at h
    exact h.symm
  haveI : Group.IsPerfect ↥G' := Group.isPerfect_def.mpr hG'perf
  obtain ⟨eC⟩ := TableCRes.centerQuot_equiv_map_central
    (Z := Subgroup.center ↥G0) (J := G') le_rfl (Group.isPerfect_def.mpr hG'perf)
  have hhasG' : GGHasLabel labA (↥G' ⧸ Subgroup.center ↥G') :=
    ggHasLabel_of_mulEquiv eC.symm hhasLbar
  have hhasL : GGHasLabel labA (↥L ⧸ Subgroup.center ↥L) :=
    ggHasLabel_quotCenter_of_mulEquiv eL hhasG'
  obtain ⟨-, hcase⟩ := GGXInL.lup8g_dispatch hS hxL
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  rcases hcase with ⟨n, K', hK'f, hK'fin, ⟨M⟩, -, h6n⟩ | he6
  ·
    letI : Field K' := hK'f
    letI : Finite K' := hK'fin
    have hΛL : LargeEvenInLambda2 (⟨.twA, n - 1, 1⟩ : LargeEvenLabel) := by
      dsimp only [LargeEvenInLambda2]
      refine ⟨le_rfl, by omega, ?_⟩
      intro h
      omega
    have hhasL' : GGHasLabel (⟨.twA, n - 1, 1⟩ : LargeEvenLabel)
        (↥L ⧸ Subgroup.center ↥L) := by
      dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeUnitary]
      refine ⟨K', hK'f, hK'fin, ?_, ?_⟩
      · rw [M.card_K]
        norm_num
      · exact ⟨by
          rw [show n - 1 + 1 = n by omega]
          exact M.theta⟩
    have hiso : GGLabelIso labA ⟨.twA, n - 1, 1⟩ :=
      hrigid labA ⟨.twA, n - 1, 1⟩ (↥L ⧸ Subgroup.center ↥L) hΛA hΛL hhasL hhasL'
    exact ggLabelIso_not_of_tagA htagA (Or.inl rfl) hiso
  ·
    unfold GGInnerDiagOnLabel at he6
    obtain ⟨-, labL, hΛL, hrawL⟩ := he6
    obtain ⟨_, _, _, _, hQL⟩ := largeEvenRawDatum_exists hrawL
    obtain ⟨-, -, _, htagL, -⟩ := hQL
    have hhasL' : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawL
    have hiso : GGLabelIso labA labL :=
      hrigid labA labL (↥L ⧸ Subgroup.center ↥L) hΛA hΛL hhasL hhasL'
    exact ggLabelIso_not_of_tagA htagA (Or.inr htagL) hiso

end CFSG.StandardType

end
