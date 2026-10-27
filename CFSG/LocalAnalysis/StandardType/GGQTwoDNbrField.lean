module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerGrp
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem qtwoDNbr_jlabel_unit {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hKcard : Nat.card K = 4) (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n))
    (hrange : ψ.range = L) (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ Bs) :
    ∃ t : ℕ, 4 ≤ t ∧ LieModel (↥J ⧸ Subgroup.center ↥J) .PSU t 2 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hKcard]; norm_num
  obtain ⟨y, hy, hyx, -, hJy⟩ := qTwoNbrA_exists_y hcfg.1 hcfg.2.1 hcfg.2.2
  have hψL : ∀ s : Su K 2 1 n, ψ s ∈ L := fun s => hrange ▸ ⟨s, rfl⟩
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := by
    intro b hb
    refine ggNSPosPF3C_mem_normalizer_of_conj_mem fun l hl => ?_
    obtain ⟨s, rfl⟩ : l ∈ ψ.range := hrange ▸ hl
    obtain ⟨g, -, hg⟩ := hdiag b hb
    obtain ⟨s', -, hs'⟩ := hg.2 s
    exact hs' ▸ hψL s'
  let πSU : Su K 2 1 n →* ↥L := ψ.codRestrict L hψL
  have hπ_surj : Function.Surjective πSU := by
    intro l
    obtain ⟨s, hs⟩ : (l : G) ∈ ψ.range := hrange ▸ l.2
    exact ⟨s, Subtype.ext hs⟩
  have hπ_ker : πSU.ker ≤ Subgroup.center (Su K 2 1 n) := by
    intro s hs
    apply hker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact congrArg Subtype.val hs
  let c : ↥L →* ↥L := MonoidHom.id _
  have hc_surj : Function.Surjective c := Function.surjective_id
  have hc_ker : c.ker ≤ Subgroup.center ↥L := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [show z = 1 from hz]
    exact Subgroup.one_mem _
  let ρ : ↥Bs →* MulAut ↥L := ggGamma L hN
  have hρ : ∀ (b : ↥Bs) (l : ↥L), c (ggGamma L hN b l) = ρ b (c l) := fun _ _ => rfl
  have hne := qTwoNbrA_rho_ne_one hcfg.1 hcfg.2.1 hN c hc_surj hc_ker ρ hρ hy hyx
  have hM := qTwoNbrA_image_isComponentOf hN c hc_surj hc_ker ρ hρ hy hJy
  have hdg : ∃ g : GL (Fin n) K, ggIsDiagMat g ∧ ∀ u : Su K 2 1 n, ∃ u' : Su K 2 1 n,
      (u' : GL (Fin n) K) = g * (u : GL (Fin n) K) * g⁻¹ ∧ ρ ⟨y, hy⟩ (πSU u) = πSU u' := by
    obtain ⟨g, hgd, hgi⟩ := hdiag y hy
    refine ⟨g, hgd, fun u => ?_⟩
    obtain ⟨u', hu'mat, hu'act⟩ := hgi.2 u
    refine ⟨u', hu'mat, Subtype.ext ?_⟩
    change y * ψ u * y⁻¹ = ψ u'
    exact hu'act
  obtain ⟨t, δ, ht, hδ, hφδ⟩ := qTwoNbrA_diag_aut hF πSU hdg
  set φ := πSU.comp (qTwoNbrRec_suEquiv hF n).symm.toMonoidHom with hφ
  have hφsurj : Function.Surjective φ :=
    hπ_surj.comp (qTwoNbrRec_suEquiv hF n).symm.surjective
  have hφker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K n) := by
    intro z hz
    have h1 : (qTwoNbrRec_suEquiv hF n).symm z ∈ πSU.ker := hz
    have h2 := hπ_ker h1
    have h3 : z ∈ (Subgroup.center (Su K 2 1 n)).map
        (qTwoNbrRec_suEquiv hF n).toMonoidHom :=
      ⟨_, h2, by simp⟩
    rwa [show (Subgroup.center (Su K 2 1 n)).map (qTwoNbrRec_suEquiv hF n).toMonoidHom =
        Subgroup.center ↥(unitarySU 2 1 K n) from
      Subgroup.map_center_eq (qTwoNbrRec_suEquiv hF n)] at h3
  obtain ⟨S, hS4, hSm, hMS⟩ := qTwoNbrA_block_of_diag hF φ hφsurj hφker hne ht hδ hφδ hM
  obtain ⟨hLie, -⟩ := qTwoNbrA_block_model hF φ hφker hS4 hSm
  rw [← hMS] at hLie
  have hJL : J ≤ L := hJy.1.trans inf_le_left
  obtain ⟨⟨e⟩, -⟩ := qTwoNbrA_center_quot_of_component hJL c hc_ker hJy
  exact ⟨S.card, hS4, LieModel.of_mulEquiv e.symm hLie⟩

theorem qtwoDNbr_jlabel (hOJ : GGQTwoDOrthJInput) {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hchart : QTwoDL1Chart 3 B Bs L) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
        (labJ.tag = .twD → labJ.rank ≠ 2) := by
  rcases hchart with ⟨K, hKf, hKfin, hKchar, n, ψ, hKcard, hloc, hrange, hdiag, -⟩ | ⟨Φ, hF, h5, hZ⟩
  · obtain ⟨t, ht, hJ⟩ := qtwoDNbr_jlabel_unit hcfg.1.1 hKcard hloc.ker hrange hdiag
    refine ⟨⟨.twA, t - 1, 1⟩, ?_, qTwoNbrA_hasLabel_of_lieModel ht hJ, rfl,
      by show LargeEvenLieTag.twA ≠ LargeEvenLieTag.A; decide,
      fun h => absurd h (by show ¬ LargeEvenLieTag.twA = LargeEvenLieTag.twD; decide)⟩
    refine ⟨le_refl 1, ?_, ?_⟩
    · change 2 ≤ t - 1
      omega
    · intro h
      change t - 1 = 2 at h
      omega
  · exact hOJ G 3 B Bs x L D J 𝒦 hcfg Φ hF h5 hZ

theorem qtwoDNbr_field (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) {B Bs L D J : Subgroup G}
    {x : G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) (hJX : J ≤ X) (hInn : GGInnerDiagOn Bs X)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (hn : labJ.n = 1) (htag : labJ.tag ≠ .A)
    (htwD : labJ.tag = .twD → labJ.rank ≠ 2) :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n = 1 := by
  intro lab hΛ hhas
  obtain ⟨labJ', hΛJ', hdvd, hhasJ'⟩ :=
    qTwoNbrA_tcj_nbr hTCJ hRig hcfg hnbr hJX hInn hΛ hhas
  have hiso : GGLabelIso labJ labJ' := hRig labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ'
  have h1 : labJ.n = labJ'.n := NSJoin.ggLabelIso_n_eq hiso htag htwD
  rw [← h1, hn] at hdvd
  exact Nat.dvd_one.mp hdvd

section Split


theorem qtwoDNbr_nonSplit {X : Subgroup G}
    (hfield : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n = 1) : ¬ GGSplitLie 3 X := by
  intro hs
  obtain ⟨lab, hΛ, hhas, hdvd⟩ := ggSplitLie_label Nat.prime_three (by norm_num) hs
  rw [hfield lab hΛ hhas] at hdvd
  norm_num at hdvd

end Split

end CFSG.StandardType.QTwo

end
