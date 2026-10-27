module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
public import CFSG.CGT.PushingUpLit.BHS6.SymLocalPerm
public import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore
public import CFSG.GH74.E2.DirectProd
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
public import CFSG.CGT.PushingUpLit.BHS6.NestedPerm
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes
public import CFSG.CGT.PushingUpLit.BHS6.SixEightGen
public import CFSG.CGT.PushingUpLit.CGT6.EmbDictXfer
public import CFSG.CGT.PushingUpLit.CGT6.EmbHol
public import CFSG.CGT.PushingUpLit.CGT6.EmbHyp
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.CGT.PushingUpLit.CGT6

private abbrev E7G : Type := ↥(adjointGroup .E7 (ZMod 2))

private instance finite_E7G :
    Finite E7G := by
  haveI : Finite (ModGL .E7 (ZMod 2)) := finite_modGL
  infer_instance

local instance e7RecogO2NeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

private theorem centralizer_subgroupOf_eq {H : Subgroup (ModGL .E7 (ZMod 2))}
    (hH : H ≤ adjointGroup .E7 (ZMod 2)) :
    Subgroup.centralizer (H.subgroupOf (adjointGroup .E7 (ZMod 2)) : Set E7G) =
      (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer (H : Set (ModGL .E7 (ZMod 2)))).subgroupOf
        (adjointGroup .E7 (ZMod 2)) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hH hy⟩ (Subgroup.mem_subgroupOf.2 hy))
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx.2 y (Subgroup.mem_subgroupOf.1 hy))

private theorem rootSpan_union {τ : Tag} {K : Type} [Field K]
    (S T : Set (Fin τ.rank → ℤ)) :
    rootSpan τ K (S ∪ T) = rootSpan τ K S ⊔ rootSpan τ K T := by
  simp only [rootSpan]
  exact iSup_union

private theorem rootSpan_pair {τ : Tag} {K : Type} [Field K]
    (a b : Fin τ.rank → ℤ) :
    rootSpan τ K ({a, b} : Set (Fin τ.rank → ℤ)) = rootSubgroup τ K a ⊔ rootSubgroup τ K b := by
  simp only [rootSpan]
  exact iSup_pair

private theorem overlapNodes_root_check :
    ∀ γ ∈ rootFinset .E7, γ 0 = 0 → γ 5 = 0 →
      γ = e7Alpha7 ∨ γ = -e7Alpha7 ∨
        (iform (highRoot .E7) γ = 0 ∧ iform e7Alpha7 γ = 0 ∧
          iform d6HighRoot γ = 0) := by
  decide +kernel

theorem parabolicRoots_overlapNodes_eq :
    parabolicRoots .E7 overlapNodes =
      ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)) ∪
        overlapRootsD4 .high .seven := by
  ext γ
  constructor
  · intro h
    rw [mem_parabolicRoots_overlapNodes] at h
    obtain ⟨hγ, h0, h5⟩ := h
    rcases overlapNodes_root_check γ (mem_rootFinset.2 hγ) h0 h5 with h | h | ⟨h1, h2, h3⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨⟨⟨hγ, h1⟩, ⟨hγ, h2⟩⟩, ⟨hγ, h3⟩⟩
  · intro h
    rw [mem_parabolicRoots_overlapNodes]
    rcases h with (h | h) | ⟨⟨hH, -⟩, hT⟩
    · subst h
      exact ⟨isRoot_single .E7 6, by simp [e7Alpha7], by simp [e7Alpha7]⟩
    · subst h
      exact ⟨isRoot_neg_single .E7 6, by simp [e7Alpha7], by simp [e7Alpha7]⟩
    · have hH' : iform (highRoot .E7) γ = 0 := hH.2
      have hT' : iform d6HighRoot γ = 0 := by
        have := hT.2
        rwa [thirdRoot_high_seven] at this
      refine ⟨hH.1, ?_, ?_⟩
      · rw [← iform_highRoot_E7 γ]; exact hH'
      · have h5 : γ 5 - γ 0 = 0 := by rw [← iform_d6HighRoot γ]; exact hT'
        have h0 : γ 0 = 0 := by rw [← iform_highRoot_E7 γ]; exact hH'
        omega

theorem overlapRootSpan_subgroupOf_eq_sup :
    (rootSpan .E7 (ZMod 2) (parabolicRoots .E7 overlapNodes)).subgroupOf
        (adjointGroup .E7 (ZMod 2)) = e7A1 ⊔ e7D4 := by
  unfold e7A1 e7D4
  rw [parabolicRoots_overlapNodes_eq, rootSpan_union, rootSpan_pair,
    Subgroup.subgroupOf_sup (sup_le (rootSubgroup_le_adjointGroup _)
      (rootSubgroup_le_adjointGroup _)) (rootSpan_le_adjointGroup' _)]
  rfl

private theorem subgroupOf_le_centralizer_subgroupOf' {τ : Tag} {K : Type} [Field K]
    {G : Subgroup (ModGL τ K)} {S T : Subgroup (ModGL τ K)}
    (h : S ≤ Subgroup.centralizer (T : Set (ModGL τ K))) :
    S.subgroupOf G ≤ Subgroup.centralizer (T.subgroupOf G : Set ↥G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hx))
    y (Subgroup.mem_subgroupOf.1 hy))

private theorem rootPair_alpha7_le_centralizer_overlapRootsD4 :
    rootSubgroup .E7 (ZMod 2) e7Alpha7 ⊔ rootSubgroup .E7 (ZMod 2) (-e7Alpha7) ≤
      Subgroup.centralizer
        (rootSpan .E7 (ZMod 2) (overlapRootsD4 .high .seven) :
          Set (ModGL .E7 (ZMod 2))) := by
  have hS : ∀ α ∈ overlapRootsD4 .high .seven, IsRoot .E7 α ∧ iform α e7Alpha7 = 0 := by
    intro α hα
    exact ⟨hα.1.1.1, by rw [iform_comm]; exact hα.1.2.2⟩
  have h := rootSpan_le_centralizer_rootPair_E7 (K := ZMod 2) (β := e7Alpha7)
    (S := overlapRootsD4 .high .seven) (isRoot_single .E7 6) hS
  simpa using (Subgroup.le_centralizer_iff.mp h)

theorem e7A1_commute_D4 :
    ∀ a ∈ e7A1, ∀ b ∈ e7D4, a * b = b * a := by
  intro a ha b hb
  have h := subgroupOf_le_centralizer_subgroupOf' (G := adjointGroup .E7 (ZMod 2))
    (S := rootSubgroup .E7 (ZMod 2) e7Alpha7 ⊔ rootSubgroup .E7 (ZMod 2) (-e7Alpha7))
    (T := rootSpan .E7 (ZMod 2) (overlapRootsD4 .high .seven))
    rootPair_alpha7_le_centralizer_overlapRootsD4
  exact (Subgroup.mem_centralizer_iff.1 (h ha) b hb).symm

private theorem pCore_eq_bot_of_odd_card {X : Type*} [Group X] [Finite X]
    (hX : Odd (Nat.card X)) : CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.eq_bot_iff_card]
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk0 : k = 0 := by
    by_contra h
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 h
    exact (Nat.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr (h2.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact hk

private theorem pCore_zpowers_eq_bot
    {r : E7G} (hr3 : orderOf r = 3) :
    CFSG.pCore 2 ↥(Subgroup.zpowers r) = ⊥ := by
  refine pCore_eq_bot_of_odd_card ?_
  rw [Nat.card_zpowers, hr3]
  norm_num

noncomputable def e7A1EquivPerm3 :
    ↥e7A1 ≃* Equiv.Perm (Fin 3) :=
  Classical.choice (by
    obtain ⟨eSL, -⟩ :=
      (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E7 (ZMod 2)
        (isRoot_single .E7 6)).2.2.1
    obtain ⟨ePerm⟩ :=
      nonempty_mulEquiv_perm_three_of_card_two (K := ZMod 2) (by norm_num)
    have hle : (rootSubgroup .E7 (ZMod 2) e7Alpha7 ⊔
        rootSubgroup .E7 (ZMod 2) (-e7Alpha7)) ≤ adjointGroup .E7 (ZMod 2) :=
      sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)
    exact ⟨((eSL.trans (Subgroup.subgroupOfEquivOfLe hle).symm).symm).trans ePerm⟩)

private theorem pCore_e7A1_eq_bot :
    CFSG.pCore 2 ↥e7A1 = ⊥ :=
  pCore_eq_bot_of_equiv e7A1EquivPerm3
    (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_perm_eq_bot
      (Or.inr (Or.inl rfl)))

private theorem center_e7A1_eq_bot :
    Subgroup.center ↥e7A1 = ⊥ := by
  have hZ : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hne
    obtain ⟨ρ, hρ⟩ := CFSG.CGT.PushingUpLit.BHS6.exists_noncommute_perm_three σ hne
    refine hρ ?_
    have hcomm := Subgroup.mem_center_iff.1 hσ ρ
    calc ρ * σ * ρ⁻¹ = (σ * ρ) * ρ⁻¹ := by rw [hcomm]
      _ = σ := by group
  have hmap := Subgroup.map_center_eq e7A1EquivPerm3
  rw [hZ] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥e7A1)
    e7A1EquivPerm3.injective).1 hmap

private theorem pCore_e7D4_eq_bot :
    CFSG.pCore 2 ↥e7D4 = ⊥ := by
  have hS : IsSimpleGroup ↥e7D4 :=
    isSimpleGroup_overlapSpanD4 (K := ZMod 2) (by decide)
  haveI := hS
  refine pCore_eq_bot_of_simple ?_
  intro hP
  have hcent : Nontrivial ↥(Subgroup.center ↥e7D4) := hP.center_nontrivial
  change Nontrivial ↥(Subgroup.center ↥(overlapSpanD4 (ZMod 2) .high .seven)) at hcent
  rw [center_overlapSpanD4_eq_bot (K := ZMod 2) (by decide)] at hcent
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hcent rfl

private theorem pCore_sup_eq_bot {H K : Subgroup E7G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hdisj : H ⊓ K = ⊥)
    (hH : CFSG.pCore 2 ↥H = ⊥) (hK : CFSG.pCore 2 ↥K = ⊥) :
    CFSG.pCore 2 ↥(H ⊔ K) = ⊥ :=
  pCore_eq_bot_of_equiv (CFSG.GH74.E2.prodSupEquiv H K hcomm hdisj).symm
    (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_prod_eq_bot hH hK)

theorem e7JThetaD6_le_perpLevi :
    e7JThetaD6 ≤ perpLevi .E7 (ZMod 2) := by
  unfold e7JThetaD6 perpLevi
  refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
  · exact le_iSup₂ (f := fun α (_ : α ∈ perpRoots .E7) => rootSubgroup .E7 (ZMod 2) α)
      d6HighRoot ((mem_perpRoots_iff_iform (Or.inr (Or.inl rfl))).2
        ⟨isRoot_d6HighRoot, iform_highRoot_d6HighRoot⟩)
  · exact le_iSup₂ (f := fun α (_ : α ∈ perpRoots .E7) => rootSubgroup .E7 (ZMod 2) α)
      (-d6HighRoot) ((mem_perpRoots_iff_iform (Or.inr (Or.inl rfl))).2
        ⟨IsRoot.neg isRoot_d6HighRoot,
          by rw [iform_neg_right, iform_highRoot_d6HighRoot, neg_zero]⟩)

private theorem subgroupOf_inf' {M : Type*} [Group M] {G H₁ H₂ : Subgroup M}
    (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁.subgroupOf G ⊓ H₂.subgroupOf G = (H₁ ⊓ H₂).subgroupOf G := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]

private theorem centralizer_zpowers_eq (r : E7G) :
    Subgroup.centralizer (Subgroup.zpowers r : Set E7G) =
      Subgroup.centralizer ({r} : Set E7G) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hx r (Subgroup.mem_zpowers r)
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute r x from hx r (Set.mem_singleton r)) k).eq

private theorem centralizer_eq_sup_of_mem_JThetaD6
    {g : E7G} (hg : e7JTheta.map (MulAut.conj g).toMonoidHom = e7JThetaD6)
    {r : E7G} (hr : r ∈ e7JThetaD6) (hr3 : orderOf r = 3) :
    Subgroup.centralizer ({r} : Set E7G) =
      Subgroup.zpowers r ⊔ (perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom := by
  classical
  let s : E7G := (MulAut.conj g).symm r
  have hr' : r ∈ e7JTheta.map (MulAut.conj g).toMonoidHom := by rwa [hg]
  have hsJ : s ∈ e7JTheta := by
    simpa [s] using (Subgroup.mem_map_equiv.mp hr')
  have hgs : (MulAut.conj g) s = r := (MulAut.conj g).apply_symm_apply r
  have hgs' : (MulEquiv.toMonoidHom (MulAut.conj g)) s = r := hgs
  have hs3 : orderOf s = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) s
    rw [hgs, hr3] at h
    exact h.symm
  let X : Subgroup E7G := Subgroup.zpowers s
  have hXJ : X ≤ e7JTheta := Subgroup.zpowers_le.2 hsJ
  have hXcard : Nat.card X = Nat.card (ZMod 2) + 1 := by
    rw [Nat.card_zpowers, hs3]
    norm_num [ZMod.card]
  have hcyc : IsCyclic X := Subgroup.isCyclic_zpowers s
  obtain ⟨hcen, -, -⟩ := centralizer_nonsplit_E7_of_finite (K := ZMod 2) hXJ hXcard hcyc
  have hmap := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcen
  rw [CFSG.SeitzReduction.F4Pilot.map_centralizer_mulEquiv] at hmap
  have hXmap : X.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers r := by
    rw [show X = Subgroup.zpowers s from rfl, MonoidHom.map_zpowers, hgs']
  rw [Subgroup.map_sup, hXmap] at hmap
  rw [centralizer_zpowers_eq r] at hmap
  exact hmap

private theorem centralizer_inf_perpLevi_eq_sup
    {g : E7G} (hg : e7JTheta.map (MulAut.conj g).toMonoidHom = e7JThetaD6)
    {r : E7G} (hr : r ∈ e7JThetaD6) (hr3 : orderOf r = 3) :
    perpLevi .E7 (ZMod 2) ⊓ Subgroup.centralizer ({r} : Set E7G) =
      Subgroup.zpowers r ⊔ (perpLevi .E7 (ZMod 2) ⊓
        (perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom) := by
  have hcen := centralizer_eq_sup_of_mem_JThetaD6 hg hr hr3
  have hrD : r ∈ perpLevi .E7 (ZMod 2) := e7JThetaD6_le_perpLevi hr
  have hzrD : Subgroup.zpowers r ≤ perpLevi .E7 (ZMod 2) := Subgroup.zpowers_le.2 hrD
  have hCJ' : (perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (e7JThetaD6 : Set E7G) := by
    rw [← centralizer_highRootSL2_subgroupOf_E7_of_charTwo,
      CFSG.SeitzReduction.F4Pilot.map_centralizer_mulEquiv, hg]
  have hcomm : Subgroup.zpowers r ≤ Subgroup.normalizer
      ((perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom : Set E7G) := by
    rw [hCJ']
    refine (Subgroup.zpowers_le.2 ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 hy r hr).symm
  rw [hcen]
  exact CFSG.SeitzReduction.E7Pilot.inf_sup_eq_sup_inf_of_le hzrD hcomm

private theorem adjointGroup_inf_centralizer_highRootSL2_inf_eq :
    (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (highRootSL2 .E7 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))) ⊓
      (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (d6HighRootSL2 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))) =
      rootSpan .E7 (ZMod 2) (parabolicRoots .E7 overlapNodes) := by
  have h : (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (highRootSL2 .E7 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))) ⊓
      (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (d6HighRootSL2 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))) =
      (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (highRootSL2 .E7 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))) ⊓
        Subgroup.centralizer (d6HighRootSL2 (ZMod 2) : Set (ModGL .E7 (ZMod 2))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hG, hH⟩, -, hH'⟩
      exact ⟨⟨hG, hH⟩, hH'⟩
    · rintro ⟨⟨hG, hH⟩, hH'⟩
      exact ⟨⟨hG, hH⟩, hG, hH'⟩
  rw [h]
  exact adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_d6HighRootSL2
    (K := ZMod 2) (fun u => Subsingleton.elim u 1)

private theorem perpLevi_eq_subgroupOf_centralizer :
    perpLevi .E7 (ZMod 2) =
      (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (highRootSL2 .E7 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))).subgroupOf
          (adjointGroup .E7 (ZMod 2)) := by
  rw [← centralizer_highRootSL2_subgroupOf_E7_of_charTwo]
  exact centralizer_subgroupOf_eq highRootSL2_le_adjointGroup

private theorem map_perpLevi_eq_subgroupOf_centralizer
    {g : E7G} (hg : e7JTheta.map (MulAut.conj g).toMonoidHom = e7JThetaD6) :
    (perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom =
      (adjointGroup .E7 (ZMod 2) ⊓ Subgroup.centralizer
        (d6HighRootSL2 (ZMod 2) : Set (ModGL .E7 (ZMod 2)))).subgroupOf
          (adjointGroup .E7 (ZMod 2)) := by
  have h1 : (perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (e7JThetaD6 : Set E7G) := by
    rw [← centralizer_highRootSL2_subgroupOf_E7_of_charTwo,
      CFSG.SeitzReduction.F4Pilot.map_centralizer_mulEquiv, hg]
  rw [h1]
  exact centralizer_subgroupOf_eq (sup_le (rootSubgroup_le_adjointGroup _)
    (rootSubgroup_le_adjointGroup _))

private theorem inf_perpLevi_map_eq_rootSpan
    {g : E7G} (hg : e7JTheta.map (MulAut.conj g).toMonoidHom = e7JThetaD6) :
    perpLevi .E7 (ZMod 2) ⊓ (perpLevi .E7 (ZMod 2)).map (MulAut.conj g).toMonoidHom =
      (rootSpan .E7 (ZMod 2) (parabolicRoots .E7 overlapNodes)).subgroupOf
        (adjointGroup .E7 (ZMod 2)) := by
  rw [map_perpLevi_eq_subgroupOf_centralizer hg, perpLevi_eq_subgroupOf_centralizer,
    subgroupOf_inf' inf_le_left inf_le_left,
    adjointGroup_inf_centralizer_highRootSL2_inf_eq]

private theorem e7A1_le_centralizer_JThetaD6 :
    e7A1 ≤ Subgroup.centralizer (e7JThetaD6 : Set E7G) := by
  have hS : ∀ α ∈ ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)),
      IsRoot .E7 α ∧ iform α d6HighRoot = 0 := by
    intro α hα
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl
    · exact ⟨isRoot_single .E7 6, by rw [iform_comm, iform_d6HighRoot]; simp⟩
    · exact ⟨isRoot_neg_single .E7 6, by rw [iform_comm, iform_d6HighRoot]; simp⟩
  have h := rootSpan_le_centralizer_rootPair_E7 (K := ZMod 2) (β := d6HighRoot)
    (S := {e7Alpha7, -e7Alpha7}) isRoot_d6HighRoot hS
  rw [rootSpan_pair] at h
  exact subgroupOf_le_centralizer_subgroupOf' h

private theorem e7D4_le_centralizer_JThetaD6 :
    e7D4 ≤ Subgroup.centralizer (e7JThetaD6 : Set E7G) := by
  have hmod : rootSpan .E7 (ZMod 2) (overlapRootsD4 .high .seven) ≤
      Subgroup.centralizer (d6HighRootSL2 (ZMod 2) : Set (ModGL .E7 (ZMod 2))) := by
    refine rootSpan_le_centralizer_rootPair_E7 (K := ZMod 2) isRoot_d6HighRoot ?_
    intro α hα
    exact ⟨hα.1.1.1, by rw [iform_comm]; exact hα.2.2⟩
  exact subgroupOf_le_centralizer_subgroupOf' hmod

private theorem commute_zpowers_of_commute {x y z : E7G} (h : y * x = x * y)
    (hz : z ∈ Subgroup.zpowers x) : z * y = y * z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_left (show Commute x y from h.symm) k).eq

private theorem center_e7D4_eq_bot :
    Subgroup.center ↥e7D4 = ⊥ := by
  change Subgroup.center ↥(overlapSpanD4 (ZMod 2) .high .seven) = ⊥
  exact center_overlapSpanD4_eq_bot (K := ZMod 2) (by decide)

private theorem e7D4_le_centralizer_zpowers
    {r : E7G} (hr : r ∈ e7JThetaD6) :
    e7D4 ≤ Subgroup.centralizer (Subgroup.zpowers r : Set E7G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hbJ : b ∈ Subgroup.centralizer (e7JThetaD6 : Set E7G) :=
    e7D4_le_centralizer_JThetaD6 hb
  have hbr : b * r = r * b := (Subgroup.mem_centralizer_iff.1 hbJ r hr).symm
  exact commute_zpowers_of_commute hbr hx

private theorem pCore_sup_zpowers_e7A1_eq_bot
    {r : E7G} (hr : r ∈ e7JThetaD6) (hr3 : orderOf r = 3) :
    CFSG.pCore 2 ↥(Subgroup.zpowers r ⊔ e7A1) = ⊥ := by
  refine pCore_sup_eq_bot ?_ ?_ (pCore_zpowers_eq_bot hr3) (pCore_e7A1_eq_bot)
  · intro a ha b hb
    have hbJ : b ∈ Subgroup.centralizer (e7JThetaD6 : Set E7G) :=
      e7A1_le_centralizer_JThetaD6 hb
    have hbr : b * r = r * b := (Subgroup.mem_centralizer_iff.1 hbJ r hr).symm
    exact commute_zpowers_of_commute hbr ha
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxr, hxA⟩ := Subgroup.mem_inf.1 hx
    have hxZ : (⟨x, hxA⟩ : ↥e7A1) ∈ Subgroup.center ↥e7A1 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyJ : (y : E7G) ∈ Subgroup.centralizer (e7JThetaD6 : Set E7G) :=
        e7A1_le_centralizer_JThetaD6 (x := (y : E7G)) y.property
      have hyr : (y : E7G) * r = r * (y : E7G) :=
        (Subgroup.mem_centralizer_iff.1 hyJ r hr).symm
      exact Subtype.ext (commute_zpowers_of_commute (x := r) (y := (y : E7G))
        (z := (x : E7G)) hyr hxr).symm
    rw [center_e7A1_eq_bot] at hxZ
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hxZ)

private theorem e7A1_sup_zpowers_le_centralizer_D4
    {r : E7G} (hr : r ∈ e7JThetaD6) :
    Subgroup.zpowers r ⊔ e7A1 ≤ Subgroup.centralizer (e7D4 : Set E7G) := by
  refine sup_le (Subgroup.le_centralizer_iff.mp (e7D4_le_centralizer_zpowers hr)) ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (e7A1_commute_D4 a ha b hb).symm

private theorem e7A1_sup_zpowers_commute_D4
    {r : E7G} (hr : r ∈ e7JThetaD6) :
    ∀ a ∈ Subgroup.zpowers r ⊔ e7A1, ∀ b ∈ e7D4, a * b = b * a := by
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1
    (e7A1_sup_zpowers_le_centralizer_D4 hr ha) b hb).symm

private theorem e7A1_sup_zpowers_disjoint_D4
    {r : E7G} (hr : r ∈ e7JThetaD6) :
    (Subgroup.zpowers r ⊔ e7A1) ⊓ e7D4 = ⊥ := by
  have hcent := e7A1_sup_zpowers_le_centralizer_D4 hr
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxB, hxD⟩ := Subgroup.mem_inf.1 hx
  have hxZ : (⟨x, hxD⟩ : ↥e7D4) ∈ Subgroup.center ↥e7D4 := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hcent hxB) (y : E7G) y.2)
  rw [center_e7D4_eq_bot] at hxZ
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hxZ)

private theorem pCore_centralizer_inf_eq_bot
    {g : E7G} (hg : e7JTheta.map (MulAut.conj g).toMonoidHom = e7JThetaD6)
    {r : E7G} (hr : r ∈ e7JThetaD6) (hr3 : orderOf r = 3) :
    CFSG.pCore 2 ↥(perpLevi .E7 (ZMod 2) ⊓
      Subgroup.centralizer ({r} : Set E7G)) = ⊥ := by
  have hCD := centralizer_inf_perpLevi_eq_sup hg hr hr3
  have hU := inf_perpLevi_map_eq_rootSpan hg
  have hUdec := overlapRootSpan_subgroupOf_eq_sup
  rw [hCD, hU]
  change CFSG.pCore 2 ↥(Subgroup.zpowers r ⊔
    (rootSpan .E7 (ZMod 2) (parabolicRoots .E7 overlapNodes)).subgroupOf
      (adjointGroup .E7 (ZMod 2))) = ⊥
  rw [hUdec]
  have hsup := pCore_sup_eq_bot (e7A1_sup_zpowers_commute_D4 hr)
    (e7A1_sup_zpowers_disjoint_D4 hr) (pCore_sup_zpowers_e7A1_eq_bot hr hr3)
    pCore_e7D4_eq_bot
  rw [sup_assoc] at hsup
  exact hsup

private theorem e7M_le_centralizer
    {N Q D : Subgroup E7G} {r : E7G}
    (hC : Q ⊔ D = Subgroup.centralizer ({e7HighInv} : Set E7G))
    (hdisj : Q ⊓ D = ⊥) (hDQ : D ≤ Subgroup.normalizer (Q : Set E7G))
    (hrD : r ∈ D)
    (hNle : N ≤ Subgroup.centralizer ({r} : Set E7G) ⊓
      Subgroup.centralizer ({e7HighInv} : Set E7G))
    (hNQ : N ≤ Subgroup.normalizer (Q : Set E7G)) :
    (N ⊔ Q) ⊓ D ≤ D ⊓ Subgroup.centralizer ({r} : Set E7G) := by
  intro x hx
  obtain ⟨hxNQ, hxD⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hxD, ?_⟩
  have hxQN : x ∈ ((Q ⊔ N : Subgroup E7G) : Set E7G) := by rw [sup_comm]; exact hxNQ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q N hNQ] at hxQN
  rw [Set.mem_mul] at hxQN
  obtain ⟨q, hqQ, n, hnN, hqn⟩ := hxQN
  have hnC : n * r = r * n :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hNle hnN)).1 r
      (Set.mem_singleton r)).symm
  have hcomm_n : r * n * r⁻¹ * n⁻¹ = 1 := by
    calc r * n * r⁻¹ * n⁻¹ = n * r * r⁻¹ * n⁻¹ := by rw [hnC]
      _ = 1 := by group
  have hrCt : r ∈ Subgroup.centralizer ({e7HighInv} : Set E7G) := by
    rw [← hC]; exact Subgroup.mem_sup_right hrD
  have hCtNQ : Subgroup.centralizer ({e7HighInv} : Set E7G) ≤
      Subgroup.normalizer (Q : Set E7G) := by
    rw [← hC]; exact sup_le Subgroup.le_normalizer hDQ
  have hqQ' : r * q * r⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.1 (hCtNQ hrCt) q).1 hqQ
  have hcomm_q : r * q * r⁻¹ * q⁻¹ ∈ Q := Q.mul_mem hqQ' (Q.inv_mem hqQ)
  have hkey : r * x * r⁻¹ * x⁻¹ = r * q * r⁻¹ * q⁻¹ := by
    rw [← hqn]
    calc r * (q * n) * r⁻¹ * (q * n)⁻¹
        = (r * q * r⁻¹ * q⁻¹) * (q * (r * n * r⁻¹ * n⁻¹) * q⁻¹) := by group
      _ = r * q * r⁻¹ * q⁻¹ := by rw [hcomm_n]; group
  have hQx : r * x * r⁻¹ * x⁻¹ ∈ Q := hkey ▸ hcomm_q
  have hDx : r * x * r⁻¹ * x⁻¹ ∈ D := by
    have h1 : r * x ∈ D := D.mul_mem hrD hxD
    have h2 : (r * x) * r⁻¹ ∈ D := D.mul_mem h1 (D.inv_mem hrD)
    exact D.mul_mem h2 (D.inv_mem hxD)
  have h1 : r * x * r⁻¹ * x⁻¹ = 1 := by
    have hmem : r * x * r⁻¹ * x⁻¹ ∈ Q ⊓ D := Subgroup.mem_inf.2 ⟨hQx, hDx⟩
    rwa [hdisj, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst h
  calc r * x = (r * x * r⁻¹ * x⁻¹) * (x * r) := by group
    _ = 1 * (x * r) := by rw [h1]
    _ = x * r := by group

private theorem e7M_normal
    {N Q D : Subgroup E7G} {r : E7G}
    (hC : Q ⊔ D = Subgroup.centralizer ({e7HighInv} : Set E7G))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set E7G))
    (hNnorm : Subgroup.centralizer ({r} : Set E7G) ⊓
      Subgroup.centralizer ({e7HighInv} : Set E7G) ≤ Subgroup.normalizer (N : Set E7G)) :
    ∀ c ∈ D ⊓ Subgroup.centralizer ({r} : Set E7G), ∀ x ∈ (N ⊔ Q) ⊓ D,
      c * x * c⁻¹ ∈ (N ⊔ Q) ⊓ D := by
  intro c hc x hx
  obtain ⟨hcD, hcCr⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hxNQ, hxD⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hcCt : c ∈ Subgroup.centralizer ({e7HighInv} : Set E7G) := by
      rw [← hC]; exact Subgroup.mem_sup_right hcD
    have hcN : c ∈ Subgroup.normalizer (N : Set E7G) :=
      hNnorm (Subgroup.mem_inf.2 ⟨hcCr, hcCt⟩)
    have hcQ : c ∈ Subgroup.normalizer (Q : Set E7G) := hDQ hcD
    have hcsup : c ∈ Subgroup.normalizer ((N ⊔ Q : Subgroup E7G) : Set E7G) :=
      Subgroup.inf_normalizer_le_normalizer_sup (H := N) (K := Q) ⟨hcN, hcQ⟩
    exact (Subgroup.mem_normalizer_iff.1 hcsup x).1 hxNQ
  · exact D.mul_mem (D.mul_mem hcD hxD) (D.inv_mem hcD)

private theorem e7N_le_Q
    {N Q D : Subgroup E7G} {n : E7G}
    (hC : Q ⊔ D = Subgroup.centralizer ({e7HighInv} : Set E7G))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set E7G))
    (hnCD : n ∈ ((Q ⊔ D : Subgroup E7G) : Set E7G)) (hnN : n ∈ N)
    (hMbot : (N ⊔ Q) ⊓ D = ⊥) : n ∈ Q := by
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q D hDQ] at hnCD
  rw [Set.mem_mul] at hnCD
  obtain ⟨q, hqQ, d, hdD, hqdn⟩ := hnCD
  have hdM : d ∈ (N ⊔ Q) ⊓ D := by
    refine Subgroup.mem_inf.2 ⟨?_, hdD⟩
    have hd : d = q⁻¹ * n := by rw [← hqdn]; group
    rw [hd]
    exact (N ⊔ Q).mul_mem (Subgroup.mem_sup_right (Q.inv_mem hqQ)) (Subgroup.mem_sup_left hnN)
  rw [hMbot, Subgroup.mem_bot] at hdM
  rw [← hqdn, hdM, mul_one]
  exact hqQ

private theorem e7M_eq_bot_of_subgroupOf_eq_bot {N Q D : Subgroup E7G} {r : E7G}
    (hM_le_C : (N ⊔ Q) ⊓ D ≤ D ⊓ Subgroup.centralizer ({r} : Set E7G))
    (hMsub : ((N ⊔ Q) ⊓ D).subgroupOf (D ⊓ Subgroup.centralizer ({r} : Set E7G)) = ⊥) :
    (N ⊔ Q) ⊓ D = ⊥ := by
  have hdisjMC : Disjoint ((N ⊔ Q) ⊓ D) (D ⊓ Subgroup.centralizer ({r} : Set E7G)) :=
    Subgroup.subgroupOf_eq_bot.mp hMsub
  have hinf : ((N ⊔ Q) ⊓ D) ⊓ (D ⊓ Subgroup.centralizer ({r} : Set E7G)) = ⊥ :=
    disjoint_iff.mp hdisjMC
  rwa [inf_eq_left.mpr hM_le_C] at hinf

theorem e7ModelO2_of_conj
    (hConj : E7ModelConj) : E7ModelO2 := by
  intro r hr hr3 N hN2 hNle hNnorm
  classical
  obtain ⟨g, hg⟩ := hConj
  set Q : Subgroup E7G := highRadical .E7 (ZMod 2)
  set D : Subgroup E7G := perpLevi .E7 (ZMod 2)
  obtain ⟨hQ2, hC, hdisj, hDQ⟩ :=
    isTwoRadicalDecomp_highRoot (K := ZMod 2) (Or.inr (Or.inl rfl)) one_ne_zero
  set C0 : Subgroup E7G := Subgroup.centralizer ({r} : Set E7G) ⊓
    Subgroup.centralizer ({e7HighInv} : Set E7G)
  have hNQ : N ≤ Subgroup.normalizer (Q : Set E7G) := by
    have hC0CD : C0 ≤ Q ⊔ D := by
      rw [hC]; exact inf_le_right
    exact hNle.trans (hC0CD.trans (sup_le Subgroup.le_normalizer hDQ))
  set M : Subgroup E7G := (N ⊔ Q) ⊓ D
  have hM_le_C : M ≤ D ⊓ Subgroup.centralizer ({r} : Set E7G) :=
    e7M_le_centralizer hC hdisj hDQ (e7JThetaD6_le_perpLevi hr) hNle hNQ
  have hM2 : IsPGroup 2 M :=
    (IsPGroup.to_sup_of_normal_right' hN2 hQ2 hNQ).to_le inf_le_left
  have hMnorm : ∀ c ∈ D ⊓ Subgroup.centralizer ({r} : Set E7G), ∀ x ∈ M,
      c * x * c⁻¹ ∈ M := e7M_normal hC hDQ hNnorm
  have hMnormal : (M.subgroupOf (D ⊓ Subgroup.centralizer ({r} : Set E7G))).Normal :=
    ⟨fun x hx c => hMnorm c c.2 x hx⟩
  have hM2' : IsPGroup 2 ↥(M.subgroupOf
      (D ⊓ Subgroup.centralizer ({r} : Set E7G))) :=
    hM2.of_equiv (Subgroup.subgroupOfEquivOfLe hM_le_C).symm
  have hcore : M.subgroupOf (D ⊓ Subgroup.centralizer ({r} : Set E7G)) ≤
      CFSG.pCore 2 ↥(D ⊓ Subgroup.centralizer ({r} : Set E7G)) :=
    CFSG.LieType.BorelTits.le_pCore 2 hMnormal hM2'
  rw [pCore_centralizer_inf_eq_bot hg hr hr3] at hcore
  have hMsub : M.subgroupOf (D ⊓ Subgroup.centralizer ({r} : Set E7G)) = ⊥ :=
    le_bot_iff.1 hcore
  have hMbot : M = ⊥ :=
    e7M_eq_bot_of_subgroupOf_eq_bot hM_le_C hMsub
  intro n hnN
  exact e7N_le_Q hC hDQ (by
    rw [hC]
    exact (Subgroup.mem_inf.1 (hNle hnN)).2) hnN hMbot

end CFSG.StandardType.FrameRoute.FS81
