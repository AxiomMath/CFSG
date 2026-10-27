module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepConjAssembly
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootGamma

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_corootPt_of_orth_left {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {a b : ↥Bs} (h : GGCorootOrth p A a b) :
    GGCorootPt p A a := by
  obtain ⟨_, φ, hφA, _, _, hφrefl, hφc, _⟩ := h
  refine ⟨?_, φ, hφA, hφrefl, hφc⟩
  rintro rfl
  have hfix : ∀ x : ↥Bs, φ x = x := by
    intro x
    have hx := hφc x
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
    exact mul_inv_eq_one.mp hx
  have hcard : Nat.card {x : ↥Bs // φ x = x} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun x : ↥Bs => hfix x))
  haveI : Nonempty ↥Bs := ⟨1⟩
  have hp1 : p = 1 := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := ↥Bs))
    calc Nat.card ↥Bs * p = Nat.card {x : ↥Bs // φ x = x} * p := by rw [hcard]
      _ = Nat.card ↥Bs := hφrefl.2
      _ = Nat.card ↥Bs * 1 := by rw [mul_one]
  have hp2 : 2 ≤ p := hp.two_le
  omega

private theorem ggTP_hasLabel_of_mulEquiv {lab : LargeEvenLabel} {R R' : Type} [Group R]
    [Group R'] (e : R ≃* R') (h : GGHasLabel lab R) : GGHasLabel lab R' := by
  unfold GGHasLabel at h ⊢
  refine largeEvenRawDatum_mono ?_ h
  rintro R'' _ I F ⟨f⟩
  exact ⟨e.symm.trans f⟩

theorem ggTPJLabel_of_coroot {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hJL : GGTPJLayerInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagOn Bs L)
    (hcardBs : Nat.card Bs = 3 ^ 6) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L))
    {c₀ : Bs} (hcL : (c₀ : G) ∈ L) (hc₀ : GGCorootPt 3 (ggAutomizer L Bs) c₀)
    (hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({(c₀ : G)} : Set G)))
    {lab₀ : LargeEvenLabel} (hlab₀ : GGE6DepLabel lab₀)
    (hmL : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = lab₀)) :
    GGHasLabel (ggTPJLabel lab₀) (J ⧸ Subgroup.center J) ∧ ¬ 3 ∣ Nat.card (Subgroup.center J) ∧
      3 ∣ Nat.card J := by
  classical
  obtain ⟨hp, hBs, -, hLx, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  obtain ⟨lab, hlab, hhas, R₀, hGrp, I₀, F₀, θ₀, hlab_eq⟩ := largeEvenMarking_exists_hasLabel hmL
  rw [hlab_eq] at hlab hhas
  have hM := ggInnerDiagOn_relabel hRig hinn hlab hhas
  have hallL : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → (lab = lab₀) →
      LargeEvenLabelAll lab (fun R _ I _ => IsSimpleGroup R →
        (∃ a b : R, a * b ≠ b * a) → GGTPJLayer lab₀ R I) := by
    intro lab hlab hs
    have hlab0 : LargeEvenInLambda2 lab₀ := by
      rwa [hs] at hlab
    rw [hs]
    exact hJL lab₀ hlab₀ hlab0
  obtain ⟨hL, lab', hlab', hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab = lab₀) hallL
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw'
  simp only [] at hQ
  obtain ⟨hsimple, hna, θ, hP, hP'⟩ := hQ
  obtain ⟨hs, hBsN, hInd⟩ := hP
  have hJLraw : GGTPJLayer lab₀ R I := hP' hsimple hna
  have hkerB : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  have hkerG : (ggGamma L hBsN).ker =
      (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hkercard : Nat.card (ggGamma L hBsN).ker = 3 := by
    rw [hkerG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcfg.card_bstar_inf_centralizer_L
  have h1 : Nat.card (ggGamma L hBsN).range * 3 = 3 ^ 6 := by
    have h := TableB.card_range_mul_card_ker (ggGamma L hBsN)
    rw [hkercard] at h
    rw [h, hcardBs]
  have hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5 := by
    have h2 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
    rw [h2] at h1
    exact Nat.mul_right_cancel (by norm_num) h1
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range := le_of_eq hcard.symm
  have h33 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by rw [hcard]; norm_num
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN hInd hb
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hL θ hBsN hBsI hr h33
  have hxmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hkerB]; exact Subgroup.mem_zpowers x
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := hxmem.2
  have hxp : x ^ 3 = 1 := hBs.2 x hxmem.1
  have hxLz : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer (p := 3) (by norm_num) hxC hxp hZ
  let A := (ggGamma L hBsN).range
  let c : ↥A := (ggGamma L hBsN).rangeRestrict c₀
  have hc : GGCorootPt 3 (ggTorusAut A) c :=
    ggCorootPt_gamma (p := 3) Nat.prime_three (by norm_num) hBs hBsN hkerB hxLz hcL hc₀
  have hJ0 : IsComponentOf (J.comap L.subtype) (ggFix (ggGamma L hBsN c₀)) := by
    refine (isComponentOf_comap_of_injective L.subtype (Subgroup.subtype_injective L) ?_).1
    rw [map_ggFix_ggGamma L hBsN c₀]
    exact hJcomp
  obtain ⟨hlabelX, hZX, hJX⟩ :=
    hJLraw ↥L (ggQuotHom θ) A hTB hcard hZ c hc (J.comap L.subtype) hJ0
  have hJle : J ≤ L := le_trans hJcomp.1 inf_le_left
  let e : J.comap L.subtype ≃* J := Subgroup.subgroupOfEquivOfLe hJle
  have hcenter : Nat.card ↥(Subgroup.center (J.comap L.subtype)) =
      Nat.card ↥(Subgroup.center J) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have hcardX : Nat.card ↥(J.comap L.subtype) = Nat.card ↥J := Nat.card_congr e.toEquiv
  have e' : (J.comap L.subtype) ⧸ Subgroup.center (J.comap L.subtype) ≃*
      J ⧸ Subgroup.center J :=
    QuotientGroup.congr (Subgroup.center (J.comap L.subtype)) (Subgroup.center J) e
      (Subgroup.map_center_eq e)
  refine ⟨ggTP_hasLabel_of_mulEquiv e' hlabelX, ?_, ?_⟩
  · rw [← hcenter]; exact hZX
  · rw [← hcardX]; exact hJX

theorem ggTPJLabel_of_config {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hJL : GGTPJLayerInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagOn Bs L)
    {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K) (hE : GGE6DepPerpCfg 3 Bs L K)
    (hconj : GGE6DepConjSetting 3 Bs x y L) {lab₀ : LargeEvenLabel} (hlab₀ : GGE6DepLabel lab₀)
    (hmL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab = lab₀)) :
    GGHasLabel (ggTPJLabel lab₀) (↥J ⧸ Subgroup.center ↥J) ∧ ¬ 3 ∣ Nat.card (Subgroup.center ↥J) ∧
      3 ∣ Nat.card ↥J := by
  obtain ⟨hZ, _, g, x₁, y₁, w, hx₁, hy₁, hy, hw, hbody⟩ := hconj
  obtain ⟨_, _, _, _, _, _, hyL, _, _, horth2, _⟩ := hbody
  have hc : GGCorootPt 3 (ggAutomizer L Bs) (⟨y, hy⟩ : Bs) :=
    ggTP_corootPt_of_orth_left Nat.prime_three horth2
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hnbr.2.1, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  have hLx := hcfg.tableB_facts.2.2.2.1
  rw [hD, inf_centralizer_sup_zpowers hLx] at hJcomp
  exact ggTPJLabel_of_coroot hRig hJL hcfg hinn hE.2.1 hZ hyL hc hJcomp hlab₀ hmL

end CFSG.StandardType

end
