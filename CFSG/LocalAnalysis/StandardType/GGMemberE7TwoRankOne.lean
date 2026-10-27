module

public import CFSG.LocalAnalysis.StandardType.GGMemberE7TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidInduced
public import CFSG.LocalAnalysis.StandardType.GGE4bOriginalA2Fixed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1MovingLine
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGResE78Module
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs

public noncomputable section

namespace CFSG.StandardType

theorem exists_point_action_of_inner_image
    {X Q : Type} [Group X] [Group Q] (e : X ≃* Q)
    {A : Subgroup (MulAut X)} {E : Subgroup Q}
    (hc : Function.Injective (MulAut.conj : Q →* MulAut Q))
    (hmodel : A.map (MulAut.congr e).toMonoidHom = E.map (MulAut.conj : Q →* MulAut Q)) :
    ∃ ρ : A →* Q, Function.Injective ρ ∧ ρ.range = E ∧
      ∀ (a : A) (x : X), e (a.1 x) = ρ a * e x * (ρ a)⁻¹ := by
  let eC : A ≃* A.map (MulAut.congr e).toMonoidHom :=
    A.equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
  let eI : A.map (MulAut.congr e).toMonoidHom ≃*
      E.map (MulAut.conj : Q →* MulAut Q) := MulEquiv.subgroupCongr hmodel
  let eE : E ≃* E.map (MulAut.conj : Q →* MulAut Q) :=
    E.equivMapOfInjective (MulAut.conj : Q →* MulAut Q) hc
  let eA : A ≃* E := (eC.trans eI).trans eE.symm
  let ρ : A →* Q := E.subtype.comp eA.toMonoidHom
  have hρ : Function.Injective ρ := E.subtype_injective.comp eA.injective
  have hρrange : ρ.range = E := by
    change (E.subtype.comp eA.toMonoidHom).range = E
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eA.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hval : ∀ a : A, MulAut.congr e a.1 = MulAut.conj (ρ a) := by
    intro a
    have h := congrArg Subtype.val (eE.apply_symm_apply (eI (eC a)))
    change MulAut.conj (ρ a) = MulAut.congr e a.1 at h
    exact h.symm
  refine ⟨ρ, hρ, hρrange, fun a x => ?_⟩
  have h := congrArg (fun f : MulAut Q => f (e x)) (hval a)
  simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] using h

theorem point_action_conj
    {X Q : Type} [Group X] [Group Q] (e : X ≃* Q)
    {A : Subgroup (MulAut X)} (ρ : A →* Q)
    (hc : Function.Injective (MulAut.conj : Q →* MulAut Q))
    (hact : ∀ (a : A) (x : X), e (a.1 x) = ρ a * e x * (ρ a)⁻¹)
    {n : X} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut X))) :
    ∀ a : A, ρ (ggConjAut A hn a) = e n * ρ a * (e n)⁻¹ := by
  have hval : ∀ a : A, MulAut.congr e a.1 = MulAut.conj (ρ a) := by
    intro a
    ext q
    obtain ⟨x, rfl⟩ := e.surjective q
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulAut.conj_apply] using hact a x
  intro a
  apply hc
  calc
    MulAut.conj (ρ (ggConjAut A hn a)) =
        MulAut.congr e (ggConjAut A hn a : MulAut X) := (hval _).symm
    _ = MulAut.congr e (MulAut.conj n * a.1 * (MulAut.conj n)⁻¹) := by
      rw [ggConjAut_apply]
    _ = MulAut.conj (e n) * MulAut.conj (ρ a) * (MulAut.conj (e n))⁻¹ := by
      rw [map_mul, map_mul, map_inv, congr_conj, hval]
    _ = MulAut.conj (e n * ρ a * (e n)⁻¹) := by rw [map_mul, map_mul, map_inv]

theorem card_ggOTwoPrime_of_p13
    {Q : Type} [Group Q] [Finite Q] {E F : Subgroup Q} {n : ℕ}
    (hP : FrameRoute.P13aConclusion Q E n) (hFE : F ≤ E) (hidx : F.relIndex E = 3)
    (hne : Subgroup.centralizer (F : Set Q) ≠ E) :
    Nat.card (ggOTwoPrime (Subgroup.centralizer (F : Set Q))) = 6 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hP.1
  have hF3 : IsPGroup 3 F := hE3.to_le hFE
  rcases (hP.2.2 F hFE hidx).2.1 with h | ⟨R, ⟨eR⟩, hFR, hdis, hCR, -, -⟩
  · exact False.elim (hne h)
  · rw [hCR, ggOTwoPrime_sup_of_isPGroup_odd (p := 3) (by decide) hF3 hFR hdis,
      ggOTwoPrime_eq_self_of_equiv_perm eR, Nat.card_congr eR.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem card_ggOTwoPrime_of_p13_reflection
    {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q]
    {A : Subgroup (MulAut X)} [Finite A] {E : Subgroup Q} {d : ℕ}
    (ρ : A →* Q) (hρ : Function.Injective ρ) (hρE : ρ.range = E)
    (hP : FrameRoute.P13aConclusion Q E d) (φ : MulAut A)
    (hφ : GGIsReflection 3 φ) (n : Q)
    (hact : ∀ a : A, ρ (φ a) = n * ρ a * n⁻¹) :
    Nat.card (ggOTwoPrime (Subgroup.centralizer
      ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map ρ : Set Q))) = 6 := by
  let H : Subgroup A := φ.toMonoidHom.eqLocus (MonoidHom.id A)
  let F : Subgroup Q := H.map ρ
  have hFE : F ≤ E := by
    rintro _ ⟨a, -, rfl⟩
    rw [← hρE]
    exact ⟨a, rfl⟩
  have hHcard : Nat.card H = Nat.card {a : A // φ a = a} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun a => by
      change φ a = a ↔ φ a = a
      rfl
  have hFcard : Nat.card F = Nat.card H := Subgroup.card_map_of_injective hρ
  have hEcard : Nat.card E = Nat.card A := by
    rw [← hρE]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  have hcard3 : Nat.card F * 3 = Nat.card E := by
    rw [hFcard, hHcard, hEcard]
    exact hφ.2
  have hidx : F.relIndex E = 3 := by
    have h := Subgroup.relIndex_mul_card F E
    rw [inf_of_le_left hFE] at h
    apply mul_right_cancel₀ (show Nat.card F ≠ 0 from Nat.card_pos.ne')
    calc F.relIndex E * Nat.card F = Nat.card E := h
      _ = 3 * Nat.card F := by rw [← hcard3, mul_comm]
  have hnC : n ∈ Subgroup.centralizer (F : Set Q) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    have hfix : φ a = a := ha
    have h := hact a
    rw [hfix] at h
    exact ((mul_inv_eq_iff_eq_mul).mp h.symm).symm
  have hne : Subgroup.centralizer (F : Set Q) ≠ E := by
    intro hCE
    have hnE : n ∈ E := hCE ▸ hnC
    have hnE' : n ∈ Subgroup.centralizer (E : Set Q) := by
      rw [hP.2.1]
      exact hnE
    have hfix : ∀ a : A, φ a = a := by
      intro a
      apply hρ
      rw [hact a, (Subgroup.mem_centralizer_iff.mp hnE' (ρ a)
        (hρE ▸ (show ρ a ∈ ρ.range from ⟨a, rfl⟩))).symm,
        mul_inv_cancel_right]
    obtain ⟨a, ha⟩ := ggExists_moved_of_isReflection Nat.prime_three hφ
    exact ha (hfix a)
  exact card_ggOTwoPrime_of_p13 hP hFE hidx hne



open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar



theorem card_ggRankOneIn_of_e7Two_member_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J X : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X)
    {t : MulAut Bs} (ht : t ∈ ggAutomizer X Bs) (htr : GGIsReflection p t) :
    Nat.card (ggRankOneIn X Bs t) = 6 := by
  obtain ⟨hp3, hN, K, iK, iFin, iChar, hK, eX, E, c, hE, -, hc, hmodel, -⟩ :=
    exists_e7Two_frame_of_member_marking hcfg hX hmark
  let := iK
  let := iFin
  let := iChar
  subst p
  obtain ⟨g, hgX, hgN, hgact⟩ := mem_ggAutomizer_iff.mp ht
  have htEq : t = ggConjAut Bs hgN :=
    MulEquiv.ext fun b => Subtype.ext (by simpa only [ggConjAut_apply] using hgact b)
  have htI : t ∈ ggInduced X Bs := ⟨g, hgX, hgN, hgact⟩
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.2.1.2.1
  obtain ⟨n, hn, hover, hrefl, -⟩ := ggReflection_overGamma_of_induced
    Nat.prime_three (by decide) hBs hN htI htr
  let A := (ggGamma X hN).range
  have hconj : Function.Injective (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    mulAut_conj_injective_adjointGroup
  obtain ⟨ρ, hρ, hρE, hρact⟩ := exists_point_action_of_inner_image eX hconj hmodel
  have hET : E.map (MulAut.conj c⁻¹).toMonoidHom =
      (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range := by
    rw [hc, Subgroup.map_map]
    have hid : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E7 K) := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  have hP : FrameRoute.P13aConclusion (adjointGroup .E7 K) E 7 :=
    FrameRoute.p13a6_E7 hK (MulAut.conj c⁻¹) hET
  have hnat := card_ggOTwoPrime_of_p13_reflection ρ hρ hρE hP
    (ggConjAut A hn) hrefl (eX n) (point_action_conj eX ρ hconj hρact hn)
  have hcent := ggHypCent_eq_centralizer_comap eX.toMonoidHom eX.injective ρ hρact hn
  have hmapC : (ggHypCent A n).map eX.toMonoidHom = Subgroup.centralizer
      (((ggConjAut A hn).toMonoidHom.eqLocus (MonoidHom.id A)).map ρ :
        Set (adjointGroup .E7 K)) := by
    rw [hcent, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr eX.surjective, top_inf_eq]
  have hmapO : (ggOTwoPrime (ggHypCent A n)).map eX.toMonoidHom =
      ggOTwoPrime (Subgroup.centralizer
        (((ggConjAut A hn).toMonoidHom.eqLocus (MonoidHom.id A)).map ρ :
          Set (adjointGroup .E7 K))) := by
    rw [ggOTwoPrime_map_of_injective eX.toMonoidHom eX.injective, hmapC]
  have hcard : Nat.card (ggOTwoPrime (ggHypCent A n)) = 6 := by
    have h := congrArg (fun H : Subgroup (adjointGroup .E7 K) => Nat.card H) hmapO
    rw [Subgroup.card_map_of_injective eX.injective] at h
    exact h.trans hnat
  have hfix : ggFixG Bs (ggConjAut Bs hgN) = ggHyperplane Bs t := by
    rw [← htEq]
    rfl
  have hmapH : (ggHypCent A n).map X.subtype =
      X ⊓ Subgroup.centralizer (ggHyperplane Bs t : Set G) := by
    simpa only [hfix] using map_ggHypCent_eq Nat.prime_three (by decide) hBs hN hn
      hgX hgN (htEq ▸ htr.1) (htEq ▸ hover)
  rw [ggRankOneIn, ← hmapH, ← ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
    Subgroup.card_map_of_injective X.subtype_injective]
  exact hcard


theorem exists_reflection_of_e7Two_base_marking
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) 3 Bs L) :
    ∃ r ∈ ggAutomizer L Bs, GGIsReflection 3 r := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, K, hnb⟩ := exists_ggNbr hcfg.1.1.1.2.2.2.2.2.2.2 hcfg.1.1.2.2
  have hH : GGResHyp 3 B Bs x L D J y K :=
    ⟨hcfg.1.1, hcfg.1.2.1, hcfg.1.2.2.1, hcfg.1.2.2.2.1,
      hnb, hcfg.2.1 y K hnb, Or.inr hcfg.2.1⟩
  have hRig : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .E7 ∧ lab.n = 1) 3 Bs L :=
    largeEvenMarking_mono
      (fun _ _ _ _ _ _ h => ⟨⟨rfl, h.1.1.1, h.1.2⟩, h.2⟩) hmark
  obtain ⟨V, iAdd, iMod, ι, φ, h, α, -, hrefl, -, ⟨eA, hA⟩, -, -, -⟩ :=
    e78_e7_actual_module hH hRig
  refine ⟨φ 0, ?_, hrefl 0⟩
  rw [← hA 0]
  exact (eA (CoxeterMatrix.E₇.simple 0)).2

theorem not_e7Two_base_marking_of_rankOne_guard
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs L) : False := by
  obtain ⟨hp3, -⟩ := exists_e7Two_frame_of_member_marking hcfg (Or.inl rfl) hmark
  subst p
  obtain ⟨r, hrA, hr⟩ := exists_reflection_of_e7Two_base_marking hcfg hmark
  have hrC : r ∈ ggCoxRefl M e := ggCoxRefl_of_cfg hcfg
    (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hr
  exact hbig r hrA hrC (card_ggRankOneIn_of_e7Two_member_marking hcfg (Or.inl rfl) hmark hrA hr)

theorem ggGenConcl_of_e7Two_base_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs L) :
    GGGenConcl M Bs L L 𝒦 e :=
  False.elim (not_e7Two_base_marking_of_rankOne_guard hcfg hpres h3 hbig hmark)

end CFSG.StandardType
