module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGHyp
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G] [Finite G]

theorem ggL45_labelAll_mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P)
    (hPP : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F) :
    LargeEvenLabelAll lab P' := fun Q hQ =>
  largeEvenRawDatum_mono (fun R _ I F ⟨hq, hp⟩ => ⟨hq, hPP R I F hp⟩) (h Q hQ)

theorem largeEvenMarking_and_labelAll_dep {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (P' lab))
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' lab R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP'⟩

theorem ggL45_markingAll_and {K : Type*} [Group K] {Q₁ Q₂ : LargeEvenMarkProp K}
    (h₁ : GGMarkingAll Q₁) (h₂ : GGMarkingAll Q₂) :
    GGMarkingAll fun lab R _ I F θ => Q₁ lab R I F θ ∧ Q₂ lab R I F θ := by
  intro P hP
  refine largeEvenMarking_mono ?_ (h₂ _ (h₁ P hP))
  rintro lab R _ I F θ ⟨⟨h, h1⟩, h2⟩
  exact ⟨h, h1, h2⟩

theorem ggL45_fixed_rhoK_eq {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ggAutFixedSubgroup (K.normalizerMonoidHom ⟨g, hg⟩) =
      (K ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf K := by
  ext k
  rw [mem_ggAutFixedSubgroup, ggL45_rhoK_fix_iff hg, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨k.2, h.symm⟩, fun h => h.2.symm⟩

theorem ggL45_isComponentOf_fixed_rhoK {K J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer ({g} : Set G))) :
    IsComponentOf (J.subgroupOf K) (ggAutFixedSubgroup (K.normalizerMonoidHom ⟨g, hg⟩)) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  rw [ggL45_fixed_rhoK_eq hg]
  exact ⟨Subgroup.comap_mono hJ.1, hJ.2.1.comap K.subtype,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ.2.2⟩

end General

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.kg_BsN
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    Bs ≤ Subgroup.normalizer (K : Set G) :=
  fun _ hb => hcfg.le_normalizer (hcfg.bs_le hb)

theorem GGL45Config.kg_markingAll
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) (hgr : GGNbrGraphInput)
    (hnone : GGL44iiiTriD4NoneInput) :
    GGMarkingAll (K := ↥K) fun lab _ _ I F θ =>
      (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
        ggLAut K θ ⟨b, hcfg.kg_BsN hb⟩ = u * f) ∧
      (lab.tag = .triD4 ∧ p = 3 →
        (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
          ggLAut K θ ⟨b, hcfg.kg_BsN hb⟩ = u * f) →
        (∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
          ggLAut K θ ⟨b, hcfg.kg_BsN hb.1⟩ ∈ I) →
        (∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hcfg.kg_BsN hb⟩ ∉ I) → False) := by
  obtain ⟨hFC, hM, h43, h44, h44ii, ⟨hDd, hd1, hnbr, hyd, -⟩, -⟩ := hcfg
  have hd : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hDd]
    exact Subgroup.mem_zpowers d
  exact ggL45_markingAll_and (hgr G p B Bs x L D J hFC.1 y K hnbr _)
    (hnone G p B Bs x L D J X B₂ hFC.noBL5 hM h43 h44 h44ii d hd hd1 y K hnbr hyd _)

theorem ggL45_exists_marking_labQ {P' : LargeEvenLabel → LargeEvenRawCont}
    {Q : LargeEvenMarkProp K}
    (hP' : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (P' lab))
    (hQ : GGMarkingAll Q) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ lab : LargeEvenLabel, LargeEvenMarking K (fun lab' _ _ _ _ _ => lab' = lab) ∧
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R),
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ GGRawInnField p R I F ∧ P' lab R I F ∧
      Q lab R I F θ ∧
      (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
        LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
      (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹)) ∧
      ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
        (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I) := by
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  obtain ⟨-, -, -, -, -, hK, -, hpart, -⟩ := hcfg
  have hM1 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
    (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) (hQ _ hK.2.2.2.2)
  have hM1' := largeEvenMarking_and_labelAll_dep (P' := P') hP' hM1
  have hM1'' := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := GGRawInndiagIso) (fun lab hl _ => hiso lab hl) (fun _ _ _ _ _ _ _ => trivial) hM1'
  obtain ⟨hperf, lab, hlab, hraw1⟩ := hM1''
  have hmk : LargeEvenMarking K (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw1⟩
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨⟨⟨⟨⟨-, hB₁I, hxF⟩, hQθ⟩, hRIF⟩, hP'RIF⟩, hisoR⟩⟩ :=
    largeEvenRawDatum_exists hraw1
  have hM2 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
    (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hpart.2.2
  obtain ⟨-, lab', hlab', hraw2⟩ := hM2
  obtain ⟨R', _, I', F', ⟨hs', hna', θ', hU₁iff, hR'⟩, hisoRR'⟩ :=
    largeEvenRawDatum_exists (hisoR lab' hlab' _ hraw2)
  obtain ⟨hmul, hinv, hinn, -⟩ := hRIF hs hna
  obtain ⟨hmul', hinv', hinn', -⟩ := hR' hs' hna'
  refine ⟨lab, hmk, R, inferInstance, I, F, θ, hs, hna, hRIF, hP'RIF, hQθ, hB₁I, hxF,
    fun u hu huN => ?_⟩
  rw [hU₁iff u hu, ggL45_exists_induces_iff hinv' huN,
    ← ggL45_mem_ggInndiag_iff hmul' hinv' hinn', ← ggL45_mem_ggInndiag_iff hmul hinv hinn,
    hisoRR' hs' hna' (θ.symm.trans θ'), ← ggLAut_congr]

theorem GGL45Config.kg_J_comp
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) (hsub : GGNbrSubcomponentInput) :
    J ≤ K ∧ IsComponentOf (J.subgroupOf K)
      (ggAutFixedSubgroup (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)) := by
  have hxN := hcfg.kg_xN
  obtain ⟨⟨⟨hI, -, hDJ⟩, -⟩, -, -, -, -, ⟨-, -, hnbr, -, -⟩, -⟩ := hcfg
  have hJK : J ≤ K := hsub G p B x L D J hI hDJ y K hnbr
  have hJc := isComponentOf_inf_centralizer_of_ggNbr hI.2.2.2.2.2.2.1 hDJ hnbr hJK
  have hcx : Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g * x = x * (x⁻¹ * g) * x := by group
        _ = x * (g * x⁻¹) * x := by rw [h]
        _ = x * g := by group
    · intro h
      calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
        _ = x⁻¹ * (g * x) * x⁻¹ := by rw [h]
        _ = x⁻¹ * g := by group
  refine ⟨hJK, ggL45_isComponentOf_fixed_rhoK (inv_mem hxN) ?_⟩
  rw [hcx]
  exact hJc

theorem GGL45Config.kg_not_torsion
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) (hsub : GGNbrSubcomponentInput)
    (hT : GGStdSubNotTorsionInput) {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hKperf : commutator K = ⊤)
    (hfix : GGL45FieldFixKGRaw p lab R I F)
    (hψ : ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ LargeEvenInduces θ
      (fun k k' => k' = K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ k) (u * f * u⁻¹))
    (htor : GGL45TorsionTag lab) : False := by
  obtain ⟨hJK, hJc⟩ := hcfg.kg_J_comp hsub
  have hQ := (hfix.2 (↥K) θ hKperf _ hcfg.kg_psi_pow hψ _ hJc).1 htor
  have hJ := largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hQ
  obtain ⟨⟨⟨hI, -, hDJ⟩, -⟩, -⟩ := hcfg
  exact hT G p B x L D J hI hDJ hJ

theorem GGL45Config.kg_A2_center
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) (hsub : GGNbrSubcomponentInput)
    (hStdL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput) {lab : LargeEvenLabel} {R : Type}
    [Group R] {I F : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R)
    (hKperf : commutator K = ⊤) (hfix : GGL45FieldFixKGRaw p lab R I F)
    (hψ : ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ LargeEvenInduces θ
      (fun k k' => k' = K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ k) (u * f * u⁻¹))
    (hA2 : GGLabelA2 lab) (hp3 : p = 3) : p ∣ Nat.card (Subgroup.center K) := by
  by_contra hZ
  obtain ⟨hJK, hJc⟩ := hcfg.kg_J_comp hsub
  obtain ⟨hQZ, hQm⟩ := (hfix.2 (↥K) θ hKperf _ hcfg.kg_psi_pow hψ _ hJc).2 hA2 hp3 hZ
  have e := (Subgroup.subgroupOfEquivOfLe hJK).symm
  have hJZ : Subgroup.center J = ⊥ := center_eq_bot_of_mulEquiv e hQZ
  have hJm := largeEvenMarking_of_mulEquiv e hQm
  have hxp := hcfg.x_pow
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := fun _ hb =>
    hcfg.kg_BsN (hcfg.1.1.2.1.1 hb)
  obtain ⟨⟨⟨hI, -, hDJ⟩, -⟩, -, -, -, -, ⟨-, -, hnbr, -, -⟩, -⟩ := hcfg
  subst hp3
  have hrank : LargeEvenTwoLocalRank 3 G ≤ 4 :=
    twoLocalRank_le_of_sHat Nat.prime_three hnbr.1 hKperf θ hBN (c := 3) (hfix.1 hA2 rfl)
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hLm := hStdL.2 G B x L D J hI hDJ hrank hJm hJZ
  have h5 := five_le_twoLocalRank_of_twE6 hE6 hS.2.2.2.1.1 hS.2.2.1 hxp hLm
  omega

end Config

end CFSG.StandardType
