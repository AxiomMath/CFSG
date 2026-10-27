module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Core
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGFieldExc
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGLabel
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangS1ExcEAux_toralAt
    {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {J : Subgroup G} (hJK : J ≤ K)
    (h : GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G))) :
    GGExcToralAct (J.subgroupOf K) ((ggBsAut hN).range : Set (MulAut ↥K)) := by
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  have untw : ∀ (τ : CFSG.Blueprint.Chevalley.Tag) (K₀ : Type) [Field K₀] [Finite K₀]
      (θJ : ↥J ⧸ Subgroup.center ↥J ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K₀))
      (W : Subgroup ↥(RecipeExcLang.inndiagGroup τ K₀)),
      (∀ α ∈ (fun b : G => MulAut.conj b) '' (Bs : Set G), ∃ w ∈ W, ∀ j : ↥J, ∃ j' : ↥J,
        (j' : G) = α j ∧ θJ (QuotientGroup.mk j') =
          RecipeExcLang.inndiagConj τ K₀ w (θJ (QuotientGroup.mk j))) →
      ∃ θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
        ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K₀),
        ∀ α ∈ (ggBsAut hN).range, ∃ w ∈ W, ∀ j : ↥(J.subgroupOf K),
          ∃ j' : ↥(J.subgroupOf K), (j' : ↥K) = α j ∧
            θ₀ (QuotientGroup.mk j') =
              RecipeExcLang.inndiagConj τ K₀ w (θ₀ (QuotientGroup.mk j)) := by
    intro τ K₀ _ _ θJ W hclause
    let θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
        ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K₀) :=
      (QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf K)) (Subgroup.center ↥J) eJ
        (Subgroup.map_center_eq eJ)).trans θJ
    refine ⟨θ₀, ?_⟩
    rintro _ ⟨b, rfl⟩
    obtain ⟨w, hw, hwcl⟩ := hclause (MulAut.conj (b : G)) ⟨b, b.2, rfl⟩
    refine ⟨w, hw, ?_⟩
    intro j
    obtain ⟨j'', hj''1, hj''2⟩ := hwcl (eJ j)
    refine ⟨eJ.symm j'', ?_, ?_⟩
    · apply Subtype.ext
      rw [MulAut.conj_apply] at hj''1
      calc ((eJ.symm j'' : ↥(J.subgroupOf K)) : G) = (j'' : G) := rfl
        _ = (b : G) * ((eJ j : ↥J) : G) * (b : G)⁻¹ := hj''1
        _ = (b : G) * (j : G) * (b : G)⁻¹ := rfl
        _ = ((ggBsAut hN b j : ↥K) : G) := rfl
    · have hθj : θ₀ (QuotientGroup.mk j) = θJ (QuotientGroup.mk (eJ j)) := by
        dsimp only [θ₀]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
      have hθj' : θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := by
        dsimp only [θ₀]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
        simp
      calc θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := hθj'
        _ = RecipeExcLang.inndiagConj τ K₀ w (θJ (QuotientGroup.mk (eJ j))) := hj''2
        _ = RecipeExcLang.inndiagConj τ K₀ w (θ₀ (QuotientGroup.mk j)) := by rw [hθj]
  have tw : ∀ (K₀ : Type) [Field K₀] [Finite K₀] (σ : K₀ ≃+* K₀) (hσ : orderOf σ = 2)
      (θJ : ↥J ⧸ Subgroup.center ↥J ≃*
        ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.E6 K₀
          σ.toRingHom))
      (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ)),
      (∀ α ∈ (fun b : G => MulAut.conj b) '' (Bs : Set G), ∃ w ∈ W, ∀ j : ↥J, ∃ j' : ↥J,
        (j' : G) = α j ∧ θJ (QuotientGroup.mk j') =
          RecipeExcLang.twConj K₀ σ w (θJ (QuotientGroup.mk j))) →
      ∃ θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
          ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.E6 K₀
            σ.toRingHom),
        ∀ α ∈ (ggBsAut hN).range, ∃ w ∈ W, ∀ j : ↥(J.subgroupOf K),
          ∃ j' : ↥(J.subgroupOf K), (j' : ↥K) = α j ∧
            θ₀ (QuotientGroup.mk j') =
              RecipeExcLang.twConj K₀ σ w (θ₀ (QuotientGroup.mk j)) := by
    intro K₀ _ _ σ _ θJ W hclause
    let θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
        ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.E6 K₀
          σ.toRingHom) :=
      (QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf K)) (Subgroup.center ↥J) eJ
        (Subgroup.map_center_eq eJ)).trans θJ
    refine ⟨θ₀, ?_⟩
    rintro _ ⟨b, rfl⟩
    obtain ⟨w, hw, hwcl⟩ := hclause (MulAut.conj (b : G)) ⟨b, b.2, rfl⟩
    refine ⟨w, hw, ?_⟩
    intro j
    obtain ⟨j'', hj''1, hj''2⟩ := hwcl (eJ j)
    refine ⟨eJ.symm j'', ?_, ?_⟩
    · apply Subtype.ext
      rw [MulAut.conj_apply] at hj''1
      calc ((eJ.symm j'' : ↥(J.subgroupOf K)) : G) = (j'' : G) := rfl
        _ = (b : G) * ((eJ j : ↥J) : G) * (b : G)⁻¹ := hj''1
        _ = (b : G) * (j : G) * (b : G)⁻¹ := rfl
        _ = ((ggBsAut hN b j : ↥K) : G) := rfl
    · have hθj : θ₀ (QuotientGroup.mk j) = θJ (QuotientGroup.mk (eJ j)) := by
        dsimp only [θ₀]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
      have hθj' : θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := by
        dsimp only [θ₀]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
        simp
      calc θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := hθj'
        _ = RecipeExcLang.twConj K₀ σ w (θJ (QuotientGroup.mk (eJ j))) := hj''2
        _ = RecipeExcLang.twConj K₀ σ w (θ₀ (QuotientGroup.mk j)) := by rw [hθj]
  rcases h with hE6 | hE7 | hTw
  · obtain ⟨K₀, hfield, hfin, θJ, W, hgeom, hclause⟩ := hE6
    letI : Field K₀ := hfield
    letI : Finite K₀ := hfin
    obtain ⟨θ₀, hθ₀⟩ := untw .E6 K₀ θJ W hclause
    exact Or.inl ⟨K₀, hfield, hfin, θ₀, W, hgeom, hθ₀⟩
  · obtain ⟨K₀, hfield, hfin, θJ, W, hgeom, hclause⟩ := hE7
    letI : Field K₀ := hfield
    letI : Finite K₀ := hfin
    obtain ⟨θ₀, hθ₀⟩ := untw .E7 K₀ θJ W hclause
    exact Or.inr (Or.inl ⟨K₀, hfield, hfin, θ₀, W, hgeom, hθ₀⟩)
  · obtain ⟨K₀, hfield, hfin, σ, hσ, θJ, W, hgeom, hclause⟩ := hTw
    letI : Field K₀ := hfield
    letI : Finite K₀ := hfin
    obtain ⟨θ₀, hθ₀⟩ := tw K₀ σ hσ θJ W hclause
    exact Or.inr (Or.inr ⟨K₀, hfield, hfin, σ, hσ, θ₀, W, hgeom, hθ₀⟩)

theorem ggNbrLangAxisOuterOn_s1ExcE (hsub : GGNbrSubcomponentInput)
    (hLID : GGBstarInnerDiagLInputOn fun _ _ => True) (hQ1 : GGBstarInnerDiagJInput)
    (hQ2E : GGBstarToralJExcInput) (hS1E : KGLangAxisS1ExcInput) :
    GGNbrLangAxisOuterOn GGNbrLangS1ExcELabel := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  have hBsab : IsElemAbelian p Bs := hBstar.2.1
  have hrawE7 : GGRawInnFieldOn fun lab => lab.tag = .E7 :=
    ggRawInnFieldOn_excInn.mono fun _ h => Or.inr (Or.inl h)
  have hrawInn : GGRawInnFieldOn fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 :=
    ggRawInnFieldOn_E6.or (ggRawInnFieldOn_twE6.or hrawE7)
  have hpcE7 : GGRawPCyclicOn fun _ lab => lab.tag = .E7 :=
    ggRawPCyclicOn_excCyclic.mono fun _ _ h => Or.inl (Or.inr (Or.inr (Or.inl h)))
  have hpcInn : GGRawPCyclicOn fun _ lab =>
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 :=
    ggRawPCyclicOn_E6.or (ggRawPCyclicOn_twE6.or hpcE7)
  refine NbrLangTypeA.ggMarkingAll_mono ?_
    (ggRegKG_markingAll_and
      (ggRegKG_markingAll_and
        (ggRegKG_markingAll_and
          (ggRegKG_markingAll_and (ggRegKG_markingAll_perfect_simple ↥K)
            (ggRegKG_markingAll_guard
              (S := fun _ lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7)
              (P := GGRawInnField p) (p := p)
              (fun lab hlab hs => hrawInn p hp hp2 lab hlab hs) ↥K))
          (ggRegKG_markingAll_guard
            (S := fun _ lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7)
            (P := GGRawPCyclic p) (p := p)
            (fun lab hlab hs => hpcInn p hp hp2 lab hlab hs) ↥K))
        (ggMarkingAll_of_labelAll_guard (S := GGNbrLangS1ExcELabel p)
          (P' := fun lab => KGFieldCompCont p lab)
          (fun lab hlab hs => kgFieldCompCont_excE hp hp2 hlab hs)))
      (ggMarkingAll_of_labelAll_guard (S := GGNbrLangS1ExcELabel p)
        (P' := fun lab => KGLangAxisS1ExcCont p)
        (fun lab hlab hs => hS1E p lab hp hp2 hlab hs)))
  rintro lab R _ I F θ ⟨⟨⟨⟨⟨hKperf, hs, hna⟩, hraw⟩, hpc⟩, hKGField⟩, hKGS1E⟩
    hSl hxout hall b₀ hb₀ hb₀I
  have hp3 : p = 3 := hSl.2.1
  have hSstar : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hxB : x ∈ B := hSstar.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hIDL : GGInnerDiagOnLab (fun _ _ => True) p B L :=
    ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hcfg.1
  have hID : GGInnerDiagOn Bs L :=
    (hLID G p B Bs x L D J hcfg hIDL).innerDiagOn
  have hIDJ : GGInnerDiagOn Bs J := hQ1 G p B Bs x L D J hcfg hID
  have hJperf : commutator ↥J = ⊤ := hIDJ.1
  have hJK : J ≤ K := hsub G p B x L D J hcfg.1 hDJ y K hK
  have hJc : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSstar hDJ hK hJK
  have hJ₀K : IsComponentOf (J.subgroupOf K) (ggFixSub (ggBsAut hN ⟨x, hxBs⟩)) :=
    ggL45_isComponentOf_fixed_rhoK (hN hxBs) hJc
  obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ :=
    exists_index_prime_of_raw_pcyclic hp hBsab hs hna (hpc hSl.1)
      ((ggLAut K θ).comp (Subgroup.inclusion hN)) hb₀ hb₀I
  set ρ : ↥K →* R :=
    (θ : ↥K ⧸ Subgroup.center ↥K →* R).comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hρdef
  set J₀R : Subgroup R := (J.subgroupOf K).map ρ with hJ₀Rdef
  have hρker : ρ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    change θ (k : ↥K ⧸ Subgroup.center ↥K) = 1 ↔ k ∈ Subgroup.center ↥K
    rw [← map_one θ, θ.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hρsurj : Function.Surjective ρ := fun r => by
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨k, hq⟩
  have hmapρ : ∀ (g : Subgroup.normalizer (K : Set G)) (k : ↥K),
      ggLAut K θ g (ρ k) = ρ (K.normalizerMonoidHom g k) := by
    intro g k
    change ggLAut K θ g (θ (k : ↥K ⧸ Subgroup.center ↥K)) =
      θ (K.normalizerMonoidHom g k : ↥K ⧸ Subgroup.center ↥K)
    rw [ggLAut_apply]
  have hJS : IsComponentOf (J.subgroupOf K) (ggFix (K.normalizerMonoidHom ⟨x, hN hxBs⟩)) := by
    have hfixK : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
        ggFix (K.normalizerMonoidHom ⟨x, hN hxBs⟩) := by
      ext k
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_ggFix]
      constructor
      · rintro ⟨-, hk⟩
        apply Subtype.ext
        rw [normalizerMonoidHom_coe]
        have hkC : (k : G) * x = x * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp hk
        calc x * (k : G) * x⁻¹ = (k : G) * x * x⁻¹ := by rw [← hkC]
          _ = (k : G) := by group
      · intro hk
        refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h2 := congrArg Subtype.val hk
        rw [normalizerMonoidHom_coe] at h2
        calc (k : G) * x = (x * (k : G) * x⁻¹) * x := by rw [h2]
          _ = x * (k : G) := by group
    have h := ggIsComponentOf_subgroupOf hJc inf_le_left
    rwa [hfixK] at h
  have hJ₀Rcomp : IsComponentOf J₀R
      (MonoidHom.eqLocus (ggLAut K θ ⟨x, hN hxBs⟩ : R →* R) (MonoidHom.id R)) := by
    rw [hJ₀Rdef]
    exact USixTwo.isComponentOf_map_fix hρsurj (le_of_eq hρker)
      (fun k => hmapρ ⟨x, hN hxBs⟩ k) hJS
  let ρJ : ↥J →* ↥J₀R :=
    { toFun := fun j => ⟨ρ (Subgroup.inclusion hJK j), by
        rw [hJ₀Rdef]
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJK j,
          Subgroup.mem_subgroupOf.mpr j.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hρJsurj : Function.Surjective ρJ := by
    intro b
    obtain ⟨k, hk, hkρ⟩ := Subgroup.mem_map.mp (by rw [← hJ₀Rdef]; exact b.2)
    rw [Subgroup.mem_subgroupOf] at hk
    exact ⟨⟨k, hk⟩, Subtype.ext hkρ⟩
  have hkerJ : ρJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hjZ : Subgroup.inclusion hJK j ∈ Subgroup.center ↥K := by
      have h2 : ρ (Subgroup.inclusion hJK j) = 1 := by
        have := congrArg (fun q : ↥J₀R => (q : R)) hj
        simpa [ρJ] using this
      have h2' : Subgroup.inclusion hJK j ∈ ρ.ker := h2
      rwa [hρker] at h2'
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hc := congrArg (fun z : ↥K => (z : G))
      (Subgroup.mem_center_iff.mp hjZ (Subgroup.inclusion hJK y))
    simpa using hc
  haveI : Group.IsPerfect ↥J := ⟨hJperf⟩
  let e' : ↥J ⧸ Subgroup.center ↥J ≃* ↥J₀R ⧸ Subgroup.center ↥J₀R :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence ρJ hρJsurj hkerJ
  have hφ : ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨x, hN hxBs⟩ = u * f :=
    hall x hxBs
  have hφI : ggLAut K θ ⟨x, hN hxBs⟩ ∉ I := hxout hxBs
  have hφp : (ggLAut K θ ⟨x, hN hxBs⟩) ^ p = 1 :=
    ggLAut_pow_eq_one_of_pow K θ (hN hxBs) (hBsab.2 x hxBs)
  obtain ⟨labJ, hlabJ, hlabel, hcardn, htagrank⟩ :=
    (hKGField hSl) (ggLAut K θ ⟨x, hN hxBs⟩) hφ hφI hφp J₀R hJ₀Rcomp
  have hnotw : ¬ (lab.tag = .twF4 ∧ labJ.tag = .twF4der) := by
    rintro ⟨h1, -⟩
    rcases hSl.1 with h | h | h
    · rw [h] at h1; exact absurd h1 (by simp)
    · rw [h] at h1; exact absurd h1 (by simp)
    · rw [h] at h1; exact absurd h1 (by simp)
  have htagrank' : labJ.tag = lab.tag ∧ labJ.rank = lab.rank := htagrank.resolve_right hnotw
  have htagJ : labJ.tag = .E6 ∨ labJ.tag = .twE6 ∨ labJ.tag = .E7 := by
    rcases hSl.1 with h | h | h
    · exact Or.inl (by rw [htagrank'.1, h])
    · exact Or.inr (Or.inl (by rw [htagrank'.1, h]))
    · exact Or.inr (Or.inr (by rw [htagrank'.1, h]))
  have hlabelJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
    largeEvenRawDatum_mono (fun R' _ _ _ hQ => ⟨e'.trans hQ.some⟩) hlabel
  have hToralJ : GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) :=
    hQ2E G B Bs x L D J (hp3 ▸ hcfg) hID hIDJ labJ hlabJ htagJ hlabelJ
  have hToralK : GGExcToralAct (J.subgroupOf K) ((ggBsAut hN).range : Set (MulAut ↥K)) :=
    ggNbrLangS1ExcEAux_toralAt hN hJK hToralJ
  have hallA : ∀ α ∈ (ggBsAut hN).range, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      kgInducedAut θ α = u * f := by
    rintro _ ⟨b, rfl⟩
    exact hall b.1 b.2
  have hcard2 : p ^ 2 ≤ Nat.card
      {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I} :=
    ggNbr_sq_le_card_A₀ hcfg hK hN θ hB₀ hcard hmem
  have hξI : kgInducedAut θ (ggBsAut hN ⟨x, hxBs⟩) ∉ I := hxout hxBs
  have hα₀I : kgInducedAut θ (ggBsAut hN ⟨b₀, hb₀⟩) ∉ I := hb₀I
  obtain ⟨k, e, he1, hep, hefix, hkfix, hke⟩ :=
    (hKGS1E hSl) ↥K θ hKperf (ggBsAut hN).range (ggBsAut_range_isElemAbelian hBsab hN)
      hallA (ggBsAut hN ⟨b₀, hb₀⟩) ⟨⟨b₀, hb₀⟩, rfl⟩ hα₀I hcard2
      (ggBsAut hN ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hξI (J.subgroupOf K) hJ₀K hToralK
  refine ⟨B₀, hB₀, hcard, hb₀', fun b hb hbI => (hmem b hb).2 hbI, ?_⟩
  exact ggNbrLangCore_of_langElem hBstar.2.2.2 hN θ (hraw hSl.1 hs hna).2.2.1 b₀ hb₀ hB₀ hmem
    ⟨k, e, he1, hep, hefix, hkfix, hke⟩

end CFSG.StandardType
