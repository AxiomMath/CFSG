module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Core
public import CFSG.LocalAnalysis.StandardType.GGStdSubUnitary
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGFieldUni
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniInput
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGLabel
import CFSG.Quasithin.EmptyFaithful.R3c18Q

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangS1UniAux_thetaAt {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {J : Subgroup G} (hJK : J ≤ K)
    {d m : ℕ} {E : Type} [Field E]
    (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m E)
    (θJ : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)))
    {At : Subgroup ↥(TableB.unitGroup (ι := Fin d) hE.bar)} (hAt : IsMulCommutative At)
    (hAtJ : ∀ b ∈ Bs, ∃ g ∈ At, ∀ j : ↥J, ∃ j' : ↥J, (j' : G) = b * (j : G) * b⁻¹ ∧
      θJ (QuotientGroup.mk j') = CFSG.HardMathSupport.C14Cl.uniConj hE d g
        (θJ (QuotientGroup.mk j))) :
    ∃ θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)),
      ∃ At' : Subgroup ↥(TableB.unitGroup (ι := Fin d) hE.bar), IsMulCommutative At' ∧
        ∀ α ∈ (ggBsAut hN).range, ∃ g ∈ At', ∀ j : ↥(J.subgroupOf K),
          ∃ j' : ↥(J.subgroupOf K), (j' : ↥K) = α j ∧ θ₀ (QuotientGroup.mk j') =
            CFSG.HardMathSupport.C14Cl.uniConj hE d g (θ₀ (QuotientGroup.mk j)) := by
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  let θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)) :=
    (QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf K)) (Subgroup.center ↥J) eJ
      (Subgroup.map_center_eq eJ)).trans θJ
  refine ⟨θ₀, At, hAt, ?_⟩
  rintro _ ⟨b, rfl⟩
  obtain ⟨g, hg, hgJ⟩ := hAtJ b.1 b.2
  refine ⟨g, hg, ?_⟩
  intro j
  obtain ⟨j'', hj''1, hj''2⟩ := hgJ (eJ j)
  refine ⟨eJ.symm j'', ?_, ?_⟩
  · apply Subtype.ext
    calc ((eJ.symm j'' : ↥(J.subgroupOf K)) : G) = (j'' : G) := rfl
      _ = b.1 * ((eJ j : ↥J) : G) * b.1⁻¹ := hj''1
      _ = b.1 * (j : G) * b.1⁻¹ := rfl
      _ = ((ggBsAut hN b j : ↥K) : G) := rfl
  · have hθj : θ₀ (QuotientGroup.mk j) = θJ (QuotientGroup.mk (eJ j)) := by
      dsimp only [θ₀]
      rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
    have hθj' : θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := by
      dsimp only [θ₀]
      rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
      simp
    calc θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := hθj'
      _ = CFSG.HardMathSupport.C14Cl.uniConj hE d g (θJ (QuotientGroup.mk (eJ j))) := hj''2
      _ = CFSG.HardMathSupport.C14Cl.uniConj hE d g (θ₀ (QuotientGroup.mk j)) := by rw [hθj]

theorem ggNbrLangAxisOuterOn_s1Uni (hsub : GGNbrSubcomponentInput)
    (hLID : GGBstarInnerDiagLInputOn fun _ _ => True) (hQ1 : GGBstarInnerDiagJInput)
    (hQ2U : GGBstarAbelianPreimageJUniS1Input) :
    GGNbrLangAxisOuterOn GGNbrLangS1UniLabel := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  have hBsab : IsElemAbelian p Bs := hBstar.2.1
  have hS1A : KGLangAxisS1UniInput := kgLangAxisS1UniInput_holds
  refine NbrLangTypeA.ggMarkingAll_mono ?_
    (ggRegKG_markingAll_and
      (ggRegKG_markingAll_and
        (ggRegKG_markingAll_and
          (ggRegKG_markingAll_and (ggRegKG_markingAll_perfect_simple ↥K)
            (ggRegKG_markingAll_guard (S := fun _ lab => lab.tag = .twA)
              (P := GGRawInnField p) (p := p)
              (fun lab hlab hs => ggRawInnFieldOn_typeA p hp hp2 lab hlab (Or.inr hs)) ↥K))
          (ggRegKG_markingAll_guard (S := fun _ lab => lab.tag = .twA)
            (P := GGRawPCyclic p) (p := p)
            (fun lab hlab hs => ggRawPCyclicOn_typeA p hp hp2 lab hlab (Or.inr hs)) ↥K))
        (ggMarkingAll_of_labelAll_guard (S := GGNbrLangS1UniLabel p)
          (P' := fun lab => KGFieldCompCont p lab)
          (fun lab hlab hs => kgFieldCompCont_uni hp hp2 hlab hs)))
      (ggMarkingAll_of_labelAll_guard (S := GGNbrLangS1UniLabel p)
        (P' := fun lab => KGLangAxisS1UniCont p)
        (fun lab hlab hs => hS1A p lab hp hp2 hlab hs)))
  rintro lab R _ I F θ ⟨⟨⟨⟨⟨hKperf, hs, hna⟩, hraw⟩, hpc⟩, hKGField⟩, hKGS1A⟩
    hSl hxout hall b₀ hb₀ hb₀I
  have hlabtag : lab.tag = .twA := hSl.2.2.2
  have hsix : (p = 3 ∧ (lab.rank = 2 ∨ lab.rank = 5)) ∨ (p = 5 ∧ lab.rank = 4) := by
    simpa [GGNbrLangTypeASixLabel] using hSl.1.2
  have hsplit : p ∣ 2 ^ lab.n + 1 := by
    rcases hSl.2.1 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by rw [hlabtag]; simp)
    · exact h
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
    exists_index_prime_of_raw_pcyclic hp hBsab hs hna (hpc hlabtag)
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
        have hkC : (k : G) * x = x * (k : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hk
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
    rw [hlabtag] at h1
    exact absurd h1 (by simp)
  have htagrank' : labJ.tag = lab.tag ∧ labJ.rank = lab.rank := htagrank.resolve_right hnotw
  have htagJ : labJ.tag = .twA := by rw [htagrank'.1, hlabtag]
  have hrankJ : labJ.rank = lab.rank := htagrank'.2
  obtain ⟨tj, lj, nj⟩ := labJ
  dsimp only at htagJ hrankJ
  subst htagJ
  subst hrankJ
  have hn1 : 1 ≤ nj := hlabJ.1
  have hcardn' : nj * p = lab.n := by simpa using hcardn
  have hpd : (p = 3 ∧ (lab.rank + 1 = 3 ∨ lab.rank + 1 = 6)) ∨
      (p = 5 ∧ lab.rank + 1 = 5) := by
    rcases hsix with ⟨h, hr | hr⟩ | ⟨h, hr⟩
    · exact Or.inl ⟨h, Or.inl (by omega)⟩
    · exact Or.inl ⟨h, Or.inr (by omega)⟩
    · exact Or.inr ⟨h, by omega⟩
  have hdm : ¬ (lab.rank + 1 = 3 ∧ nj = 1) := by
    rintro ⟨h3, hnj1⟩
    have hr2 : lab.rank = 2 := by omega
    have h2 : 2 ≤ nj := hlabJ.2.2 hr2
    omega
  have hpm : p ∣ 2 ^ nj + 1 := by
    have h2pow : 2 ^ lab.n = (2 ^ nj) ^ p := by
      rw [← hcardn', pow_mul]
    have h' : p ∣ (2 ^ nj) ^ p + 1 := by
      rw [← h2pow]
      exact hsplit
    exact CFSG.Quasithin.R3c18.dvd_add_one_of_dvd_pow_add_one hp h'
  have hlabel' : LargeEvenRecipeUnitary (lab.rank + 1) (2 ^ nj)
      (fun R' _ _ _ => Nonempty (↥J₀R ⧸ Subgroup.center ↥J₀R ≃* R')) := by
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hlabel
    exact hlabel
  rw [LargeEvenRecipeUnitary] at hlabel'
  obtain ⟨E, hEfield, -, hEcard, ⟨iso⟩⟩ := hlabel'
  letI : Field E := hEfield
  have hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nj E :=
    unitaryFieldData_of_card hn1 hEcard
  let σ : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) E (2 ^ nj)) := e'.trans iso
  obtain ⟨E', hE'field, m', hE'data, θJ, At, hAt, hAtJ⟩ :=
    ggConfig_exists_abelianPreimage_psu hcfg hID hQ2U hIDJ hpd hE hpm hdm σ
  letI : Field E' := hE'field
  obtain ⟨θ₀, hAt'⟩ := ggNbrLangS1UniAux_thetaAt hN hJK hE'data θJ hAt hAtJ
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
    (hKGS1A hSl) ↥K θ hKperf (ggBsAut hN).range (ggBsAut_range_isElemAbelian hBsab hN)
      hallA (ggBsAut hN ⟨b₀, hb₀⟩) ⟨⟨b₀, hb₀⟩, rfl⟩ hα₀I hcard2
      (ggBsAut hN ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hξI (J.subgroupOf K) hJ₀K
      (lab.rank + 1) m' E' hE'data θ₀ hAt'
  refine ⟨B₀, hB₀, hcard, hb₀', fun b hb hbI => (hmem b hb).2 hbI, ?_⟩
  exact ggNbrLangCore_of_langElem hBstar.2.2.2 hN θ (hraw hlabtag hs hna).2.2.1 b₀ hb₀ hB₀ hmem
    ⟨k, e, he1, hep, hefix, hkfix, hke⟩

end CFSG.StandardType
