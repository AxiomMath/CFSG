module

public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.LieModelL3U3Torus
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LieType.SeitzGeneration.QuasiHigh
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGenericCatalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Exc
public import CFSG.HardMathSupport.Dickson.Bal207.SU38Exc

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusNine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSporGenInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LieType.SeitzGeneration
open CFSG.LieType.SeitzGeneration.QuasiHigh
open CFSG.LieType.Seitz (seitzHyperGamma)

theorem exists_unitary_plane_le_sylow
    {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have hXr : 2 ≤ CFSG.Open.pRank 3 X := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hX.two_le_pRank_psu3_of_dvd Nat.prime_three (by norm_num)
  have hPr : 2 ≤ CFSG.Open.pRank 3 P := by
    rwa [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
      Nat.prime_three hP]
  exact UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hPr

theorem closure_unitary_plane_le_of_gamma
    {G : Type} [Group G] [Finite G] {K P M E : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian 3 E)
    (hGamma : rankThreeGamma 1 3 P ≤ M) :
    Subgroup.closure {k : K | ∃ x ∈ E, x ≠ 1 ∧ x * (k : G) = (k : G) * x} ≤
      M.subgroupOf K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro k ⟨x, hxE, hx1, hxk⟩
  have hxo : orderOf x = 3 := orderOf_eq_prime (hE.2 x hxE) hx1
  have hC := CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le
    hGamma (hEP hxE) hxo
  apply hC
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain rfl := Set.mem_singleton_iff.mp hy
  exact hxk

theorem false_of_unitary_plane_generation
    {G : Type} [Group G] [Finite G] {K P M E : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian 3 E)
    (hGamma : rankThreeGamma 1 3 P ≤ M) (hKM : ¬ K ≤ M)
    (hgen : Subgroup.closure
      {k : K | ∃ x ∈ E, x ≠ 1 ∧ x * (k : G) = (k : G) * x} = ⊤) : False := by
  have hle := closure_unitary_plane_le_of_gamma (K := K) hEP hE hGamma
  rw [hgen] at hle
  exact hKM fun k hk => hle (Subgroup.mem_top (⟨k, hk⟩ : K))

private theorem conj_unitary_injective
    {G : Type} [Group G] {X K : Subgroup G} (hXK : X ≤ K)
    (hXq : CFSG.Open.IsQuasisimple X) (hXs : IsSimpleGroup X) :
    Function.Injective ((MulAut.conj : K →* MulAut K).comp (Subgroup.inclusion hXK)) := by
  have hZX : Subgroup.center X = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      hXs (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple hXq)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx1 : MulAut.conj (Subgroup.inclusion hXK x) = 1 := hx
  have hxZ : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun f : MulAut K => f (Subgroup.inclusion hXK y)) hx1
    have h' : (x : G) * (y : G) * (x : G)⁻¹ = y := by
      simpa [MulAut.conj_apply] using congrArg Subtype.val h
    exact Subtype.ext ((mul_inv_eq_iff_eq_mul.mp h').symm)
  rwa [hZX] at hxZ

theorem plane_generation_of_quotient_inner_planeGen
    {G : Type} [Group G] [Finite G] {X K E : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X) (hXs : IsSimpleGroup X)
    (hKq : CFSG.Open.IsQuasisimple K) (hEX : E ≤ X)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center K))
    (hQ : ∀ A : Subgroup (MulAut (K ⧸ Subgroup.center K)),
      IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      A ≤ (MulAut.conj : (K ⧸ Subgroup.center K) →* MulAut (K ⧸ Subgroup.center K)).range →
      PlaneGen A) :
    Subgroup.closure
      {k : K | ∃ x ∈ E, x ≠ 1 ∧ x * (k : G) = (k : G) * x} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : X →* MulAut K :=
    (MulAut.conj : K →* MulAut K).comp (Subgroup.inclusion hXK)
  have hψ : Function.Injective ψ := conj_unitary_injective hXK hXq hXs
  let F := E.subgroupOf X
  have hF : IsElemAbelian 3 F := CFSG.SectionRank.isElemAbelian_subgroupOf hE X
  have hFc : Nat.card F = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hEc]
  let A : Subgroup (MulAut K) := F.map ψ
  have hA : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hF _
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hψ, hFc]
  have hperf := hKq.1
  let β := CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut' K
  have hbarA : IsElemAbelian 3 (A.map β) := CFSG.SectionRank.isElemAbelian_map hA _
  have hbarAc : Nat.card (A.map β) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective
      (CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut'_injective hperf), hAc]
  have hinner : A.map β ≤
      (MulAut.conj : (K ⧸ Subgroup.center K) →* MulAut (K ⧸ Subgroup.center K)).range := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hf
    refine ⟨QuotientGroup.mk (Subgroup.inclusion hXK x), ?_⟩
    exact (CFSG.LieType.SeitzGeneration.QuasiHigh.quotientCenterAut'_conj
      (Subgroup.inclusion hXK x)).symm
  have hbarGen : PlaneGen (A.map β) :=
    hQ (A.map β) hbarA hbarAc hinner
  have hquot := closure_fixed_quotAut_of_seitzHyperGamma hperf
    ((planeGen_iff_seitzHyperGamma Nat.prime_three hbarAc).mp hbarGen)
  have hgen : seitzHyperGamma 3 A = ⊤ :=
    seitzHyperGamma_eq_top_of_coprime_center hperf hZ hA.isPGroup hquot
  have hplane : PlaneGen A := (planeGen_iff_seitzHyperGamma Nat.prime_three hAc).mpr hgen
  apply top_le_iff.mp
  rw [← hplane]
  refine Subgroup.closure_mono ?_
  rintro k ⟨f, ⟨x, hxF, rfl⟩, hf1, hfk⟩
  refine ⟨x.1, hxF, ?_, ?_⟩
  · intro hx1
    have hxK : x = 1 := Subtype.ext hx1
    exact hf1 (hxK ▸ map_one _)
  · have h := congrArg Subtype.val hfk
    simpa [ψ, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using h


theorem plane_generation_of_coprime_center
    {G : Type} [Group G] [Finite G] {X K E : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X) (hXs : IsSimpleGroup X)
    (hKq : CFSG.Open.IsQuasisimple K) (hEX : E ≤ X)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center K))
    (d : TauCeti.ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : 3 ≠ d.1.characteristic)
    (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (hSeitz : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) :
    Subgroup.closure
      {k : K | ∃ x ∈ E, x ≠ 1 ∧ x * (k : G) = (k : G) * x} = ⊤ := by
  exact plane_generation_of_quotient_inner_planeGen hXK hXq hXs hKq hEX hE hEc hZ
    (fun A hA hAc _ => CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.planeGen_of_kfact
      hSeitz Nat.prime_three (by norm_num) d e hpd hex hA hAc)


theorem quotient_center_inclusion_injective
    {G : Type} [Group G] {X K : Subgroup G} (hXK : X ≤ K)
    (hXq : CFSG.Open.IsQuasisimple X) (hXs : IsSimpleGroup X) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center K)).comp
      (Subgroup.inclusion hXK)) := by
  have hZX :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      hXs (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple hXq)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxZ : Subgroup.inclusion hXK x ∈ Subgroup.center K :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hxZX : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact congrArg (fun z : K => (z : G))
      (Subgroup.mem_center_iff.mp hxZ (Subgroup.inclusion hXK y))
  rwa [hZX] at hxZX

theorem unitary_order_dvd_center_quotient
    {G : Type} [Group G] [Finite G] {X K : Subgroup G} (hXK : X ≤ K)
    (hXq : CFSG.Open.IsQuasisimple X)
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3) :
    5515776 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hXs := hX.isSimpleGroup_of_mem_classicalTags
    (by simp [CFSG.Blueprint.classicalTags])
  have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
    (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  rw [← hc]
  let φ := (QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hXK)
  have hφ : Function.Injective φ := quotient_center_inclusion_injective hXK hXq hXs
  rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact Subgroup.card_subgroup_dvd_card φ.range

section LieOrder


theorem not_nineteen_dvd_seitz_exception
    (d : TauCeti.ValidLieTypeIndex)
    (hex : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1) :
    ¬ 19 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  rcases hex with ⟨_, h | h | h | h | h⟩ | ⟨h, _⟩
  · obtain ⟨q, hp, hf, rfl⟩ := h
    have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)
    rw [hp, hf] at hM
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight hM]
    norm_num
  · obtain ⟨q, hp, hf, rfl⟩ := h
    have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group)
    rw [hp, hf] at hM
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hM]
    norm_num
  · obtain ⟨q, hp, hf, rfl⟩ := h
    have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
    rw [hp, hf] at hM
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hM]
    norm_num
  · obtain ⟨q, hp, hf, h⟩ := h
    rcases h with rfl | rfl
    · rcases CFSG.Models.lieModel_B 3 q hv (MulEquiv.refl _) with hM | hM
      · rw [hp, hf] at hM
        exact CFSG.HardMathSupport.Dickson.Bal207.not_nineteen_dvd_card_of_numerator
          (CFSG.HardMathSupport.Dickson.Bal207.dvdAux_blueprint_of_models
            (by simp [CFSG.Blueprint.classicalTags]) hM) (by decide +kernel)
      · rw [hp] at hM
        exact absurd hM.1.2.2.2 (by simp)
    · rcases CFSG.Models.lieModel_B 4 q hv (MulEquiv.refl _) with hM | hM
      · rw [hp, hf] at hM
        exact CFSG.HardMathSupport.Dickson.Bal207.not_nineteen_dvd_card_of_numerator
          (CFSG.HardMathSupport.Dickson.Bal207.dvdAux_blueprint_of_models
            (by simp [CFSG.Blueprint.classicalTags]) hM) (by decide +kernel)
      · rw [hp] at hM
        exact absurd hM.1.2.2.2 (by simp)
  · subst h
    exact CFSG.HardMathSupport.Dickson.Bal207.not_nineteen_dvd_card_tits hv
  · norm_num at h

theorem not_nineteen_dvd_lie_char_three
    {A : Type} [Group A] [Finite A] (d : TauCeti.ValidLieTypeIndex)
    (e : A ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : d.1.characteristic = 3) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup A) ≤ 3) :
    ¬ 19 ∣ Nat.card A := by
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3.rank_dichotomy d hd e with
    h4 | ⟨q, hq, hc, _⟩ | ⟨q, hq, hc⟩ | ⟨q, hq, hc⟩
  · omega
  · obtain ⟨d, hv⟩ := d
    change d = .A 1 q at hq
    subst hq
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hp : q.p = 3 := by simpa using hd
    have hf : q.exponent = 3 := by
      have hpow : 3 ^ q.exponent = 3 ^ 3 := by
        simpa [TauCeti.PrimePower.card_def, hp] using hc
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ))) hpow
    rw [hp, hf] at hm
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hm]
    decide +kernel
  · obtain ⟨d, hv⟩ := d
    change d = .A 2 q at hq
    subst hq
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hp : q.p = 3 := by simpa using hd
    have hf : q.exponent = 1 := by
      have hpow : 3 ^ q.exponent = 3 ^ 1 := by
        simpa [TauCeti.PrimePower.card_def, hp] using hc
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ))) hpow
    rw [hp, hf] at hm
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three hm]
    norm_num
  · obtain ⟨d, hv⟩ := d
    change d = .twistedA 2 q at hq
    subst hq
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hp : q.p = 3 := by simpa using hd
    have hf : q.exponent = 1 := by
      have hpow : 3 ^ q.exponent = 3 ^ 1 := by
        simpa [TauCeti.PrimePower.card_def, hp] using hc
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ))) hpow
    rw [hp, hf] at hm
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm]
    norm_num

end LieOrder

theorem false_of_unitary_alternating_quotient
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X)
    (hKq : CFSG.Open.IsQuasisimple K)
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3)
    (hr : CFSG.Open.pRank 3 K ≤ 3) {n : ℕ} (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) : False := by
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hKq.1
  have hr' : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hnr := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.le_pRank_top
    hn e Nat.prime_three (by norm_num)
  have hn11 : n ≤ 11 := by omega
  have h19 : 19 ∣ Nat.card (K ⧸ Subgroup.center K) :=
    (by norm_num : 19 ∣ 5515776).trans (unitary_order_dvd_center_quotient hXK hXq hX)
  rw [Nat.card_congr e.toEquiv] at h19
  have hnot : ¬ 19 ∣ Nat.card (alternatingGroup (Fin n)) := by
    interval_cases n <;>
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;>
      decide +kernel
  exact hnot h19

theorem three_le_pRank_of_unitary_three_center
    {G : Type} [Group G] [Finite G] {X K P : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X)
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) : 3 ≤ CFSG.Open.pRank 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEP, hE, hEc⟩ := exists_unitary_plane_le_sylow hX hP
  have hEX : E ≤ X := hEP.trans hP.le
  have hZX :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      (hX.isSimpleGroup_of_mem_classicalTags (by simp [CFSG.Blueprint.classicalTags]))
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple hXq)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hZ
  let zG : G := (z : K)
  have hzorder : orderOf zG = 3 := by
    change orderOf (((z : Subgroup.center K) : K) : G) = 3
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzX : zG ∉ X := by
    intro hzX
    have hxZ : (⟨zG, hzX⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact congrArg (fun k : K => (k : G))
        (Subgroup.mem_center_iff.mp z.2 (Subgroup.inclusion hXK y))
    rw [hZX, Subgroup.mem_bot] at hxZ
    have hz1 : zG = 1 := congrArg Subtype.val hxZ
    rw [hz1, orderOf_one] at hzorder
    norm_num at hzorder
  have hzC : zG ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg (fun k : K => (k : G))
      (Subgroup.mem_center_iff.mp z.2 ⟨y, hXK (hEX hy)⟩)
  exact CFSG.AGLEmbedding.three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer
    Nat.prime_three hE hEc hzorder (fun h => hzX (hEX h)) hzC
    (hEX.trans hXK) (z : K).2


section SporadicQuotient

theorem false_of_unitary_sporadic_quotient
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X)
    (_hKq : CFSG.Open.IsQuasisimple K)
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3)
    (hr : CFSG.Open.pRank 3 K ≤ 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center K)) {s : TauCeti.SporadicName}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv := unitary_order_dvd_center_quotient hXK hXq hX
  rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s]
    at hdiv
  have hFour : CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree.RankFourSporadic s := by
    cases s <;> simp_all [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd,
      orderJ3, orderJ4, orderRu, orderTh, orderBabyMonster, orderMonster, orderON, orderHN,
      orderFi23, orderFi24Prime, orderCo1, orderLy, CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree.RankFourSporadic]
  have h4 := CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree.four_le_pRank_of_rankFourSporadic s hFour
    (K ⧸ Subgroup.center K) ⟨e⟩
  have hq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hr
  omega

end SporadicQuotient

section ThreeCenter

theorem rest15_false_of_unitary_three_center
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (S : Setup4 G) {X H K P : Subgroup G}
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H)
    (hXK : X ≤ K) (_hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (_hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) : False := by
  have hKq : CFSG.Open.IsQuasisimple K := hKcomp.2.2
  have hXq : CFSG.Open.IsQuasisimple X := hXcomp.2.2
  have hKtop : K ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hKcomp.1))
  have hcat := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup
    hKq (hS.kProper.isKGroup K hKtop)
  have hKr : CFSG.Open.pRank 3 K ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  have hK3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact Nat.le_antisymm hKr (three_le_pRank_of_unitary_three_center hXK hXq hX hP hZ)
  have hON := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_threeCover_of_three_dvd
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    K hKq hcat hZ hK3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel
    (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148H.exists_orderOf_nine_projSU_three_eight
  let x : K := Subgroup.inclusion hXK (e.symm a)
  have hx : orderOf x = 9 := by
    calc orderOf x = orderOf (x : G) := (Subgroup.orderOf_coe x).symm
      _ = orderOf ((e.symm a : X) : G) := rfl
      _ = orderOf (e.symm a) := Subgroup.orderOf_coe _
      _ = orderOf a := e.symm.orderOf_eq _
      _ = 9 := ha
  have hpg : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨T, hT⟩ := hpg.exists_le_sylow
  have hx3 : x ^ 3 = 1 := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
    K hON T x (hT (Subgroup.mem_zpowers x))
  have hdiv := orderOf_dvd_of_pow_eq_one hx3
  rw [hx] at hdiv
  norm_num at hdiv

end ThreeCenter

section ActualSeitz

theorem rest15_false_of_unitary_overcomponent
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (S : Setup4 G) {X H K P : Subgroup G}
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H)
    (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKq : CFSG.Open.IsQuasisimple K := hKcomp.2.2
  have hXq : CFSG.Open.IsQuasisimple X := hXcomp.2.2
  have hKr : CFSG.Open.pRank 3 K ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center K)
  · exact rest15_false_of_unitary_three_center hS S hHtop hHr hXcomp hKcomp
      hXK hKM hX hP hGamma hZ
  have hKtop : K ≠ ⊤ := fun h => hHtop
    (top_le_iff.mp (h ▸ hKcomp.1))
  have hcat := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup
    hKq (hS.kProper.isKGroup K hKtop)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hrq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hKr
  have h19 : 19 ∣ Nat.card (K ⧸ Subgroup.center K) :=
    (by norm_num : 19 ∣ 5515776).trans (unitary_order_dvd_center_quotient hXK hXq hX)
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.exists_noncomm_quot hKq
    apply hab
    apply e.injective
    simpa only [map_mul] using mul_comm (e a) (e b)
  | alternating n hn =>
    exact false_of_unitary_alternating_quotient hXK hXq hKq hX hKr hn e
  | lie d =>
    by_cases hd : d.1.characteristic = 3
    · exact not_nineteen_dvd_lie_char_three d e hd hrq h19
    by_cases hex : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1
    · exact not_nineteen_dvd_seitz_exception d hex
        (by rwa [Nat.card_congr e.toEquiv] at h19)
    obtain ⟨E, hEP, hE, hEc⟩ := exists_unitary_plane_le_sylow hX hP
    have hEX : E ≤ X := hEP.trans hP.le
    have hXs := hX.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags])
    exact false_of_unitary_plane_generation hEP hE hGamma hKM
      (plane_generation_of_coprime_center hXK hXq hXs hKq hEX hE hEc hZ
        d e (Ne.symm hd) hex kFactSeitzRankTwo_holds)
  | sporadic s =>
    exact false_of_unitary_sporadic_quotient hXK hXq hKq hX hKr hZ e

end ActualSeitz

end CFSG.LocalAnalysis.UniquenessCase.UC22
