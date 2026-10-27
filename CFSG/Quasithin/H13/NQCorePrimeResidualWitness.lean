module

public import CFSG.Quasithin.H13.NQBlockPrimeResidualCenter
public import CFSG.Quasithin.H13.NQCatSubnormalCore
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {E : Type*} [Group E]

theorem omegaOneCenterOf_normal (p : ℕ) (R : Subgroup E) [R.Normal] :
    (NQBlock.omegaOneCenterOf p R).Normal :=
  ⟨fun _ hu g =>
    NQBlock.conj_mem_omegaOneCenterOf (by rw [normalizer_eq_top]; exact mem_top g) hu⟩

theorem centerTorsion_le_omegaOneCenterOf (p : ℕ) (R : Subgroup E) :
    centerTorsion p R ≤ NQBlock.omegaOneCenterOf p R := fun z hz => by
  obtain ⟨hzR, hzc, hzp⟩ := mem_centerTorsion_iff.mp hz
  exact NQBlock.subset_omegaOneCenterOf hzR (mem_centralizer_iff.mpr hzc) hzp

theorem centralPChief_of_surjective_of_le_ker {p : ℕ} {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') (hφ : Function.Surjective φ) {K₀ : Subgroup H} (hK₀ : K₀ ≤ φ.ker)
    (h : ∀ B A : Subgroup H, CFSG.IsChiefFactor B A → K₀ ≤ B →
      (∃ n : ℕ, B.relIndex A = p ^ n) → ⁅A, ⊤⁆ ≤ B) :
    CFSG.QuasithinUnique.Setup.Offender.CentralPChief p H' := by
  intro K' X' hc hpow
  have hKn := hc.normal_K
  have hXn := hc.normal_H
  have hK : (K'.comap φ).Normal := inferInstance
  have hX : (X'.comap φ).Normal := inferInstance
  have hkerK : φ.ker ≤ K'.comap φ := fun x hx => by
    show φ x ∈ K'
    rw [MonoidHom.mem_ker.1 hx]
    exact K'.one_mem
  have hchief : CFSG.IsChiefFactor (K'.comap φ) (X'.comap φ) := by
    refine ⟨hK, hX, ?_, fun Q hQ hKQ hQX => ?_⟩
    · exact (Subgroup.comap_lt_comap_of_surjective hφ).2 hc.lt
    · have hQm : (Q.map φ).Normal := hQ.map φ hφ
      have hker : φ.ker ≤ Q := hkerK.trans hKQ
      have h1 : K' ≤ Q.map φ := by
        calc K' = (K'.comap φ).map φ := (Subgroup.map_comap_eq_self_of_surjective hφ K').symm
          _ ≤ Q.map φ := Subgroup.map_mono hKQ
      have h2 : Q.map φ ≤ X' := by
        calc Q.map φ ≤ (X'.comap φ).map φ := Subgroup.map_mono hQX
          _ = X' := Subgroup.map_comap_eq_self_of_surjective hφ X'
      have hQeq : Q = (Q.map φ).comap φ := by
        rw [Subgroup.comap_map_eq, sup_eq_left.2 hker]
      rcases hc.is_maximal (Q.map φ) hQm h1 h2 with h3 | h3
      · left; rw [hQeq, h3]
      · right; rw [hQeq, h3]
  have hidx : (K'.comap φ).relIndex (X'.comap φ) = K'.relIndex X' := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hφ]
  have := h _ _ hchief (hK₀.trans hkerK) ⟨hpow.choose, by rw [hidx]; exact hpow.choose_spec⟩
  have h4 := Subgroup.map_mono (f := φ) this
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφ,
    Subgroup.map_top_of_surjective φ hφ, Subgroup.map_comap_eq_self_of_surjective hφ] at h4
  exact h4

theorem commute_of_commutator_mem_central_pCore {G : Type*} [Group G] {p : ℕ}
    {Y : Subgroup G} (hno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient p Y)
    (hZ : CFSG.pCore p Y ≤ center Y) {r : G}
    (hr : ∀ y ∈ Y, ⁅y, r⁆ ∈ (CFSG.pCore p Y).map Y.subtype) :
    ∀ y ∈ Y, y * r = r * y := by
  have hrY : ∀ y ∈ Y, ⁅y, r⁆ ∈ Y := fun y hy => map_subtype_le _ (hr y hy)
  have hmem : ∀ y : Y, (⟨⁅(y : G), r⁆, hrY y y.2⟩ : Y) ∈ CFSG.pCore p Y := by
    intro y
    obtain ⟨z, hz, hzeq⟩ := hr y y.2
    have hz' : (⟨⁅(y : G), r⁆, hrY y y.2⟩ : Y) = z := Subtype.ext hzeq.symm
    rw [hz']
    exact hz
  have hcen : ∀ y ∈ Y, ∀ z ∈ Y, z * ⁅y, r⁆ = ⁅y, r⁆ * z := fun y hy z hz =>
    congrArg Subtype.val (mem_center_iff.mp (hZ (hmem ⟨y, hy⟩)) ⟨z, hz⟩)
  have hmul : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a * b, r⁆ = ⁅a, r⁆ * ⁅b, r⁆ := by
    intro a ha b hb
    have h1 := hcen b hb a ha
    have h2 := hcen a ha _ (hrY b hb)
    calc ⁅a * b, r⁆ = a * ⁅b, r⁆ * r * a⁻¹ * r⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅b, r⁆ * a * r * a⁻¹ * r⁻¹ := by rw [h1]
      _ = ⁅b, r⁆ * ⁅a, r⁆ := by simp only [commutatorElement_def]; group
      _ = ⁅a, r⁆ * ⁅b, r⁆ := h2
  let f : Y →* CFSG.pCore p Y :=
    MonoidHom.mk' (fun y => ⟨⟨⁅(y : G), r⁆, hrY y y.2⟩, hmem y⟩) fun a b =>
      Subtype.ext (Subtype.ext (hmul a a.2 b b.2))
  have hpq : IsPGroup p (Y ⧸ f.ker) :=
    (CFSG.pCore_isPGroup (p := p) (G := Y)).of_injective (QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)
  have htop := hno f.ker hpq
  intro y hy
  have hy1 : f ⟨y, hy⟩ = 1 := by
    rw [← MonoidHom.mem_ker, htop]
    exact mem_top _
  have h2 : ⁅y, r⁆ = 1 := congrArg (fun z : CFSG.pCore p Y => ((z : Y) : G)) hy1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem prime_residual_subnormal_reduced_witness [Finite E] {p : ℕ} [hp : Fact p.Prime]
    {X : Subgroup E} (hX : X.IsSubnormal)
    (hno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient p X) :
    ((∃ V : Subgroup E, IsPrimeReduced p V ∧ ⁅V, X⁆ ≠ ⊥) ↔
        ⁅primeReducedAggregate E p, X⁆ ≠ ⊥) ∧
      ((∃ V : Subgroup E, IsPrimeReduced p V ∧ ⁅V, X⁆ ≠ ⊥) →
        ⁅NQBlock.omegaOneCenterOf p ((CFSG.pCore p X).map X.subtype), X⁆ ≠ ⊥) ∧
      (⁅primeReducedAggregate E p, X⁆ ≠ ⊥ →
        ⁅NQBlock.omegaOneCenterOf p ((CFSG.pCore p X).map X.subtype), X⁆ ≠ ⊥) ∧
      ((∀ B A : Subgroup X, CFSG.IsChiefFactor B A → CFSG.pCore p X ≤ B →
          (∃ n : ℕ, B.relIndex A = p ^ n) → ⁅A, ⊤⁆ ≤ B) →
        ((⁅NQBlock.omegaOneCenterOf p ((CFSG.pCore p X).map X.subtype), X⁆ ≠ ⊥ ↔
            ∃ V : Subgroup E, IsPrimeReduced p V ∧ ⁅V, X⁆ ≠ ⊥) ∧
          (⁅NQBlock.omegaOneCenterOf p ((CFSG.pCore p X).map X.subtype), X⁆ ≠ ⊥ ↔
            ⁅primeReducedAggregate E p, X⁆ ≠ ⊥))) := by
  classical
  set Q : Subgroup E := (CFSG.pCore p X).map X.subtype with hQdef
  set R : Subgroup E := CFSG.pCore p E with hRdef
  set U : Subgroup E := NQBlock.omegaOneCenterOf p R with hUdef
  have hRn : R.Normal := CFSG.pCore_normal
  have hRp : IsPGroup p R := CFSG.pCore_isPGroup
  have hQR : Q ≤ R := NQCat.map_pCore_le_pCore_of_isSubnormal' hX
  have haU : ⁅NQBlock.omegaOneCenterOf p Q, X⁆ ≠ ⊥ ↔ ⁅U, X⁆ ≠ ⊥ :=
    not_congr (NQBlock.prime_residual_subnormal_core_center_action hX hno hRp hQR)
  have hbc : (∃ V : Subgroup E, IsPrimeReduced p V ∧ ⁅V, X⁆ ≠ ⊥) ↔
      ⁅primeReducedAggregate E p, X⁆ ≠ ⊥ := by
    constructor
    · rintro ⟨V, hV, hVX⟩ hbot
      apply hVX
      rw [eq_bot_iff, ← hbot]
      exact commutator_mono (le_primeReducedAggregate hV) le_rfl
    · intro h
      exact ⟨_, isPrimeReduced_primeReducedAggregate p, h⟩
  have hba : (∃ V : Subgroup E, IsPrimeReduced p V ∧ ⁅V, X⁆ ≠ ⊥) →
      ⁅NQBlock.omegaOneCenterOf p Q, X⁆ ≠ ⊥ := by
    rintro ⟨V, hV, hVX⟩
    rw [haU]
    intro hbot
    apply hVX
    rw [eq_bot_iff, ← hbot]
    exact commutator_mono ((isPrimeReduced_le_centerTorsion_pCore hV).trans
      (centerTorsion_le_omegaOneCenterOf p R)) le_rfl
  refine ⟨hbc, hba, fun h => hba (hbc.mpr h), fun hchief => ?_⟩
  have hab : ⁅NQBlock.omegaOneCenterOf p Q, X⁆ ≠ ⊥ →
      ∃ V : Subgroup E, IsPrimeReduced p V ∧ ⁅V, X⁆ ≠ ⊥ := by
    intro ha
    have hUX : ⁅U, X⁆ ≠ ⊥ := haU.mp ha
    have hUn : U.Normal := omegaOneCenterOf_normal p R
    obtain ⟨V, -, hVmin⟩ := Finite.exists_le_minimal
      (p := fun W : Subgroup E => W.Normal ∧ W ≤ U ∧ ⁅W, X⁆ ≠ ⊥) ⟨hUn, le_rfl, hUX⟩
    obtain ⟨hVn, hVU, hVX⟩ := hVmin.prop
    refine ⟨V, ?_, hVX⟩
    have hUR : ∀ u ∈ U, u ∈ R ∧ ∀ r ∈ R, r * u = u * r := fun u hu =>
      ⟨(mem_inf.mp (NQBlock.omegaOneCenterOf_le p R hu)).1,
        mem_centralizer_iff.mp (mem_inf.mp (NQBlock.omegaOneCenterOf_le p R hu)).2⟩
    have hVe : CFSG.IsElementaryAbelian p V := isElementaryAbelian_iff.mpr
      ⟨fun a ha b hb => (hUR b (hVU hb)).2 a (hUR a (hVU ha)).1,
        fun a ha => NQBlock.pow_eq_one_of_mem_omegaOneCenterOf (hVU ha)⟩
    have hVp : IsPGroup p V := hRp.to_le fun v hv => (hUR v (hVU hv)).1
    refine ⟨hVn, hVe, ?_⟩
    set C : Subgroup E := centralizer (V : Set E) with hCdef
    have hCn : C.Normal := by
      rw [hCdef]
      infer_instance
    set π : E →* E ⧸ C := QuotientGroup.mk' C with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective C
    have hkerπ : π.ker = C := QuotientGroup.ker_mk' C
    set P : Subgroup (E ⧸ C) := CFSG.pCore p (E ⧸ C) with hPdef
    have hPn : P.Normal := CFSG.pCore_normal
    have hPp : IsPGroup p P := CFSG.pCore_isPGroup
    set Y : Subgroup (E ⧸ C) := X.map π with hYdef
    have hYs : Y.IsSubnormal := hX.map hπs
    let θ : X →* Y := π.subgroupMap X
    have hθs : Function.Surjective θ := π.subgroupMap_surjective X
    have hnoY : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient p Y :=
      CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective θ hθs hno
    have hRC : R ≤ C := fun r hr => mem_centralizer_iff.mpr fun v hv =>
      ((hUR v (hVU hv)).2 r hr).symm
    have hK₀ : CFSG.pCore p X ≤ θ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show π (x : E) = 1
      rw [← MonoidHom.mem_ker, hkerπ]
      exact hRC (hQR ⟨x, hx, rfl⟩)
    have hchY : CFSG.QuasithinUnique.Setup.Offender.CentralPChief p Y :=
      centralPChief_of_surjective_of_le_ker θ hθs hK₀ hchief
    have hZY : CFSG.pCore p Y ≤ center Y :=
      CFSG.QuasithinUnique.Setup.Offender.pCore_le_center_of_central_chief hp.out hnoY hchY
    obtain ⟨-, hYP⟩ :=
      CFSG.QuasithinUnique.Setup.Campbell.prime_residual_subnormal_p_signalizer_action hYs hnoY
        hPp fun y _ => by rw [normalizer_eq_top]; exact mem_top y
    rw [CFSG.QuasithinUnique.Setup.Campbell.pCoreOf_eq] at hYP
    have hYPc : ∀ y ∈ Y, ∀ r ∈ P, y * r = r * y := fun y hy r hr =>
      commute_of_commutator_mem_central_pCore hnoY hZY
        (fun z hz => hYP (commutator_mem_commutator hz hr)) y hy
    have hCker : C ≤ (MulAut.conjNormal : E →* MulAut V).ker := by
      intro c hc
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have h1 : (v : E) * c = c * v := mem_centralizer_iff.mp hc v v.2
      rw [← h1, mul_inv_cancel_right]
    let β₀ : E ⧸ C →* MulAut V := QuotientGroup.lift C MulAut.conjNormal hCker
    let β : P →* MulAut V := β₀.comp P.subtype
    let α : X →* MulAut V := MulAut.conjNormal.comp X.subtype
    have hβapp : ∀ (g : E) (hg : π g ∈ P) (v : V),
        ((β ⟨π g, hg⟩ v : V) : E) = g * v * g⁻¹ := fun _ _ _ => rfl
    have hαapp : ∀ (x : X) (v : V), ((α x v : V) : E) = x * v * (x : E)⁻¹ := fun _ _ => rfl
    have hcomm : ∀ (x : X) (b : P), α x * β b = β b * α x := by
      intro x b
      obtain ⟨e, he⟩ := hπs (b : E ⧸ C)
      have hbe : b = ⟨π e, he ▸ b.2⟩ := Subtype.ext he.symm
      have hxe : π x * π e = π e * π x := by
        rw [he]
        exact hYPc (π x) ⟨x, x.2, rfl⟩ b b.2
      have hc : ((x : E) * e)⁻¹ * (e * x) ∈ C := by
        rw [← hkerπ]
        refine MonoidHom.mem_ker.mpr ?_
        rw [map_mul, map_inv, map_mul, map_mul, hxe, inv_mul_cancel]
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, hbe, hαapp, hβapp, hβapp, hαapp]
      set c : E := ((x : E) * e)⁻¹ * (e * x) with hcdef
      have hex : e * (x : E) = (x : E) * e * c := by rw [hcdef]; group
      have hcv : (v : E) * c = c * v := mem_centralizer_iff.mp hc v v.2
      calc (x : E) * (e * v * e⁻¹) * (x : E)⁻¹
          = (x : E) * e * (c * v * c⁻¹) * e⁻¹ * (x : E)⁻¹ := by rw [← hcv]; group
        _ = (e * x) * v * (e * x)⁻¹ := by rw [hex]; group
        _ = e * ((x : E) * v * (x : E)⁻¹) * e⁻¹ := by group
    have hfix := (CFSG.ComponentClassification.OutcomeLocal.prime_residual_commuting_fixed_points
      hVp hno hPp α β hcomm).mp
    set PE : Subgroup E := P.comap π with hPE
    have hPEn : PE.Normal := hPn.comap π
    set D : Subgroup E := V ⊓ centralizer (PE : Set E) with hD
    have hDn : D.Normal := by
      rw [hD]
      infer_instance
    by_cases hDX : ⁅D, X⁆ = ⊥
    ·
      exfalso
      apply hVX
      have h1 : ∀ (x : X) (v : V), (∀ b : P, β b v = v) → α x v = v := by
        intro x v hv
        have hvD : (v : E) ∈ D := by
          refine ⟨v.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
          have h3 : g * (v : E) * g⁻¹ = v := by
            rw [← hβapp g hg v]
            exact congrArg Subtype.val (hv ⟨π g, hg⟩)
          calc g * (v : E) = g * v * g⁻¹ * g := by group
            _ = v * g := by rw [h3]
        have h4 := (commutator_eq_bot_iff_le_centralizer.mp hDX) hvD
        apply Subtype.ext
        rw [hαapp, mem_centralizer_iff.mp h4 x x.2, mul_inv_cancel_right]
      have h5 := hfix h1
      rw [commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [mem_centralizer_iff]
      intro x hx
      have h6 : x * v * x⁻¹ = v := by
        rw [← hαapp ⟨x, hx⟩ ⟨v, hv⟩]
        exact congrArg Subtype.val (h5 ⟨x, hx⟩ ⟨v, hv⟩)
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [h6]
    ·
      have hDV : D ≤ V := inf_le_left
      have hVD : V ≤ D := hVmin.2 ⟨hDn, hDV.trans hVU, hDX⟩ hDV
      have hPEC : PE ≤ C := by
        show PE ≤ centralizer (V : Set E)
        rw [le_centralizer_iff]
        exact fun v hv => (hVD hv).2
      rw [eq_bot_iff]
      intro b hb
      obtain ⟨e, rfl⟩ := hπs b
      rw [mem_bot, ← MonoidHom.mem_ker, hkerπ]
      exact hPEC hb
  exact ⟨⟨hab, hba⟩, fun h => hbc.mp (hab h), fun h => hba (hbc.mpr h)⟩

end CFSG.Quasithin.H13.NQCore
