module

public import CFSG.Quasithin.EmptyFaithful.S153H32

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def XSIrreducibleOnP32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Preamble32 T V₁ I L → Clause32One T I L →
      Clause32Four T M V₁ I L →
        ∀ D : Subgroup G, pCoreOf 2 I ≤ D → D ≤ pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) →
          X153 T M V₁ ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (D : Set G) →
            D = pCoreOf 2 I ∨ D = pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁)

namespace SBd2

section Generic

variable {G : Type} [Group G]

theorem mem_conjBy_iff {t x : G} {X : Subgroup G} : x ∈ conjBy153 t X ↔ t⁻¹ * x * t ∈ X := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show t⁻¹ * (t * y * t⁻¹) * t ∈ X
    rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group]
  · intro hy
    exact ⟨t⁻¹ * x * t, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_centralizer_conjBy_iff {t x : G} {X : Subgroup G} :
    x ∈ Subgroup.centralizer (conjBy153 t X : Set G) ↔
      t⁻¹ * x * t ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have h1 := h (t * u * t⁻¹) (mem_conjBy_iff.mpr (by rw [show t⁻¹ * (t * u * t⁻¹) * t = u by group]; exact hu))
    have e : u * (t⁻¹ * x * t) = t⁻¹ * ((t * u * t⁻¹) * x) * t := by group
    have e' : t⁻¹ * x * t * u = t⁻¹ * (x * (t * u * t⁻¹)) * t := by group
    rw [e, h1, ← e']
  · intro h u hu
    have hu' := mem_conjBy_iff.mp hu
    have h1 := h _ hu'
    have e : u * x = t * ((t⁻¹ * u * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
    have e' : x * u = t * ((t⁻¹ * x * t) * (t⁻¹ * u * t)) * t⁻¹ := by group
    rw [e, e', h1]

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input32SixP_of_irreducible (h113 : StageLemma14113) (hirr : XSIrreducibleOnP32) :
    Input32SixP := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hpre h1 h4 _h5 t' ht' hnS
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have Dc : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
    c25.facts.case_two.2
  obtain ⟨hLc, hLn, -⟩ := c25.conc
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hh Dc
  have hTX : T ≤ Subgroup.normalizer (X153 T M V₁ : Set G) := S153H.T_le_normalizer_X c
  have hSI : Sgp153 T V₁ ≤ I := S153H.Sgp153_le_I c
  have hLI : L ≤ I := S153H.L_le_I c
  have hYL : Yp ≤ L := c.c27.Yp_le
  have h4' := h4
  obtain ⟨K, hKL, -, -, hX⟩ := h4
  have hXL : X153 T M V₁ ≤ L :=
    hX ▸ (((Subgroup.closure_le _).mpr fun x hx => hx.1 : oPrimeResidualOf 3 K ≤ K).trans hKL)
  have hXSI : X153 T M V₁ ⊔ Sgp153 T V₁ ≤ I := sup_le (hXL.trans hLI) hSI
  have hTXS : T ≤ Subgroup.normalizer ((X153 T M V₁ ⊔ Sgp153 T V₁ : Subgroup G) : Set G) :=
    fun g hg => S153H.mem_normalizer_sup (hTX hg) (hTS hg)
  have hSt : ∀ x : G, t'⁻¹ * x * t' ∈ Sgp153 T V₁ ↔ x ∈ Sgp153 T V₁ := fun x => by
    have := Subgroup.mem_normalizer_iff.mp (hTS (T.inv_mem ht')) x
    rw [inv_inv] at this
    exact this.symm
  have hPIC : pCoreOf 2 I = Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G) :=
    hpre.2.1.trans hpre.2.2
  have hPIS : pCoreOf 2 I ≤ Sgp153 T V₁ := S153D.pCoreOf_le_Sgp153' hF
  have hF2 : Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G) =
      conjBy153 t' (pCoreOf 2 I) := by
    ext x
    constructor
    · rintro ⟨hxS, hxC⟩
      refine mem_conjBy_iff.mpr ?_
      rw [hPIC]
      exact ⟨(hSt x).mpr hxS, mem_centralizer_conjBy_iff.mp hxC⟩
    · intro hx
      have h2 := mem_conjBy_iff.mp hx
      rw [hPIC] at h2
      exact ⟨(hSt x).mp h2.1, mem_centralizer_conjBy_iff.mpr h2.2⟩
  rw [hF2, ← hPIC]
  have hIN : I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := le_normalizer_pCoreOf 2 I
  have hPI2 : IsPGroup 2 ↥(pCoreOf 2 I) := pCoreOf_isPGroup 2 I
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hF.sylow.2.1
  have hPIle : pCoreOf 2 I ≤ pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) :=
    le_pCoreOf_of_le_normalizer 2 (hPIS.trans le_sup_right) (hXSI.trans hIN) hPI2
  have hPItS : conjBy153 t' (pCoreOf 2 I) ≤ Sgp153 T V₁ := by
    rintro _ ⟨p, hp, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTS ht') p).mp (hPIS hp)
  have hNPIt : ∀ g ∈ X153 T M V₁ ⊔ Sgp153 T V₁,
      g ∈ Subgroup.normalizer ((conjBy153 t' (pCoreOf 2 I) : Subgroup G) : Set G) := by
    intro g hg
    refine S153H.mem_normalizer_conjBy ?_
    have h1' : t'⁻¹ * g * t' ∈ X153 T M V₁ ⊔ Sgp153 T V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTXS (T.inv_mem ht')) g).mp hg
      simpa using this
    exact hIN (hXSI h1')
  have hPItle : conjBy153 t' (pCoreOf 2 I) ≤ pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) :=
    le_pCoreOf_of_le_normalizer 2 (hPItS.trans le_sup_right) (fun g hg => hNPIt g hg)
      (hS2.to_le hPItS)
  have hDle : pCoreOf 2 I ⊔ conjBy153 t' (pCoreOf 2 I) ≤
      pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) := sup_le hPIle hPItle
  have hDN : X153 T M V₁ ⊔ Sgp153 T V₁ ≤
      Subgroup.normalizer ((pCoreOf 2 I ⊔ conjBy153 t' (pCoreOf 2 I) : Subgroup G) : Set G) :=
    fun g hg => S153H.mem_normalizer_sup (hIN (hXSI hg)) (hNPIt g hg)
  rcases hirr G T Mc M V₁ V₂ Yp I L t c hpre h1 h4' _ le_sup_left hDle hDN with hD | hD
  ·
    exfalso
    have hPItPI : conjBy153 t' (pCoreOf 2 I) ≤ pCoreOf 2 I := by
      have h2 : conjBy153 t' (pCoreOf 2 I) ≤ pCoreOf 2 I ⊔ conjBy153 t' (pCoreOf 2 I) := le_sup_right
      rwa [hD] at h2
    have hcard : Nat.card ↥(conjBy153 t' (pCoreOf 2 I)) = Nat.card ↥(pCoreOf 2 I) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj t').toMonoidHom) (MulAut.conj t').injective
    have hPIteq : conjBy153 t' (pCoreOf 2 I) = pCoreOf 2 I :=
      Subgroup.eq_of_le_of_card_ge hPItPI hcard.symm.le
    have ht'N : t' ∈ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPIteq
    have hidx : (Sgp153 T V₁).relIndex T = 2 := Dc.relIndex_nS hh
    have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := by
      intro g hg
      rcases coset_of_relIndex_two hidx hg ht' hnS with hgS | hgS
      · exact hIN (hSI hgS)
      · have e : g = (g * t'⁻¹) * t' := by group
        rw [e]
        exact Subgroup.mul_mem _ (hIN (hSI hgS)) ht'N
    have hLN : L ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := hLI.trans hIN
    have hPIne : pCoreOf 2 I ≠ ⊥ := c25.ctx.inH.1.2
    have hInH : InH (Yp ⊔ T) (Subgroup.normalizer (pCoreOf 2 I : Set G)) :=
      ⟨sup_le (hYL.trans hLN) hTN, fun hb => hPIne (le_bot_iff.mp
        (hb ▸ le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hPI2))⟩
    have hYM : Yp ≤ M := by
      rw [hYp]
      exact (oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))
    rcases hh.lemma_15_3_2_four (X := Yp ⊔ T) le_sup_right (sup_le hYM hh.T_le) with hres | ⟨-, hU⟩
    · exfalso
      have hYres : Yp ≤ opResidual 2 (Yp ⊔ T) := by
        have h2 : oTwoUpper Yp ≤ opResidual 2 (Yp ⊔ T) := by
          refine (Subgroup.closure_le _).mpr fun x hx => ?_
          exact mem_opResidual_of_coprime (Subgroup.mem_sup_left hx.1)
            (Nat.coprime_two_right.mpr hx.2)
        rwa [hyp.oTwoUpper_eq] at h2
      exact hh.Yplus_not_le_centralizer h113 Dc (hYp ▸ hYres.trans hres)
    · exact hLn (le_inf (hLN.trans (le_of_isUniqueM hU hInH)) hLI)
  · exact hD.symm

end Context

end SBd2

end CFSG.Quasithin
