module

public import CFSG.Quasithin.EmptyFaithful.SzN15Top

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153F

open CFSG.Quasithin.S153D

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input15320M_of_named_inputs3 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (kN : SL3Sp4NotA38Type) (kA : SzN15.NoGraphAutOnFFModule3) (kB : SolvOvergroupsInBorel)
    (kC : RankTwoMaxParabolics) : Input15320M := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _ _ _
  have key : IsSL3Quot L ∨ IsSp4Quot L → False := by
    intro hlie
    have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
    have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
    have hF : Facts15311 T M V₁ Yp I := c.facts
    obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
    have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
    have hLle : L ≤ I := le_of_mem_cComp hLI
    have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
      isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
    have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh hI hLI
    have hSQL : SQTKGroup ↥L := by
      have hq := hh.hyp.qtfe
      have := hq.simple
      have hSQI : SQTKGroup ↥I :=
        InternalSec.sqtkGroup_of_localSQTK (qtkeCore_of_cat hq.nonabelian hq.qtke).1 hI.1.2
      exact InternalSec.sqtkGroup_mono hSQI hLle
    have hSIL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
      have hq := hh.hyp.qtfe
      rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hI.1.2 hLI with hn | ⟨-, h2⟩
      · exact hF.sylow.1.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn)
      · exact absurd h2 (kN G L hlie)
    have hAR : Sgp153 T V₁ ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
      le_sup_right.trans (le_normalizer_pCoreOf 2 _)
    have hAS : Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
      F7.le_normalizer_inf Subgroup.le_normalizer hSIL
    obtain ⟨hC1, hC2, -⟩ := c.c16.desc
    have hR2 : IsPGroup 2 ↥(R153 T V₁ Yp) := pCoreOf_isPGroup 2 _
    have hAP := kA G L (R153 T V₁ Yp) (Sgp153 T V₁) (Sgp153 T V₁ ⊓ L) hlie hSQL hSL hR2
      c.c16.R_norm hSIL hAR hAS ⟨hC1, hC2⟩
    obtain ⟨P₁, P₂, hP₁, hP₂, hne, hB₁, hB₂, huniq⟩ := kC G L (Sgp153 T V₁ ⊓ L) hlie hSL
    have hSLsolv : Group.IsSolvable ↥(Sgp153 T V₁ ⊓ L) := F1.isSolvable_of_isPGroup_two hSL.2.1
    have hSLn : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (Yp : Set G) :=
      inf_le_left.trans (Sgp153_le_normalizer_Yp hh)
    have hXsolv : Group.IsSolvable ↥(Yp ⊔ (Sgp153 T V₁ ⊓ L)) :=
      F1.isSolvable_sup_of_le_normalizer (isSolvable_Yp hF) hSLsolv hSLn
    have hXN : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤ Subgroup.normalizer (L : Set G) :=
      sup_le hYL (inf_le_right.trans Subgroup.le_normalizer)
    have hXLsolv : Group.IsSolvable ↥((Yp ⊔ (Sgp153 T V₁ ⊓ L)) ⊓ L) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_left : (Yp ⊔ (Sgp153 T V₁ ⊓ L)) ⊓ L ≤ _))
        (Subgroup.inclusion_injective _)
    have hXL : (Yp ⊔ (Sgp153 T V₁ ⊓ L)) ⊓ L ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
      kB G L (Sgp153 T V₁ ⊓ L) _ hlie hSL (le_inf le_sup_right inf_le_right) inf_le_right hXLsolv
    have hSLX : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) ((Yp ⊔ (Sgp153 T V₁ ⊓ L)) ⊓ L) :=
      A4.isSylowTwoOf_mono hSL (le_inf le_sup_right inf_le_right) inf_le_right
    have hYSL : Yp ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
      have key1 : ∀ y ∈ Yp, ∀ x ∈ Sgp153 T V₁ ⊓ L, y * x * y⁻¹ ∈ Sgp153 T V₁ ⊓ L := by
        intro y hy x hx
        have hyX : y ∈ Yp ⊔ (Sgp153 T V₁ ⊓ L) := Subgroup.mem_sup_left hy
        have hDle : B6.conjSub y (Sgp153 T V₁ ⊓ L) ≤ (Yp ⊔ (Sgp153 T V₁ ⊓ L)) ⊓ L := by
          intro z hz
          rw [B6.mem_conjSub] at hz
          have hz' : y⁻¹ * z * y ∈ Sgp153 T V₁ ⊓ L := hz
          have e : z = y * (y⁻¹ * z * y) * y⁻¹ := by group
          rw [e]
          refine ⟨(Yp ⊔ (Sgp153 T V₁ ⊓ L)).mul_mem
            ((Yp ⊔ (Sgp153 T V₁ ⊓ L)).mul_mem hyX
              ((le_sup_right : Sgp153 T V₁ ⊓ L ≤ Yp ⊔ (Sgp153 T V₁ ⊓ L)) hz'))
            ((Yp ⊔ (Sgp153 T V₁ ⊓ L)).inv_mem hyX), ?_⟩
          exact (Subgroup.mem_normalizer_iff.mp (hYL hy) _).mp hz'.2
        have hD2 : IsPGroup 2 ↥(B6.conjSub y (Sgp153 T V₁ ⊓ L)) :=
          (B6.isSylowTwoOf_conjSub hSL y).2.1
        have hle : B6.conjSub y (Sgp153 T V₁ ⊓ L) ≤ Sgp153 T V₁ ⊓ L :=
          le_of_normal_sylow hSLX hXL hD2 hDle
        refine hle (B6.mem_conjSub.mpr ?_)
        have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
        rw [e]
        exact hx
      intro y hy
      refine B6.mem_normalizer_of_forall_mem (key1 y hy) (fun x hx => ?_)
      have := key1 y⁻¹ (inv_mem hy) x hx
      rwa [inv_inv] at this
    have hyB : ∀ y ∈ Yp, B6.conjSub y
        (L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G)) =
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
      intro y hy
      rw [OrderIso.map_inf, B6.conjSub_eq_self (hYL hy),
        B6.conjSub_eq_self (Subgroup.le_normalizer (hYSL hy))]
    have hconj : ∀ y ∈ Yp, ∀ P : Subgroup G, IsMaxParabolic2 L P →
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P →
        B6.conjSub y P = P₁ ∨ B6.conjSub y P = P₂ := by
      intro y hy P hP hBP
      refine huniq _ (isMaxParabolic2_conjSub (hYL hy) hP) ?_
      have := (B6.conjSub y).monotone hBP
      rwa [hyB y hy] at this
    have hYp : oTwoUpper Yp = Yp := hh.oTwoUpper_eq
    have hYP₁ : Yp ≤ Subgroup.normalizer (P₁ : Set G) :=
      le_normalizer_of_two hYp hne (fun y hy => hconj y hy P₁ hP₁ hB₁)
        (fun y hy => hconj y hy P₂ hP₂ hB₂)
    have hYP₂ : Yp ≤ Subgroup.normalizer (P₂ : Set G) :=
      le_normalizer_of_two hYp hne.symm (fun y hy => (hconj y hy P₂ hP₂ hB₂).symm)
        (fun y hy => (hconj y hy P₁ hP₁ hB₁).symm)
    have hPM : ∀ P : Subgroup G, IsMaxParabolic2 L P →
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P →
        Yp ≤ Subgroup.normalizer (P : Set G) → P ≤ M := by
      intro P hP hBP hYP
      have hSP : Sgp153 T V₁ ≤ Subgroup.normalizer (P : Set G) := hAP P hP hBP
      have hYS : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (P : Set G) := sup_le hYP hSP
      have hPle : P ≤ L := hP.1.1
      have hXI : P ⊔ (Yp ⊔ Sgp153 T V₁) ≤ I := sup_le (hPle.trans hLle) hI.1.1
      have hne' : P ⊔ (Yp ⊔ Sgp153 T V₁) ≠ I := by
        intro heq
        have hIN : I ≤ Subgroup.normalizer (P : Set G) :=
          heq ▸ sup_le Subgroup.le_normalizer hYS
        have hLN : L ≤ Subgroup.normalizer (P : Set G) := hLle.trans hIN
        obtain ⟨-, S', hS', hNS'⟩ := hP.1
        have hS'P : S' ≤ P := (le_inf hS'.1 Subgroup.le_normalizer).trans hNS'
        have hS'syl : IsSylowTwoOf S' P := A4.isSylowTwoOf_mono hS' hS'P hPle
        have hfr := B6.frattini_two hPle hLN hS'syl
        apply hP.2.1
        refine le_antisymm hPle ?_
        exact hfr.trans (sup_le le_rfl hNS')
      exact le_sup_left.trans (le_M_of_minCE c.ctx hF c.minimal hXI le_sup_right hne')
    have hLsup : P₁ ⊔ P₂ = L := by
      by_contra hQne
      have hQpar : IsParabolic2 L (P₁ ⊔ P₂) := by
        obtain ⟨-, S', hS', hNS'⟩ := hP₁.1
        exact ⟨sup_le hP₁.1.1 hP₂.1.1, S', hS', hNS'.trans le_sup_left⟩
      have e1 : P₁ ⊔ P₂ = P₁ := hP₁.2.2 _ hQpar hQne le_sup_left
      have e2 : P₁ ⊔ P₂ = P₂ := hP₂.2.2 _ hQpar hQne le_sup_right
      exact hne (e1.symm.trans e2)
    have hP₁M := hPM P₁ hP₁ hB₁ hYP₁
    have hP₂M := hPM P₂ hP₂ hB₂ hYP₂
    exact hLn (le_inf (hLsup ▸ sup_le hP₁M hP₂M) hLle)
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

end Main

end S153F

end CFSG.Quasithin
