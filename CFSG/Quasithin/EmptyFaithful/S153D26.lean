module

public import CFSG.Quasithin.EmptyFaithful.S153D25Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def Input15326Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    Ctx15325 T Mc M V₁ V₂ Yp I t → Facts15325 T Mc M V₁ V₂ Yp I →
      ∃ L : Subgroup G, L ∈ cComp (thompsonJ I) ∧ ¬ L ≤ M ⊓ I ∧ 1 ≤ CFSG.Open.pRank 3 L ∧
        CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem isSolvable_of_le_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {X : Subgroup G}
    (hXY : X ≤ Y153 Mc M) : Group.IsSolvable ↥X := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, -⟩ := h.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hXY
  have hQ3 : ∀ x : ↥(imageOTwoQuot M X), x ^ 3 = 1 := by
    intro x
    have h3 := (h.Ystar_structure h113).1.2.2 ⟨(x : OTwoQuot M), imageOTwoQuot_mono hXY x.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val h3)
  have hP : IsPGroup 3 ↥(imageOTwoQuot M X) := fun x => ⟨1, by simpa using hQ3 x⟩
  have hq : Group.IsSolvable (OTwoQuot X) := by
    have : Group.IsNilpotent ↥(imageOTwoQuot M X) := hP.isNilpotent
    have : Group.IsSolvable ↥(imageOTwoQuot M X) := inferInstance
    exact Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have h2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥X) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥X) := by
    have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥X) := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥X).subtype
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_Yp_sup' (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := by
  have hSs : Group.IsSolvable ↥(Sgp153 T V₁) :=
    F1.isSolvable_of_isPGroup_two (h.hyp.qtfe.sylow.1.to_le inf_le_left)
  exact F1.isSolvable_sup_of_le_normalizer (isSolvable_of_le_Y153 h113 h.hyp h.Yp_le_Y153) hSs
    (Sgp153_le_normalizer_Yp h)

theorem comm_eq_of_quasisimple' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts153 T M V₁ Yp I) (hLc : L ∈ cComp (thompsonJ I)) (hLn : ¬ L ≤ M ⊓ I)
    (hLq : CFSG.IsQuasisimple ↥(autOn L (UI153 T I))) : ⁅L, Yp⁆ = L := by
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 h hI hLI
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hUN
  have hYU : Yp ≤ Subgroup.normalizer (UI153 T I : Set G) := hYI.trans hUN
  by_contra hne
  have hKL : ⁅L, Yp⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hYL
  have hlt : ⁅L, Yp⁆ < L := lt_of_le_of_ne hKL hne
  have hKn : (⁅L, Yp⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr
      (Subgroup.normalizer_commutator_ge_left L Yp)
  have hKsub : IsSubnormal ⁅L, Yp⁆ L := A4.subnormal_of_normal hKL hKn
  have hKrad : ⁅L, Yp⁆ ≤ solvRad L := le_solvRad_of_subnormal_lt hLI hKsub hlt
  have : Group.IsSolvable ↥(solvRad L) := solvRad_isSolvable L
  have hKsolv : Group.IsSolvable ↥⁅L, Yp⁆ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKrad)
  set A : Subgroup (MulAut ↥(UI153 T I)) := autOn L (UI153 T I) with hA
  set B : Subgroup (MulAut ↥(UI153 T I)) := autOn Yp (UI153 T I) with hB
  have hBA : B ≤ Subgroup.normalizer (A : Set (MulAut ↥(UI153 T I))) :=
    autOn_le_normalizer_autOn hYU hLU hYL
  have hcomm : ⁅A, B⁆ = autOn ⁅L, Yp⁆ (UI153 T I) := (autOn_commutator hLU hYU).symm
  have hABA : ⁅A, B⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hBA
  have hNn : (⁅A, B⁆.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hABA).mpr
      (Subgroup.normalizer_commutator_ge_left A B)
  have hABsolv : Group.IsSolvable ↥⁅A, B⁆ := by
    rw [hcomm]
    exact isSolvable_autOn (hKL.trans hLU) hKsolv
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hNn with htop | hcen
  · have hAle : A ≤ ⁅A, B⁆ := Subgroup.subgroupOf_eq_top.mp htop
    exact not_isSolvable_of_isQuasisimple hLq
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAle))
  · have hcent : ⁅A, B⁆ ≤ Subgroup.centralizer (A : Set (MulAut ↥(UI153 T I))) := by
      intro x hx
      have hxA : x ∈ A := hABA hx
      have hx' : (⟨x, hxA⟩ : ↥A) ∈ Subgroup.center ↥A := hcen (Subgroup.mem_subgroupOf.mpr hx)
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      have := Subgroup.mem_center_iff.mp hx' ⟨a, ha⟩
      exact congrArg Subtype.val this
    have hbot := commutator_eq_bot_of_quasisimple hLq hcent
    have hAB : A ≤ Subgroup.centralizer (B : Set (MulAut ↥(UI153 T I))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hAI : A ≤ autOn I (UI153 T I) := autOn_le_autOn (UI153 T I) hLle
    have hsn : Subgroup.normalizer (autOn Yp (UI153 T I) : Set (MulAut ↥(UI153 T I))) ⊓
        autOn I (UI153 T I) = autOn (M ⊓ I) (UI153 T I) := hF.star_norm
    have hAMI : A ≤ autOn (M ⊓ I) (UI153 T I) := by
      rw [← hsn]
      exact le_inf ((hAB.trans (Subgroup.centralizer_le_normalizer _))) hAI
    exact hLn (le_of_autOn_le hUN hLle inf_le_right hF.cent_le hAMI)

theorem pCoreOf_le_Sgp153' (hF : Facts153 T M V₁ Yp I) : pCoreOf 2 I ≤ Sgp153 T V₁ := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact A4.le_of_normal_of_isSylowTwoOf hF.sylow (pCoreOf_le 2 I)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 I)).mpr
      (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)

theorem ctx25_of_le (c : Ctx15325 T Mc M V₁ V₂ Yp I t) (hF : Facts153 T M V₁ Yp I)
    {H : Subgroup G} (hHI : H ≤ I) (hYSH : Yp ⊔ Sgp153 T V₁ ≤ H) (hHM : ¬ H ≤ M) :
    Ctx15325 T Mc M V₁ V₂ Yp H t := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOH : pCoreOf 2 I ≤ H := (pCoreOf_le_Sgp153' hF).trans (le_sup_right.trans hYSH)
  have h1 : pCoreOf 2 I ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hOH (fun g hg => le_normalizer_pCoreOf 2 I (hHI hg))
      (pCoreOf_isPGroup 2 I)
  refine ⟨c.hyp, ⟨⟨hYSH, ?_⟩, hHM⟩, c.rank, charTwo_of_le c.charTwo hHI hOH⟩
  intro hbot
  exact c.inH.1.2 (eq_bot_iff.mpr (hbot ▸ h1))

theorem lemma_15_3_26_two (hin : Input15326Two) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15325 T Mc M V₁ V₂ Yp I t) (hF : Facts15325 T Mc M V₁ V₂ Yp I) :
    ∃ L : Subgroup G, Concl15315Two T M Yp I L := by
  obtain ⟨L, hLc, hLn, hL3, hLq, hLq2⟩ := hin G T Mc M V₁ V₂ Yp I t c hF
  exact ⟨L, hLc, hLn, hL3, comm_eq_of_quasisimple' h37 h38 c.hyp c.inH hF.toFacts153 hLc hLn hLq,
    hLq, hLq2⟩

theorem lemma_15_3_26_three (h113 : StageLemma14113) (hin : Input15326Two)
    (c : Ctx15325 T Mc M V₁ V₂ Yp I t) (hF : Facts15325 T Mc M V₁ V₂ Yp I)
    (hFall : ∀ H : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M H → Facts15325 T Mc M V₁ V₂ Yp H)
    {X : Subgroup G} (hXI : X ≤ I) (hXs : Group.IsSolvable ↥X)
    (hXn : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (X : Set G)) : X ≤ M ⊓ I := by
  by_contra hXM
  set H : Subgroup G := X ⊔ (Yp ⊔ Sgp153 T V₁) with hH
  have hHI : H ≤ I := sup_le hXI c.inH.1.1
  have hYSH : Yp ⊔ Sgp153 T V₁ ≤ H := le_sup_right
  have hHM : ¬ H ≤ M := fun hm => hXM (le_inf (le_sup_left.trans hm) hXI)
  have hctx : Ctx15325 T Mc M V₁ V₂ Yp H t := ctx25_of_le c hF.toFacts153 hHI hYSH hHM
  have hFH : Facts15325 T Mc M V₁ V₂ Yp H := hFall H hctx.inH
  obtain ⟨L, hLc, -, -, hLq, -⟩ := hin G T Mc M V₁ V₂ Yp H t hctx hFH
  have hHs : Group.IsSolvable ↥H :=
    F1.isSolvable_sup_of_le_normalizer hXs (isSolvable_Yp_sup' h113 c.hyp) hXn
  have hLH : L ≤ H := (le_of_mem_cComp hLc).trans (thompsonJ_le_self H)
  have hHU : H ≤ Subgroup.normalizer (UI153 T H : Set G) := le_normalizer_conjClosure _ H
  have hAs : Group.IsSolvable ↥(autOn H (UI153 T H)) := isSolvable_autOn hHU hHs
  have hAL : Group.IsSolvable ↥(autOn L (UI153 T H)) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (autOn_le_autOn (UI153 T H) hLH))
  exact not_isSolvable_of_isQuasisimple hLq hAL

end S153D

end CFSG.Quasithin
