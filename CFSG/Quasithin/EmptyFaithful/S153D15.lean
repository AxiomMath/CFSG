module

public import CFSG.Quasithin.EmptyFaithful.S153D12
public import CFSG.Quasithin.EmptyFaithful.S153DGen2
public import CFSG.Quasithin.EmptyFaithful.S153DIn15
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.Background.F1Cartan
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem normalizer_le_CGS {R C : Subgroup G} (hC : C ≤ R) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf R).Characteristic) : Subgroup.normalizer (C : Set G) ≤ CGS R := by
  unfold CGS
  exact le_iSup_of_le C (le_iSup_of_le hC (le_iSup_of_le hC1 (le_iSup_of_le hchar le_rfl)))

omit [Finite G] in
theorem cgsIn_le_of_CGS_le {R : Subgroup G} (h : CGS R ≤ M) : cgsIn I R ≤ M ⊓ I := by
  refine iSup_le fun C => iSup_le fun hC => iSup_le fun hC1 => iSup_le fun hchar => ?_
  exact le_inf (inf_le_right.trans ((normalizer_le_CGS hC hC1 hchar).trans h)) inf_le_left

theorem lemma_15_3_15_one (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts15311 T M V₁ Yp I) :
    HypC23 I (R153 T V₁ Yp) (M ⊓ I) where
  sqtk := sqtkGroup_of_pCoreOf_ne_bot h.hyp.qtfe.qtke h.hyp.qtfe.simple h.hyp.qtfe.nonabelian
    hI.1.2
  radical := hF.radical
  le := inf_le_right
  cgs := cgsIn_le_of_CGS_le hF.cgs
  sylow := hF.sylow_R

omit [Finite G] in
theorem isSubnormal_thompsonJ (I : Subgroup G) : IsSubnormal (thompsonJ I) I :=
  A4.subnormal_of_normal (thompsonJ_le_self I)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (thompsonJ_le_self I)).mpr fun _ hg =>
      GammaExtra.normalizer_le_normalizer_thompsonJ I (Subgroup.le_normalizer hg))

omit [Finite G] in
theorem mem_cComp_of_mem_cComp_thompsonJ {I L : Subgroup G} (hL : L ∈ cComp (thompsonJ I)) :
    L ∈ cComp I :=
  cComp_mem_of_subnormal (isSubnormal_thompsonJ I) hL

theorem comm_eq_of_quasisimple (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I)
    (hLc : L ∈ cComp (thompsonJ I)) (hLn : ¬ L ≤ M ⊓ I)
    (hLq : CFSG.IsQuasisimple ↥(autOn L (UI153 T I))) : ⁅L, Yp⁆ = L := by
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 c.hyp c.inH hLI
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hUN
  have hYU : Yp ≤ Subgroup.normalizer (UI153 T I : Set G) := hYI.trans hUN
  by_contra hne
  have hKL : ⁅L, Yp⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hYL
  have hlt : ⁅L, Yp⁆ < L := lt_of_le_of_ne hKL hne
  have hKn : (⁅L, Yp⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr (Subgroup.normalizer_commutator_ge_left L Yp)
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
    (Subgroup.normal_subgroupOf_iff_le_normalizer hABA).mpr (Subgroup.normalizer_commutator_ge_left A B)
  have hABsolv : Group.IsSolvable ↥⁅A, B⁆ := by
    rw [hcomm]
    exact isSolvable_autOn (hKL.trans hLU) hKsolv
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hNn with htop | hcen
  ·
    have hAle : A ≤ ⁅A, B⁆ := Subgroup.subgroupOf_eq_top.mp htop
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
    have hAMI : A ≤ autOn (M ⊓ I) (UI153 T I) := by
      rw [← hF.star_norm]
      exact le_inf ((hAB.trans (Subgroup.centralizer_le_normalizer _))) hAI
    exact hLn (le_of_autOn_le hUN hLle inf_le_right hF.cent_le hAMI)

theorem charTwo_of_le {I X : Subgroup G} (hI : CharTwo I) (hXI : X ≤ I) (hOX : pCoreOf 2 I ≤ X) :
    CharTwo X := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hI hXI hOX

theorem pCoreOf_le_Sgp153 (hF : Facts15311 T M V₁ Yp I) : pCoreOf 2 I ≤ Sgp153 T V₁ := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact A4.le_of_normal_of_isSylowTwoOf hF.sylow (pCoreOf_le 2 I)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 I)).mpr
      (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)

theorem ctx_of_le (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I)
    {H : Subgroup G} (hHI : H ≤ I) (hYSH : Yp ⊔ Sgp153 T V₁ ≤ H) (hHM : ¬ H ≤ M) :
    Ctx15313 T Mc M V₁ V₂ Yp H t := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOH : pCoreOf 2 I ≤ H :=
    (pCoreOf_le_Sgp153 hF).trans (le_sup_right.trans hYSH)
  have h1 : pCoreOf 2 I ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hOH (fun g hg => le_normalizer_pCoreOf 2 I (hHI hg))
      (pCoreOf_isPGroup 2 I)
  refine ⟨c.hyp, ⟨⟨hYSH, ?_⟩, hHM⟩, c.rank, charTwo_of_le c.charTwo hHI hOH⟩
  intro hbot
  exact c.inH.1.2 (eq_bot_iff.mpr (hbot ▸ h1))

theorem isSolvable_Yp (hF : Facts15311 T M V₁ Yp I) : Group.IsSolvable ↥Yp := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Group.IsSolvable (OTwoQuot Yp) := by
    rcases hF.struct_Yp with he | ⟨-, hcard, -⟩
    · obtain ⟨e⟩ := he
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · have hP : IsPGroup 3 (OTwoQuot Yp) := IsPGroup.of_card (n := 3) hcard
      have : Group.IsNilpotent (OTwoQuot Yp) := hP.isNilpotent
      infer_instance
  have h2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥Yp) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥Yp) := by
    have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥Yp) := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥Yp).subtype
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Yp))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_Yp_sup (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts15311 T M V₁ Yp I) :
    Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := by
  have hSs : Group.IsSolvable ↥(Sgp153 T V₁) := F1.isSolvable_of_isPGroup_two hF.sylow.2.1
  exact F1.isSolvable_sup_of_le_normalizer (isSolvable_Yp hF) hSs
    (le_sup_right.trans (sup_Sgp153_le_normalizer_Yp h hI hF))

theorem lemma_15_3_15_two (hin : Input15315Two) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I) :
    ∃ L : Subgroup G, Concl15315Two T M Yp I L := by
  obtain ⟨L, hLc, hLn, hL3, hLq, hLq2⟩ := hin G T Mc M V₁ V₂ Yp I t c hF
  exact ⟨L, hLc, hLn, hL3, comm_eq_of_quasisimple h37 h38 c hF hLc hLn hLq, hLq, hLq2⟩

theorem lemma_15_3_15_three (hin : Input15315Two) (c : Ctx15313 T Mc M V₁ V₂ Yp I t)
    (hF : Facts15311 T M V₁ Yp I)
    (hFall : ∀ H : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M H → Facts15311 T M V₁ Yp H)
    {X : Subgroup G} (hXI : X ≤ I) (hXs : Group.IsSolvable ↥X)
    (hXn : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (X : Set G)) : X ≤ M ⊓ I := by
  by_contra hXM
  set H : Subgroup G := X ⊔ (Yp ⊔ Sgp153 T V₁) with hH
  have hHI : H ≤ I := sup_le hXI c.inH.1.1
  have hYSH : Yp ⊔ Sgp153 T V₁ ≤ H := le_sup_right
  have hHM : ¬ H ≤ M := fun hm => hXM (le_inf (le_sup_left.trans hm) hXI)
  have hctx : Ctx15313 T Mc M V₁ V₂ Yp H t := ctx_of_le c hF hHI hYSH hHM
  have hFH : Facts15311 T M V₁ Yp H := hFall H hctx.inH
  obtain ⟨L, hLc, -, -, hLq, -⟩ := hin G T Mc M V₁ V₂ Yp H t hctx hFH
  have hHs : Group.IsSolvable ↥H :=
    F1.isSolvable_sup_of_le_normalizer hXs (isSolvable_Yp_sup c.hyp c.inH hF) hXn
  have hLH : L ≤ H := (le_of_mem_cComp hLc).trans (thompsonJ_le_self H)
  have hHU : H ≤ Subgroup.normalizer (UI153 T H : Set G) := le_normalizer_conjClosure _ H
  have hAs : Group.IsSolvable ↥(autOn H (UI153 T H)) := isSolvable_autOn hHU hHs
  have hAL : Group.IsSolvable ↥(autOn L (UI153 T H)) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (autOn_le_autOn (UI153 T H) hLH))
  exact not_isSolvable_of_isQuasisimple hLq hAL

end S153D

end CFSG.Quasithin
