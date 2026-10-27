module

public import CFSG.Quasithin.Background.C124AsmBuild
public import CFSG.Quasithin.Background.C124BlkBasic
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ord
public import CFSG.Quasithin.H13.GoldschmidtC137Concl
public import CFSG.Quasithin.H13.GoldschmidtC137Bridge

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open CFSG.Quasithin.C124 (b51Case1i_ffJP b51Hyp_ffJP entryPlus_or_concl1 concl1_of_baum_eq
  pCoreOf_eq_pCoreOf_inf B2_10_2 pCoreOf_autI_L_eq_bot le_normalizer_of_prod
  ker_starHom_eq_pCore)

open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSimple_u33 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  refine (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 ?_).2
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact h
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem isQuasisimple_u33 {L : Subgroup G} (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hs := isSimple_u33 h
  have hnp : ¬ (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := by
    rw [card_of_psu33 h]
    norm_num
  have hnc : ∃ a b : (↥L ⧸ CFSG.pCore 2 ↥L), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      { (inferInstance : Group (↥L ⧸ CFSG.pCore 2 ↥L)) with mul_comm := hc }
    exact hnp IsSimpleGroup.prime_card
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (↥L ⧸ CFSG.pCore 2 ↥L)) with
      h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h0
  exact B1Red.isQuasisimple_of_open (CFSG.ComponentClassification.Quasisimple.simple_of_perfect _)

theorem pCoreOf_eq_inf_u33 [Finite G] {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hle : pCoreOf 2 L ≤ centralizer (V : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥) :
    pCoreOf 2 L = L ⊓ centralizer (V : Set G) := by
  apply le_antisymm (le_inf (pCoreOf_le 2 L) hle)
  set σ := C124.starHom hV L hLN with hσ
  have hker : ∀ l : ↥L, l ∈ σ.ker ↔ (l : G) ∈ centralizer (V : Set G) := by
    intro l
    rw [C124.ker_starHom hV hLN, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  have hP : CFSG.pCore 2 ↥L ≤ σ.ker := fun x hx =>
    (hker x).2 (hle ((mem_pCoreOf_iff_gc L x).2 hx))
  have hN : (σ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  haveI := hN
  rcases hs.eq_bot_or_eq_top_of_normal (σ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with
    h0 | h0
  · intro x hx
    have hxk : (⟨x, hx.1⟩ : ↥L) ∈ σ.ker := (hker _).2 hx.2
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx.1⟩ ∈
        σ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := ⟨_, hxk, rfl⟩
    rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (mem_pCoreOf_iff_gc L ⟨x, hx.1⟩).2 h1
  · exfalso
    apply hVL
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        σ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by rw [h0]; trivial
    obtain ⟨k, hk, hkl⟩ := h1
    have h2 : k⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.1 hkl
    have h3 : (⟨l, hl⟩ : ↥L) = k * (k⁻¹ * ⟨l, hl⟩) := by group
    have h4 : (⟨l, hl⟩ : ↥L) ∈ σ.ker := by
      rw [h3]
      exact σ.ker.mul_mem hk (hP h2)
    exact ((Subgroup.mem_centralizer_iff.1 ((hker _).1 h4)) v hv).symm

theorem card_autI_u33 [Finite G] {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hker : pCoreOf 2 L = L ⊓ centralizer (V : Set G)) :
    Nat.card ↥(autI hV L) = 6048 := by
  have hσs := C124.starHom_surjective hV hLN
  have h1 : Nat.card (↥L ⧸ (C124.starHom hV L hLN).ker) = Nat.card ↥(autI hV L) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hσs).toEquiv
  rw [ker_starHom_eq_pCore hV hLN hker] at h1
  rw [← h1]
  exact card_of_psu33 hlie

structure Entry33 (X T V L R : Subgroup G) [Finite G] (hV : IsElemAbelian 2 V) : Prop where
  charTwo : CharTwo X
  sqtk : SQTKGroup ↥X
  red : IsTwoReducedIn X V
  sylow : IsSylowTwoOf T X
  prod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  comp : L ∈ cComp X
  charTwoL : CharTwo L
  VL : ⁅V, L⁆ ≠ ⊥
  lie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1
  QR : pCoreOf 2 X ≤ R
  RT : R ≤ T
  normal : X ≤ normalizer (L : Set G)
  QC : pCoreOf 2 X = R ⊓ centralizer (V : Set G)
  hJ : ¬ thompsonJ R ≤ centralizer (V : Set G)
  fstarX : quasithinGenFitting (autI hV X) = autI hV L
  stab : IsStableFF (autI hV X) (C124.offenderImagesConjIn hV X R)
  ffJP_le : ffJP (C124.offenderImagesConjIn hV X R) (autI hV X) ≤ ffJ (autI hV X)
  fstar : quasithinGenFitting (ffJP (C124.offenderImagesConjIn hV X R) (autI hV X)) = autI hV L
  quasi : CFSG.IsQuasisimple ↥(autI hV L)
  o2 : pCoreOf 2 (autI hV L) = ⊥
  Lq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  Csyl : IsSylowTwoOf (pCoreOf 2 X) (X ⊓ centralizer (V : Set G))
  kerL : pCoreOf 2 L = L ⊓ centralizer (V : Set G)
  card : Nat.card ↥(autI hV L) = 6048
  case1i : B51Case1i (ffJP (C124.offenderImagesConjIn hV X R) (autI hV X)) (autI hV L)

theorem entry33_or_concl1 [Finite G] (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) {X T V L R : Subgroup G} (hC : CharTwo X) (hSQ : SQTKGroup ↥X)
    (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hcomp : L ∈ cComp X) (hCL : CharTwo L)
    (hVL : ⁅V, L⁆ ≠ ⊥) (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hQR : pCoreOf 2 X ≤ R) (hRT : R ≤ T) :
    (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R ∧ (C.subgroupOf (baum R)).Characteristic ∧
        X ≤ normalizer (C : Set G)) ∨ Entry33 X T V L R hred.2.2.1 := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hcomp
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := isQuasisimple_u33 hlie
  obtain ⟨⟨hCsyl, hQC⟩, hqc, hF, hbranch⟩ :=
    B2_10_2 hV hred hQR hRT hT hLX hn hprod hVL (Or.inl hLq)
  have hVR : V ≤ R := (C124.le_pCoreOf_of_reduced hred).trans hQR
  rcases hbranch with hb | ⟨hstab, hffle, hfstar⟩
  · exact Or.inl (concl1_of_baum_eq hT hred hQR hRT hVL hb)
  by_cases hJ : thompsonJ R ≤ centralizer (V : Set G)
  · refine Or.inl (concl1_of_baum_eq hT hred hQR hRT hVL ?_)
    have hJR : thompsonJ R ≤ R ⊓ centralizer (V : Set G) := le_inf (thompsonJ_le_self R) hJ
    rw [← hQC] at hJR
    rw [baum_eq_baum_centralizer hV hVR (hQC ▸ hJR), hQC]
  right
  have hquasi : CFSG.IsQuasisimple ↥(autI hV L) := by
    rcases hqc with h | h3
    · exact h
    · exfalso
      have hperf : Group.IsPerfect ↥(autI hV L) := by
        have : Group.IsPerfect ↥L := C124.isPerfect_of_comm_eq (perfect_of_mem_cComp hcomp)
        exact Group.IsPerfect.ofSurjective (f := C124.starHom hV L (hLX.trans hred.2.1))
          (C124.starHom_surjective hV _)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥(autI hV L) := isCyclic_of_prime_card h3
      have hnil : Group.IsNilpotent ↥(autI hV L) := inferInstance
      have : Nontrivial ↥(autI hV L) :=
        Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
      exact Group.IsPerfect.not_isNilpotent _ hnil
  have ho2 : pCoreOf 2 (autI hV L) = ⊥ := pCoreOf_autI_L_eq_bot hV hred hLX hn
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hred.2.1
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
      (C124.pCoreOf_le_centralizer hred)
  have hkerL := pCoreOf_eq_inf_u33 hV hLN (isSimple_u33 hlie) hOL hVL
  have hcard := card_autI_u33 hV hLN hlie hkerL
  have hHyp := b51Hyp_ffJP hV hA21 hSQ hred.2.1 hLX hstab hfstar hquasi ho2
  have hU : commV (autI hV L) ∈ IrrPlus (autI hV L) ⊤ := by
    by_contra hU
    exact not_isL345Type_of_card hcard
      (B5.b51_ident hA21 hI.b42 hA36 IntMod.sq_eq_one hHyp hU)
  have hcase1i := B5.b51_case1i hI IntMod.sq_eq_one hHyp hU
  have hCsyl' : IsSylowTwoOf (pCoreOf 2 X) (X ⊓ centralizer (V : Set G)) := by
    rw [pCoreOf_eq_pCoreOf_inf hred]
    exact hCsyl
  exact
    { charTwo := hC, sqtk := hSQ, red := hred, sylow := hT, prod := hprod, comp := hcomp
      charTwoL := hCL, VL := hVL, lie := hlie, QR := hQR, RT := hRT, normal := hn, QC := hQC,
      hJ := hJ, fstarX := hF, stab := hstab, ffJP_le := hffle, fstar := hfstar, quasi := hquasi,
      o2 := ho2, Lq := hLq, Csyl := hCsyl', kerL := hkerL, card := hcard, case1i := hcase1i }

end CFSG.Quasithin.H13.U3.GC137
