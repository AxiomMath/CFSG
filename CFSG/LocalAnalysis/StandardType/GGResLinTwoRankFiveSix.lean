module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResJNormalComplement
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelD
public import Certificates.Certificate1
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13657
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.StandardType.HdRo7C

private theorem largeEvenRawDatumLegacy_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatumLegacy lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [LargeEvenRawDatumLegacy] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, _, b, c, _, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, _, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem GGResHyp.false_of_exact3_linTwo_rank_five_six
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {KJ : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y KJ)
    (hcell : ∃ lab : LargeEvenLabel, GGLinTwoLabel 3 lab ∧
      (lab.rank = 5 ∨ lab.rank = 6) ∧
      GGInnerDiagOnLabel (fun p lab' => p = 3 ∧ lab' = lab) 3 Bs L)
    (h3 : GGResLeviDatumExact3 3 Bs L J KJ ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs KJ J L ggSelAny ggTypAny) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨lab, hlab, hrank, hL⟩ := hcell
  obtain ⟨hperf, lab', hlab', hraw⟩ := hL
  let Q : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
        (fun p lab' => p = 3 ∧ lab' = lab) 3 lab' ∧
          Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L =>
              (l' : G) = b⁻¹ * (l : G) * b) φ
  have hrawQ : LargeEvenRawDatumLegacy lab' Q := hraw
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatumLegacy_exists (Q := Q) hrawQ
  have hlab'_eq : lab' = lab := hQ.2.2.choose_spec.1.2
  subst lab'
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := hlab
  subst ht
  subst hn
  dsimp only at hrank
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hfield, hfinite, hK, hrawP⟩ := hraw
  obtain ⟨θ, hP⟩ := hrawP.2.2
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by simpa using hK
  let d : ℕ := l + 1
  have hd : 6 ≤ d := by
    dsimp [d]
    omega
  have hd2 : d / 2 = 3 := by
    dsimp [d]
    omega
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hBs3 : ∀ b ∈ Bs, ∃ φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      LargeEvenInduces (θ := θ) (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ := by
    simpa [d] using hP.2.2
  let ψ : ↥L →* projectiveSL d K :=
    (TypeA.recipeEquiv d K).toMonoidHom.comp (ggQuotHom θ)
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hA : IsElemAbelian 3 A :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.2)) (ggGamma L hBsN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : ↥L,
      φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨φ, hφI, hφind⟩ := hBs3 (b⁻¹) (Bs.inv_mem b.2)
    refine ⟨MulAut.congr (TypeA.recipeEquiv d K) φ,
      TypeA.congr_recipeEquiv_mem hφI, ?_⟩
    intro l
    have hmemL : (b : G) * (l : G) * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hBsN b.2) (l : G)).mp l.2
    let l' : ↥L := ⟨(b : G) * (l : G) * (b : G)⁻¹, hmemL⟩
    have hrel : (l' : G) = (b⁻¹ : ↥Bs)⁻¹ * (l : G) * (b⁻¹ : ↥Bs) := by
      dsimp [l']
      simp only [Subgroup.coe_inv, inv_inv]
    have hind := hφind l l' hrel
    have hgl : ((ggGamma L hBsN) b) l = l' := Subtype.ext (ggGamma_coe L hBsN b l)
    change (MulAut.congr (TypeA.recipeEquiv d K) φ) (ψ l) =
      ψ (((ggGamma L hBsN) b) l)
    have hψl : ψ l = (TypeA.recipeEquiv d K) (θ (QuotientGroup.mk l)) := rfl
    have hψl' : ψ l' = (TypeA.recipeEquiv d K) (θ (QuotientGroup.mk l')) := rfl
    rw [hgl, MulAut.congr_apply, hψl, hψl']
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hind]
  have hker : ψ.ker = Subgroup.center ↥L := by
    ext l
    show (TypeA.recipeEquiv d K) ((ggQuotHom θ) l) = 1 ↔ l ∈ Subgroup.center ↥L
    rw [(TypeA.recipeEquiv d K).map_eq_one_iff, ← MonoidHom.mem_ker, ker_ggQuotHom]
  have hψ : Function.Surjective (ψ) :=
    (TypeA.recipeEquiv d K).surjective.comp (ggQuotHom_surjective θ)
  have hkerGG : (ggGamma L hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    constructor
    · intro h
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, h⟩
      rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH] at hmem
    · intro h
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH]
      exact hmem.2
  have hkernelCard : Nat.card ↥((ggGamma L hBsN).ker) = 3 := by
    rw [hkerGG]
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hH.1.tableB_facts.2.2.1)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH)
        (hdRo7CLCoordAux_x_ne_one hH)]
  have hcardRangeMul : Nat.card A * 3 = Nat.card Bs := by
    have h1 := TableB.card_range_mul_card_ker (ggGamma L hBsN)
    rw [hkerGG] at h1
    have hk : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = 3 := by
      rw [← hkerGG]
      exact hkernelCard
    rw [hk] at h1
    simpa [A] using h1
  have hcardBs4 : 3 ^ 4 ≤ Nat.card Bs := hdRo7CLCoordAux_card_bstar_ge hH
  have hr : 3 ^ (d / 2) ≤ Nat.card A := by
    rw [hd2]
    have h1 : 3 ^ 4 ≤ Nat.card A * 3 := by
      rw [hcardRangeMul]
      exact hcardBs4
    nlinarith [show (3 : ℕ) ^ 4 = 3 ^ 3 * 3 by norm_num]
  have hcardA : Nat.card A = 3 ^ 3 := by
    have h := LinTwoTB.exists_data_card_eq hK2 hd (ψ) hψ hker.le hperf A hA hAI hr
    rwa [hd2] at h
  have hcardBs : Nat.card Bs = 3 ^ 4 := by
    rw [← hcardRangeMul, hcardA]
    norm_num
  have hp5 : (3 : ℕ) ≠ 5 := by norm_num
  have hD : GGResLeviDatumExact3 3 Bs L J KJ ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs KJ J L ggSelAny ggTypAny := h3
  have hne : ggAutomizer J Bs ≠ ⊥ := hH.automizerJ_ne_bot
  have hbot : ggAutomizer J Bs = ⊥ := by
    rcases h3 with h3L | h3K
    · exact ggResLeviExact3_automizerJ_eq_bot_of_card_le_four hH (Or.inl rfl) hp5
        (le_of_eq hcardBs) h3L
    · exact ggResLeviExact3_automizerJ_eq_bot_of_card_le_four hH (Or.inr rfl) hp5
        (le_of_eq hcardBs) h3K
  exact hne hbot

end CFSG.StandardType

end
