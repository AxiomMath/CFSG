module

public import CFSG.Quasithin.H13.L32AC36e
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Background.F918J3
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

omit [Finite G] in
theorem mem_subM_of_normal {I : Subgroup G} (hHI : H ≤ Subgroup.normalizer (I : Set G))
    (w : ↥(tildeOf (fsuV1 T V) (conjClosure I H))) :
    w ∈ subM (fsuV1 T V) (conjClosure I H) I := by
  have hcI : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)
  have key : tildeOf (fsuV1 T V) (conjClosure I H) = tildeOf (fsuV1 T V) I := by rw [hcI]
  rw [mem_subM_iff]
  exact key.le w.2

theorem autIH_le_stabSub {I : Subgroup G}
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hV₁I : fsuV1 T V ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) {X : Subgroup G}
    (hXH : X ≤ H) :
    autIH (fsuV1 T V) I H X ≤ stabSub (subM (fsuV1 T V) (conjClosure I H) I) := by
  intro t ht
  rw [autIH_eq_map hF hXH] at ht
  obtain ⟨x, -, rfl⟩ := ht
  exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) x).mpr (hHI x.2)

omit [Finite G] in
theorem autIH_inf_centSub {I : Subgroup G}
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) (X : Subgroup G) :
    autIH (fsuV1 T V) I H X ⊓ centSub (subM (fsuV1 T V) (conjClosure I H) I) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨-, hg⟩
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun w => hg w (mem_subM_of_normal hHI w)

theorem code_m22
    (hIrr : MathieuSmallIrr22) (hA21 : AsA21SQTKSection) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K)
    (hM : IsSporadic .M22 (cStar K)) {I : Subgroup G} (hV₁I : fsuV1 T V ≤ I)
    (hIU : I ≤ conjClosure V H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hHI : H ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] :
    MathieuCode22 (autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) := by
  set V' := subM (fsuV1 T V) (conjClosure I H) I with hV'
  set L' := autIH (fsuV1 T V) I H K with hL'
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hSQ := sqtkGroup_of_setting S
  have hirr' : V' ∈ IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
      (orbSup (autIH (fsuV1 T V) I H T) V') (autIH (fsuV1 T V) I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hD3 : D3Std (autIH (fsuV1 T V) I H H) (autIH (fsuV1 T V) I H (conjClosure K T))
      (autIH (fsuV1 T V) I H T) L' V' := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = L' := by rw [hK₀]
  have hT := autIH_le_stabSub hF hIU hV₁I hHI hF.T_le_H
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  have hB4 := lred3_b4Hyp hA21 hD hMp hO2
  have hqh := lred3_qhatOf_autSec hD3 hMp hT
  have hq := lred3_qOf_autSec hD3 hMp hT (hA.qOf_VT hD.exp)
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    have := isSimpleGroup_of_m22 hM
    (cStarEquiv K).symm.isSimpleGroup
  have hne : L' ≠ ⊥ := by
    rw [hL', autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have e2 := autSubEquivOfFaithful (autIH_le_stabSub hF hIU hV₁I hHI hKH) (autIH_inf_centSub hHI K)
  have e1 := B5.secEquiv (autSub L' V') (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  obtain ⟨eM⟩ := hM
  have e : ↥(autSec (autSub L' V') ⊤
      ((V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf V')) ≃*
        ↥NativeSporadic.M22 :=
    e1.symm.trans (e2.symm.trans (e3.symm.trans ((cStarEquiv K).symm.trans eM)))
  have hsM := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hs := e.isSimpleGroup
  have hType : B45TypeSpor .M22 ↥(autSec (autSub L' V') ⊤
      ((V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf V')) :=
    ⟨center_eq_bot_of_isSimpleGroup hs (exists_noncomm_of_isQuasisimple hB4.2.2.1), ⟨e⟩⟩
  have hexp : ∀ v : Sec (⊤ : Subgroup ↥V')
      ((V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf V'), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  rcases code22_of_qhat hIrr hexp hB4 hType hqh with ⟨hc, -⟩ | ⟨-, hc⟩
  · exact InternalSec.mathieuCode22_of_autSec hQS.stabKC hQS.faithful hc
  · exact absurd (hc.trans_le hq) (lt_irrefl _)

end CFSG.Quasithin.H13.L32A.C
