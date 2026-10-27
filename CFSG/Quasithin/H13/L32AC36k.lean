module

public import CFSG.Quasithin.H13.L32AC36g
public import CFSG.Quasithin.Background.SmithB45M22HatDim
public import CFSG.Quasithin.Background.SmithB45M22HatHat
public import CFSG.Quasithin.Background.SmithB45M22HatSmall
public import CFSG.Quasithin.H13.L32AC36f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

section Psi

variable {I : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]

theorem psiI_eq_one_iff (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hV₁I : fsuV1 T V ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G))
    (hUI : conjClosure V H ≤ I) (x : ↥H) :
    psiI hF hIU hV₁I hHI x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  refine ⟨fun hx => ?_, psiI_eq_one_of_mem_pCoreOf hF hIU hV₁I hHI⟩
  have hx' : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x = 1 := by
    refine MulEquiv.ext fun w => ?_
    have h1 := congrArg (fun φ : MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I) =>
      ((φ ⟨w, mem_subM_of_normal hHI w⟩ :
        ↥(subM (fsuV1 T V) (conjClosure I H) I)) : ↥(tildeOf (fsuV1 T V) (conjClosure I H)))) hx
    exact h1
  rw [hF.toHypF98.toHypF91.pCoreOf_eq_centralizerMod]
  exact ⟨x.2, hF.H_le_normalizer_V₁ x.2, fun u hu =>
    hF.commutator_mem_of_actH_eq_one hIU hx' u (le_conjClosure I H (hUI hu))⟩

@[expose] noncomputable def psiK (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hIU : I ≤ conjClosure V H) (hV₁I : fsuV1 T V ≤ I)
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) :
    cStar K →* MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I) :=
  QuotientGroup.lift _
    ((psiI hF hIU hV₁I hHI).comp (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp)))
    fun k hk => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact psiI_eq_one_of_mem_pCoreOf hF hIU hV₁I hHI
        (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp)
          (Subgroup.mem_subgroupOf.mp hk))

theorem psiK_mk (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hV₁I : fsuV1 T V ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) (k : ↥K) :
    psiK hF hIU hV₁I hHI (QuotientGroup.mk k) =
      psiI hF hIU hV₁I hHI (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp) k) :=
  rfl

theorem range_psiK (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hV₁I : fsuV1 T V ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) :
    (psiK hF hIU hV₁I hHI).range =
      autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  rw [← map_psiI hF hIU hV₁I hHI hKH]
  ext φ
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨Subgroup.inclusion hKH k, k.2, (psiK_mk hF hIU hV₁I hHI k).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk ⟨(x : G), hx⟩, psiK_mk hF hIU hV₁I hHI _⟩

end Psi

theorem twelve_hat
    (hSmall : HatM22SmallModules) (hA21 : AsA21SQTKSection) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K) {I : Subgroup G}
    (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hHI : H ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (hHat : IsHat ↥(autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I))
      (NativeSporadic.Carrier .M22)) :
    Mhat22Twelve (autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) := by
  set V' := subM (fsuV1 T V) (conjClosure I H) I with hV'
  set L' := autIH (fsuV1 T V) I H K with hL'
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
  have e1 := B5.secEquiv (autSub L' V') (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  have hType : B45TypeHatM22 ↥(autSec (autSub L' V') ⊤
      ((V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf V')) :=
    IsHat.of_mulEquiv e1 hHat
  have hexp : ∀ v : Sec (⊤ : Subgroup ↥V')
      ((V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf V'), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  have hcard : Nat.card (Sec (⊤ : Subgroup ↥V')
      ((V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf V')) < 2 ^ 30 :=
    lt_of_le_of_lt (card_le_of_hatM22 hexp hB4 hType hqh) (by norm_num)
  have hR := hSmall _ hexp _ hType hB4.2.2.2 hcard
  exact InternalSec.mhat22Twelve_of_autSec hQS.stabKC hQS.faithful
    ⟨FieldFour, inferInstance, inferInstance, hatM22Γ₀, FieldFour.natCard_eq, isHat_hatM22Γ₀,
      ⟨hatM22Form, hatM22Form_det_ne_zero, hatM22Form_hermitian, hatM22Form_invariant⟩, hR⟩

end CFSG.Quasithin.H13.L32A.C
