module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.A6S13821l
public import CFSG.Quasithin.H13.A6S13821zp

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

namespace A6S20

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem ff_data_gen (hA21 : AsA21SQTKSection) (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hFF : IsFFModule (autSec (autIH V₁ I H K ⊔ autIH V₁ I H T) (subM V₁ (conjClosure I H) I)
      (fixV (autIH V₁ I H (conjClosure K T))))) :
    B4Hyp (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)))
      (autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ∧
    (∀ v : Sec (⊤ : Subgroup ↥(subM V₁ (conjClosure I H) I))
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)), v ^ 2 = 1) ∧
    IsFFModule (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) := by
  classical
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  have hT := A6L32.autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hB4 := lred3_b4Hyp hA21 hD hMp hO2
  refine ⟨hB4, fun v => ?_, ?_⟩
  · induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  · have hFF1 : IsFFModule (autSec (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)))) := by
      rw [hMp]
      have key : ∀ S S' : Subgroup ↥(subM V₁ (conjClosure I H) I), S = S' →
          IsFFModule (autQuot (autSub (autIH V₁ I H K ⊔ autIH V₁ I H T)
            (subM V₁ (conjClosure I H) I)) S) →
          IsFFModule (autQuot (autSub (autIH V₁ I H K ⊔ autIH V₁ I H T)
            (subM V₁ (conjClosure I H) I)) S') := by
        rintro S S' rfl h
        exact h
      refine key _ _ ?_ (hMp ▸ hFF)
      ext x
      simp [Subgroup.mem_subgroupOf]
    exact isFFModule_autSec_top hFF1

omit [Finite G] in
theorem exists_quot_range_eq_top {X A B : Type*} [Group X] [Group A] [Group B] (t : X →* A)
    (ht : Function.Surjective t) (ψ : A →* B) (hψ : Function.Surjective ψ) (N : Subgroup X)
    [N.Normal] (hN : ∀ x ∈ N, t x = 1) : ∃ φ : X ⧸ N →* B, φ.range = ⊤ := by
  have hker : N ≤ (ψ.comp t).ker := fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hN x hx, map_one]
  refine ⟨QuotientGroup.lift N (ψ.comp t) hker, MonoidHom.range_eq_top.mpr fun y => ?_⟩
  obtain ⟨a, rfl⟩ := hψ y
  obtain ⟨x, rfl⟩ := ht a
  exact ⟨QuotientGroup.mk x, rfl⟩

omit [Finite G] in
theorem toAutI_eq_one_of_mem_pCore [Finite G] (hF : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    {x : ↥K} (hx : x ∈ CFSG.pCore 2 ↥K) : toAutI hF I x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [toAutI_eq_one_iff]
  apply hF.actH_eq_one_of_mem_pCoreOf hIU
  have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
    assumption
  have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
  exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp) hx1

theorem exists_surj_autSec (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    ∃ φ : (↥K ⧸ CFSG.pCore 2 ↥K) →*
        ↥(autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
          ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
            (subM V₁ (conjClosure I H) I))), φ.range = ⊤ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hT := A6L32.autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  have hLs := A6L32.autIH_le_stabSub_of hF hIU hV₁I hKH hKI'
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  obtain ⟨ψ, hψs⟩ : ∃ ψ : ↥(autIH V₁ I H K) →*
      ↥(autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))), Function.Surjective ψ := by
    have e1 := B5.secEquiv _ (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
    have e2 := MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs)
    exact ⟨e1.toMonoidHom.comp (e2.symm.toMonoidHom.comp (resHomOn _ hLs).rangeRestrict),
      e1.surjective.comp (e2.symm.surjective.comp (resHomOn _ hLs).rangeRestrict_surjective)⟩
  exact exists_quot_range_eq_top (toAutI hF I) (toAutI_surjective hF I) ψ hψs (CFSG.pCore 2 ↥K)
    fun x hx => toAutI_eq_one_of_mem_pCore hF hIU hx

end A6S20


end CFSG.Quasithin.H13.A6
