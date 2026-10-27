module

public import CFSG.Quasithin.H13.A6S13821zp
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42
public import CFSG.Quasithin.Vol2.Ch10SecA312LA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
public import CFSG.Quasithin.H13.A6S13821l

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

namespace A6S20

attribute [local instance] commGroupOfFact

theorem exists_equiv_sl2_of_perfect {Q : Type} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) (hodd : Odd (Nat.card (Subgroup.center Q))) {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n (Q ⧸ Subgroup.center Q)) :
    Subgroup.center Q = ⊥ ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, F, hFf, hFfin, hFc, hF, ⟨eS⟩⟩ := Vol2.Ch10.A312LF.exists_sl2_of_isPSL h
  have hcSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    CFSG.ComponentClassification.RankTwoClassical.center_SL2_eq_bot'
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hcSL).trans QuotientGroup.quotientBot
  have hZ : Subgroup.center Q = ⊥ := by
    refine CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes hperf _ rfl
      hodd fun r hr _ hr2 S' => ?_
    let e' : (Q ⧸ Subgroup.center Q) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      eS.trans ePSL.symm
    let S'' : Sylow r (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Sylow.mapSurjective (f := e'.toMonoidHom) e'.surjective S'
    have hcyc := CFSG.ComponentClassification.RankTwoClassical.psl2_sylow_isCyclic hn hF r
      hr.out hr2 S''
    have hmap : (S'' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
        (S' : Subgroup (Q ⧸ Subgroup.center Q)).map e'.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e'.toMonoidHom) e'.surjective S'
    have hmapcyc : IsCyclic ((S' : Subgroup (Q ⧸ Subgroup.center Q)).map e'.toMonoidHom) := by
      change IsCyclic (S'' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) at hcyc
      rw [hmap] at hcyc
      exact hcyc
    exact (e'.subgroupMap (S' : Subgroup (Q ⧸ Subgroup.center Q))).isCyclic.mpr hmapcyc
  exact ⟨hZ, F, hFf, hFfin, hF, ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eS⟩⟩

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem ff_data_sl2 (hA21 : AsA21SQTKSection) (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K) {F : Type} [Field F] [Finite F]
    (eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
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
    InternalSec.QSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I))
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) ∧
    IsSimpleGroup ↥(autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ∧
    Nonempty (↥(autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
    (∀ v : Sec (⊤ : Subgroup ↥(subM V₁ (conjClosure I H) I))
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)), v ^ 2 = 1) ∧
    IsFFModule (autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hT := A6L32.autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  have hLs := A6L32.autIH_le_stabSub_of hF hIU hV₁I hKH hKI'
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  have hB4 := lred3_b4Hyp hA21 hD hMp hO2
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have hL'S : IsSimpleGroup ↥(autIH V₁ I H K) := e3.symm.isSimpleGroup
  have hLnc : ¬ autIH V₁ I H K ≤ centSub (subM V₁ (conjClosure I H) I) := by
    intro hle
    apply ne_of_lt hirr'.1.2.2.2.1
    ext w
    constructor
    · exact fun h => h.1
    · intro hw
      refine ⟨hw, fun a => ?_⟩
      have ha : (a : MulAut _) ∈ autIH V₁ I H K := hMp ▸ a.2
      exact hle ha w hw
  have hfaith := inf_centSub_eq_bot_of_isSimpleGroup hL'S hLs hLnc
  let e2 := autSubEquivOfFaithful hLs hfaith
  let e1 := B5.secEquiv _ (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  let eLs := e1.symm.trans (e2.symm.trans (e3.symm.trans eK))
  have hsimp : IsSimpleGroup ↥(autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
        (subM V₁ (conjClosure I H) I))) :=
    (e1.symm.trans (e2.symm.trans e3.symm)).isSimpleGroup
  have hexp : ∀ v : Sec (⊤ : Subgroup ↥(subM V₁ (conjClosure I H) I))
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  have hFF1 : IsFFModule (autSec (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
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
  exact ⟨hB4, hQS, hsimp, ⟨eLs⟩, hexp, isFFModule_autSec_top hFF1⟩

theorem ff_cases_sl2 (hA21 : AsA21SQTKSection) (h42 : AsB42)
    (hF10 : Vol2.Ch10.SecA.Facts10_1) (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hFn : Nat.card F = 2 ^ n)
    (eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hFF : IsFFModule (autSec (autIH V₁ I H K ⊔ autIH V₁ I H T) (subM V₁ (conjClosure I H) I)
      (fixV (autIH V₁ I H (conjClosure K T))))) :
    (∃ m, 2 ≤ m ∧ BinaryNaturalSL (autSec (autSub (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ⊤ ⊥ 2 m) ∨
      AlternatingNatural (autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ⊤ ⊥ 5 := by
  obtain ⟨hB4, -, hsimp, ⟨eLs⟩, hexp, hFF2⟩ :=
    ff_data_sl2 hA21 hSQ hF hK₀ eK hS' hV₁I hIU hirrT hTI hFF
  have hsh : Vol2.Ch10.SecA.IsShapeGroup ↥(autSec (autSub (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
        (subM V₁ (conjClosure I H) I))) :=
    Or.inl ⟨n, hn, F, inferInstance, inferInstance, hFn, ⟨eLs⟩⟩
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF2
  have hc := h42 _ hexp _ _ hB4 A hA
  rcases Vol2.Ch10.SecA.b42_of_isShapeGroup hF10 hexp hB4 hA hc hsh with h | h | h
  · exact Or.inl h
  · exfalso
    have h168 := card_eq_of_binaryNaturalSL h (by norm_num)
    have hcard : Nat.card ↥(autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
      Nat.card_congr eLs.toEquiv
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hFn] at hcard
    have e3 : ∏ j ∈ Finset.Icc 2 3, (2 ^ j - 1) = 21 := by decide
    have e2 : ∀ q : ℕ, ∏ j ∈ Finset.Icc 2 2, (q ^ j - 1) = q ^ 2 - 1 := fun q => by
      rw [Finset.Icc_self, Finset.prod_singleton]
    rw [e3] at h168
    rw [e2] at hcard
    norm_num at hcard h168
    rw [hcard] at h168
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    generalize 2 ^ n = q at hq h168
    rcases Nat.lt_or_ge q 6 with hlt | hge
    · interval_cases q <;> omega
    · have h1 : 35 ≤ q ^ 2 - 1 := by
        have : 36 ≤ q ^ 2 := by nlinarith
        omega
      have : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hge h1
      omega
  · exact Or.inr h

end A6S20

namespace Setting4

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

end Setting4

end CFSG.Quasithin.H13.A6
