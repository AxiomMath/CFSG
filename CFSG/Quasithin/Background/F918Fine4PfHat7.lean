module

public import CFSG.Quasithin.Background.F918Fine4PfCore
public import CFSG.Quasithin.Background.SmithB45Exc3A7
public import CFSG.Quasithin.Background.F918Fine4PfIrr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F918Fine4Pf

section Module

theorem isIrrOn_of_isIrrSec {U : Type} [CommGroup U] {L : Subgroup (MulAut U)}
    (h : XMod.IsIrrSec ↥L (⊥ : Subgroup U) ⊤) : Setup.X1.IsIrrOn L := by
  refine ⟨?_, fun J hJ => h.2 J (fun l v hv => ?_) bot_le le_top⟩
  · obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt h.1
    exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩
  · have h2 : l • v = (l : MulAut U) v := by simp [Subgroup.smul_def, MulAut.smul_def]
    rw [h2]
    exact hJ l l.2 v hv

private theorem sec_sq_eq_one_pf {Y : Type} [CommGroup Y] (hY : ∀ y : Y, y ^ 2 = 1)
    (A C : Subgroup Y) : ∀ q : Sec A C, q ^ 2 = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, show a ^ 2 = 1 from Subtype.ext (by simpa using hY a),
      QuotientGroup.mk_one]

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem false_of_hatMod_alt7 {Q : Type} [Group Q] (hM : HatMod M Mp T L V Q)
    (hQ : IsHat Q ↥(alternatingGroup (Fin 7))) : False := by
  obtain ⟨hD, hMp, hT, hq, -, -, ⟨e⟩⟩ := hM
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQS := lred3_qsec hD.hyp hMp hO2
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one_pf hexp ⊤ _
  let e₃ := B5.secEquiv (autSub L V) (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  obtain ⟨hqL, hZ3, ⟨eA⟩⟩ := IsHat.of_mulEquiv (e.symm.trans e₃) hQ
  have hqs := lred3_qOf_autSec hD hMp hT hq
  obtain ⟨E, hE2, -, hEr⟩ := kq_le_iff.mp hqs
  have hle := (rAV_le_two_iff hsv hE2).mp hEr
  have hEN : E ≤ Subgroup.normalizer
      ((autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V) : Subgroup _) : Set _) := by
    intro y hy
    have hyX := hE2.1 hy
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => hQS.normal_autSec y hyX l hl, fun hl => ?_⟩
    have := hQS.normal_autSec y⁻¹ (inv_mem hyX) _ hl
    simpa [mul_assoc] using this
  have hZL : Subgroup.center ↥(autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hZ3
    omega
  have hlt := B45Exc.threeA7Exclusion2F_holds _ (fun w => by rw [← pow_two]; exact hsv w) _ E
    hqL (isIrrOn_of_isIrrSec hQS.isIrrSec_autSec) ⟨eA⟩ hZL hEN hE2.2.1 hE2.2.2
  omega

end Module

section Group

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem card_of_isHat_alt7 {Q : Type} [Group Q] [Finite Q]
    (hQ : IsHat Q ↥(alternatingGroup (Fin 7))) : Nat.card Q = 7560 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hQ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hZ,
    Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
  norm_num [Nat.factorial]

theorem not_isHat_alt7 (h310 : D310) (h391 : D391) (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hK : conjClosure K T = K) :
    ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 7)) := by
  intro hHat
  have hcard := card_of_isHat_alt7 hHat
  have hq := hHat.1
  have hZ3 := hHat.2.1
  have hZ : Subgroup.center ↥(autIH V₁ Vp H K) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨I, hV₁I, hIU, ⟨W, hW, hirr⟩, hfpf⟩ := exists_irrPlus_fixFree h hK hZ
  obtain ⟨-, hcore⟩ :=
    hatCore_of h hH hK h310 h391 hV₁I hIU W hW hirr hfpf hq hZ3 (Or.inl hcard)
  have := factElem h hIU
  exact false_of_hatMod_alt7 hcore.1 hHat

end Group

end F918Fine4Pf

end CFSG.Quasithin
